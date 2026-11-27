//! libzstd's compression C API, as an unverified adapter over the proven
//! compressor.
//!
//! Every frame comes from `compress::compress_exec`, which is proven to
//! give a frame that the specification decodes back to its input. This
//! file only maps the C API onto it: parameters, the destination buffer,
//! and streaming.
//!
//! Streaming collects input and compresses it a frame at a time: a frame
//! is made when `ZSTD_e_flush` or `ZSTD_e_end` asks for one, or when the
//! input collected reaches eight windows. A stream is then a series of
//! whole frames, which every zstd decoder decodes to the concatenated
//! input.
//!
//! Symbols are exported as `vzstd_*`, or under libzstd's names with the
//! `zstd-abi-compress` feature.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::capi::{
    err, Bounds, InBuffer, OutBuffer, ERR_DST_SIZE_TOO_SMALL, ERR_PARAMETER_OUT_OF_BOUND, ERR_PARAMETER_UNSUPPORTED,
    ERR_SRC_SIZE_WRONG, ERR_STAGE_WRONG, RESET_SESSION,
};
use crate::compress::{compress_exec, Params, IN_MAX};
use crate::enc::level_params;
use core::ffi::{c_int, c_ulonglong, c_void};

/// libzstd's default level (`ZSTD_CLEVEL_DEFAULT`).
const LEVEL_DEFAULT: c_int = 3;
const LEVEL_MAX: c_int = 22;
/// libzstd's lowest (fastest) level, `-ZSTD_TARGETLENGTH_MAX`.
const LEVEL_MIN: c_int = -(1 << 17);
const BLOCK_MAX: usize = 131072;

/// `ZSTD_cParameter` values.
const C_LEVEL: c_int = 100;
const C_WINDOWLOG: c_int = 101;
const C_HASHLOG: c_int = 102;
const C_CHAINLOG: c_int = 103;
const C_SEARCHLOG: c_int = 104;
const C_MINMATCH: c_int = 105;
const C_TARGETLENGTH: c_int = 106;
const C_STRATEGY: c_int = 107;
const C_LDM: c_int = 160;
const C_LDM_HASHLOG: c_int = 161;
const C_LDM_MINMATCH: c_int = 162;
const C_LDM_BUCKETSIZELOG: c_int = 163;
const C_LDM_HASHRATELOG: c_int = 164;
const C_CONTENTSIZE: c_int = 200;
const C_CHECKSUM: c_int = 201;
const C_DICTID: c_int = 202;
const C_NBWORKERS: c_int = 400;
const C_JOBSIZE: c_int = 401;
const C_OVERLAPLOG: c_int = 402;

/// `ZSTD_EndDirective`.
const E_CONTINUE: c_int = 0;
const E_FLUSH: c_int = 1;
const E_END: c_int = 2;

/// A compression context, also the streaming state.
pub struct CCtx {
    level: c_int,
    /// 0: the level's window.
    wlog: u32,
    checksum: bool,
    /// Input collected for the next frame.
    inbuf: Vec<u8>,
    /// Compressed output not yet handed out, from `outpos`.
    out: Vec<u8>,
    outpos: usize,
    /// A frame was made in this session (so `ZSTD_e_end` with no input
    /// needs no empty frame).
    framed: bool,
    /// The input size pledged for this session, if any.
    pledged: Option<u64>,
    /// Input taken in this session.
    taken: u64,
    /// `ZSTD_e_end` was given and its frame is being handed out.
    ending: bool,
}

impl CCtx {
    fn new() -> CCtx {
        CCtx {
            level: LEVEL_DEFAULT,
            wlog: 0,
            checksum: false,
            inbuf: Vec::new(),
            out: Vec::new(),
            outpos: 0,
            framed: false,
            pledged: None,
            taken: 0,
            ending: false,
        }
    }

    fn reset_session(&mut self) {
        self.inbuf = Vec::new();
        self.out = Vec::new();
        self.outpos = 0;
        self.framed = false;
        self.pledged = None;
        self.taken = 0;
        self.ending = false;
    }

    fn reset_params(&mut self) {
        self.level = LEVEL_DEFAULT;
        self.wlog = 0;
        self.checksum = false;
    }

    /// A session is under way: parameters can no longer change.
    fn busy(&self) -> bool {
        self.taken > 0 || self.outpos < self.out.len() || self.ending
    }

    fn params(&self) -> Params {
        let level = clamp_level(self.level);
        let wlog = if self.wlog == 0 { level_params(level).0 } else { self.wlog };
        Params { wlog, checksum: self.checksum, level }
    }

    /// The input collected that makes a frame by itself.
    fn frame_size(&self) -> usize {
        let w = self.params().wlog.min(26);
        (8usize << w).max(1 << 20)
    }

    /// Compresses the collected input into one frame.
    fn make_frame(&mut self) {
        let f = compress_exec(&self.inbuf, self.params());
        if self.outpos == self.out.len() {
            self.out = f;
            self.outpos = 0;
        } else {
            self.out.extend_from_slice(&f);
        }
        self.inbuf.clear();
        self.framed = true;
    }

    /// Hands out compressed output; the bytes left to hand out.
    unsafe fn drain(&mut self, o: &mut OutBuffer) -> usize {
        let left = self.out.len() - self.outpos;
        let room = o.size - o.pos;
        let k = left.min(room);
        if k > 0 {
            core::ptr::copy_nonoverlapping(self.out.as_ptr().add(self.outpos), (o.dst as *mut u8).add(o.pos), k);
            o.pos += k;
            self.outpos += k;
        }
        if self.outpos == self.out.len() && !self.out.is_empty() {
            self.out.clear();
            self.outpos = 0;
        }
        left - k
    }
}

/// The level to compress at: 0 is the default, negative levels are
/// level 1, and levels above 22 are 22.
fn clamp_level(l: c_int) -> i32 {
    if l == 0 {
        LEVEL_DEFAULT
    } else if l < 1 {
        1
    } else if l > LEVEL_MAX {
        LEVEL_MAX
    } else {
        l
    }
}

/// libzstd's `ZSTD_COMPRESSBOUND`. Every frame `compress_exec` makes fits:
/// a block is stored raw (its size plus 3) unless compressing it is smaller.
const fn bound(n: usize) -> usize {
    n + (n >> 8) + if n < BLOCK_MAX { (BLOCK_MAX - n) >> 11 } else { 0 }
}

unsafe fn slice<'a>(p: *const c_void, n: usize) -> &'a [u8] {
    if n == 0 || p.is_null() { &[] } else { core::slice::from_raw_parts(p as *const u8, n) }
}

/// One-shot compression of `src` into `dst`.
unsafe fn compress_into(dst: *mut c_void, cap: usize, src: &[u8], p: Params) -> usize {
    if src.len() > IN_MAX {
        return err(ERR_SRC_SIZE_WRONG);
    }
    let f = compress_exec(src, p);
    if f.len() > cap {
        return err(ERR_DST_SIZE_TOO_SMALL);
    }
    core::ptr::copy_nonoverlapping(f.as_ptr(), dst as *mut u8, f.len());
    f.len()
}

macro_rules! export {
    ($zstd:literal, $vz:literal, $(#[$m:meta])* fn $name:ident($($a:ident: $t:ty),*) -> $r:ty $body:block) => {
        $(#[$m])*
        #[cfg_attr(feature = "zstd-abi-compress", unsafe(export_name = $zstd))]
        #[cfg_attr(not(feature = "zstd-abi-compress"), unsafe(export_name = $vz))]
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

export! {"ZSTD_compressBound", "vzstd_compressBound",
    /// # Safety
    /// Always safe.
    fn zstd_compress_bound(n: usize) -> usize {
        if n > IN_MAX { err(ERR_SRC_SIZE_WRONG) } else { bound(n) }
    }
}

export! {"ZSTD_compress", "vzstd_compress",
    /// # Safety
    /// `dst` and `src` must be valid for `cap` and `n` bytes.
    fn zstd_compress(dst: *mut c_void, cap: usize, src: *const c_void, n: usize, level: c_int) -> usize {
        let mut c = CCtx::new();
        c.level = level;
        compress_into(dst, cap, slice(src, n), c.params())
    }
}

export! {"ZSTD_maxCLevel", "vzstd_maxCLevel",
    /// # Safety
    /// Always safe.
    fn zstd_max_clevel() -> c_int {
        LEVEL_MAX
    }
}

export! {"ZSTD_minCLevel", "vzstd_minCLevel",
    /// # Safety
    /// Always safe.
    fn zstd_min_clevel() -> c_int {
        LEVEL_MIN
    }
}

export! {"ZSTD_defaultCLevel", "vzstd_defaultCLevel",
    /// # Safety
    /// Always safe.
    fn zstd_default_clevel() -> c_int {
        LEVEL_DEFAULT
    }
}

export! {"ZSTD_createCCtx", "vzstd_createCCtx",
    /// # Safety
    /// Always safe; free the result with `ZSTD_freeCCtx`.
    fn zstd_create_cctx() -> *mut CCtx {
        Box::into_raw(Box::new(CCtx::new()))
    }
}

export! {"ZSTD_freeCCtx", "vzstd_freeCCtx",
    /// # Safety
    /// `cctx` must come from `ZSTD_createCCtx` (or be null), once.
    fn zstd_free_cctx(cctx: *mut CCtx) -> usize {
        if !cctx.is_null() {
            drop(Box::from_raw(cctx));
        }
        0
    }
}

export! {"ZSTD_createCStream", "vzstd_createCStream",
    /// # Safety
    /// Always safe; free the result with `ZSTD_freeCStream`.
    fn zstd_create_cstream() -> *mut CCtx {
        zstd_create_cctx()
    }
}

export! {"ZSTD_freeCStream", "vzstd_freeCStream",
    /// # Safety
    /// As `ZSTD_freeCCtx`.
    fn zstd_free_cstream(cctx: *mut CCtx) -> usize {
        zstd_free_cctx(cctx)
    }
}

export! {"ZSTD_sizeof_CCtx", "vzstd_sizeof_CCtx",
    /// # Safety
    /// `cctx` must be a live context or null.
    fn zstd_sizeof_cctx(cctx: *const CCtx) -> usize {
        match cctx.as_ref() {
            None => 0,
            Some(c) => core::mem::size_of::<CCtx>() + c.inbuf.capacity() + c.out.capacity(),
        }
    }
}

export! {"ZSTD_compressCCtx", "vzstd_compressCCtx",
    /// # Safety
    /// As `ZSTD_compress`; `cctx` must be a live context.
    fn zstd_compress_cctx(cctx: *mut CCtx, dst: *mut c_void, cap: usize, src: *const c_void, n: usize, level: c_int) -> usize {
        let c = &mut *cctx;
        c.reset_session();
        // As libzstd: the level given, the context's other parameters.
        let mut p = c.params();
        p.level = clamp_level(level);
        if c.wlog == 0 {
            p.wlog = level_params(p.level).0;
        }
        compress_into(dst, cap, slice(src, n), p)
    }
}

export! {"ZSTD_compress2", "vzstd_compress2",
    /// # Safety
    /// As `ZSTD_compress`; `cctx` must be a live context.
    fn zstd_compress2(cctx: *mut CCtx, dst: *mut c_void, cap: usize, src: *const c_void, n: usize) -> usize {
        let c = &mut *cctx;
        c.reset_session();
        compress_into(dst, cap, slice(src, n), c.params())
    }
}

/// The range of a parameter, or `None` if it is not one.
fn param_bounds(p: c_int) -> Option<(c_int, c_int)> {
    Some(match p {
        C_LEVEL => (LEVEL_MIN, LEVEL_MAX),
        C_WINDOWLOG => (10, if cfg!(target_pointer_width = "64") { 31 } else { 30 }),
        C_HASHLOG => (6, 30),
        C_CHAINLOG => (6, 30),
        C_SEARCHLOG => (1, 30),
        C_MINMATCH => (3, 7),
        C_TARGETLENGTH => (0, 1 << 17),
        C_STRATEGY => (1, 9),
        C_LDM => (0, 2),
        C_LDM_HASHLOG => (6, 30),
        C_LDM_MINMATCH => (4, 4096),
        C_LDM_BUCKETSIZELOG => (1, 8),
        C_LDM_HASHRATELOG => (0, 25),
        C_CONTENTSIZE | C_CHECKSUM | C_DICTID => (0, 1),
        C_NBWORKERS => (0, 200),
        C_JOBSIZE => (0, if cfg!(target_pointer_width = "64") { 1 << 30 } else { 1 << 29 }),
        C_OVERLAPLOG => (0, 9),
        _ => return None,
    })
}

export! {"ZSTD_cParam_getBounds", "vzstd_cParam_getBounds",
    /// # Safety
    /// Always safe.
    fn zstd_cparam_get_bounds(p: c_int) -> Bounds {
        match param_bounds(p) {
            Some((lower, upper)) => Bounds { error: 0, lower, upper },
            None => Bounds { error: err(ERR_PARAMETER_UNSUPPORTED), lower: 0, upper: 0 },
        }
    }
}

export! {"ZSTD_CCtx_setParameter", "vzstd_CCtx_setParameter",
    /// # Safety
    /// `cctx` must be a live context.
    ///
    /// The level, window log and checksum flag are used. The content size
    /// is always written and no dictionary ID is (there is no dictionary),
    /// worker threads do not apply, and the fine-grained match finder
    /// parameters are taken and left to the level.
    fn zstd_cctx_set_parameter(cctx: *mut CCtx, p: c_int, v: c_int) -> usize {
        let c = &mut *cctx;
        if c.busy() {
            return err(ERR_STAGE_WRONG);
        }
        let Some((lo, hi)) = param_bounds(p) else { return err(ERR_PARAMETER_UNSUPPORTED) };
        // 0 means "default" for every parameter but the flags.
        if v != 0 && (v < lo || v > hi) {
            return err(ERR_PARAMETER_OUT_OF_BOUND);
        }
        match p {
            C_LEVEL => c.level = if v == 0 { LEVEL_DEFAULT } else { v },
            C_WINDOWLOG => c.wlog = v as u32,
            C_CHECKSUM => c.checksum = v != 0,
            _ => {},
        }
        0
    }
}

export! {"ZSTD_CCtx_getParameter", "vzstd_CCtx_getParameter",
    /// # Safety
    /// `cctx` must be a live context and `v` valid for a write.
    fn zstd_cctx_get_parameter(cctx: *const CCtx, p: c_int, v: *mut c_int) -> usize {
        let c = &*cctx;
        if param_bounds(p).is_none() {
            return err(ERR_PARAMETER_UNSUPPORTED);
        }
        *v = match p {
            C_LEVEL => c.level,
            C_WINDOWLOG => c.wlog as c_int,
            C_CHECKSUM => c.checksum as c_int,
            C_CONTENTSIZE => 1,
            _ => 0,
        };
        0
    }
}

export! {"ZSTD_CCtx_setPledgedSrcSize", "vzstd_CCtx_setPledgedSrcSize",
    /// # Safety
    /// `cctx` must be a live context.
    fn zstd_cctx_set_pledged_src_size(cctx: *mut CCtx, n: c_ulonglong) -> usize {
        let c = &mut *cctx;
        if c.busy() {
            return err(ERR_STAGE_WRONG);
        }
        c.pledged = if n == u64::MAX { None } else { Some(n) };
        0
    }
}

export! {"ZSTD_CCtx_reset", "vzstd_CCtx_reset",
    /// # Safety
    /// `cctx` must be a live context.
    fn zstd_cctx_reset(cctx: *mut CCtx, how: c_int) -> usize {
        let c = &mut *cctx;
        match how {
            RESET_SESSION => c.reset_session(),
            2 => {
                if c.busy() {
                    return err(ERR_STAGE_WRONG);
                }
                c.reset_params();
            },
            3 => {
                c.reset_session();
                c.reset_params();
            },
            _ => return err(ERR_PARAMETER_OUT_OF_BOUND),
        }
        0
    }
}

export! {"ZSTD_initCStream", "vzstd_initCStream",
    /// # Safety
    /// `cctx` must be a live context.
    fn zstd_init_cstream(cctx: *mut CCtx, level: c_int) -> usize {
        let c = &mut *cctx;
        c.reset_session();
        c.level = level;
        0
    }
}

export! {"ZSTD_CStreamInSize", "vzstd_CStreamInSize",
    /// # Safety
    /// Always safe.
    fn zstd_cstream_in_size() -> usize {
        BLOCK_MAX
    }
}

export! {"ZSTD_CStreamOutSize", "vzstd_CStreamOutSize",
    /// # Safety
    /// Always safe.
    fn zstd_cstream_out_size() -> usize {
        bound(BLOCK_MAX) + 3 + 4
    }
}

export! {"ZSTD_compressStream2", "vzstd_compressStream2",
    /// # Safety
    /// `cctx` must be a live context; `output` and `input` must describe
    /// valid buffers.
    fn zstd_compress_stream2(cctx: *mut CCtx, output: *mut OutBuffer, input: *mut InBuffer, end: c_int) -> usize {
        let c = &mut *cctx;
        let o = &mut *output;
        let i = &mut *input;
        if o.pos > o.size || i.pos > i.size || !(E_CONTINUE..=E_END).contains(&end) {
            return err(ERR_PARAMETER_OUT_OF_BOUND);
        }
        if c.ending && (end != E_END || i.pos < i.size) {
            // libzstd: no new input or other directive until the frame is out.
            return err(ERR_STAGE_WRONG);
        }
        // Hand out what is ready first, so the buffer kept stays small.
        let mut left = c.drain(o);
        // Take the input.
        let mut src = slice(i.src, i.size - i.pos);
        while !src.is_empty() {
            let fs = c.frame_size();
            let k = (fs - c.inbuf.len()).min(src.len());
            c.inbuf.extend_from_slice(&src[..k]);
            i.pos += k;
            c.taken += k as u64;
            src = &src[k..];
            if c.inbuf.len() >= fs {
                c.make_frame();
                left = c.drain(o);
                if left > 0 {
                    // Stop taking input until the output is handed out.
                    break;
                }
            }
        }
        if let Some(p) = c.pledged {
            if c.taken > p || (end == E_END && i.pos == i.size && c.taken != p) {
                return err(ERR_SRC_SIZE_WRONG);
            }
        }
        if (end == E_FLUSH || end == E_END) && i.pos == i.size {
            if !c.inbuf.is_empty() || (end == E_END && !c.framed && !c.ending) {
                c.make_frame();
            }
            if end == E_END {
                c.ending = true;
            }
            left = c.drain(o);
            if end == E_END && left == 0 {
                // The frame is out: the next call starts a new session.
                let (lvl, w, ck) = (c.level, c.wlog, c.checksum);
                c.reset_session();
                c.level = lvl;
                c.wlog = w;
                c.checksum = ck;
            }
            return left;
        }
        if left > 0 { left } else { BLOCK_MAX }
    }
}

export! {"ZSTD_compressStream2_simpleArgs", "vzstd_compressStream2_simpleArgs",
    /// # Safety
    /// As `ZSTD_compressStream2`, with `dst_pos` and `src_pos` valid for
    /// reads and writes.
    fn zstd_compress_stream2_simple_args(cctx: *mut CCtx, dst: *mut c_void, cap: usize, dst_pos: *mut usize, src: *const c_void, n: usize, src_pos: *mut usize, end: c_int) -> usize {
        let mut o = OutBuffer { dst, size: cap, pos: *dst_pos };
        let mut i = InBuffer { src, size: n, pos: *src_pos };
        let r = zstd_compress_stream2(cctx, &mut o, &mut i, end);
        *dst_pos = o.pos;
        *src_pos = i.pos;
        r
    }
}

export! {"ZSTD_compressStream", "vzstd_compressStream",
    /// # Safety
    /// As `ZSTD_compressStream2`.
    fn zstd_compress_stream(cctx: *mut CCtx, output: *mut OutBuffer, input: *mut InBuffer) -> usize {
        let r = zstd_compress_stream2(cctx, output, input, E_CONTINUE);
        if crate::capi::is_error(r) { r } else { BLOCK_MAX }
    }
}

export! {"ZSTD_flushStream", "vzstd_flushStream",
    /// # Safety
    /// As `ZSTD_compressStream2`.
    fn zstd_flush_stream(cctx: *mut CCtx, output: *mut OutBuffer) -> usize {
        let mut i = InBuffer { src: core::ptr::null(), size: 0, pos: 0 };
        zstd_compress_stream2(cctx, output, &mut i, E_FLUSH)
    }
}

export! {"ZSTD_endStream", "vzstd_endStream",
    /// # Safety
    /// As `ZSTD_compressStream2`.
    fn zstd_end_stream(cctx: *mut CCtx, output: *mut OutBuffer) -> usize {
        let mut i = InBuffer { src: core::ptr::null(), size: 0, pos: 0 };
        zstd_compress_stream2(cctx, output, &mut i, E_END)
    }
}

/// The compressor's C ABI on arbitrary bytes, for the fuzz target and
/// `tests/compress.rs`: the first four bytes pick the level, window,
/// checksum and the streaming piece sizes; the rest is the input. Every
/// frame, one-shot and streamed, must decode back to the input.
pub fn exercise(data: &[u8]) {
    if data.len() < 4 {
        return;
    }
    let (opt, src) = data.split_at(4);
    let level = (opt[0] % 24) as c_int - 1;
    let wlog = if opt[1] & 0x80 != 0 { 10 + (opt[1] & 15) as c_int } else { 0 };
    let checksum = (opt[2] & 1) as c_int;
    let piece = 1 + opt[3] as usize * 31;
    let limit = 1 << 30;
    unsafe {
        let c = zstd_create_cctx();
        zstd_cctx_set_parameter(c, C_LEVEL, level);
        zstd_cctx_set_parameter(c, C_WINDOWLOG, wlog);
        zstd_cctx_set_parameter(c, C_CHECKSUM, checksum);
        // One-shot, into exactly the bound and into too little room.
        let cap = zstd_compress_bound(src.len());
        let mut dst = vec![0u8; cap];
        let n = zstd_compress2(c, dst.as_mut_ptr() as *mut c_void, cap, src.as_ptr() as *const c_void, src.len());
        assert!(!crate::capi::is_error(n) && n <= cap);
        assert_eq!(crate::frame::decompress_exec(&dst[..n], limit).as_deref(), Ok(src));
        let small = zstd_compress2(c, dst.as_mut_ptr() as *mut c_void, n - 1, src.as_ptr() as *const c_void, src.len());
        assert_eq!(small, err(ERR_DST_SIZE_TOO_SMALL));
        // Streaming in pieces, with a flush every third piece.
        let mut out = Vec::new();
        let mut buf = vec![0u8; piece];
        let mut ip = 0;
        let mut k = 0;
        loop {
            let take = piece.min(src.len() - ip);
            let end = if ip + take == src.len() { E_END } else if k % 3 == 2 { E_FLUSH } else { E_CONTINUE };
            let mut i = InBuffer { src: src[ip..].as_ptr() as *const c_void, size: take, pos: 0 };
            loop {
                let mut o = OutBuffer { dst: buf.as_mut_ptr() as *mut c_void, size: piece, pos: 0 };
                let left = zstd_compress_stream2(c, &mut o, &mut i, end);
                assert!(!crate::capi::is_error(left));
                out.extend_from_slice(&buf[..o.pos]);
                if i.pos == i.size && (end == E_CONTINUE || left == 0) {
                    break;
                }
            }
            ip += take;
            k += 1;
            if end == E_END {
                break;
            }
        }
        assert_eq!(crate::frame::decompress_exec(&out, limit).as_deref(), Ok(src));
        zstd_free_cctx(c);
    }
}
