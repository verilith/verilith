//! liblz4's C API (`lz4.h` and `lz4frame.h`), as an unverified adapter
//! over the proven compressor and decompressor.
//!
//! Every byte produced comes from a proven function: blocks from
//! `compress::compress_block` and `block::decode_block`, frames from
//! `fcompress::compress` and `frame::decode_frame`. This file turns C
//! pointers into slices, maps preferences and results, and, for
//! `LZ4F_decompress`, collects a frame's bytes before decoding it (see
//! DEPARTURES.md).
//!
//! Symbols are exported as `vlz4_*`, or under liblz4's own names with the
//! `lz4-abi` feature.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::block::decode_block;
use crate::compress::{compress_bound, compress_into, MAX_INPUT};
use crate::fcompress::{compress_into as frame_compress, Prefs};
use crate::frame::{decode_frame, decode_frame_into, read_header, Error, Hdr, MAX_OUT};
use core::ffi::{c_char, c_int, c_uint, c_void};

macro_rules! export {
    ($vz:literal, $lz:literal, fn $name:ident($($a:ident: $t:ty),* $(,)?) -> $r:ty $body:block) => {
        #[cfg_attr(feature = "lz4-abi", unsafe(export_name = $lz))]
        #[cfg_attr(not(feature = "lz4-abi"), unsafe(export_name = $vz))]
        /// # Safety
        /// As the liblz4 function of the same name: pointers must be valid
        /// for the sizes given with them.
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

/// The liblz4 release whose API and behaviour this follows.
pub const VERSION_NUMBER: c_int = 10904;
const VERSION_STRING: &[u8] = b"1.9.4\0";

unsafe fn input<'a>(p: *const c_char, n: usize) -> &'a [u8] {
    if n == 0 || p.is_null() {
        &[]
    } else {
        // SAFETY: the caller gives `n` readable bytes at `p`.
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

unsafe fn output<'a>(p: *mut c_char, n: usize) -> &'a mut [u8] {
    if n == 0 || p.is_null() {
        &mut []
    } else {
        // SAFETY: the caller gives `n` writable bytes at `p`.
        core::slice::from_raw_parts_mut(p as *mut u8, n)
    }
}

// ---------------------------------------------------------------------------
// lz4.h: blocks
// ---------------------------------------------------------------------------

export!("vlz4_versionNumber", "LZ4_versionNumber", fn version_number() -> c_int { VERSION_NUMBER });

export!("vlz4_versionString", "LZ4_versionString", fn version_string() -> *const c_char {
    VERSION_STRING.as_ptr() as *const c_char
});

export!("vlz4_compressBound", "LZ4_compressBound", fn compress_bound_c(n: c_int) -> c_int {
    if n < 0 {
        0
    } else {
        compress_bound(n as usize) as c_int
    }
});

unsafe fn block_compress(src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int, accel: c_int) -> c_int {
    if n < 0 || cap <= 0 || n as usize > MAX_INPUT {
        return 0;
    }
    let s = input(src, n as usize);
    let d = output(dst, cap as usize);
    let a = accel.clamp(1, 65537) as usize;
    match compress_into(s, d, a) {
        Some(m) => m as c_int,
        None => 0,
    }
}

export!("vlz4_compress_default", "LZ4_compress_default", fn compress_default(src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int) -> c_int {
    block_compress(src, dst, n, cap, 1)
});

export!("vlz4_compress_fast", "LZ4_compress_fast", fn compress_fast(src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int, accel: c_int) -> c_int {
    block_compress(src, dst, n, cap, accel)
});

/// liblz4's `LZ4_STREAMSIZE`: callers allocate this much for a state.
const STREAM_SIZE: c_int = 16416;

export!("vlz4_sizeofState", "LZ4_sizeofState", fn sizeof_state() -> c_int { STREAM_SIZE });

// The state is the caller's scratch memory; the table used here lives on
// the stack instead, so it is left alone.
export!("vlz4_compress_fast_extState", "LZ4_compress_fast_extState", fn compress_fast_ext_state(_state: *mut c_void, src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int, accel: c_int) -> c_int {
    block_compress(src, dst, n, cap, accel)
});

export!("vlz4_decompress_safe", "LZ4_decompress_safe", fn decompress_safe(src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int) -> c_int {
    if n < 0 || cap < 0 {
        return -1;
    }
    let s = input(src, n as usize);
    let d = output(dst, cap as usize);
    match decode_block(s, d, 0, 0) {
        Some(m) => m as c_int,
        None => -1,
    }
});

export!("vlz4_decompress_safe_usingDict", "LZ4_decompress_safe_usingDict", fn decompress_safe_using_dict(src: *const c_char, dst: *mut c_char, n: c_int, cap: c_int, dict: *const c_char, dict_size: c_int) -> c_int {
    if n < 0 || cap < 0 || dict_size < 0 {
        return -1;
    }
    let s = input(src, n as usize);
    let d = output(dst, cap as usize);
    if dict_size == 0 {
        return match decode_block(s, d, 0, 0) {
            Some(m) => m as c_int,
            None => -1,
        };
    }
    // Only the last 64 KiB of a dictionary can be reached.
    let whole = input(dict, dict_size as usize);
    let hist = &whole[whole.len().saturating_sub(65536)..];
    let mut buf = Vec::new();
    if buf.try_reserve_exact(hist.len() + d.len()).is_err() {
        return -1;
    }
    buf.extend_from_slice(hist);
    buf.resize(hist.len() + d.len(), 0);
    match decode_block(s, &mut buf, 0, hist.len()) {
        Some(end) => {
            let m = end - hist.len();
            d[..m].copy_from_slice(&buf[hist.len()..end]);
            m as c_int
        }
        None => -1,
    }
});

// ---------------------------------------------------------------------------
// lz4frame.h: errors
// ---------------------------------------------------------------------------

pub const ERR_GENERIC: usize = 1;
pub const ERR_MAX_BLOCK_SIZE_INVALID: usize = 2;
pub const ERR_ALLOCATION_FAILED: usize = 9;
pub const ERR_DST_MAX_SIZE_TOO_SMALL: usize = 11;
pub const ERR_FRAME_HEADER_INCOMPLETE: usize = 12;
pub const ERR_FRAME_TYPE_UNKNOWN: usize = 13;
pub const ERR_SRC_PTR_WRONG: usize = 15;
pub const ERR_DECOMPRESSION_FAILED: usize = 16;
pub const ERR_FRAME_DECODING_ALREADY_STARTED: usize = 19;
pub const ERR_PARAMETER_NULL: usize = 21;
pub const ERR_MAX_CODE: usize = 22;

const NAMES: [&[u8]; 23] = [
    b"OK_NoError\0",
    b"ERROR_GENERIC\0",
    b"ERROR_maxBlockSize_invalid\0",
    b"ERROR_blockMode_invalid\0",
    b"ERROR_contentChecksumFlag_invalid\0",
    b"ERROR_compressionLevel_invalid\0",
    b"ERROR_headerVersion_wrong\0",
    b"ERROR_blockChecksum_invalid\0",
    b"ERROR_reservedFlag_set\0",
    b"ERROR_allocation_failed\0",
    b"ERROR_srcSize_tooLarge\0",
    b"ERROR_dstMaxSize_tooSmall\0",
    b"ERROR_frameHeader_incomplete\0",
    b"ERROR_frameType_unknown\0",
    b"ERROR_frameSize_wrong\0",
    b"ERROR_srcPtr_wrong\0",
    b"ERROR_decompressionFailed\0",
    b"ERROR_headerChecksum_invalid\0",
    b"ERROR_contentChecksum_invalid\0",
    b"ERROR_frameDecoding_alreadyStarted\0",
    b"ERROR_compressionState_uninitialized\0",
    b"ERROR_parameter_null\0",
    b"ERROR_maxCode\0",
];

const fn err(code: usize) -> usize {
    code.wrapping_neg()
}

fn is_error(r: usize) -> bool {
    r > err(ERR_MAX_CODE)
}

export!("vlz4f_isError", "LZ4F_isError", fn f_is_error(code: usize) -> c_uint { is_error(code) as c_uint });

export!("vlz4f_getErrorName", "LZ4F_getErrorName", fn f_get_error_name(code: usize) -> *const c_char {
    let name: &[u8] = if is_error(code) { NAMES[code.wrapping_neg()] } else { b"Unspecified error code\0" };
    name.as_ptr() as *const c_char
});

export!("vlz4f_getErrorCode", "LZ4F_getErrorCode", fn f_get_error_code(code: usize) -> c_int {
    if is_error(code) { code.wrapping_neg() as c_int } else { 0 }
});

export!("vlz4f_getVersion", "LZ4F_getVersion", fn f_get_version() -> c_uint { 100 });

export!("vlz4f_compressionLevel_max", "LZ4F_compressionLevel_max", fn f_compression_level_max() -> c_int { 12 });

// ---------------------------------------------------------------------------
// lz4frame.h: compressing a frame
// ---------------------------------------------------------------------------

/// `LZ4F_frameInfo_t`.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct FrameInfo {
    pub block_size_id: c_uint,
    pub block_mode: c_uint,
    pub content_checksum_flag: c_uint,
    pub frame_type: c_uint,
    pub content_size: u64,
    pub dict_id: c_uint,
    pub block_checksum_flag: c_uint,
}

/// `LZ4F_preferences_t`.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct Preferences {
    pub frame_info: FrameInfo,
    pub compression_level: c_int,
    pub auto_flush: c_uint,
    pub favor_dec_speed: c_uint,
    pub reserved: [c_uint; 3],
}

fn block_size(id: c_uint) -> Option<usize> {
    match id {
        0 | 4 => Some(0x1_0000),
        5 => Some(0x4_0000),
        6 => Some(0x10_0000),
        7 => Some(0x40_0000),
        _ => None,
    }
}

/// Room that is always enough for `n` bytes as one frame.
fn frame_bound(n: usize, p: &Preferences) -> usize {
    let bs = block_size(p.frame_info.block_size_id).unwrap_or(0x1_0000);
    let blocks = n / bs + (n % bs != 0) as usize;
    let per_block = 4 + 4 * (p.frame_info.block_checksum_flag != 0) as usize;
    let tail = 4 + 4 * (p.frame_info.content_checksum_flag != 0) as usize;
    19usize.saturating_add(n).saturating_add(blocks.saturating_mul(per_block)).saturating_add(tail)
}

export!("vlz4f_compressFrameBound", "LZ4F_compressFrameBound", fn f_compress_frame_bound(n: usize, prefs: *const Preferences) -> usize {
    let p = if prefs.is_null() { Preferences::default() } else { *prefs };
    frame_bound(n, &p)
});

export!("vlz4f_compressFrame", "LZ4F_compressFrame", fn f_compress_frame(dst: *mut c_void, cap: usize, src: *const c_void, n: usize, prefs: *const Preferences) -> usize {
    let p = if prefs.is_null() { Preferences::default() } else { *prefs };
    let Some(_) = block_size(p.frame_info.block_size_id) else {
        return err(ERR_MAX_BLOCK_SIZE_INVALID);
    };
    if cap < frame_bound(n, &p) {
        return err(ERR_DST_MAX_SIZE_TOO_SMALL);
    }
    let s = input(src as *const c_char, n);
    // Levels below 0 are liblz4's acceleration. Levels from 3 up ask
    // liblz4 for its slower, stronger compressor, which is not here.
    let accel = if p.compression_level < 0 { (-(p.compression_level as i64) + 1).min(65537) as usize } else { 1 };
    let prefs = Prefs {
        block_id: p.frame_info.block_size_id.max(4) as u8,
        indep: p.frame_info.block_mode != 0,
        bsum: p.frame_info.block_checksum_flag != 0,
        csum: p.frame_info.content_checksum_flag != 0,
        csize: p.frame_info.content_size != 0,
        accel,
    };
    match frame_compress(s, output(dst as *mut c_char, cap), &prefs) {
        Some(m) => m,
        None => err(ERR_DST_MAX_SIZE_TOO_SMALL),
    }
});

// ---------------------------------------------------------------------------
// lz4frame.h: decompressing
// ---------------------------------------------------------------------------

const MAGIC: u32 = 0x184D_2204;

fn is_skippable(m: u32) -> bool {
    m >> 4 == 0x184D_2A5
}

fn le32(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
}

/// Where the collecting of a frame's bytes has got to. Sizes are read
/// here only to know how many bytes to collect; the proven decoder reads
/// them again and is what decides whether the frame is valid.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Stage {
    /// The magic number is not complete.
    Magic,
    /// A skippable frame's size is not complete.
    SkipSize,
    /// A skippable frame's body is not complete.
    SkipBody,
    /// The first 7 bytes of the header are not complete.
    HeaderStart,
    /// The rest of the header is not complete.
    HeaderRest,
    /// A block's size word is not complete.
    BlockSize,
    /// A block's body (and its checksum) is not complete.
    BlockBody,
    /// The content checksum is not complete.
    Checksum,
    /// The frame's content is being handed out.
    Output,
}

/// `LZ4F_dctx`.
pub struct Dctx {
    stage: Stage,
    /// The frame's bytes so far.
    buf: Vec<u8>,
    /// `buf` is wanted up to this length before the next step.
    want: usize,
    hdr: Option<Hdr>,
    /// The decoded content, and how much of it has been handed out.
    out: Vec<u8>,
    given: usize,
}

impl Dctx {
    fn new() -> Dctx {
        Dctx { stage: Stage::Magic, buf: Vec::new(), want: 4, hdr: None, out: Vec::new(), given: 0 }
    }

    /// Back to the start of a frame. The buffers keep their memory, so a
    /// context used for frame after frame does not allocate each time.
    fn reset(&mut self) {
        self.stage = Stage::Magic;
        self.buf.clear();
        self.want = 4;
        self.hdr = None;
        self.out.clear();
        self.given = 0;
    }

    /// The length of the frame at the start of `src`, if all of it is
    /// there: the same walk over the sizes as `collect`, without copying.
    fn whole_frame(src: &[u8]) -> Option<usize> {
        if src.len() < 7 || le32(src, 0) != MAGIC {
            return None;
        }
        let h = read_header(src, 0)?;
        let mut i = h.end;
        loop {
            if src.len() - i < 4 {
                return None;
            }
            let size = (le32(src, i) & 0x7fff_ffff) as usize;
            i += 4;
            if size == 0 {
                let end = i + 4 * h.csum as usize;
                return (end <= src.len()).then_some(end);
            }
            let step = size + 4 * h.bsum as usize;
            if size > h.bmax || src.len() - i < step {
                return None;
            }
            i += step;
        }
    }

    /// Takes bytes from `src` until the frame is complete or `src` runs
    /// out. Gives how many were taken. `Ok(true)`: the frame is complete.
    /// With `header_only`, stops once the header is complete.
    fn collect(&mut self, src: &[u8], header_only: bool) -> Result<(usize, bool), usize> {
        let mut used = 0;
        loop {
            if self.stage == Stage::Output {
                return Ok((used, true));
            }
            if header_only && self.hdr.is_some() {
                return Ok((used, false));
            }
            let take = (self.want - self.buf.len()).min(src.len() - used);
            if self.buf.try_reserve(take).is_err() {
                return Err(ERR_ALLOCATION_FAILED);
            }
            self.buf.extend_from_slice(&src[used..used + take]);
            used += take;
            if self.buf.len() < self.want {
                return Ok((used, false));
            }
            let n = self.buf.len();
            match self.stage {
                Stage::Magic => {
                    let m = le32(&self.buf, 0);
                    if m == MAGIC {
                        self.stage = Stage::HeaderStart;
                        self.want = 7;
                    } else if is_skippable(m) {
                        self.stage = Stage::SkipSize;
                        self.want = 8;
                    } else {
                        return Err(ERR_FRAME_TYPE_UNKNOWN);
                    }
                }
                Stage::SkipSize => {
                    self.stage = Stage::SkipBody;
                    self.want = 8 + le32(&self.buf, 4) as usize;
                    if self.want == 8 {
                        self.stage = Stage::Output;
                    }
                }
                Stage::SkipBody => {
                    self.stage = Stage::Output;
                }
                Stage::HeaderStart => {
                    let flg = self.buf[4];
                    self.stage = Stage::HeaderRest;
                    self.want = 7 + 8 * ((flg >> 3) & 1) as usize + 4 * (flg & 1) as usize;
                    if self.want == 7 {
                        self.header()?;
                    }
                }
                Stage::HeaderRest => {
                    self.header()?;
                }
                Stage::BlockSize => {
                    let h = self.hdr.unwrap();
                    let size = (le32(&self.buf, n - 4) & 0x7fff_ffff) as usize;
                    if size == 0 {
                        if h.csum {
                            self.stage = Stage::Checksum;
                            self.want = n + 4;
                        } else {
                            self.stage = Stage::Output;
                        }
                    } else if size > h.bmax {
                        return Err(ERR_MAX_BLOCK_SIZE_INVALID);
                    } else {
                        self.stage = Stage::BlockBody;
                        self.want = n + size + 4 * h.bsum as usize;
                    }
                }
                Stage::BlockBody => {
                    self.stage = Stage::BlockSize;
                    self.want = n + 4;
                }
                Stage::Checksum => {
                    self.stage = Stage::Output;
                }
                Stage::Output => {}
            }
            if self.stage == Stage::Output {
                self.decode()?;
            }
        }
    }

    /// The header is complete: has the proven reader check it.
    fn header(&mut self) -> Result<(), usize> {
        match read_header(&self.buf, 0) {
            Some(h) if h.end == self.buf.len() => {
                self.hdr = Some(h);
                self.stage = Stage::BlockSize;
                self.want = self.buf.len() + 4;
                Ok(())
            }
            _ => Err(ERR_GENERIC),
        }
    }

    /// The frame is complete: decodes it with the proven decoder.
    fn decode(&mut self) -> Result<(), usize> {
        self.out.clear();
        self.given = 0;
        if self.hdr.is_none() {
            // A skippable frame has no content.
            return Ok(());
        }
        match decode_frame(&self.buf, 0, &mut self.out, MAX_OUT) {
            Ok(end) if end == self.buf.len() => Ok(()),
            Ok(_) => Err(ERR_GENERIC),
            Err(Error::Corrupt) => Err(ERR_DECOMPRESSION_FAILED),
            Err(Error::TooLarge) => Err(ERR_ALLOCATION_FAILED),
        }
    }

    /// How many more bytes the next step needs.
    fn hint(&self) -> usize {
        (self.want - self.buf.len()).max(1)
    }
}

export!("vlz4f_createDecompressionContext", "LZ4F_createDecompressionContext", fn f_create_dctx(out: *mut *mut Dctx, version: c_uint) -> usize {
    if out.is_null() {
        return err(ERR_PARAMETER_NULL);
    }
    if version != 100 {
        *out = core::ptr::null_mut();
        return err(6);
    }
    *out = Box::into_raw(Box::new(Dctx::new()));
    0
});

export!("vlz4f_freeDecompressionContext", "LZ4F_freeDecompressionContext", fn f_free_dctx(d: *mut Dctx) -> usize {
    if !d.is_null() {
        // SAFETY: `d` came from `Box::into_raw` in the create function.
        drop(Box::from_raw(d));
    }
    0
});

export!("vlz4f_resetDecompressionContext", "LZ4F_resetDecompressionContext", fn f_reset_dctx(d: *mut Dctx) -> () {
    if let Some(d) = d.as_mut() {
        d.reset();
    }
});

export!("vlz4f_headerSize", "LZ4F_headerSize", fn f_header_size(src: *const c_void, n: usize) -> usize {
    if src.is_null() {
        return err(ERR_SRC_PTR_WRONG);
    }
    if n < 5 {
        return err(ERR_FRAME_HEADER_INCOMPLETE);
    }
    let s = input(src as *const c_char, n);
    let m = le32(s, 0);
    if is_skippable(m) {
        return 8;
    }
    if m != MAGIC {
        return err(ERR_FRAME_TYPE_UNKNOWN);
    }
    7 + 8 * ((s[4] >> 3) & 1) as usize + 4 * (s[4] & 1) as usize
});

fn info_of(h: &Hdr) -> FrameInfo {
    FrameInfo {
        block_size_id: match h.bmax {
            0x1_0000 => 4,
            0x4_0000 => 5,
            0x10_0000 => 6,
            _ => 7,
        },
        block_mode: h.indep as c_uint,
        content_checksum_flag: h.csum as c_uint,
        frame_type: 0,
        content_size: h.csize.unwrap_or(0),
        dict_id: h.dict.unwrap_or(0),
        block_checksum_flag: h.bsum as c_uint,
    }
}

export!("vlz4f_getFrameInfo", "LZ4F_getFrameInfo", fn f_get_frame_info(d: *mut Dctx, info: *mut FrameInfo, src: *const c_void, n: *mut usize) -> usize {
    let (Some(d), false, false) = (d.as_mut(), info.is_null(), n.is_null()) else {
        return err(ERR_PARAMETER_NULL);
    };
    let avail = *n;
    *n = 0;
    if d.hdr.is_none() {
        if d.stage != Stage::Magic || !d.buf.is_empty() {
            return err(ERR_FRAME_DECODING_ALREADY_STARTED);
        }
        let s = input(src as *const c_char, avail);
        // liblz4 wants the whole header in this one call.
        if s.len() < 5 {
            return err(ERR_FRAME_HEADER_INCOMPLETE);
        }
        if is_skippable(le32(s, 0)) {
            // As liblz4: a skippable frame has no information to give.
            *info = FrameInfo { frame_type: 1, ..FrameInfo::default() };
            return 4;
        }
        if le32(s, 0) != MAGIC {
            return err(ERR_FRAME_TYPE_UNKNOWN);
        }
        let hs = 7 + 8 * ((s[4] >> 3) & 1) as usize + 4 * (s[4] & 1) as usize;
        if s.len() < hs {
            return err(ERR_FRAME_HEADER_INCOMPLETE);
        }
        match d.collect(&s[..hs], true) {
            Ok((used, _)) => *n = used,
            Err(e) => return err(e),
        }
    }
    match &d.hdr {
        Some(h) => {
            *info = info_of(h);
            d.hint()
        }
        None => err(ERR_GENERIC),
    }
});

export!("vlz4f_decompress", "LZ4F_decompress", fn f_decompress(d: *mut Dctx, dst: *mut c_void, dst_size: *mut usize, src: *const c_void, src_size: *mut usize, _options: *const c_void) -> usize {
    let (Some(d), false, false) = (d.as_mut(), dst_size.is_null(), src_size.is_null()) else {
        return err(ERR_PARAMETER_NULL);
    };
    let s = input(src as *const c_char, *src_size);
    let o = output(dst as *mut c_char, *dst_size);
    *src_size = 0;
    *dst_size = 0;
    // A whole frame in one call, at the start of a frame: decode it from
    // the caller's buffer without collecting it first.
    let mut pre = 0;
    if d.stage == Stage::Magic && d.buf.is_empty() {
        if let Some(end) = Dctx::whole_frame(s) {
            // Straight into the caller's buffer if the content fits.
            if let Some((e, n)) = decode_frame_into(&s[..end], 0, o, 0) {
                if e == end {
                    *src_size = end;
                    *dst_size = n;
                    return 0;
                }
            }
            // Not valid, or no room: the decoder with its own buffer says
            // which, and hands the content out in pieces.
            d.out.clear();
            d.given = 0;
            let e = match decode_frame(&s[..end], 0, &mut d.out, MAX_OUT) {
                Ok(e) if e == end => 0,
                Ok(_) => ERR_GENERIC,
                Err(Error::Corrupt) => ERR_DECOMPRESSION_FAILED,
                Err(Error::TooLarge) => ERR_ALLOCATION_FAILED,
            };
            if e != 0 {
                d.reset();
                return err(e);
            }
            pre = end;
            d.stage = Stage::Output;
        }
    }
    let done = match d.collect(&s[pre..], false) {
        Ok((used, done)) => {
            *src_size = pre + used;
            done
        }
        Err(e) => {
            d.reset();
            return err(e);
        }
    };
    if !done {
        return d.hint();
    }
    let give = (d.out.len() - d.given).min(o.len());
    o[..give].copy_from_slice(&d.out[d.given..d.given + give]);
    d.given += give;
    *dst_size = give;
    if d.given == d.out.len() {
        d.reset();
        0
    } else {
        // More content is waiting for room.
        d.out.len() - d.given
    }
});
