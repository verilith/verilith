//! libzstd's decompression C API, as an unverified adapter over the proven
//! decoder.
//!
//! One-shot calls (`ZSTD_decompress`, `ZSTD_decompressDCtx`) run the proven
//! `frame::decompress_exec` on the whole input; streaming
//! (`ZSTD_decompressStream`) runs the proven `stream::Stream::stream` on the
//! caller's buffers. This file only maps the C API onto those and their
//! results onto libzstd's error codes.
//!
//! With a dictionary (`ZSTD_decompress_usingDict`, `..._usingDDict`,
//! `ZSTD_DCtx_loadDictionary`, `refPrefix`, `refDDict`), one-shot calls run
//! the proven `dict::DictDecoder::decompress`, and streaming hands the
//! dictionary to the proven stream (`stream::Stream::set_dict`).
//!
//! Symbols are exported as `vzstd_*`, or under libzstd's names with the
//! `zstd-abi` feature. `zstd-abi` exports only the decompression side, so
//! that libzstd's compressor can be linked alongside; `zstd-abi-common`
//! adds the functions libzstd keeps in `common/` (`ZSTD_isError`,
//! `ZSTD_getErrorName`, ...), for builds with no libzstd at all.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::dict::{DictDecoder, DICT_LIMIT, DICT_MAX};
use crate::frame::*;
use crate::seq::MAX_LIMIT;
use crate::stream::{Fail, Stream};
use core::ffi::{c_char, c_int, c_uint, c_ulonglong, c_void};
use vstd::prelude::Ghost;

// ---------------------------------------------------------------------------
// Errors (zstd_errors.h)
// ---------------------------------------------------------------------------

pub const ERR_GENERIC: usize = 1;
pub const ERR_PREFIX_UNKNOWN: usize = 10;
pub const ERR_FRAME_PARAMETER_UNSUPPORTED: usize = 14;
pub const ERR_WINDOW_TOO_LARGE: usize = 16;
pub const ERR_CORRUPTION: usize = 20;
pub const ERR_CHECKSUM: usize = 22;
pub const ERR_DICTIONARY_CORRUPTED: usize = 30;
pub const ERR_DICTIONARY_WRONG: usize = 32;
pub const ERR_PARAMETER_UNSUPPORTED: usize = 40;
pub const ERR_PARAMETER_OUT_OF_BOUND: usize = 42;
pub const ERR_STAGE_WRONG: usize = 60;
pub const ERR_MEMORY: usize = 64;
pub const ERR_DST_SIZE_TOO_SMALL: usize = 70;
pub const ERR_SRC_SIZE_WRONG: usize = 72;
pub const ERR_DST_BUFFER_NULL: usize = 74;
pub const ERR_MAX_CODE: usize = 120;

const fn err(code: usize) -> usize {
    code.wrapping_neg()
}

fn is_error(r: usize) -> bool {
    r > err(ERR_MAX_CODE)
}

fn error_code(r: usize) -> usize {
    if is_error(r) {
        r.wrapping_neg()
    } else {
        0
    }
}

fn error_name(code: usize) -> &'static [u8] {
    match code {
        0 => b"No error detected\0",
        ERR_GENERIC => b"Error (generic)\0",
        ERR_PREFIX_UNKNOWN => b"Unknown frame descriptor\0",
        ERR_FRAME_PARAMETER_UNSUPPORTED => b"Unsupported frame parameter\0",
        ERR_WINDOW_TOO_LARGE => b"Frame requires too much memory for decoding\0",
        ERR_CORRUPTION => b"Data corruption detected\0",
        ERR_CHECKSUM => b"Restored data doesn't match checksum\0",
        ERR_DICTIONARY_CORRUPTED => b"Dictionary is corrupted\0",
        ERR_DICTIONARY_WRONG => b"Dictionary mismatch\0",
        ERR_STAGE_WRONG => b"Operation not authorized at current processing stage\0",
        ERR_PARAMETER_UNSUPPORTED => b"Unsupported parameter\0",
        ERR_PARAMETER_OUT_OF_BOUND => b"Parameter is out of bound\0",
        ERR_MEMORY => b"Allocation error : not enough memory\0",
        ERR_DST_SIZE_TOO_SMALL => b"Destination buffer is too small\0",
        ERR_SRC_SIZE_WRONG => b"Src size is incorrect\0",
        ERR_DST_BUFFER_NULL => b"Operation on NULL destination buffer\0",
        _ => b"Unspecified error code\0",
    }
}

// ---------------------------------------------------------------------------
// Frame layout (no decoding: sizes and positions only)
// ---------------------------------------------------------------------------

const MAGIC: u32 = 0xFD2F_B528;
const BLOCK_MAX: usize = 131072;
pub const CONTENTSIZE_UNKNOWN: u64 = u64::MAX;
pub const CONTENTSIZE_ERROR: u64 = u64::MAX - 1;
/// Matches the limit `decompress_exec` and `block_exec` are proven for.
const LIMIT: usize = MAX_LIMIT;
/// libzstd's default `ZSTD_d_windowLogMax`.
const WINDOWLOG_DEFAULT: u32 = 27;
const WINDOWLOG_MAX: u32 = 31;

fn le32(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
}

fn is_skippable(m: u32) -> bool {
    m >> 4 == 0x184D2A5
}

/// The size of the frame header (magic included) whose first five bytes
/// are at the start of `b`.
fn header_size(fhd: u8) -> usize {
    let single = fhd & 0x20 != 0;
    let did = [0, 1, 2, 4][(fhd & 3) as usize];
    let fcs = [if single { 1 } else { 0 }, 2, 4, 8][(fhd >> 6) as usize];
    4 + 1 + (!single as usize) + did + fcs
}

/// The frame header of the frame at the start of `b`, or the error code.
fn read_header(b: &[u8]) -> Result<Hdr, usize> {
    if b.len() < 5 {
        return Err(ERR_SRC_SIZE_WRONG);
    }
    if le32(b, 0) != MAGIC {
        return Err(ERR_PREFIX_UNKNOWN);
    }
    if b.len() < header_size(b[4]) {
        return Err(ERR_SRC_SIZE_WRONG);
    }
    if b[4] & 0x08 != 0 {
        return Err(ERR_FRAME_PARAMETER_UNSUPPORTED);
    }
    match frame_header_exec(&b[4..]) {
        Some(h) => Ok(h),
        None => Err(ERR_WINDOW_TOO_LARGE),
    }
}

/// The compressed size of the first frame (zstd or skippable) of `b`.
fn frame_size(b: &[u8]) -> Result<usize, usize> {
    if b.len() >= 8 && is_skippable(le32(b, 0)) {
        let n = le32(b, 4) as usize;
        if n.checked_add(8).map_or(true, |t| t > b.len() || n > u32::MAX as usize - 8) {
            return Err(ERR_SRC_SIZE_WRONG);
        }
        return Ok(8 + n);
    }
    let h = read_header(b)?;
    let mut p = 4 + h.size;
    loop {
        if b.len() - p < 3 {
            return Err(ERR_SRC_SIZE_WRONG);
        }
        let bh = b[p] as usize | (b[p + 1] as usize) << 8 | (b[p + 2] as usize) << 16;
        let (last, ty, size) = (bh & 1 == 1, (bh >> 1) & 3, bh >> 3);
        p += 3;
        let body = match ty {
            0 | 2 => size,
            1 => 1,
            _ => return Err(ERR_CORRUPTION),
        };
        if b.len() - p < body {
            return Err(ERR_SRC_SIZE_WRONG);
        }
        p += body;
        if last {
            break;
        }
    }
    if h.checksum {
        if b.len() - p < 4 {
            return Err(ERR_SRC_SIZE_WRONG);
        }
        p += 4;
    }
    Ok(p)
}

/// Why the proven decoder rejected `b` (with `cap` bytes of room), as
/// the libzstd error code libzstd would give, as far as it can be told
/// apart: layout errors first, frame by frame, then corruption.
fn classify(b: &[u8], cap: usize) -> usize {
    let mut i = 0;
    let mut room = cap;
    while i < b.len() {
        let rest = &b[i..];
        if rest.len() >= 4 && is_skippable(le32(rest, 0)) {
            match frame_size(rest) {
                Err(e) => return e,
                Ok(n) => {
                    i += n;
                    continue;
                },
            }
        }
        if rest.len() < 5 {
            return if rest.len() >= 4 && le32(rest, 0) != MAGIC { ERR_PREFIX_UNKNOWN } else { ERR_SRC_SIZE_WRONG };
        }
        let h = match read_header(rest) {
            Err(e) => return e,
            Ok(h) => h,
        };
        if h.dict_id != 0 {
            return ERR_DICTIONARY_WRONG;
        }
        let n = match frame_size(rest) {
            Ok(n) => n,
            Err(ERR_SRC_SIZE_WRONG) if h.checksum => {
                // libzstd decodes the blocks before it misses the checksum.
                let mut g = rest.to_vec();
                g[4] &= !0x04;
                return match frame_size(&g) {
                    Ok(_) => ERR_CHECKSUM,
                    Err(e) => e,
                };
            },
            Err(e) => return e,
        };
        match decompress_exec(&rest[..n], room) {
            Ok(v) => room -= v.len(),
            Err(Error::TooLarge) => return ERR_DST_SIZE_TOO_SMALL,
            Err(Error::Corrupt) => return checksum_or_corrupt(&rest[..n]),
        }
        i += n;
    }
    ERR_CORRUPTION
}

/// A single frame the decoder rejected: is it only the checksum?
fn checksum_or_corrupt(f: &[u8]) -> usize {
    let Ok(h) = read_header(f) else { return ERR_CORRUPTION };
    if !h.checksum {
        return ERR_CORRUPTION;
    }
    // Same frame with the checksum flag cleared and the checksum dropped.
    let mut g = f[..f.len() - 4].to_vec();
    g[4] &= !0x04;
    match decompress_exec(&g, LIMIT) {
        Ok(_) => ERR_CHECKSUM,
        Err(_) => ERR_CORRUPTION,
    }
}

unsafe fn slice<'a>(p: *const c_void, n: usize) -> &'a [u8] {
    if n == 0 || p.is_null() {
        &[]
    } else {
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

/// One-shot decompression of all frames of `src` into `dst`.
fn decompress_into(dst: *mut c_void, cap: usize, src: &[u8]) -> usize {
    if src.is_empty() {
        return err(ERR_SRC_SIZE_WRONG);
    }
    match decompress_exec(src, cap.min(LIMIT)) {
        Ok(v) => {
            if !v.is_empty() {
                if dst.is_null() {
                    return err(ERR_DST_BUFFER_NULL);
                }
                unsafe { core::ptr::copy_nonoverlapping(v.as_ptr(), dst as *mut u8, v.len()) };
            }
            v.len()
        },
        Err(Error::TooLarge) => err(ERR_DST_SIZE_TOO_SMALL),
        Err(Error::Corrupt) => err(classify(src, cap.min(LIMIT))),
    }
}

/// Why the proven decoder rejected `b` with a dictionary whose ID is `id`:
/// a frame that names another dictionary, a layout error, or corruption.
fn classify_dict(b: &[u8], dd: DictDecoder) -> (DictDecoder, usize) {
    let id = dd.id() as u64;
    let mut i = 0;
    while i < b.len() {
        let rest = &b[i..];
        if !(rest.len() >= 4 && is_skippable(le32(rest, 0))) {
            match read_header(rest) {
                Err(e) => return (dd, e),
                Ok(h) if h.dict_id != 0 && h.dict_id != id => return (dd, ERR_DICTIONARY_WRONG),
                Ok(_) => {},
            }
        }
        match frame_size(rest) {
            Ok(n) => i += n,
            Err(e) => return (dd, e),
        }
    }
    // One frame with a checksum: is it only the checksum?
    if let (Ok(h), Ok(n)) = (read_header(b), frame_size(b)) {
        if h.checksum && n == b.len() {
            let mut g = b[..b.len() - 4].to_vec();
            g[4] &= !0x04;
            let (dd, r) = dd.decompress(&g, DICT_LIMIT);
            return (dd, if r.is_ok() { ERR_CHECKSUM } else { ERR_CORRUPTION });
        }
    }
    (dd, ERR_CORRUPTION)
}

/// One-shot decompression of all frames of `src` into `dst`, with the
/// dictionary `dd` for every frame.
fn decompress_into_dict(dst: *mut c_void, cap: usize, src: &[u8], dd: DictDecoder) -> (DictDecoder, usize) {
    if src.is_empty() {
        return (dd, err(ERR_SRC_SIZE_WRONG));
    }
    let (dd, r) = dd.decompress(src, cap.min(DICT_LIMIT));
    match r {
        Ok(v) => {
            if !v.is_empty() {
                if dst.is_null() {
                    return (dd, err(ERR_DST_BUFFER_NULL));
                }
                unsafe { core::ptr::copy_nonoverlapping(v.as_ptr(), dst as *mut u8, v.len()) };
            }
            (dd, v.len())
        },
        Err(Error::TooLarge) => (dd, err(ERR_DST_SIZE_TOO_SMALL)),
        Err(Error::Corrupt) => {
            let (dd, e) = classify_dict(src, dd);
            (dd, err(e))
        },
    }
}

/// A dictionary from the caller's bytes, as `ZSTD_dct_auto` reads it.
unsafe fn load(dict: *const c_void, n: usize) -> Result<Option<DictDecoder>, usize> {
    if n == 0 || dict.is_null() {
        return Ok(None);
    }
    if n >= DICT_MAX {
        return Err(ERR_MEMORY);
    }
    match DictDecoder::load(slice(dict, n)) {
        Some(d) => Ok(Some(d)),
        None => Err(ERR_DICTIONARY_CORRUPTED),
    }
}

/// `ZSTD_DDict`: a loaded dictionary, read-only once made. Each context
/// that uses it keeps its own copy (`DictDecoder` keeps a buffer it writes
/// to), made once and recognised again by `serial`.
pub struct DDictH {
    serial: u64,
    d: DictDecoder,
}

static SERIAL: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(1);

// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

pub struct DCtx {
    s: Stream,
    wlog_max: u32,
    /// The dictionary for every frame (`ZSTD_DCtx_loadDictionary`,
    /// `ZSTD_DCtx_refDDict`).
    dict: Option<DictDecoder>,
    /// A prefix for the next decompression only (`ZSTD_DCtx_refPrefix`).
    prefix: Option<DictDecoder>,
    /// Bumped whenever `dict` or `prefix` is set, so the stream can tell
    /// whether the dictionary it holds is still the one asked for.
    generation: u64,
    /// The generation of the dictionary the stream holds (0: none).
    installed: u64,
    /// The copy of the last `ZSTD_DDict` used with this context, by serial.
    cache: Option<(u64, DictDecoder)>,
    /// No frame is under way in streaming.
    at_start: bool,
}

impl DCtx {
    fn new() -> DCtx {
        DCtx {
            s: Stream::new((1 << WINDOWLOG_DEFAULT) + 1),
            wlog_max: WINDOWLOG_DEFAULT,
            dict: None,
            prefix: None,
            generation: 0,
            installed: 0,
            cache: None,
            at_start: true,
        }
    }

    fn reset_session(&mut self) {
        self.s.reset();
        self.at_start = true;
    }

    /// The dictionary or prefix asked for has changed.
    fn changed(&mut self) {
        self.generation += 1;
    }

    /// The context's copy of `h`.
    fn ddict(&mut self, h: &DDictH) -> DictDecoder {
        match self.cache.take() {
            Some((serial, d)) if serial == h.serial => d,
            _ => h.d.copy(),
        }
    }

    fn set_max_window(&mut self, w: u64) {
        self.s.max_window = w;
    }

    /// The streaming step: 0 at the end of a frame (all output handed
    /// out), an error code, or a hint of the input still wanted. At the
    /// start of a frame the proven stream is given the dictionary for it:
    /// a prefix (used for this frame only), the loaded dictionary, or none.
    fn stream(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> usize {
        if self.at_start {
            if let Some(p) = self.prefix.take() {
                self.s.set_dict(&p);
                // A prefix is used once: the next frame gets the dictionary
                // again (or none), so it is not the generation held.
                self.installed = u64::MAX;
            } else {
                let want = if self.dict.is_some() { self.generation } else { 0 };
                if want != self.installed {
                    match &self.dict {
                        Some(d) => self.s.set_dict(d),
                        None => self.s.clear_dict(),
                    }
                    self.installed = want;
                }
            }
        }
        let r = self.stream_plain(out, opos, inp, ipos);
        self.at_start = r == 0;
        r
    }

    fn stream_plain(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> usize {
        match self.s.stream(out, opos, inp, ipos) {
            Ok(n) => n,
            Err(f) => err(match f {
                Fail::Prefix => ERR_PREFIX_UNKNOWN,
                Fail::Param => ERR_FRAME_PARAMETER_UNSUPPORTED,
                Fail::Header => ERR_WINDOW_TOO_LARGE,
                Fail::Dict => ERR_DICTIONARY_WRONG,
                Fail::Window => ERR_WINDOW_TOO_LARGE,
                Fail::Corrupt => ERR_CORRUPTION,
                Fail::Checksum => ERR_CHECKSUM,
                Fail::Limit => ERR_WINDOW_TOO_LARGE,
            }),
        }
    }
}

#[repr(C)]
pub struct InBuffer {
    pub src: *const c_void,
    pub size: usize,
    pub pos: usize,
}

#[repr(C)]
pub struct OutBuffer {
    pub dst: *mut c_void,
    pub size: usize,
    pub pos: usize,
}

// ---------------------------------------------------------------------------
// Exports
// ---------------------------------------------------------------------------

macro_rules! export {
    ($zstd:literal, $vz:literal, $(#[$m:meta])* fn $name:ident($($a:ident: $t:ty),*) -> $r:ty $body:block) => {
        $(#[$m])*
        #[cfg_attr(feature = "zstd-abi", unsafe(export_name = $zstd))]
        #[cfg_attr(not(feature = "zstd-abi"), unsafe(export_name = $vz))]
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

macro_rules! export_common {
    ($zstd:literal, $vz:literal, $(#[$m:meta])* fn $name:ident($($a:ident: $t:ty),*) -> $r:ty $body:block) => {
        $(#[$m])*
        #[cfg_attr(feature = "zstd-abi-common", unsafe(export_name = $zstd))]
        #[cfg_attr(not(feature = "zstd-abi-common"), unsafe(export_name = $vz))]
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

export! {"ZSTD_decompress", "vzstd_decompress",
    /// # Safety
    /// `dst` and `src` must be valid for `cap` and `n` bytes.
    fn zstd_decompress(dst: *mut c_void, cap: usize, src: *const c_void, n: usize) -> usize {
        decompress_into(dst, cap, slice(src, n))
    }
}

export! {"ZSTD_decompressDCtx", "vzstd_decompressDCtx",
    /// # Safety
    /// As `ZSTD_decompress`; `dctx` must come from `ZSTD_createDCtx`.
    fn zstd_decompress_dctx(dctx: *mut DCtx, dst: *mut c_void, cap: usize, src: *const c_void, n: usize) -> usize {
        let Some(d) = dctx.as_mut() else {
            return decompress_into(dst, cap, slice(src, n));
        };
        // A prefix is used for this call only; a loaded dictionary stays.
        if let Some(p) = d.prefix.take() {
            return decompress_into_dict(dst, cap, slice(src, n), p).1;
        }
        match d.dict.take() {
            Some(dd) => {
                let (dd, r) = decompress_into_dict(dst, cap, slice(src, n), dd);
                d.dict = Some(dd);
                r
            },
            None => decompress_into(dst, cap, slice(src, n)),
        }
    }
}

export! {"ZSTD_getFrameContentSize", "vzstd_getFrameContentSize",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_get_frame_content_size(src: *const c_void, n: usize) -> c_ulonglong {
        let b = slice(src, n);
        if b.len() >= 4 && is_skippable(le32(b, 0)) {
            return if b.len() >= 8 { 0 } else { CONTENTSIZE_ERROR };
        }
        match read_header(b) {
            Ok(h) => h.fcs.unwrap_or(CONTENTSIZE_UNKNOWN),
            Err(_) => CONTENTSIZE_ERROR,
        }
    }
}

export! {"ZSTD_getDecompressedSize", "vzstd_getDecompressedSize",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_get_decompressed_size(src: *const c_void, n: usize) -> c_ulonglong {
        let r = zstd_get_frame_content_size(src, n);
        if r >= CONTENTSIZE_ERROR { 0 } else { r }
    }
}

export! {"ZSTD_findFrameCompressedSize", "vzstd_findFrameCompressedSize",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_find_frame_compressed_size(src: *const c_void, n: usize) -> usize {
        match frame_size(slice(src, n)) {
            Ok(n) => n,
            Err(e) => err(e),
        }
    }
}

export! {"ZSTD_decompressBound", "vzstd_decompressBound",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_decompress_bound(src: *const c_void, n: usize) -> c_ulonglong {
        let b = slice(src, n);
        let mut i = 0;
        let mut total: u64 = 0;
        while i < b.len() {
            let Ok(size) = frame_size(&b[i..]) else { return CONTENTSIZE_ERROR };
            if !is_skippable(le32(b, i)) {
                let Ok(h) = read_header(&b[i..]) else { return CONTENTSIZE_ERROR };
                let add = match h.fcs {
                    Some(f) => f,
                    None => {
                        // Each block holds at most one block maximum.
                        let mut p = i + 4 + h.size;
                        let mut blocks = 0u64;
                        loop {
                            let bh = b[p] as usize | (b[p + 1] as usize) << 8 | (b[p + 2] as usize) << 16;
                            blocks += 1;
                            p += 3 + if (bh >> 1) & 3 == 1 { 1 } else { bh >> 3 };
                            if bh & 1 == 1 {
                                break;
                            }
                        }
                        blocks * (h.window.min(BLOCK_MAX as u64))
                    },
                };
                total = total.saturating_add(add);
            }
            i += size;
        }
        total
    }
}

export! {"ZSTD_getDictID_fromFrame", "vzstd_getDictID_fromFrame",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_get_dict_id_from_frame(src: *const c_void, n: usize) -> c_uint {
        match read_header(slice(src, n)) {
            Ok(h) => h.dict_id as c_uint,
            Err(_) => 0,
        }
    }
}

export! {"ZSTD_isFrame", "vzstd_isFrame",
    /// # Safety
    /// `src` must be valid for `n` bytes.
    fn zstd_is_frame(src: *const c_void, n: usize) -> c_uint {
        let b = slice(src, n);
        (b.len() >= 4 && (le32(b, 0) == MAGIC || is_skippable(le32(b, 0)))) as c_uint
    }
}

export! {"ZSTD_createDCtx", "vzstd_createDCtx",
    /// # Safety
    /// Always safe; free the result with `ZSTD_freeDCtx`.
    fn zstd_create_dctx() -> *mut DCtx {
        Box::into_raw(Box::new(DCtx::new()))
    }
}

export! {"ZSTD_freeDCtx", "vzstd_freeDCtx",
    /// # Safety
    /// `dctx` must come from `ZSTD_createDCtx` (or be null), once.
    fn zstd_free_dctx(dctx: *mut DCtx) -> usize {
        if !dctx.is_null() {
            drop(Box::from_raw(dctx));
        }
        0
    }
}

export! {"ZSTD_createDStream", "vzstd_createDStream",
    /// # Safety
    /// Always safe; free the result with `ZSTD_freeDStream`.
    fn zstd_create_dstream() -> *mut DCtx {
        zstd_create_dctx()
    }
}

export! {"ZSTD_freeDStream", "vzstd_freeDStream",
    /// # Safety
    /// As `ZSTD_freeDCtx`.
    fn zstd_free_dstream(dctx: *mut DCtx) -> usize {
        zstd_free_dctx(dctx)
    }
}

export! {"ZSTD_initDStream", "vzstd_initDStream",
    /// # Safety
    /// `dctx` must be a live context.
    fn zstd_init_dstream(dctx: *mut DCtx) -> usize {
        (*dctx).reset_session();
        5
    }
}

export! {"ZSTD_DStreamInSize", "vzstd_DStreamInSize",
    /// # Safety
    /// Always safe.
    fn zstd_dstream_in_size() -> usize {
        BLOCK_MAX + 3
    }
}

export! {"ZSTD_DStreamOutSize", "vzstd_DStreamOutSize",
    /// # Safety
    /// Always safe.
    fn zstd_dstream_out_size() -> usize {
        BLOCK_MAX
    }
}

export! {"ZSTD_sizeof_DCtx", "vzstd_sizeof_DCtx",
    /// # Safety
    /// `dctx` must be a live context or null.
    fn zstd_sizeof_dctx(dctx: *const DCtx) -> usize {
        if dctx.is_null() {
            return 0;
        }
        let d = &*dctx;
        core::mem::size_of::<DCtx>() + d.s.unit.capacity() + d.s.dec.out.capacity() + d.s.dec.lits.capacity()
    }
}

/// `ZSTD_reset_session_only`, `ZSTD_reset_parameters`, `ZSTD_reset_session_and_parameters`.
pub const RESET_SESSION: c_int = 1;
const RESET_PARAMETERS: c_int = 2;
const RESET_BOTH: c_int = 3;
/// `ZSTD_d_windowLogMax`.
pub const D_WINDOWLOG_MAX: c_int = 100;
/// `ZSTD_d_format` (`ZSTD_d_experimentalParam1`): only `ZSTD_f_zstd1`.
const D_FORMAT: c_int = 1000;

export! {"ZSTD_DCtx_reset", "vzstd_DCtx_reset",
    /// # Safety
    /// `dctx` must be a live context.
    fn zstd_dctx_reset(dctx: *mut DCtx, how: c_int) -> usize {
        let d = &mut *dctx;
        match how {
            RESET_SESSION => d.reset_session(),
            RESET_PARAMETERS | RESET_BOTH => {
                d.reset_session();
                d.dict = None;
                d.prefix = None;
                d.changed();
                d.wlog_max = WINDOWLOG_DEFAULT;
                d.set_max_window((1 << WINDOWLOG_DEFAULT) + 1);
            },
            _ => return err(ERR_PARAMETER_OUT_OF_BOUND),
        }
        0
    }
}

#[repr(C)]
pub struct Bounds {
    pub error: usize,
    pub lower: c_int,
    pub upper: c_int,
}

export! {"ZSTD_dParam_getBounds", "vzstd_dParam_getBounds",
    /// # Safety
    /// Always safe.
    fn zstd_dparam_get_bounds(p: c_int) -> Bounds {
        match p {
            D_WINDOWLOG_MAX => Bounds { error: 0, lower: 10, upper: WINDOWLOG_MAX as c_int },
            D_FORMAT => Bounds { error: 0, lower: 0, upper: 0 },
            _ => Bounds { error: err(ERR_PARAMETER_UNSUPPORTED), lower: 0, upper: 0 },
        }
    }
}

export! {"ZSTD_DCtx_setParameter", "vzstd_DCtx_setParameter",
    /// # Safety
    /// `dctx` must be a live context.
    fn zstd_dctx_set_parameter(dctx: *mut DCtx, p: c_int, v: c_int) -> usize {
        let d = &mut *dctx;
        match p {
            D_WINDOWLOG_MAX => {
                let v = if v == 0 { WINDOWLOG_DEFAULT as c_int } else { v };
                if !(10..=WINDOWLOG_MAX as c_int).contains(&v) {
                    return err(ERR_PARAMETER_OUT_OF_BOUND);
                }
                d.wlog_max = v as u32;
                d.set_max_window(1 << v);
                0
            },
            D_FORMAT => {
                if v != 0 {
                    return err(ERR_PARAMETER_OUT_OF_BOUND);
                }
                0
            },
            _ => err(ERR_PARAMETER_UNSUPPORTED),
        }
    }
}

export! {"ZSTD_DCtx_getParameter", "vzstd_DCtx_getParameter",
    /// # Safety
    /// `dctx` must be a live context and `v` writable.
    fn zstd_dctx_get_parameter(dctx: *mut DCtx, p: c_int, v: *mut c_int) -> usize {
        match p {
            D_WINDOWLOG_MAX => {
                *v = (*dctx).wlog_max as c_int;
                0
            },
            D_FORMAT => {
                *v = 0;
                0
            },
            _ => err(ERR_PARAMETER_UNSUPPORTED),
        }
    }
}

export! {"ZSTD_DCtx_setMaxWindowSize", "vzstd_DCtx_setMaxWindowSize",
    /// # Safety
    /// `dctx` must be a live context.
    fn zstd_dctx_set_max_window_size(dctx: *mut DCtx, max: usize) -> usize {
        // The smallest window log that holds `max`.
        let mut wlog = 10;
        while wlog < WINDOWLOG_MAX && (1usize << wlog) < max {
            wlog += 1;
        }
        if max > 1usize << WINDOWLOG_MAX {
            return err(ERR_PARAMETER_OUT_OF_BOUND);
        }
        (*dctx).wlog_max = wlog;
        (*dctx).set_max_window(max as u64);
        0
    }
}

export! {"ZSTD_DCtx_loadDictionary", "vzstd_DCtx_loadDictionary",
    /// # Safety
    /// `dctx` must be a live context; `dict` valid for `n` bytes. The
    /// dictionary is copied: it is used for every frame until it is
    /// replaced or the parameters are reset. An empty one clears it.
    fn zstd_dctx_load_dictionary(dctx: *mut DCtx, dict: *const c_void, n: usize) -> usize {
        let d = &mut *dctx;
        if !d.at_start {
            return err(ERR_STAGE_WRONG);
        }
        d.prefix = None;
        d.changed();
        match load(dict, n) {
            Ok(dd) => {
                d.dict = dd;
                0
            },
            Err(e) => {
                d.dict = None;
                err(e)
            },
        }
    }
}

export! {"ZSTD_DCtx_loadDictionary_byReference", "vzstd_DCtx_loadDictionary_byReference",
    /// # Safety
    /// As `ZSTD_DCtx_loadDictionary` (which this is: the content is
    /// copied all the same).
    fn zstd_dctx_load_dictionary_by_reference(dctx: *mut DCtx, dict: *const c_void, n: usize) -> usize {
        zstd_dctx_load_dictionary(dctx, dict, n)
    }
}

export! {"ZSTD_DCtx_refPrefix", "vzstd_DCtx_refPrefix",
    /// # Safety
    /// `dctx` must be a live context; `prefix` valid for `n` bytes. The
    /// prefix is raw content, for the next decompression only.
    fn zstd_dctx_ref_prefix(dctx: *mut DCtx, prefix: *const c_void, n: usize) -> usize {
        let d = &mut *dctx;
        if !d.at_start {
            return err(ERR_STAGE_WRONG);
        }
        d.dict = None;
        d.changed();
        if n == 0 || prefix.is_null() {
            d.prefix = None;
            return 0;
        }
        if n >= DICT_MAX {
            return err(ERR_MEMORY);
        }
        d.prefix = Some(DictDecoder::raw(slice(prefix, n)));
        0
    }
}

export! {"ZSTD_DCtx_refDDict", "vzstd_DCtx_refDDict",
    /// # Safety
    /// `dctx` must be a live context; `ddict` null or from
    /// `ZSTD_createDDict`. The context keeps its own copy.
    fn zstd_dctx_ref_ddict(dctx: *mut DCtx, ddict: *const DDictH) -> usize {
        let d = &mut *dctx;
        if !d.at_start {
            return err(ERR_STAGE_WRONG);
        }
        d.prefix = None;
        d.changed();
        d.dict = ddict.as_ref().map(|h| h.d.copy());
        0
    }
}

export! {"ZSTD_decompress_usingDict", "vzstd_decompress_usingDict",
    /// # Safety
    /// As `ZSTD_decompressDCtx`; `dict` valid for `dict_size` bytes.
    fn zstd_decompress_using_dict(dctx: *mut DCtx, dst: *mut c_void, cap: usize, src: *const c_void, n: usize, dict: *const c_void, dict_size: usize) -> usize {
        let _ = dctx;
        match load(dict, dict_size) {
            Ok(Some(dd)) => decompress_into_dict(dst, cap, slice(src, n), dd).1,
            Ok(None) => decompress_into(dst, cap, slice(src, n)),
            Err(e) => err(e),
        }
    }
}

export! {"ZSTD_createDDict", "vzstd_createDDict",
    /// # Safety
    /// `dict` valid for `n` bytes. Null if the dictionary is corrupted.
    fn zstd_create_ddict(dict: *const c_void, n: usize) -> *mut DDictH {
        let d = match load(dict, n) {
            Ok(Some(d)) => d,
            Ok(None) => DictDecoder::raw(&[]),
            Err(_) => return core::ptr::null_mut(),
        };
        let serial = SERIAL.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        Box::into_raw(Box::new(DDictH { serial, d }))
    }
}

export! {"ZSTD_createDDict_byReference", "vzstd_createDDict_byReference",
    /// # Safety
    /// As `ZSTD_createDDict` (the content is copied all the same).
    fn zstd_create_ddict_by_reference(dict: *const c_void, n: usize) -> *mut DDictH {
        zstd_create_ddict(dict, n)
    }
}

export! {"ZSTD_freeDDict", "vzstd_freeDDict",
    /// # Safety
    /// `ddict` from `ZSTD_createDDict` (or null), once.
    fn zstd_free_ddict(ddict: *mut DDictH) -> usize {
        if !ddict.is_null() {
            drop(Box::from_raw(ddict));
        }
        0
    }
}

export! {"ZSTD_sizeof_DDict", "vzstd_sizeof_DDict",
    /// # Safety
    /// `ddict` from `ZSTD_createDDict` (or null).
    fn zstd_sizeof_ddict(ddict: *const DDictH) -> usize {
        match ddict.as_ref() {
            Some(h) => core::mem::size_of::<DDictH>() + h.d.content_len(),
            None => 0,
        }
    }
}

export! {"ZSTD_getDictID_fromDDict", "vzstd_getDictID_fromDDict",
    /// # Safety
    /// `ddict` from `ZSTD_createDDict` (or null).
    fn zstd_get_dict_id_from_ddict(ddict: *const DDictH) -> c_uint {
        match ddict.as_ref() {
            Some(h) => h.d.id(),
            None => 0,
        }
    }
}

export! {"ZSTD_getDictID_fromDict", "vzstd_getDictID_fromDict",
    /// # Safety
    /// `dict` valid for `n` bytes.
    fn zstd_get_dict_id_from_dict(dict: *const c_void, n: usize) -> c_uint {
        let b = slice(dict, n);
        if b.len() < 8 || le32(b, 0) != 0xEC30_A437 { 0 } else { le32(b, 4) }
    }
}

export! {"ZSTD_decompress_usingDDict", "vzstd_decompress_usingDDict",
    /// # Safety
    /// As `ZSTD_decompressDCtx`; `ddict` null or from `ZSTD_createDDict`.
    fn zstd_decompress_using_ddict(dctx: *mut DCtx, dst: *mut c_void, cap: usize, src: *const c_void, n: usize, ddict: *const DDictH) -> usize {
        let Some(h) = ddict.as_ref() else {
            return decompress_into(dst, cap, slice(src, n));
        };
        let Some(d) = dctx.as_mut() else {
            return decompress_into_dict(dst, cap, slice(src, n), h.d.copy()).1;
        };
        let dd = d.ddict(h);
        let (dd, r) = decompress_into_dict(dst, cap, slice(src, n), dd);
        d.cache = Some((h.serial, dd));
        r
    }
}

export! {"ZSTD_initDStream_usingDict", "vzstd_initDStream_usingDict",
    /// # Safety
    /// `dctx` must be a live context; `dict` valid for `n` bytes.
    fn zstd_init_dstream_using_dict(dctx: *mut DCtx, dict: *const c_void, n: usize) -> usize {
        (*dctx).reset_session();
        let r = zstd_dctx_load_dictionary(dctx, dict, n);
        if is_error(r) { r } else { zstd_dstream_in_size() }
    }
}

export! {"ZSTD_initDStream_usingDDict", "vzstd_initDStream_usingDDict",
    /// # Safety
    /// `dctx` must be a live context; `ddict` null or from
    /// `ZSTD_createDDict`.
    fn zstd_init_dstream_using_ddict(dctx: *mut DCtx, ddict: *const DDictH) -> usize {
        (*dctx).reset_session();
        let r = zstd_dctx_ref_ddict(dctx, ddict);
        if is_error(r) { r } else { zstd_dstream_in_size() }
    }
}

export! {"ZSTD_decompressStream", "vzstd_decompressStream",
    /// # Safety
    /// `dctx` must be a live context; the buffers must be valid for their
    /// sizes, with `pos <= size`.
    fn zstd_decompress_stream(dctx: *mut DCtx, output: *mut OutBuffer, input: *mut InBuffer) -> usize {
        let d = &mut *dctx;
        let o = &mut *output;
        let i = &mut *input;
        if o.pos > o.size || i.pos > i.size {
            return err(ERR_SRC_SIZE_WRONG);
        }
        if o.size > 0 && o.dst.is_null() {
            return err(ERR_DST_BUFFER_NULL);
        }
        let out: &mut [u8] = if o.size == 0 { &mut [] } else { core::slice::from_raw_parts_mut(o.dst as *mut u8, o.size) };
        let inp = slice(i.src, i.size);
        d.stream(out, &mut o.pos, inp, &mut i.pos)
    }
}

export! {"ZSTD_decompressStream_simpleArgs", "vzstd_decompressStream_simpleArgs",
    /// # Safety
    /// As `ZSTD_decompressStream`, with the positions writable.
    fn zstd_decompress_stream_simple_args(dctx: *mut DCtx, dst: *mut c_void, cap: usize, dpos: *mut usize, src: *const c_void, n: usize, spos: *mut usize) -> usize {
        let mut o = OutBuffer { dst, size: cap, pos: *dpos };
        let mut i = InBuffer { src, size: n, pos: *spos };
        let r = zstd_decompress_stream(dctx, &mut o, &mut i);
        *dpos = o.pos;
        *spos = i.pos;
        r
    }
}

export_common! {"ZSTD_isError", "vzstd_isError",
    /// # Safety
    /// Always safe.
    fn zstd_is_error(code: usize) -> c_uint {
        is_error(code) as c_uint
    }
}

export_common! {"ZSTD_getErrorCode", "vzstd_getErrorCode",
    /// # Safety
    /// Always safe.
    fn zstd_get_error_code(code: usize) -> c_int {
        error_code(code) as c_int
    }
}

export_common! {"ZSTD_getErrorName", "vzstd_getErrorName",
    /// # Safety
    /// Always safe; the result is a static string.
    fn zstd_get_error_name(code: usize) -> *const c_char {
        error_name(error_code(code)).as_ptr() as *const c_char
    }
}

export_common! {"ZSTD_getErrorString", "vzstd_getErrorString",
    /// # Safety
    /// Always safe; the result is a static string.
    fn zstd_get_error_string(code: c_int) -> *const c_char {
        error_name(code as usize).as_ptr() as *const c_char
    }
}

export_common! {"ZSTD_versionNumber", "vzstd_versionNumber",
    /// # Safety
    /// Always safe. Reports the libzstd version whose API this follows.
    fn zstd_version_number() -> c_uint {
        10505
    }
}

export_common! {"ZSTD_versionString", "vzstd_versionString",
    /// # Safety
    /// Always safe.
    fn zstd_version_string() -> *const c_char {
        b"1.5.5\0".as_ptr() as *const c_char
    }
}

/// Runs `data` through every entry point with buffer sizes taken from its
/// first bytes, checking the adapter's own invariants (positions within
/// the buffers, `0` only at a frame end). Used by the fuzz target and
/// `tests/stress.rs`.
pub fn exercise(data: &[u8]) {
    if data.len() < 3 {
        return;
    }
    let (opt, input) = data.split_at(3);
    let cap = opt[0] as usize * 97;
    let mut out = vec![0u8; cap];
    unsafe {
        let p = input.as_ptr() as *const c_void;
        let r = zstd_decompress(out.as_mut_ptr() as *mut c_void, cap, p, input.len());
        assert!(is_error(r) || r <= cap);
        zstd_get_frame_content_size(p, input.len());
        let r = zstd_find_frame_compressed_size(p, input.len());
        assert!(is_error(r) || r <= input.len());
        zstd_decompress_bound(p, input.len());
        zstd_get_dict_id_from_frame(p, input.len());
        let d = zstd_create_dctx();
        zstd_dctx_set_parameter(d, D_WINDOWLOG_MAX, 10 + (opt[1] % 22) as c_int);
        let istep = 1 + opt[1] as usize;
        let ostep = 1 + opt[2] as usize * 13;
        let mut buf = vec![0u8; ostep];
        let mut ip = 0;
        let mut idle = 0;
        for _ in 0..100_000 {
            let n = istep.min(input.len() - ip);
            let mut i = InBuffer { src: input[ip..].as_ptr() as *const c_void, size: n, pos: 0 };
            let mut o = OutBuffer { dst: buf.as_mut_ptr() as *mut c_void, size: ostep, pos: 0 };
            let r = zstd_decompress_stream(d, &mut o, &mut i);
            assert!(i.pos <= n && o.pos <= ostep);
            ip += i.pos;
            if is_error(r) {
                // Stays failed until reset.
                let mut o2 = OutBuffer { dst: buf.as_mut_ptr() as *mut c_void, size: ostep, pos: 0 };
                let mut i2 = InBuffer { src: input.as_ptr() as *const c_void, size: 0, pos: 0 };
                assert!(is_error(zstd_decompress_stream(d, &mut o2, &mut i2)));
                break;
            }
            if i.pos == 0 && o.pos == 0 {
                idle += 1;
                if idle > 2 {
                    break;
                }
            } else {
                idle = 0;
            }
        }
        zstd_dctx_reset(d, RESET_SESSION);
        zstd_free_dctx(d);
    }
}
