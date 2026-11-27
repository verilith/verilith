//! A C ABI compatible with google/brotli's encoder (`brotli/encode.h`).
//!
//! A thin adapter, not verified: pointer checks, parameters and an output
//! queue. All compression happens in the verified `estream::Compressor`
//! (or `compress::compress` for the one-shot call), whose output is proven
//! to decode to its input.
//!
//! Functions are exported as `vbrotli_*`, or under google/brotli's own
//! names with the `brotli-abi` feature.
//!
//! Differences from google/brotli:
//! - `alloc_func`/`free_func` are accepted but not called.
//! - The streaming encoder keeps all of its input in memory until the
//!   instance is destroyed (google/brotli keeps a window).
//! - `BROTLI_PARAM_MODE`, `LGBLOCK`, `DISABLE_LITERAL_CONTEXT_MODELING`,
//!   `SIZE_HINT`, `NPOSTFIX` and `NDIRECT` are accepted and ignored. Large
//!   windows, stream offsets, metadata (`BROTLI_OPERATION_EMIT_METADATA`)
//!   and prepared dictionaries are not supported.
//! - The output differs byte for byte (it is a different compressor).
#![allow(non_snake_case)]
#![allow(unsafe_op_in_unsafe_fn)]
use crate::estream::Compressor;
use std::os::raw::{c_int, c_void};

pub const BROTLI_FALSE: c_int = 0;
pub const BROTLI_TRUE: c_int = 1;

pub const OPERATION_PROCESS: c_int = 0;
pub const OPERATION_FLUSH: c_int = 1;
pub const OPERATION_FINISH: c_int = 2;
pub const OPERATION_EMIT_METADATA: c_int = 3;

pub const PARAM_MODE: c_int = 0;
pub const PARAM_QUALITY: c_int = 1;
pub const PARAM_LGWIN: c_int = 2;
pub const PARAM_LGBLOCK: c_int = 3;
pub const PARAM_DISABLE_LITERAL_CONTEXT_MODELING: c_int = 4;
pub const PARAM_SIZE_HINT: c_int = 5;
pub const PARAM_LARGE_WINDOW: c_int = 6;
pub const PARAM_NPOSTFIX: c_int = 7;
pub const PARAM_NDIRECT: c_int = 8;
pub const PARAM_STREAM_OFFSET: c_int = 9;

pub const DEFAULT_QUALITY: u32 = 11;
pub const DEFAULT_WINDOW: u32 = 22;

/// google/brotli 1.2.0, the version this API follows.
pub const VERSION: u32 = 0x1002000;

/// The encoder instance behind a `BrotliEncoderState*`.
pub struct EncState {
    quality: u32,
    lgwin: u32,
    c: Option<Compressor>,
    /// Output not yet handed to the caller, from `pos`.
    out: Vec<u8>,
    pos: usize,
    total: usize,
    finished: bool,
}

impl EncState {
    fn compressor(&mut self) -> &mut Compressor {
        if self.c.is_none() {
            self.c = Some(Compressor::new(self.quality, self.lgwin));
        }
        self.c.as_mut().unwrap()
    }

    fn queue(&mut self, v: Vec<u8>) {
        if self.pos == self.out.len() {
            self.out = v;
            self.pos = 0;
        } else {
            self.out.extend_from_slice(&v);
        }
    }

    fn pending(&self) -> usize {
        self.out.len() - self.pos
    }
}

/// # Safety
/// As google/brotli's `BrotliEncoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderCreateInstance"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderCreateInstance(
    _alloc: *const c_void,
    _free: *const c_void,
    _opaque: *mut c_void,
) -> *mut EncState {
    Box::into_raw(Box::new(EncState {
        quality: DEFAULT_QUALITY,
        lgwin: DEFAULT_WINDOW,
        c: None,
        out: Vec::new(),
        pos: 0,
        total: 0,
        finished: false,
    }))
}

/// # Safety
/// `state` is null or came from `BrotliEncoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderDestroyInstance"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderDestroyInstance(state: *mut EncState) {
    if !state.is_null() {
        drop(Box::from_raw(state));
    }
}

/// # Safety
/// `state` came from `BrotliEncoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderSetParameter"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderSetParameter(state: *mut EncState, param: c_int, value: u32) -> c_int {
    if state.is_null() {
        return BROTLI_FALSE;
    }
    let s = &mut *state;
    if s.c.is_some() {
        return BROTLI_FALSE;
    }
    match param {
        PARAM_QUALITY => s.quality = value.min(11),
        PARAM_LGWIN => s.lgwin = value.clamp(10, 24),
        PARAM_LARGE_WINDOW | PARAM_STREAM_OFFSET => {
            if value != 0 {
                return BROTLI_FALSE;
            }
        }
        PARAM_MODE | PARAM_LGBLOCK | PARAM_DISABLE_LITERAL_CONTEXT_MODELING | PARAM_SIZE_HINT | PARAM_NPOSTFIX
        | PARAM_NDIRECT => {}
        _ => return BROTLI_FALSE,
    }
    BROTLI_TRUE
}

/// # Safety
/// As google/brotli's `BrotliEncoderCompressStream`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderCompressStream"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderCompressStream(
    state: *mut EncState,
    op: c_int,
    available_in: *mut usize,
    next_in: *mut *const u8,
    available_out: *mut usize,
    next_out: *mut *mut u8,
    total_out: *mut usize,
) -> c_int {
    if state.is_null() || available_in.is_null() || available_out.is_null() {
        return BROTLI_FALSE;
    }
    if (*available_in != 0 && (next_in.is_null() || (*next_in).is_null()))
        || (*available_out != 0 && (next_out.is_null() || (*next_out).is_null()))
    {
        return BROTLI_FALSE;
    }
    let s = &mut *state;
    if !(OPERATION_PROCESS..=OPERATION_FINISH).contains(&op) {
        return BROTLI_FALSE;
    }
    if s.finished && *available_in != 0 {
        return BROTLI_FALSE;
    }
    // Hand out queued output before taking more input.
    if s.pending() == 0 && !s.finished {
        let input: &[u8] = if *available_in == 0 { &[] } else { std::slice::from_raw_parts(*next_in, *available_in) };
        let c = s.compressor();
        c.push(input);
        let v = match op {
            OPERATION_PROCESS => {
                c.compress_pending(false);
                c.take()
            }
            OPERATION_FLUSH => c.flush(),
            _ => {
                let c = s.c.take().unwrap();
                s.finished = true;
                c.finish()
            }
        };
        if *available_in != 0 {
            *next_in = (*next_in).add(*available_in);
            *available_in = 0;
        }
        s.queue(v);
    }
    let k = s.pending().min(*available_out);
    if k > 0 {
        std::ptr::copy_nonoverlapping(s.out.as_ptr().add(s.pos), *next_out, k);
        *next_out = (*next_out).add(k);
        *available_out -= k;
        s.pos += k;
        s.total += k;
    }
    if !total_out.is_null() {
        *total_out = s.total;
    }
    BROTLI_TRUE
}

/// # Safety
/// `state` came from `BrotliEncoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderIsFinished"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderIsFinished(state: *const EncState) -> c_int {
    if !state.is_null() && (*state).finished && (*state).pending() == 0 { BROTLI_TRUE } else { BROTLI_FALSE }
}

/// # Safety
/// `state` came from `BrotliEncoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderHasMoreOutput"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderHasMoreOutput(state: *const EncState) -> c_int {
    if !state.is_null() && (*state).pending() > 0 { BROTLI_TRUE } else { BROTLI_FALSE }
}

/// # Safety
/// As google/brotli's `BrotliEncoderTakeOutput`: the bytes stay valid until
/// the next call on `state`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderTakeOutput"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderTakeOutput(state: *mut EncState, size: *mut usize) -> *const u8 {
    if size.is_null() {
        return std::ptr::null();
    }
    if state.is_null() {
        *size = 0;
        return std::ptr::null();
    }
    let s = &mut *state;
    let n = s.pending();
    let k = if *size == 0 { n } else { (*size).min(n) };
    if k == 0 {
        *size = 0;
        return std::ptr::null();
    }
    let p = s.out.as_ptr().add(s.pos);
    s.pos += k;
    s.total += k;
    *size = k;
    p
}

/// The largest output of `BrotliEncoderCompress` for `input_size` bytes
/// (google/brotli's bound, which a stored stream always meets).
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderMaxCompressedSize"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub extern "C" fn vbrotli_BrotliEncoderMaxCompressedSize(input_size: usize) -> usize {
    let large = input_size >> 14;
    let overhead = 2 + 4 * large + 3 + 1;
    let r = input_size.wrapping_add(overhead);
    if input_size == 0 {
        2
    } else if r < input_size {
        0
    } else {
        r
    }
}

/// # Safety
/// As google/brotli's `BrotliEncoderCompress`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderCompress"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderCompress(
    quality: c_int,
    lgwin: c_int,
    _mode: c_int,
    input_size: usize,
    input_buffer: *const u8,
    encoded_size: *mut usize,
    encoded_buffer: *mut u8,
) -> c_int {
    if encoded_size.is_null() || *encoded_size == 0 || encoded_buffer.is_null() {
        return BROTLI_FALSE;
    }
    if input_size != 0 && input_buffer.is_null() {
        return BROTLI_FALSE;
    }
    if !(10..=24).contains(&lgwin) && lgwin != 0 {
        // google/brotli accepts up to 30 only with large windows.
        if lgwin > 24 {
            return BROTLI_FALSE;
        }
    }
    let input: &[u8] = if input_size == 0 { &[] } else { std::slice::from_raw_parts(input_buffer, input_size) };
    let q = quality.clamp(0, 11) as u32;
    let mut c = crate::compress::compress(input, q, lgwin.clamp(10, 24) as u32);
    if c.len() > *encoded_size {
        // As google/brotli: an uncompressed stream if that fits.
        c = crate::encoder::compress_stored(input);
        if c.len() > *encoded_size {
            return BROTLI_FALSE;
        }
    }
    std::ptr::copy_nonoverlapping(c.as_ptr(), encoded_buffer, c.len());
    *encoded_size = c.len();
    BROTLI_TRUE
}

#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderVersion"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub extern "C" fn vbrotli_BrotliEncoderVersion() -> u32 {
    VERSION
}

/// Roughly the memory an instance uses for `input_size` bytes.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderEstimatePeakMemoryUsage"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub extern "C" fn vbrotli_BrotliEncoderEstimatePeakMemoryUsage(quality: c_int, _lgwin: c_int, input_size: usize) -> usize {
    let tables = 8 << 20;
    let chains = if quality >= 7 { 4 * input_size } else { 0 };
    tables + chains + input_size.saturating_mul(3)
}

/// Prepared dictionaries are not supported: always null.
///
/// # Safety
/// Any arguments.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderPrepareDictionary"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderPrepareDictionary(
    _type: c_int,
    _size: usize,
    _data: *const u8,
    _quality: c_int,
    _alloc: *const c_void,
    _free: *const c_void,
    _opaque: *mut c_void,
) -> *mut c_void {
    std::ptr::null_mut()
}

/// # Safety
/// Any arguments.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderDestroyPreparedDictionary"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderDestroyPreparedDictionary(_d: *mut c_void) {}

/// Prepared dictionaries are not supported: always false.
///
/// # Safety
/// Any arguments.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderAttachPreparedDictionary"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderAttachPreparedDictionary(_s: *mut EncState, _d: *const c_void) -> c_int {
    BROTLI_FALSE
}

/// # Safety
/// Any arguments.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliEncoderGetPreparedDictionarySize"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliEncoderGetPreparedDictionarySize(_d: *const c_void) -> usize {
    0
}
