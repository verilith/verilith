//! A C ABI compatible with google/brotli's decoder (`brotli/decode.h`).
//!
//! A thin adapter, not verified: pointer checks, bookkeeping and result
//! codes. All decoding happens in the verified `Decoder`, driven by
//! `stream::Stream`.
//!
//! Functions are exported as `vbrotli_*`. With the `brotli-abi` feature they
//! are exported under google/brotli's own names instead, so a program linked
//! against `libvbrotli.a` (Node.js, for one) uses them in place of
//! `libbrotlidec`.
//!
//! Differences from google/brotli:
//! - `alloc_func`/`free_func` are accepted but not called: memory comes from
//!   the Rust allocator.
//! - Large-window streams are not supported: setting
//!   `BROTLI_DECODER_PARAM_LARGE_WINDOW` to 1 fails.
//! - Shared dictionaries (`BrotliDecoderAttachDictionary`) are not
//!   supported, nor are metadata callbacks.
//! - Every malformed stream reports the same error code, `ERROR_FORMAT`:
//!   the decoder does not say which rule the stream broke.
//! - A command whose insert length runs past the end of its meta-block is
//!   rejected as soon as the command is read; google/brotli decodes the
//!   literals first. On a truncated malformed stream the result can be
//!   `ERROR` where google/brotli says `NEEDS_MORE_INPUT`.
//! - With `NEEDS_MORE_OUTPUT` a byte the decoder has read part of is left in
//!   the input (google/brotli keeps those bits itself).
#![allow(non_snake_case)]
#![allow(unsafe_op_in_unsafe_fn)]
use crate::stream::{Result as R, Stream};
use std::os::raw::{c_char, c_int, c_void};

pub const BROTLI_FALSE: c_int = 0;
pub const BROTLI_TRUE: c_int = 1;

pub const RESULT_ERROR: c_int = 0;
pub const RESULT_SUCCESS: c_int = 1;
pub const RESULT_NEEDS_MORE_INPUT: c_int = 2;
pub const RESULT_NEEDS_MORE_OUTPUT: c_int = 3;

/// The error code reported for any malformed stream.
pub const ERROR_FORMAT: c_int = -1;
pub const ERROR_INVALID_ARGUMENTS: c_int = -20;
pub const ERROR_UNREACHABLE: c_int = -31;

pub const PARAM_DISABLE_RING_BUFFER_REALLOCATION: c_int = 0;
pub const PARAM_LARGE_WINDOW: c_int = 1;

/// google/brotli 1.2.0, the version this decoder follows.
pub const VERSION: u32 = 0x1002000;

/// The decoder instance behind a `BrotliDecoderState*`.
pub struct State {
    stream: Stream,
    /// The last result or error code.
    code: c_int,
    used: bool,
}

/// # Safety
/// As google/brotli's `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderCreateInstance"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderCreateInstance(
    _alloc: *const c_void,
    _free: *const c_void,
    _opaque: *mut c_void,
) -> *mut State {
    Box::into_raw(Box::new(State { stream: Stream::open(), code: 0, used: false }))
}

/// # Safety
/// `state` is null or came from `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderDestroyInstance"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderDestroyInstance(state: *mut State) {
    if !state.is_null() {
        drop(Box::from_raw(state));
    }
}

/// # Safety
/// As google/brotli's `BrotliDecoderSetParameter`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderSetParameter"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderSetParameter(state: *mut State, param: c_int, value: u32) -> c_int {
    if state.is_null() || (*state).used {
        return BROTLI_FALSE;
    }
    match param {
        // The ring grows as needed either way; this only changes memory use.
        PARAM_DISABLE_RING_BUFFER_REALLOCATION => BROTLI_TRUE,
        PARAM_LARGE_WINDOW => {
            if value == 0 {
                BROTLI_TRUE
            } else {
                BROTLI_FALSE
            }
        },
        _ => BROTLI_FALSE,
    }
}

/// # Safety
/// As google/brotli's `BrotliDecoderDecompressStream`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderDecompressStream"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderDecompressStream(
    state: *mut State,
    available_in: *mut usize,
    next_in: *mut *const u8,
    available_out: *mut usize,
    next_out: *mut *mut u8,
    total_out: *mut usize,
) -> c_int {
    if state.is_null() || available_in.is_null() || available_out.is_null() {
        return RESULT_ERROR;
    }
    let s = &mut *state;
    if s.code < 0 {
        return RESULT_ERROR;
    }
    if (*available_in != 0 && (next_in.is_null() || (*next_in).is_null()))
        || (*available_out != 0 && (next_out.is_null() || (*next_out).is_null()))
    {
        s.code = ERROR_INVALID_ARGUMENTS;
        return RESULT_ERROR;
    }
    let input: &[u8] = if *available_in == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(*next_in, *available_in)
    };
    let output: &mut [u8] = if *available_out == 0 {
        &mut []
    } else {
        std::slice::from_raw_parts_mut(*next_out, *available_out)
    };
    if !input.is_empty() {
        s.used = true;
    }
    let (r, used, made) = s.stream.decompress(input, output);
    if used > 0 {
        *next_in = (*next_in).add(used);
        *available_in -= used;
    }
    if made > 0 {
        *next_out = (*next_out).add(made);
        *available_out -= made;
    }
    if !total_out.is_null() {
        *total_out = s.stream.dec.flushed as usize;
    }
    let code = match r {
        R::Error => ERROR_FORMAT,
        R::Success => RESULT_SUCCESS,
        R::NeedsMoreInput => RESULT_NEEDS_MORE_INPUT,
        R::NeedsMoreOutput => RESULT_NEEDS_MORE_OUTPUT,
    };
    s.code = code;
    if code < 0 {
        RESULT_ERROR
    } else {
        code
    }
}

/// # Safety
/// As google/brotli's `BrotliDecoderDecompress`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderDecompress"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderDecompress(
    encoded_size: usize,
    encoded_buffer: *const u8,
    decoded_size: *mut usize,
    decoded_buffer: *mut u8,
) -> c_int {
    if decoded_size.is_null()
        || (encoded_size != 0 && encoded_buffer.is_null())
        || (*decoded_size != 0 && decoded_buffer.is_null())
    {
        return RESULT_ERROR;
    }
    let input: &[u8] = if encoded_size == 0 { &[] } else { std::slice::from_raw_parts(encoded_buffer, encoded_size) };
    let output: &mut [u8] =
        if *decoded_size == 0 { &mut [] } else { std::slice::from_raw_parts_mut(decoded_buffer, *decoded_size) };
    let mut s = Stream::open();
    let (r, _, made) = s.decompress(input, output);
    *decoded_size = made;
    if r == R::Success {
        RESULT_SUCCESS
    } else {
        RESULT_ERROR
    }
}

/// # Safety
/// `state` came from `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderHasMoreOutput"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderHasMoreOutput(state: *const State) -> c_int {
    if state.is_null() || (*state).code < 0 {
        return BROTLI_FALSE;
    }
    if (*state).stream.has_more_output() {
        BROTLI_TRUE
    } else {
        BROTLI_FALSE
    }
}

/// # Safety
/// As google/brotli's `BrotliDecoderTakeOutput`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderTakeOutput"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderTakeOutput(state: *mut State, size: *mut usize) -> *const u8 {
    if size.is_null() {
        return std::ptr::null();
    }
    if state.is_null() || (*state).code < 0 {
        *size = 0;
        return std::ptr::null();
    }
    let max = if *size == 0 { 1 << 24 } else { *size };
    let out = (*state).stream.dec.take(max);
    *size = out.len();
    if out.is_empty() {
        std::ptr::null()
    } else {
        out.as_ptr()
    }
}

/// # Safety
/// `state` came from `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderIsUsed"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderIsUsed(state: *const State) -> c_int {
    if !state.is_null() && (*state).used {
        BROTLI_TRUE
    } else {
        BROTLI_FALSE
    }
}

/// # Safety
/// `state` came from `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderIsFinished"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderIsFinished(state: *const State) -> c_int {
    if !state.is_null() && (*state).code >= 0 && (*state).stream.is_finished() {
        BROTLI_TRUE
    } else {
        BROTLI_FALSE
    }
}

/// # Safety
/// `state` came from `BrotliDecoderCreateInstance`.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderGetErrorCode"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderGetErrorCode(state: *const State) -> c_int {
    if state.is_null() {
        return ERROR_INVALID_ARGUMENTS;
    }
    (*state).code
}

macro_rules! cstr {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const c_char
    };
}

#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderErrorString"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub extern "C" fn vbrotli_BrotliDecoderErrorString(c: c_int) -> *const c_char {
    match c {
        0 => cstr!("_NO_ERROR"),
        1 => cstr!("_SUCCESS"),
        2 => cstr!("_NEEDS_MORE_INPUT"),
        3 => cstr!("_NEEDS_MORE_OUTPUT"),
        -1 => cstr!("_ERROR_FORMAT_EXUBERANT_NIBBLE"),
        -2 => cstr!("_ERROR_FORMAT_RESERVED"),
        -3 => cstr!("_ERROR_FORMAT_EXUBERANT_META_NIBBLE"),
        -4 => cstr!("_ERROR_FORMAT_SIMPLE_HUFFMAN_ALPHABET"),
        -5 => cstr!("_ERROR_FORMAT_SIMPLE_HUFFMAN_SAME"),
        -6 => cstr!("_ERROR_FORMAT_CL_SPACE"),
        -7 => cstr!("_ERROR_FORMAT_HUFFMAN_SPACE"),
        -8 => cstr!("_ERROR_FORMAT_CONTEXT_MAP_REPEAT"),
        -9 => cstr!("_ERROR_FORMAT_BLOCK_LENGTH_1"),
        -10 => cstr!("_ERROR_FORMAT_BLOCK_LENGTH_2"),
        -11 => cstr!("_ERROR_FORMAT_TRANSFORM"),
        -12 => cstr!("_ERROR_FORMAT_DICTIONARY"),
        -13 => cstr!("_ERROR_FORMAT_WINDOW_BITS"),
        -14 => cstr!("_ERROR_FORMAT_PADDING_1"),
        -15 => cstr!("_ERROR_FORMAT_PADDING_2"),
        -16 => cstr!("_ERROR_FORMAT_DISTANCE"),
        -17 => cstr!("_ERROR_FORMAT_BLOCK_SWITCH"),
        -18 => cstr!("_ERROR_COMPOUND_DICTIONARY"),
        -19 => cstr!("_ERROR_DICTIONARY_NOT_SET"),
        -20 => cstr!("_ERROR_INVALID_ARGUMENTS"),
        -21 => cstr!("_ERROR_ALLOC_CONTEXT_MODES"),
        -22 => cstr!("_ERROR_ALLOC_TREE_GROUPS"),
        -25 => cstr!("_ERROR_ALLOC_CONTEXT_MAP"),
        -26 => cstr!("_ERROR_ALLOC_RING_BUFFER_1"),
        -27 => cstr!("_ERROR_ALLOC_RING_BUFFER_2"),
        -30 => cstr!("_ERROR_ALLOC_BLOCK_TYPE_TREES"),
        -31 => cstr!("_ERROR_UNREACHABLE"),
        _ => cstr!("INVALID"),
    }
}

#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderVersion"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub extern "C" fn vbrotli_BrotliDecoderVersion() -> u32 {
    VERSION
}

/// Shared dictionaries are not supported.
///
/// # Safety
/// Any arguments.
#[cfg_attr(feature = "brotli-abi", unsafe(export_name = "BrotliDecoderAttachDictionary"))]
#[cfg_attr(not(feature = "brotli-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vbrotli_BrotliDecoderAttachDictionary(
    _state: *mut State,
    _type: c_int,
    _size: usize,
    _data: *const u8,
) -> c_int {
    BROTLI_FALSE
}
