//! google/snappy's C API (`snappy-c.h`), as an unverified adapter over
//! the proven compressor and decompressor. It turns C pointers into
//! slices and results into `snappy_status`; every byte produced, and
//! every verdict on an input, comes from a proven function.
//!
//! Symbols are exported as `vsnappy_*`, or under snappy's own names with
//! the `snappy-abi` feature.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::compress::{compress_into, max_compressed_length};
use crate::decode::{decompress_into, uncompressed_length, validate, Error};
use core::ffi::{c_char, c_int};

pub const SNAPPY_OK: c_int = 0;
pub const SNAPPY_INVALID_INPUT: c_int = 1;
pub const SNAPPY_BUFFER_TOO_SMALL: c_int = 2;

macro_rules! export {
    ($vs:literal, $snappy:literal, fn $name:ident($($a:ident: $t:ty),* $(,)?) -> $r:ty $body:block) => {
        #[cfg_attr(feature = "snappy-abi", unsafe(export_name = $snappy))]
        #[cfg_attr(not(feature = "snappy-abi"), unsafe(export_name = $vs))]
        /// # Safety
        /// As the snappy function of the same name: pointers must be
        /// valid for the sizes given with them.
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

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

export!("vsnappy_max_compressed_length", "snappy_max_compressed_length", fn max_compressed_length_c(n: usize) -> usize {
    // As snappy: the formula, whatever the length. (The second test is
    // always true on 64-bit targets.)
    if n <= 0xffff_ffff && n <= isize::MAX as usize {
        max_compressed_length(n)
    } else {
        32usize.wrapping_add(n).wrapping_add(n / 6)
    }
});

export!("vsnappy_compress", "snappy_compress", fn compress(src: *const c_char, n: usize, dst: *mut c_char, dst_len: *mut usize) -> c_int {
    if dst_len.is_null() || n > 0xffff_ffff || n > isize::MAX as usize {
        return SNAPPY_INVALID_INPUT;
    }
    if *dst_len < max_compressed_length(n) {
        return SNAPPY_BUFFER_TOO_SMALL;
    }
    match compress_into(input(src, n), output(dst, *dst_len)) {
        Some(m) => {
            *dst_len = m;
            SNAPPY_OK
        }
        None => SNAPPY_BUFFER_TOO_SMALL,
    }
});

export!("vsnappy_uncompress", "snappy_uncompress", fn uncompress(src: *const c_char, n: usize, dst: *mut c_char, dst_len: *mut usize) -> c_int {
    if dst_len.is_null() {
        return SNAPPY_INVALID_INPUT;
    }
    let s = input(src, n);
    let Some(len) = uncompressed_length(s) else {
        return SNAPPY_INVALID_INPUT;
    };
    if *dst_len < len {
        return SNAPPY_BUFFER_TOO_SMALL;
    }
    // Exactly the length the input declares: nothing after the result is
    // touched.
    match decompress_into(s, output(dst, len)) {
        Ok(m) => {
            *dst_len = m;
            SNAPPY_OK
        }
        Err(Error::Corrupt) | Err(Error::TooSmall) => SNAPPY_INVALID_INPUT,
    }
});

export!("vsnappy_uncompressed_length", "snappy_uncompressed_length", fn uncompressed_length_c(src: *const c_char, n: usize, result: *mut usize) -> c_int {
    match uncompressed_length(input(src, n)) {
        Some(len) if !result.is_null() => {
            *result = len;
            SNAPPY_OK
        }
        _ => SNAPPY_INVALID_INPUT,
    }
});

export!("vsnappy_validate_compressed_buffer", "snappy_validate_compressed_buffer", fn validate_compressed_buffer(src: *const c_char, n: usize) -> c_int {
    if validate(input(src, n)) {
        SNAPPY_OK
    } else {
        SNAPPY_INVALID_INPUT
    }
});
