//! The C API. This file is not verified: it is glue between C pointers
//! and the verified decoder.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::decode::{decode, Picture};
use crate::types::Error;

/// Decodes `len` bytes at `data`. On success returns a buffer of
/// `*w * *h * *nc` bytes (1 gray or 3 red-green-blue bytes per pixel, rows
/// top to bottom), to be released with `vjpeg_free`. On failure returns
/// null and sets `*nc` to 1 for a file that is invalid or not supported,
/// 2 for a failed allocation.
///
/// # Safety
/// `data` must point to `len` readable bytes, and `w`, `h` and `nc` to
/// writable `u32`s.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vjpeg_decode(data: *const u8, len: usize, w: *mut u32, h: *mut u32, nc: *mut u32) -> *mut u8 {
    let input: &[u8] = if len == 0 { &[] } else { core::slice::from_raw_parts(data, len) };
    match decode(input) {
        Ok(Picture { w: pw, h: ph, nc: pn, px }) => {
            *w = pw;
            *h = ph;
            *nc = pn as u32;
            Box::into_raw(px.into_boxed_slice()) as *mut u8
        }
        Err(e) => {
            *w = 0;
            *h = 0;
            *nc = match e {
                Error::Invalid => 1,
                Error::OutOfMemory => 2,
            };
            core::ptr::null_mut()
        }
    }
}

/// Releases a buffer `vjpeg_decode` returned, of the `len` bytes it had.
///
/// # Safety
/// `p` must come from `vjpeg_decode` and `len` be its `w * h * nc`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vjpeg_free(p: *mut u8, len: usize) {
    if !p.is_null() {
        drop(Box::from_raw(core::ptr::slice_from_raw_parts_mut(p, len)));
    }
}
