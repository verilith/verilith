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

/// Encodes `h` rows of `w` pixels at `px`, `bpp` (3 or 4) bytes each with
/// red, green and blue first, at `quality` (1 to 100), with 4:2:0 chroma
/// if `sub` is nonzero. Returns the file, of `*len` bytes, to be released
/// with `vjpeg_free`; or null for an image of no pixels or wider or higher
/// than 65500.
///
/// # Safety
/// `px` must point to `w * h * bpp` readable bytes and `len` to a writable
/// `usize`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vjpeg_encode(
    px: *const u8,
    w: u32,
    h: u32,
    bpp: u32,
    quality: u32,
    sub: i32,
    len: *mut usize,
) -> *mut u8 {
    *len = 0;
    let n = (w as usize).saturating_mul(h as usize).saturating_mul(bpp as usize);
    if px.is_null() || n == 0 {
        return core::ptr::null_mut();
    }
    let input = core::slice::from_raw_parts(px, n);
    let q = quality.clamp(1, 100) as u8;
    match crate::encode::encode_rgb(input, w as usize, h as usize, bpp as usize, q, sub != 0) {
        Some(o) => {
            *len = o.len();
            Box::into_raw(o.into_boxed_slice()) as *mut u8
        }
        None => core::ptr::null_mut(),
    }
}
