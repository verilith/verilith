//! The C ABI: `vfont_sanitize` and `vfont_free` (declared in
//! `include/vfont.h`).
//!
//! A thin adapter, not verified: it checks the pointers, hands the input to
//! the verified [`crate::sanitize_index`], and passes the output buffer to
//! the caller. `include/opentype-sanitiser.h` builds OTS's C++ interface
//! (`ots::OTSContext::Process`) on these two functions.
use std::os::raw::c_int;

/// Sanitizes the `len` bytes at `input`. `index` picks the font in a
/// TrueType Collection and is ignored for other files.
///
/// Returns 1 and stores a newly allocated font in `*out` and its length in
/// `*out_len` if the font was accepted; release it with [`vfont_free`].
/// Returns 0 and stores a null pointer and 0 if it was refused or an
/// argument is null.
///
/// # Safety
/// `input` must point to `len` readable bytes (it may be null if `len` is
/// 0), and `out` and `out_len` must be valid for writes.
#[no_mangle]
pub unsafe extern "C" fn vfont_sanitize(
    input: *const u8,
    len: usize,
    index: u32,
    out: *mut *mut u8,
    out_len: *mut usize,
) -> c_int {
    if out.is_null() || out_len.is_null() {
        return 0;
    }
    *out = std::ptr::null_mut();
    *out_len = 0;
    if input.is_null() && len != 0 {
        return 0;
    }
    let data: &[u8] = if len == 0 { &[] } else { std::slice::from_raw_parts(input, len) };
    match crate::sanitize_index(data, index) {
        Some(v) => {
            let b = v.into_boxed_slice();
            *out_len = b.len();
            *out = Box::into_raw(b) as *mut u8;
            1
        }
        None => 0,
    }
}

/// Releases a font returned by [`vfont_sanitize`]. `len` must be the
/// length that call stored. A null `ptr` is ignored.
///
/// # Safety
/// `ptr` and `len` must come from one successful [`vfont_sanitize`] call,
/// and the buffer must not have been freed already.
#[no_mangle]
pub unsafe extern "C" fn vfont_free(ptr: *mut u8, len: usize) {
    if !ptr.is_null() {
        drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(ptr, len)));
    }
}
