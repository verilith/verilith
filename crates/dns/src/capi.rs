//! C ABI compatible with c-ares's `ares_expand_name`.
//!
//! A thin adapter, not verified: pointer and length checks, presentation
//! formatting (`Name::write_presentation`) and `malloc`. All wire-format
//! handling happens in the verified `parse::read_name_into`.
#![allow(unsafe_op_in_unsafe_fn)]
use alloc::vec::Vec;
use crate::name::Name;
use crate::parse::read_name_into;
use core::ffi::{c_char, c_int, c_long, c_uchar};

// Inside c-ares, strings come from its allocator, so that
// `ares_free_string` (and any `ares_library_init_mem` hooks) apply.
#[cfg(feature = "cares")]
unsafe extern "C" {
    fn ares_malloc(size: usize) -> *mut core::ffi::c_void;
}

#[cfg(feature = "cares")]
unsafe fn alloc(n: usize) -> *mut core::ffi::c_void {
    ares_malloc(n)
}

#[cfg(not(feature = "cares"))]
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[cfg(not(feature = "cares"))]
unsafe fn alloc(n: usize) -> *mut core::ffi::c_void {
    malloc(n)
}

pub const ARES_SUCCESS: c_int = 0;
pub const ARES_EBADNAME: c_int = 8;
pub const ARES_ENOMEM: c_int = 15;

/// Drop-in for `ares_expand_name`. With the `ares-abi` feature it is exported
/// under that exact symbol name.
///
/// # Safety
/// `abuf` must point to `alen` readable bytes, and `s` and `enclen` must be
/// valid for writes (`s` may be null), as with c-ares.
#[cfg_attr(feature = "ares-abi", unsafe(export_name = "ares_expand_name"))]
#[cfg_attr(not(feature = "ares-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vdns_expand_name(
    encoded: *const c_uchar,
    abuf: *const c_uchar,
    alen: c_int,
    s: *mut *mut c_char,
    enclen: *mut c_long,
) -> c_int {
    if encoded.is_null() || abuf.is_null() || alen <= 0 || enclen.is_null() {
        return ARES_EBADNAME;
    }
    let alen = alen as usize;
    if encoded < abuf || encoded >= abuf.add(alen) {
        return ARES_EBADNAME;
    }
    *enclen = 0;
    if !s.is_null() {
        *s = core::ptr::null_mut();
    }
    let buf = core::slice::from_raw_parts(abuf, alen);
    let pos = encoded.offset_from(abuf) as usize;
    let mut wire = Vec::with_capacity(256);
    let end = match read_name_into(buf, pos, &mut wire) {
        Some((end, _)) => end,
        None => return ARES_EBADNAME,
    };
    if !s.is_null() {
        // At most 4 output bytes per name byte, plus the terminator.
        let mut text = Vec::with_capacity(4 * wire.len() + 1);
        Name::from_wire(&wire).write_presentation(&mut text);
        let p = alloc(text.len() + 1) as *mut u8;
        if p.is_null() {
            return ARES_ENOMEM;
        }
        core::ptr::copy_nonoverlapping(text.as_ptr(), p, text.len());
        *p.add(text.len()) = 0;
        *s = p as *mut c_char;
    }
    *enclen = (end - pos) as c_long;
    ARES_SUCCESS
}
