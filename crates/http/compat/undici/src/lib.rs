//! The Rust half of vhttp's `llhttp.wasm` for undici: vhttp's parser (which
//! exports `llhttp__internal_init` and `llhttp__internal_execute`) plus the
//! `malloc`, `free` and `abort` that llhttp's `api.c` and undici's
//! JavaScript call. `wasm32-unknown-unknown` has no libc, so `malloc` sits
//! on Rust's allocator (dlmalloc there), with the block size kept in an
//! 8-byte header.
pub use verilith_http;

use std::alloc::{alloc, dealloc, Layout};
use std::ffi::c_void;

const HEADER: usize = 8;

/// `malloc(n)`: 8-byte aligned, or null.
#[no_mangle]
pub unsafe extern "C" fn malloc(n: usize) -> *mut c_void {
    let Some(total) = n.checked_add(HEADER) else { return std::ptr::null_mut() };
    let Ok(layout) = Layout::from_size_align(total, HEADER) else { return std::ptr::null_mut() };
    let p = alloc(layout);
    if p.is_null() {
        return std::ptr::null_mut();
    }
    (p as *mut usize).write(total);
    p.add(HEADER) as *mut c_void
}

/// `free(p)`, for a pointer from `malloc`, or null.
#[no_mangle]
pub unsafe extern "C" fn free(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    // On wasm32 the parser's state lives beside it (see verilith_http::llhttp);
    // llhttp_free frees the parser with free().
    verilith_http::llhttp::forget(p);
    let base = (p as *mut u8).sub(HEADER);
    let total = (base as *const usize).read();
    dealloc(base, Layout::from_size_align_unchecked(total, HEADER));
}

/// llhttp's `api.c` calls `abort()` on an impossible enum value.
#[no_mangle]
pub extern "C" fn abort() -> ! {
    std::process::abort()
}
