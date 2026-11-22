//! One native library for the Verilith parsers.
//!
//! Linking two Rust static libraries into one program duplicates the Rust
//! standard library and fails, so every language binding links this crate
//! instead of the libraries one by one. It re-exports:
//!
//! * vurl's C API (`vurl_*`, ada's `ada_c.h` under another prefix), as vurl
//!   builds it, unchanged;
//! * a C API over vjson documents (`vbind_json_*`, in [`json`]), which the
//!   simdjson-compatible C++ header reads;
//! * vtext's transcoding and base64 C API (`vtext_*`, vtext's `vtext_utf.h`),
//!   which the simdutf-compatible C++ header calls;
//! * with the `http` feature, llhttp's whole C API (`llhttp_*`): llhttp's
//!   own `api.c` and `http.c` over vhttp's verified parser;
//! * with the `dns` feature, c-ares's `ares_dns_parse`, `ares_expand_name`
//!   and vdns's `vdns_ares_dns_write_buf`, for a c-ares patched to call
//!   them (vdns's `cares/README.md`).
//!
//! Everything here is unverified glue: it calls the verified parsers and
//! hands their results across the boundary. `include/` has the C header and
//! the C++ headers built on it.
#![allow(clippy::missing_safety_doc)]

#[cfg(feature = "url")]
pub use verilith_url;
#[cfg(feature = "json")]
pub use verilith_json;
#[cfg(feature = "text")]
pub use verilith_text;

#[cfg(feature = "json")]
pub mod json;

/// Keeps vurl's C API in the static library: nothing in this crate calls it,
/// and the linker would otherwise be free to leave its object out.
#[cfg(feature = "url")]
#[used]
static KEEP_VURL: unsafe extern "C" fn(*const core::ffi::c_char, usize) -> *mut verilith_url::capi::Handle = verilith_url::capi::parse;

/// Keeps vtext's transcoding C API in the static library, as for vurl.
#[cfg(feature = "text")]
#[used]
static KEEP_VTEXT: unsafe extern "C" fn(*const core::ffi::c_char, usize) -> bool = verilith_text::capi_utf::vtext_validate_utf8;

#[cfg(feature = "http")]
pub use verilith_http;
#[cfg(feature = "dns")]
pub use verilith_dns;

/// Keeps vhttp's llhttp parser in the static library, as for vurl.
#[cfg(feature = "http")]
#[used]
static KEEP_VHTTP: unsafe extern "C" fn(*mut verilith_http::llhttp::LlhttpT, *const core::ffi::c_char, *const core::ffi::c_char) -> core::ffi::c_int =
    verilith_http::llhttp::vhttp_llhttp_internal_execute;

/// Keeps vdns's c-ares functions in the static library, as for vurl.
#[cfg(feature = "dns")]
#[used]
static KEEP_VDNS_PARSE: unsafe extern "C" fn(*const u8, usize, core::ffi::c_uint, *mut *mut core::ffi::c_void) -> core::ffi::c_int =
    verilith_dns::cares::vdns_ares_dns_parse;
#[cfg(feature = "dns")]
#[used]
static KEEP_VDNS_EXPAND: unsafe extern "C" fn(*const u8, *const u8, core::ffi::c_int, *mut *mut core::ffi::c_char, *mut core::ffi::c_long) -> core::ffi::c_int =
    verilith_dns::capi::vdns_expand_name;
#[cfg(feature = "dns")]
#[used]
static KEEP_VDNS_WRITE: unsafe extern "C" fn(*const core::ffi::c_void, core::ffi::c_uint, *mut core::ffi::c_void) -> core::ffi::c_int =
    verilith_dns::cares::vdns_ares_dns_write_buf;
