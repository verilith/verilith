#![warn(missing_docs)]
//! A formally verified TIFF decoder.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod spec;
pub mod work;
pub mod lzw;
pub mod packbits;
pub mod ifd;
pub mod params;
pub mod chunk;
pub mod predict;
pub mod place;
pub mod decode;
// libtiff's C API (not on WebAssembly, which has no C library for its
// variadic half, capi/tiffshim.c).
#[cfg(all(not(verus_only), not(target_family = "wasm")))]
pub mod capi;
