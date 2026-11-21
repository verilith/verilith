//! Formally verified (Verus) text encodings and Unicode.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod base64;
#[cfg(not(verus_only))]
pub mod capi;
#[cfg(not(verus_only))]
pub mod capi_utf;
pub mod hex;
pub mod idna;
pub mod percent;
pub mod simd;
pub mod unicode;
pub mod utf;
