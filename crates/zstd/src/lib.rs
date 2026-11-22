//! A formally verified Zstandard (RFC 8878) decompressor.
//!
//! - [`spec`]: the format as pure functions (the trusted specification).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("vzstd is proven for 64-bit targets only");

pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The decoder is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

pub mod prims;
pub mod bits;
pub mod fse;
pub mod huf;
pub mod seq;
pub mod cpu;
pub mod frame;
pub mod stream;
pub mod capi;
