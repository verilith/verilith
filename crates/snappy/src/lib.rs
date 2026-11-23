//! A formally verified Snappy compressor and decompressor.
//!
//! - [`spec`]: the format as pure functions (the trusted specification).
//! - [`decode`]: the decompressor, proven equal to the spec.
//! - [`compress`]: the compressor, proven to round-trip.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-snappy is proven for 64-bit targets only");

pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The code is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

pub mod decode;
pub mod compress;
pub mod frame;
pub mod capi;
