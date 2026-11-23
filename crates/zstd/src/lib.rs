#![doc = include_str!("../README.md")]
// A formally verified Zstandard (RFC 8878) decompressor.
//
// - [`spec`]: the format as pure functions (the trusted specification).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-zstd is proven for 64-bit targets only");

#[doc(hidden)]
pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The decoder is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod bits;
#[doc(hidden)]
pub mod fse;
#[doc(hidden)]
pub mod huf;
#[doc(hidden)]
pub mod seq;
#[doc(hidden)]
pub mod cpu;
#[doc(hidden)]
pub mod frame;
#[doc(hidden)]
pub mod dict;
#[doc(hidden)]
pub mod stream;
#[doc(hidden)]
pub mod capi;

pub use dict::DictDecoder;
pub use frame::{decompress_exec as decompress, Error};
pub use stream::Stream;
