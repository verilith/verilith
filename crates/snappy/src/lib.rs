#![doc = include_str!("../README.md")]
// A formally verified Snappy compressor and decompressor.
//
// - [`spec`]: the format as pure functions (the trusted specification).
// - [`decode`]: the decompressor, proven equal to the spec.
// - [`compress`]: the compressor, proven to round-trip.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-snappy is proven for 64-bit targets only");

#[doc(hidden)]
pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The code is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

#[doc(hidden)]
pub mod decode;
#[doc(hidden)]
pub mod compress;
#[doc(hidden)]
pub mod frame;
#[doc(hidden)]
pub mod capi;

pub use compress::{compress, compress_into, max_compressed_length};
pub use decode::{decompress_into, decompress_vec as decompress, uncompressed_length, validate, Error};
pub use frame::{frame_decode, frame_encode, FrameError};
