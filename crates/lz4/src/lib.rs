#![doc = include_str!("../README.md")]
// A formally verified LZ4 compressor and decompressor.
//
// - [`spec`]: the block and frame formats as pure functions (the trusted
//   specification).
// - [`block`]: the block decoder, proven equal to the spec.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-lz4 is proven for 64-bit targets only");

#[doc(hidden)]
pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The code is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

#[doc(hidden)]
pub mod block;
#[doc(hidden)]
pub mod compress;
#[doc(hidden)]
pub mod frame;
#[doc(hidden)]
pub mod fcompress;
#[doc(hidden)]
pub mod capi;

pub use block::decompress_into as decompress_block;
pub use compress::{compress_bound, compress_into as compress_block};
pub use fcompress::{compress, Prefs};
pub use frame::{decompress, Error};
