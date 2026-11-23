#![doc = include_str!("../README.md")]
// A formally verified LZ4 compressor and decompressor.
//
// - [`spec`]: the block and frame formats as pure functions (the trusted
//   specification).
// - [`block`]: the block decoder, proven equal to the spec.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[doc(hidden)]
pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The proofs are checked once per pointer width.
#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

#[cfg(target_pointer_width = "32")]
global size_of usize == 4;

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
