#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified Zstandard (RFC 8878) decompressor.
//
// - [`spec`]: the format as pure functions (the trusted specification).
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
pub mod work;
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
#[doc(hidden)]
pub mod ent;
#[doc(hidden)]
pub mod enc;
#[doc(hidden)]
pub mod opt;
#[doc(hidden)]
pub mod compress;
#[doc(hidden)]
pub mod ccapi;

pub use dict::DictDecoder;
pub use frame::{decompress_exec as decompress, Error};
pub use stream::Stream;
pub use compress::{compress, compress_exec, Params};
