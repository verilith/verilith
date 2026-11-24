#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified JPEG decoder: baseline, extended sequential and
// progressive Huffman.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod types;
#[doc(hidden)]
pub mod bits;
#[doc(hidden)]
pub mod huff;
#[doc(hidden)]
pub mod num;
#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod block;
#[doc(hidden)]
pub mod scan;
#[doc(hidden)]
pub mod parse;
#[doc(hidden)]
pub mod idct_neon;
#[doc(hidden)]
pub mod idct16;
#[doc(hidden)]
pub mod color_neon;
#[doc(hidden)]
pub mod idct;
#[doc(hidden)]
pub mod render;
#[doc(hidden)]
pub mod stream;
#[doc(hidden)]
pub mod decode;
#[cfg(not(verus_only))]
#[doc(hidden)]
pub mod capi;
#[cfg(not(verus_only))]
#[doc(hidden)]
pub mod tj;

pub use decode::{decode, read_header, Header, Picture};
pub use types::Error;





