//! A formally verified JPEG decoder: baseline, extended sequential and
//! progressive Huffman.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod spec;
pub mod types;
pub mod bits;
pub mod huff;
pub mod num;
pub mod prims;
pub mod block;
pub mod scan;
pub mod parse;
pub mod idct_neon;
pub mod idct16;
pub mod color_neon;
pub mod idct;
pub mod render;
pub mod stream;
pub mod decode;
#[cfg(not(verus_only))]
pub mod capi;
#[cfg(not(verus_only))]
pub mod tj;

pub use decode::{decode, read_header, Header, Picture};
pub use types::Error;





