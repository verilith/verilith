#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified HPACK (RFC 7541) header decoder and encoder.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod bits;
#[doc(hidden)]
pub mod capi;
pub mod decoder;
#[doc(hidden)]
pub mod emit;
pub mod encoder;
#[doc(hidden)]
pub mod henc;
#[doc(hidden)]
pub mod htables;
#[doc(hidden)]
pub mod huffman;
#[doc(hidden)]
pub mod integer;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod spec;
mod sindex;
mod stable;
#[doc(hidden)]
pub mod table;

pub use decoder::{Decoder, Feed};
pub use encoder::{Encoder, Header};
