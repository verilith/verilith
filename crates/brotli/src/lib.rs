#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified Brotli (RFC 7932) decompressor.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#[doc(hidden)]
pub mod bitread;
#[doc(hidden)]
pub mod huffman;
#[doc(hidden)]
pub mod items;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod tables;
#[doc(hidden)]
pub mod decoder;
#[doc(hidden)]
pub mod dict;
#[doc(hidden)]
pub mod prefix;
#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod stream;
#[doc(hidden)]
pub mod rank;
#[doc(hidden)]
pub mod codes;
#[doc(hidden)]
pub mod words;
#[doc(hidden)]
pub mod work;
#[doc(hidden)]
pub mod bitwriter;
#[doc(hidden)]
pub mod elemmas;
#[doc(hidden)]
pub mod encoder;
#[doc(hidden)]
pub mod pcode;
#[doc(hidden)]
pub mod ehuff;
#[doc(hidden)]
pub mod cmeta;

pub use api::{decompress, Error};
pub use stream::{Result as StreamResult, Stream};

/// One-shot decompression over [`Stream`].
mod api;
