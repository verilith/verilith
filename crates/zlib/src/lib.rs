#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified DEFLATE (RFC 1951), zlib (RFC 1950) and gzip
// (RFC 1952) decompressor and compressor.
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_assignments, dead_code))]
//
// - [`spec`]: the formats as pure functions (the trusted specification).
// - [`huffman`]: canonical Huffman decoding tables.
// - [`inflate`]: the verified DEFLATE decoder.
// - [`checksum`]: Adler-32 and CRC-32.
// - [`wrap`]: zlib and gzip containers and the Rust API.
// - [`deflate`]: the verified compressor ([`deflate::compress_raw`],
//   [`deflate::zlib_compress`], [`deflate::gzip_compress`]) and
//   [`dstream::Deflater`], its streaming form.
// - [`capi`]: unverified C ABI adapters for zlib's and libdeflate's
//   functions, with their bookkeeping verified in [`glue`].
#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod bitwriter;
#[doc(hidden)]
pub mod checksum;
#[doc(hidden)]
pub mod deflate;
#[doc(hidden)]
pub mod dlemmas;
#[doc(hidden)]
pub mod dstream;
#[doc(hidden)]
pub mod glue;
#[doc(hidden)]
pub mod huffman;
#[doc(hidden)]
pub mod inflate;
#[doc(hidden)]
pub mod par;
#[doc(hidden)]
pub mod ilemmas;
#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod simd;
#[doc(hidden)]
pub mod slemmas;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod stream;
#[doc(hidden)]
pub mod wrap;

pub use wrap::{Decompressor, Error, Format};
pub use deflate::{compress_raw as deflate, gzip_compress, zlib_compress};
pub use dstream::Deflater;

/// Most output the functions below produce: 1 GiB. Use
/// [`Decompressor::decompress_vec`] to choose another limit.
pub const DEFAULT_LIMIT: usize = 1 << 30;

/// Decompresses raw DEFLATE data.
pub fn inflate(input: &[u8]) -> Result<Vec<u8>, Error> {
    Decompressor::new().decompress_vec(Format::Raw, input, DEFAULT_LIMIT).map(|r| r.0)
}

/// Decompresses a zlib stream.
pub fn zlib_decompress(input: &[u8]) -> Result<Vec<u8>, Error> {
    Decompressor::new().decompress_vec(Format::Zlib, input, DEFAULT_LIMIT).map(|r| r.0)
}

/// Decompresses one gzip member.
pub fn gzip_decompress(input: &[u8]) -> Result<Vec<u8>, Error> {
    Decompressor::new().decompress_vec(Format::Gzip, input, DEFAULT_LIMIT).map(|r| r.0)
}
