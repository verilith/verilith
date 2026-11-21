//! A formally verified DEFLATE (RFC 1951), zlib (RFC 1950) and gzip
//! (RFC 1952) decompressor and compressor.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
//!
//! - [`spec`]: the formats as pure functions (the trusted specification).
//! - [`huffman`]: canonical Huffman decoding tables.
//! - [`inflate`]: the verified DEFLATE decoder.
//! - [`checksum`]: Adler-32 and CRC-32.
//! - [`wrap`]: zlib and gzip containers and the Rust API.
//! - [`deflate`]: the verified compressor ([`deflate::compress_raw`],
//!   [`deflate::zlib_compress`], [`deflate::gzip_compress`]) and
//!   [`dstream::Deflater`], its streaming form.
//! - [`capi`]: unverified C ABI adapters for zlib's and libdeflate's
//!   functions, with their bookkeeping verified in [`glue`].
pub mod capi;
pub mod bitwriter;
pub mod checksum;
pub mod deflate;
pub mod dlemmas;
pub mod dstream;
pub mod glue;
pub mod huffman;
pub mod inflate;
pub mod par;
pub mod ilemmas;
pub mod prims;
pub mod simd;
pub mod slemmas;
pub mod spec;
pub mod stream;
pub mod wrap;

pub use wrap::{Decompressor, Error, Format};

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
