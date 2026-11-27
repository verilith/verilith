#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// Formally verified (Verus) building blocks shared by the
// Verilith libraries.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#![cfg_attr(not(feature = "std"), no_std)]
//
// - [`prims`]: the memory primitives with hand-written specs. This one file
//   (with three wrappers in [`binary64`]) is the
//   trusted base; everything else is proven.
// - [`spare`]: a `Vec`'s spare capacity, and stores into it without a
//   capacity check (trusted).
// - [`tail`]: `Tail`, a byte vector appended to without capacity tests,
//   the room being reserved once and proven enough (trusted).
// - [`bytes`] and [`cursor`]: fixed-width integers in byte strings, and a
//   bounds-checked reader over a slice.
// - [`bits`]: bit strings packed least significant bit first, as DEFLATE,
//   WebP lossless and PNG read them.
// - [`huffman`]: canonical Huffman codes, and the proofs that make decoding
//   tables exact.
// - [`lz`]: LZ77 over byte slices: what a match copy means, and proven
//   match copies (16 bytes at a time), literal copies and match lengths.
// - [`utf8`]: well-formed UTF-8, and a verified validator.
// - [`num`]: decimal digits and numbers.
// - [`binary64`]: IEEE 754 doubles as a model in spec integers, round to
//   nearest even, and the hardware `*`, `/` and `u64 as f64` (trusted).
// - [`sort`]: a merge sort of positions by a caller's comparison.
// - [`varint`]: QUIC variable-length integers (RFC 9000 §16), for QUIC and
//   HTTP/3.
// - [`clen`]: a message body counted against its declared Content-Length,
//   as HTTP/2 and HTTP/3 check requests.
// - [`scan`]: byte-class tests eight bytes at a time (uppercase letters;
//   NUL, CR and LF), as HTTP/2 and HTTP/3 field checks need.
extern crate alloc;

pub mod binary64;
pub mod bits;
pub mod bytes;
pub mod clen;
pub mod cursor;
pub mod htable;
pub mod huffman;
pub mod lz;
pub mod num;
pub mod prims;
pub mod scan;
pub mod sort;
pub mod spare;
pub mod tail;
pub mod utf8;
pub mod varint;
