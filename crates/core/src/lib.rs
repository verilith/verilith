//! Formally verified (Verus) building blocks shared by the
//! Verilith libraries.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#![cfg_attr(not(feature = "std"), no_std)]
//!
//! - [`prims`]: the memory primitives with hand-written specs. This one file
//!   (with [`checksum::cpu`] and three wrappers in [`binary64`]) is the
//!   trusted base; everything else is proven.
//! - [`tail`]: `Tail`, a byte vector appended to without capacity tests,
//!   the room being reserved once and proven enough (trusted).
//! - [`bytes`] and [`cursor`]: fixed-width integers in byte strings, and a
//!   bounds-checked reader over a slice.
//! - [`bits`]: bit strings packed least significant bit first, as DEFLATE,
//!   WebP lossless and PNG read them.
//! - [`huffman`]: canonical Huffman codes, and the proofs that make decoding
//!   tables exact.
//! - [`lz`]: LZ77 over byte slices: what a match copy means, and proven
//!   match copies (16 bytes at a time), literal copies and match lengths.
//! - [`utf8`]: well-formed UTF-8, and a verified validator.
//! - [`num`]: decimal digits and numbers.
//! - [`binary64`]: IEEE 754 doubles as a model in spec integers, round to
//!   nearest even, and the hardware `*`, `/` and `u64 as f64` (trusted).
//! - [`checksum`]: Adler-32, CRC-32 and CRC-32C.
extern crate alloc;

pub mod binary64;
pub mod bits;
pub mod bytes;
pub mod checksum;
pub mod cursor;
pub mod htable;
pub mod huffman;
pub mod lz;
pub mod num;
pub mod prims;
pub mod tail;
pub mod utf8;
