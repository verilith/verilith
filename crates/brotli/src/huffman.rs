//! Canonical prefix code decoding tables. The builder and its proofs live in
//! `verilith_core::htable`, shared with vwebp (which proved them for WebP lossless;
//! Brotli's prefix codes are the same canonical codes).
pub use verilith_core::htable::*;
#[cfg(verus_only)]
pub use verilith_core::huffman::valid_code;
