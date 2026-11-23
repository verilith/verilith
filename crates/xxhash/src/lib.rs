#![doc = include_str!("../README.md")]
// - `spec`: XXH32 and XXH64 as pure functions (the trusted specification).
// - `xxh32`: XXH32 of a slice, proven equal to `spec::xxh32_seed`.
// - `xxh64`: XXH64 of a slice, and `Xxh64` and `XxHash64` for input that
//   comes in pieces, proven equal to `spec::xxh64_seed`.
//
// These are the checksums of the LZ4 frame format (XXH32) and of
// Zstandard frames (XXH64), and verilith-lz4 and verilith-zstd use them
// from here. They are not cryptographic hashes.
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
pub mod bytes;
#[doc(hidden)]
pub mod xxh32;
#[doc(hidden)]
pub mod xxh64;

pub use xxh32::{xxh32_exec, xxh32_with_seed as xxh32};
pub use xxh64::{XxHash64, Xxh64, xxh64_exec, xxh64_with_seed as xxh64};
