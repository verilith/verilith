//! XXH32 and XXH64 (seed 0), formally verified with Verus: the code is
//! proven to compute exactly the functions of the xxHash specification.
//!
//! - [`spec`]: XXH32 and XXH64 as pure functions (the trusted
//!   specification).
//! - [`xxh32`]: XXH32 of a slice, proven equal to `spec::xxh32`.
//! - [`xxh64`]: XXH64 of a slice, and [`Xxh64`] for input that comes in
//!   pieces, proven equal to `spec::xxh64`.
//!
//! These are the checksums of the LZ4 frame format (XXH32) and of
//! Zstandard frames (XXH64), and verilith-lz4 and verilith-zstd use them
//! from here. They are not cryptographic hashes.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-xxhash is proven for 64-bit targets only");

pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {
// The code is proven for 64-bit targets.
global size_of usize == 8;
} // verus!

pub mod bytes;
pub mod xxh32;
pub mod xxh64;

pub use xxh32::xxh32_exec;
pub use xxh64::{Xxh64, xxh64_exec};
