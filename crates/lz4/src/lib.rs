//! A formally verified LZ4 compressor and decompressor.
//!
//! - [`spec`]: the block and frame formats as pure functions (the trusted
//!   specification).
//! - [`block`]: the block decoder, proven equal to the spec.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-lz4 is proven for 64-bit targets only");

pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The code is proven for 64-bit targets.
global size_of usize == 8;

} // verus!

pub mod block;
pub mod compress;
pub mod frame;
pub mod fcompress;
pub mod capi;
