#![doc = include_str!("../README.md")]
// A formally verified PNG decoder.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-png is proven for 64-bit targets only");

// The image-size arithmetic is proven with 64-bit usize. Only where it
// holds, so that a 32-bit build stops at the error above rather than at the
// size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
global size_of usize == 8;
}

#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod chunks;
#[doc(hidden)]
pub mod unfilter;
#[doc(hidden)]
pub mod geom;
#[doc(hidden)]
pub mod passes;
#[doc(hidden)]
pub mod decode;
#[doc(hidden)]
pub mod output;
#[doc(hidden)]
pub mod fast;
#[doc(hidden)]
pub mod deint;
#[doc(hidden)]
pub mod top;
#[doc(hidden)]
#[cfg(not(verus_only))]
pub mod libpng;

pub use chunks::Header;
pub use decode::Error;
pub use top::{decode, PixelFormat};
