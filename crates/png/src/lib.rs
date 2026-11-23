#![doc = include_str!("../README.md")]
// A formally verified PNG decoder.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
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
