//! A formally verified PNG decoder.
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

pub mod spec;
pub mod prims;
pub mod chunks;
pub mod unfilter;
pub mod geom;
pub mod passes;
pub mod decode;
pub mod output;
pub mod fast;
pub mod deint;
pub mod top;
