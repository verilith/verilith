//! A formally verified image proxy and thumbnailer: imgproxy-style URLs,
//! decoding with the Verilith decoders, area-average resizing and PNG
//! output, served by verilith-server.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-imgproxy is verified for 64-bit targets only");

vstd::prelude::verus! {

// The proofs assume 64-bit sizes.
global size_of usize == 8;

} // verus!

pub mod spec;
pub mod resize;
pub mod pngenc;
pub mod fit;
pub mod pixels;
