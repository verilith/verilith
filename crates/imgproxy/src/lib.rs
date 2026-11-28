//! A formally verified image proxy and thumbnailer: imgproxy-style URLs (parsed by verified code),
//! decoding with the Verilith decoders, cropping, rotating and placing on a
//! canvas, Lanczos (or area-average)
//! resizing and PNG or JPEG output, served by verilith-server.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-imgproxy is verified for 64-bit targets only");

vstd::prelude::verus! {

// The proofs assume 64-bit sizes.
global size_of usize == 8;

} // verus!

pub mod spec;
pub mod resize;
pub mod spec_lanczos;
pub mod spec_geom;
pub mod geom;
pub mod spec_url;
pub mod url;
pub mod lanczos;
pub mod pngenc;
pub mod fit;
pub mod pixels;
#[cfg(not(verus_keep_ghost))]
pub mod proxy;
#[cfg(not(verus_keep_ghost))]
pub mod handler;
