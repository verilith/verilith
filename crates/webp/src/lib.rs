//! A formally verified WebP decoder: lossless (VP8L) and lossy (VP8).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod spec;
pub mod huffman;
pub mod bitreader;
pub mod codes;
pub mod slemmas;
pub mod pixels;
pub mod image;
pub mod pxops;
pub mod transform;
pub mod vlemmas;
pub mod vx;
pub mod vpred;
pub mod vpx;
pub mod undo;
pub mod decode;
pub mod container;
pub mod vp8tables;
pub mod vp8spec;
pub mod vp8bool;
pub mod vp8parse;
pub mod vp8dsp;
pub mod vp8p4;
pub mod vp8frame;
pub mod vp8yuv;
pub mod lossy;
#[cfg(not(verus_only))]
pub mod capi;

#[cfg(not(verus_only))]
pub use capi::{decode, decode_to, get_features, Features, Image, Mode};
pub use pixels::Error;
