#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified WebP decoder: lossless (VP8L) and lossy (VP8).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod huffman;
#[doc(hidden)]
pub mod bitreader;
#[doc(hidden)]
pub mod codes;
#[doc(hidden)]
pub mod slemmas;
#[doc(hidden)]
pub mod pixels;
#[doc(hidden)]
pub mod image;
#[doc(hidden)]
pub mod pxops;
#[doc(hidden)]
pub mod transform;
#[doc(hidden)]
pub mod vlemmas;
#[doc(hidden)]
pub mod vx;
#[doc(hidden)]
pub mod vpred;
#[doc(hidden)]
pub mod vpx;
#[doc(hidden)]
pub mod undo;
#[doc(hidden)]
pub mod decode;
#[doc(hidden)]
pub mod container;
#[doc(hidden)]
pub mod vp8tables;
#[doc(hidden)]
pub mod vp8spec;
#[doc(hidden)]
pub mod vp8order;
#[doc(hidden)]
pub mod vp8bool;
#[doc(hidden)]
pub mod vp8parse;
#[doc(hidden)]
pub mod vp8dsp;
#[doc(hidden)]
pub mod vp8p4;
#[doc(hidden)]
pub mod vp8frame;
#[doc(hidden)]
pub mod vp8yuv;
#[doc(hidden)]
pub mod lossy;
#[doc(hidden)]
pub mod enc_bw;
#[doc(hidden)]
pub mod enc_lem;
#[doc(hidden)]
pub mod enc_code;
#[doc(hidden)]
pub mod enc_hl;
pub mod enc_llc;
pub mod enc_tok;
pub mod enc_lz;
pub mod enc_img;
pub mod enc_pred;
#[doc(hidden)]
pub mod enc_bool;
#[doc(hidden)]
pub mod enc_vp8hdr;
#[doc(hidden)]
pub mod enc_vp8modes;
#[doc(hidden)]
pub mod enc_vp8l;
#[cfg(not(verus_only))]
#[doc(hidden)]
pub mod capi;

#[cfg(not(verus_only))]
pub use capi::{decode, decode_to, get_features, Features, Image, Mode};
pub use pixels::Error;
