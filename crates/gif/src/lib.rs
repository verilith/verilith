//! A formally verified GIF decoder.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod spec;
pub mod prims;
pub mod lzw;
pub mod blocks;
pub mod interlace;
pub mod decode;
