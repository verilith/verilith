//! A formally verified PNG decoder.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
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
