//! A formally verified WHATWG URL parser.
#![cfg_attr(not(verus_only), allow(unused_variables, non_shorthand_field_patterns))]
pub mod encode;
pub mod host;
pub mod api;
pub mod ascii;
pub mod creds;
pub mod idna;
pub mod parse;
mod public;
pub mod set;
pub mod setters;
pub mod searchparams;
pub mod capi;
pub mod compat;
pub mod spec;
pub mod simd;
pub mod swar;
pub mod tables;
pub mod url;

pub use url::Url;
