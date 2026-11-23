#![doc = include_str!("../README.md")]
// A formally verified WHATWG URL parser.
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_assignments, dead_code, non_shorthand_field_patterns))]
#[doc(hidden)]
pub mod encode;
#[doc(hidden)]
pub mod host;
#[doc(hidden)]
pub mod api;
#[doc(hidden)]
pub mod ascii;
#[doc(hidden)]
pub mod creds;
#[doc(hidden)]
pub mod idna;
#[doc(hidden)]
pub mod parse;
mod public;
#[doc(hidden)]
pub mod set;
#[doc(hidden)]
pub mod setters;
pub mod searchparams;
#[doc(hidden)]
pub mod capi;
pub mod compat;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod simd;
#[doc(hidden)]
pub mod swar;
#[doc(hidden)]
pub mod tables;
#[doc(hidden)]
pub mod url;

pub use url::Url;
pub use searchparams::UrlSearchParams;
