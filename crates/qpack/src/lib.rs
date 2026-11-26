#![doc = include_str!("../README.md")]
// A formally verified QPACK (RFC 9204) encoder and decoder.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod spec;
mod stable;
pub mod integer;
pub mod henc;
