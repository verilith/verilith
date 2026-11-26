#![doc = include_str!("../README.md")]
// A formally verified QPACK (RFC 9204) encoder and decoder.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod spec;
mod stable;
pub mod integer;
pub mod henc;
pub mod table;
pub mod lemmas;
pub mod decoder;
pub mod fields;
pub mod section;
pub mod strings;

#[cfg(verus_only)]
vstd::prelude::verus! {

// The proofs are checked once per pointer width.
#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

#[cfg(target_pointer_width = "32")]
global size_of usize == 4;

} // verus!
