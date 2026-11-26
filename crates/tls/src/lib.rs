#![doc = include_str!("../README.md")]
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
extern crate alloc;

#[doc(hidden)]
pub mod seen;
pub mod hello;
pub mod record;
pub mod spec;
