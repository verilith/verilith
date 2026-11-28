#![doc = include_str!("../README.md")]
// A recursive DNS resolver: verified decisions on a small trusted I/O layer.
//
// - [`spec`]: what the resolver may believe and answer (the specification).
// - [`name`]: names in wire form: case-insensitive comparison, bailiwick.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
pub mod spec;
pub mod sha1;
pub mod dspec;
pub mod crypto;
pub mod canon;
pub mod sigcheck;
pub mod nsec;
pub mod trust;
pub mod check;
pub mod name;
pub mod rr;
pub mod accept;
pub mod classify;
pub mod cache;
pub mod reply;
pub mod resolve;

pub mod frontend;
#[cfg(not(verus_keep_ghost))]
pub mod net;
#[cfg(not(verus_keep_ghost))]
pub mod service;
