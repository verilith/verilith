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

/// The shard of the shared cache a name's entries live in (any function
/// of the lowercased name would do).
pub(crate) fn shared_shard(n: usize, name: &[u8]) -> usize {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &c in name {
        h = (h ^ c.to_ascii_lowercase() as u64).wrapping_mul(0x100_0000_01b3);
    }
    (h % n as u64) as usize
}
pub mod frontend;
#[cfg(not(verus_keep_ghost))]
pub mod net;
#[cfg(not(verus_keep_ghost))]
pub mod service;
