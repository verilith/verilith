#![doc = include_str!("../README.md")]
pub mod array_queue;
// Unverified glue over the verified queue; not part of the Verus build,
// where verified functions take extra ghost arguments.
#[cfg(not(verus_only))]
pub mod channel;
pub mod chan_core;
pub mod chan_model;
pub mod chan_sync;
pub mod mono;
pub mod mutex;
pub mod parking;
pub mod progress;
pub mod ra;
pub mod rwlock;
pub mod spsc;
pub mod util;

vstd::prelude::verus! {
global size_of usize == 8;
}
