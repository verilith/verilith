#![doc = include_str!("../README.md")]
pub mod array_queue;
// Unverified glue over the verified queue; not part of the Verus build,
// where verified functions take extra ghost arguments.
#[cfg(not(verus_only))]
pub mod channel;
#[doc(hidden)]
pub mod chan_core;
#[doc(hidden)]
pub mod chan_model;
#[doc(hidden)]
pub mod chan_sync;
#[doc(hidden)]
pub mod mono;
pub mod mutex;
#[doc(hidden)]
pub mod parking;
#[doc(hidden)]
pub mod progress;
#[doc(hidden)]
pub mod ra;
pub mod rwlock;
pub mod spsc;
#[doc(hidden)]
pub mod util;

vstd::prelude::verus! {
global size_of usize == 8;
}
