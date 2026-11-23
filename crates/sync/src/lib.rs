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

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-sync is proven for 64-bit targets only");

// The queues' position arithmetic is proven with 64-bit usize. Only where it
// holds, so that a 32-bit build stops at the error above rather than at the
// size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
global size_of usize == 8;
}
