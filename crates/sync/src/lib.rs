#![doc = include_str!("../README.md")]
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_assignments, dead_code, unused_braces, unused_parens))]
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

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-sync is proven for 64-bit targets only");

// The queues' position arithmetic is proven with 64-bit usize. Only where it
// holds, so that a 32-bit build stops at the error above rather than at the
// size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
global size_of usize == 8;
}
