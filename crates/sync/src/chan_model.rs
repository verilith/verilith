//! The channel's progress model as a ghost resource the code must follow:
//! `model::Model` for the protocol of `progress::channel`.
//!
//! `src/chan_sync.rs` keeps one per direction inside the channel's
//! invariant, next to the permissions for the real atomics, and the
//! invariant ties the two together (the count of handles is `alive`, a
//! waiter's flag is set exactly when its ticket is in `notified`, and so
//! on). So Verus checks, at every access the channel code makes to shared
//! state, that the model can make the same move. See `src/model.rs` for
//! the resource and its one assumption, `Model::pool_nonempty`.
use vstd::prelude::*;

verus! {

/// The right to take steps as one thread of the channel's model, with that
/// thread's current phase.
pub type ThreadTok = crate::model::Tok<crate::progress::channel::P>;

/// The channel's model.
pub type Model = crate::model::Model<crate::progress::channel::P>;

} // verus!
