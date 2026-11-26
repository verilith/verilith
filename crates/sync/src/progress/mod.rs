//! Progress proofs: the blocking protocols never strand a thread.
//!
//! The safety proofs in the rest of the crate say what the primitives do
//! when an operation finishes. These modules prove that operations do
//! finish: that a lock is always eventually taken while someone wants it,
//! and that a thread parked on a channel is always woken once it can make
//! progress. Verus has no temporal logic, so each property is stated over
//! infinite executions directly: an execution is a sequence of states
//! `ex(0), ex(1), ...` where step `i` is taken by thread `sched(i)`, and a
//! schedule is fair when it lets every thread take infinitely many steps
//! (`trace::fair`). Nothing else is assumed about timing.
//!
//! Each module models one protocol at the granularity of its atomic
//! accesses, including the global parking lot (`src/lot.rs`) or the
//! channel's waiter lists. `TRUST.md` ("Progress") maps every model step
//! to the code it stands for and explains why one step per access is faithful.
//! Everything here is spec and proof code: it compiles to nothing.
pub mod channel;
pub mod handles;
pub mod mutex;
pub mod queue;
pub mod rwlock;
pub mod ticket;
pub mod trace;
