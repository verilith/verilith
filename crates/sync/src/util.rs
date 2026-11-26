//! Small trusted helpers shared by the verified modules.
use std::cell::Cell;
use std::sync::Arc;
use vstd::prelude::*;

/// An optional point in time to stop waiting at.
#[derive(Clone, Copy)]
pub struct Deadline(pub Option<std::time::Instant>);

verus! {

/// Keeps a value on its own cache line (128 bytes covers the adjacent-line
/// prefetcher on x86 and the line size on Apple silicon).
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

/// `Arc::clone`, which vstd does not specify.
#[verifier::external_body]
#[inline(always)]
pub fn arc_clone<T>(a: &Arc<T>) -> (r: Arc<T>)
    ensures
        *r == **a,
{
    Arc::clone(a)
}

/// Called when a 64-bit position counter would overflow, which takes at
/// least 2^63 operations on one queue. Aborting rather than wrapping is what
/// rules out ABA on the counters.
#[verifier::external_body]
#[cold]
#[inline(never)]
pub fn exhausted() -> !
    ensures
        false,
{
    std::process::abort()
}

/// Mutable access to the contents of a tracked `Some`.
pub proof fn tracked_borrow_mut<A>(tracked o: &mut Option<A>) -> (tracked r: &mut A)
    requires
        old(o).is_some(),
    ensures
        *r == old(o).unwrap(),
        *final(o) == Some(*final(r)),
{
    match o {
        Some(x) => x,
        None => proof_from_false(),
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDeadline(Deadline);

#[verifier::external_body]
#[inline(always)]
pub fn no_deadline() -> (r: Deadline)
    ensures
        !has_deadline(r),
{
    Deadline(None)
}

/// Reached when a lock is consumed while a leaked guard still holds it.
#[verifier::external_body]
#[cold]
#[inline(never)]
pub fn leaked_guard() -> !
    ensures
        false,
{
    panic!("lock consumed while a leaked guard holds it")
}

/// A pause inside a spin-wait loop.
#[verifier::external_body]
#[inline(always)]
pub fn spin_hint() {
    core::hint::spin_loop()
}

/// Exponential backoff for contended retry loops, as in crossbeam-utils.
/// It only affects timing, never which states are reachable.
#[verifier::external_body]
pub struct Backoff {
    step: Cell<u32>,
}

impl Backoff {
    const SPIN_LIMIT: u32 = 6;
    const YIELD_LIMIT: u32 = 10;

    #[verifier::external_body]
    #[inline]
    pub fn new() -> Self {
        Backoff { step: Cell::new(0) }
    }

    /// Backs off in a lock-free loop: spins only.
    #[verifier::external_body]
    #[inline]
    pub fn spin(&self) {
        for _ in 0..1u32 << self.step.get().min(Self::SPIN_LIMIT) {
            core::hint::spin_loop();
        }
        if self.step.get() <= Self::SPIN_LIMIT {
            self.step.set(self.step.get() + 1);
        }
    }

    /// Backs off while waiting for another thread: spins, then yields.
    #[verifier::external_body]
    #[inline]
    pub fn snooze(&self) {
        if self.step.get() <= Self::SPIN_LIMIT {
            for _ in 0..1u32 << self.step.get() {
                core::hint::spin_loop();
            }
        } else {
            std::thread::yield_now();
        }
        if self.step.get() <= Self::YIELD_LIMIT {
            self.step.set(self.step.get() + 1);
        }
    }

    /// Whether waiting has gone on long enough that the thread should park.
    #[verifier::external_body]
    #[inline]
    pub fn is_completed(&self) -> bool {
        self.step.get() > Self::YIELD_LIMIT
    }
}

/// A fair lock's waiter with `ahead` tickets before its own (counting the
/// holder's) pauses before it looks again: the next in line spins, then
/// yields; the others yield at once, so that on an oversubscribed machine
/// the threads ahead of them get the CPU. Only timing, like `Backoff`.
#[verifier::external_body]
#[inline]
pub fn wait_turn(ahead: u64, backoff: &Backoff) {
    if ahead <= 1 {
        backoff.snooze()
    } else {
        std::thread::yield_now()
    }
}

} // verus!

verus! {

#[verifier::external_body]
pub struct Unparker {
    t: std::thread::Thread,
}

impl Unparker {
    /// A handle to the calling thread.
    #[verifier::external_body]
    pub fn current() -> Self {
        Unparker { t: std::thread::current() }
    }

    /// Wakes the thread if it is parked, or makes its next park return at
    /// once.
    #[verifier::external_body]
    #[inline]
    pub fn unpark(&self) {
        self.t.unpark()
    }
}

/// Whether there is a point in time to stop waiting at.
pub uninterp spec fn has_deadline(d: Deadline) -> bool;

#[verifier::external_body]
#[inline]
pub fn is_timed(d: &Deadline) -> (r: bool)
    ensures
        r == has_deadline(*d),
{
    d.0.is_some()
}

/// How long a thread may still sleep.
#[verifier::external_body]
pub struct TimeLeft(Option<std::time::Duration>);

/// Whether the deadline has passed, and if not, how long is left.
#[verifier::external_body]
pub fn time_left(d: &Deadline) -> (r: (bool, TimeLeft))
    ensures
        r.0 ==> has_deadline(*d),
{
    match d.0 {
        None => (false, TimeLeft(None)),
        Some(at) => {
            let now = std::time::Instant::now();
            if now >= at {
                (true, TimeLeft(None))
            } else {
                (false, TimeLeft(Some(at - now)))
            }
        }
    }
}

/// Parks the calling thread until it is unparked or the time is up. It may
/// also return early for no reason; callers re-check and park again.
#[verifier::external_body]
pub fn park_for(t: TimeLeft) {
    match t.0 {
        None => std::thread::park(),
        Some(d) => std::thread::park_timeout(d),
    }
}

} // verus!

pub use crate::fair::{Lock, LockGuard, LockInv};
