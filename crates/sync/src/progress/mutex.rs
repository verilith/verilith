//! The mutex never deadlocks: while a thread waits for it without a
//! deadline, some thread holds it at some later point.
//!
//! The model is `Mutex::lock`, `lock_slow`, `unlock` and the global parking
//! lot together, one step per atomic access to the lock word and one step
//! per critical section of a parking-lot bucket. The bucket mutex makes
//! each such section atomic with respect to every other access to the same
//! list, and `park`'s re-check of the lock word happens inside it, which is
//! the point of the design: a waiter checks "contended" and joins the list
//! in one step, so an unlock that clears the word either comes before the
//! check (and the waiter does not sleep) or finds the waiter on the list.
//!
//! What is proved (`theorem_deadlock_free`): in every fair execution,
//! if a thread is inside `lock()` at time `i`, some thread is in its
//! critical section at some time `j >= i`. The proof rests on two
//! invariants, both checked inductively over every step of every thread:
//!
//! - the lock word is nonzero only while some thread holds the lock, and
//! - **no lost wakeups**: while any thread sleeps on the list, either the
//!   word says "contended" (so the holder's unlock will wake someone), or
//!   some thread is already committed to waking a sleeper or to marking
//!   the word contended.
//!
//! Not proved, because it is false: that every waiter eventually gets the
//! lock. Drepper's mutex lets a newcomer take the lock between an unlock
//! and the woken thread's retry, as parking_lot's does between its
//! fairness timeouts. Threads that hold the lock are assumed to release
//! it, which the model builds in: a holder's next step is its unlock.
use super::trace::*;
use vstd::prelude::*;

verus! {

/// Where a thread is in the lock protocol.
pub enum Ph {
    /// Not inside `lock`, `try_lock*` or `unlock`.
    Idle,
    /// About to try the fast-path CAS from 0 to 1.
    Fast,
    /// In `lock_slow`'s spin loop, about to load the word; `left` is how
    /// many more snoozes the backoff allows.
    Spin { left: nat },
    /// The spin loop saw 0 and is about to CAS it to 1.
    SpinCas { left: nat },
    /// About to swap the word to 2 (`swap_contended`).
    Swap,
    /// In `park`, about to lock the bucket and re-check that the word is 2.
    Check,
    /// Asleep in `park` with waiter ticket `tk`.
    Asleep { tk: nat },
    /// Holds the lock.
    Crit,
    /// Released a contended lock; about to take one sleeper off the list.
    Unpark,
    /// Took sleeper `tk` off the list; about to set its `notified` flag.
    Notify { tk: nat },
}

pub struct Th {
    pub ph: Ph,
    /// Whether the current call has a deadline (`try_lock`,
    /// `try_lock_for`, `try_lock_until`).
    pub timed: bool,
}

pub struct St {
    /// The lock word: 0 unlocked, 1 locked, 2 locked and contended.
    pub word: nat,
    pub th: Seq<Th>,
    /// Tickets of the waiters on the parking-lot list for this lock.
    pub list: Set<nat>,
    /// The thread each ticket belongs to.
    pub owner: Map<nat, nat>,
    /// Tickets whose `notified` flag is set.
    pub notified: Set<nat>,
    /// The next fresh ticket (each `park` call makes a new `Waiter`).
    pub next_tk: nat,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.word == 0
    &&& s.th.len() == n
    &&& forall|t: int| 0 <= t < n ==> (#[trigger] s.th[t]).ph == Ph::Idle
    &&& s.list.is_empty()
    &&& s.notified.is_empty()
    &&& s.next_tk == 0
}

pub open spec fn ph(s: St, t: nat) -> Ph {
    s.th[t as int].ph
}

pub open spec fn timed(s: St, t: nat) -> bool {
    s.th[t as int].timed
}

/// Thread `t` moves to phase `p`.
pub open spec fn go(s: St, t: nat, p: Ph) -> St {
    St { th: s.th.update(t as int, Th { ph: p, timed: s.th[t as int].timed }), ..s }
}

/// One step of thread `t`.
pub open spec fn step(s: St, t: nat, s2: St) -> bool {
    match ph(s, t) {
        // Call `lock` (untimed) or a `try_lock*` (timed), or do nothing.
        Ph::Idle => s2 == s || exists|b: bool|
            s2 == (St { th: s.th.update(t as int, Th { ph: Ph::Fast, timed: b }), ..s }),
        // `cas(UNLOCKED, LOCKED)`. On failure `lock_slow` starts a fresh
        // backoff; `try_lock` instead gives up.
        Ph::Fast => if s.word == 0 {
            s2 == (St { word: 1, ..go(s, t, Ph::Crit) })
        } else {
            (exists|left: nat| s2 == go(s, t, Ph::Spin { left })) || (timed(s, t) && s2 == go(s, t, Ph::Idle))
        },
        // `while !backoff.is_completed() { let st = self.load(); ... }`
        Ph::Spin { left } => if left == 0 {
            s2 == go(s, t, Ph::Swap)
        } else if s.word == 0 {
            s2 == go(s, t, Ph::SpinCas { left })
        } else if s.word == 2 {
            s2 == go(s, t, Ph::Swap)
        } else {
            s2 == go(s, t, Ph::Spin { left: (left - 1) as nat })
        },
        Ph::SpinCas { left } => if s.word == 0 {
            s2 == (St { word: 1, ..go(s, t, Ph::Crit) })
        } else {
            s2 == go(s, t, Ph::Spin { left: (left - 1) as nat })
        },
        // `swap_contended`: on 0 the lock is ours (marked contended).
        Ph::Swap => if s.word == 0 {
            s2 == (St { word: 2, ..go(s, t, Ph::Crit) })
        } else {
            s2 == (St { word: 2, ..go(s, t, Ph::Check) })
        },
        // `Mutex::check`'s bucket section (park if the word is still 2).
        // If the check fails, `park` returns and `lock_slow` loops (or,
        // past the deadline, gives up).
        Ph::Check => if s.word == 2 {
            s2 == (St {
                list: s.list.insert(s.next_tk),
                owner: s.owner.insert(s.next_tk, t),
                next_tk: s.next_tk + 1,
                ..go(s, t, Ph::Asleep { tk: s.next_tk })
            })
        } else {
            s2 == go(s, t, Ph::Swap) || (timed(s, t) && s2 == go(s, t, Ph::Idle))
        },
        // `while !me.notified.load(SeqCst) { park() }`. With a deadline,
        // the thread may time out: it leaves the list if it is still on it
        // and gives up; if a waker already took it off, `park` reports a
        // wakeup and `lock_slow` retries.
        Ph::Asleep { tk } => if s.notified.contains(tk) {
            s2 == go(s, t, Ph::Swap)
        } else if !timed(s, t) {
            s2 == s
        } else if s.list.contains(tk) {
            s2 == s || s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Idle) })
        } else {
            s2 == s || s2 == go(s, t, Ph::Swap)
        },
        // `unlock`: swap 0, then wake one sleeper if the word was 2.
        Ph::Crit => if s.word == 2 {
            s2 == (St { word: 0, ..go(s, t, Ph::Unpark) })
        } else {
            s2 == (St { word: 0, ..go(s, t, Ph::Idle) })
        },
        // `Mutex::unpark_one`'s bucket section.
        Ph::Unpark => if s.list.is_empty() {
            s2 == go(s, t, Ph::Idle)
        } else {
            exists|tk: nat| s.list.contains(tk) && s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Notify { tk }) })
        },
        // `w.notified.store(true); w.thread.unpark()`.
        Ph::Notify { tk } => s2 == (St { notified: s.notified.insert(tk), ..go(s, t, Ph::Idle) }),
    }
}

/// An execution: `ex(0)` is initial and step `i` is taken by `sched(i)`.
pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

pub open spec fn crit(s: St, n: nat) -> bool {
    exists|t: nat| t < n && ph(s, t) == Ph::Crit
}

/// Inside `lock()`: called and not yet holding the lock.
pub open spec fn waiting(p: Ph) -> bool {
    match p {
        Ph::Fast | Ph::Spin { .. } | Ph::SpinCas { .. } | Ph::Swap | Ph::Check | Ph::Asleep { .. } => true,
        _ => false,
    }
}

/// A thread whose own steps will mark the word contended (or take the
/// lock), or a thread about to wake a sleeper.
pub open spec fn committed(s: St, u: nat) -> bool {
    match ph(s, u) {
        Ph::Unpark | Ph::Swap => true,
        Ph::Asleep { tk } => !s.list.contains(tk),
        _ => false,
    }
}

pub open spec fn inv(s: St, n: nat) -> bool {
    &&& s.th.len() == n
    &&& s.word <= 2
    // The word is nonzero only while someone holds the lock.
    &&& s.word != 0 ==> crit(s, n)
    // Tickets on the list or being notified are old, belong to the
    // sleeper that took them, and are not yet notified.
    &&& forall|tk: nat| #[trigger] s.list.contains(tk) ==> {
        &&& tk < s.next_tk
        &&& !s.notified.contains(tk)
        &&& s.owner[tk] < n
        &&& ph(s, s.owner[tk]) == (Ph::Asleep { tk })
    }
    &&& forall|tk: nat| #[trigger] s.notified.contains(tk) ==> tk < s.next_tk
    &&& forall|t: nat| t < n ==> match #[trigger] ph(s, t) {
        Ph::Asleep { tk } => tk < s.next_tk && s.owner[tk] == t,
        Ph::Notify { tk } => tk < s.next_tk && !s.list.contains(tk),
        _ => true,
    }
    // A sleeper taken off the list but not yet notified has a waker.
    &&& forall|t: nat| t < n ==> match #[trigger] ph(s, t) {
        Ph::Asleep { tk } => !s.list.contains(tk) && !s.notified.contains(tk)
            ==> exists|u: nat| u < n && #[trigger] ph(s, u) == (Ph::Notify { tk }),
        _ => true,
    }
    // No lost wakeups.
    &&& !s.list.is_empty() ==> s.word == 2 || exists|u: nat| u < n && #[trigger] committed(s, u)
}

pub proof fn lemma_init(s: St, n: nat)
    requires
        init(s, n),
    ensures
        inv(s, n),
{
    assert forall|t: nat| t < n implies #[trigger] ph(s, t) == Ph::Idle by {
        assert(s.th[t as int].ph == Ph::Idle);
    }
}

/// Only `t`'s own step changes `t`'s phase, and nothing changes the
/// thread count.
pub proof fn lemma_step_frame(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        timed(s2, t) == timed(s, t) || ph(s, t) == Ph::Idle,
        forall|tk: nat| s.notified.contains(tk) ==> #[trigger] s2.notified.contains(tk),
        forall|tk: nat| #[trigger] s2.list.contains(tk) ==> s.list.contains(tk) || tk >= s.next_tk,
        s2.next_tk >= s.next_tk,
{
}

pub proof fn lemma_step(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        inv(s2, n),
{
    lemma_step_frame(s, n, t, s2);
    // The holder, if any, keeps holding unless it is the one stepping.
    if s2.word != 0 {
        match ph(s, t) {
            Ph::Fast | Ph::SpinCas { .. } | Ph::Swap => {
                if ph(s2, t) != Ph::Crit {
                    let h = choose|h: nat| h < n && ph(s, h) == Ph::Crit;
                    assert(ph(s2, h) == Ph::Crit);
                } else {
                    assert(ph(s2, t) == Ph::Crit);
                }
            },
            _ => {
                let h = choose|h: nat| h < n && ph(s, h) == Ph::Crit;
                assert(h != t);
                assert(ph(s2, h) == Ph::Crit);
            },
        }
    }
    assert forall|tk: nat| #[trigger] s2.list.contains(tk) implies {
        &&& tk < s2.next_tk
        &&& !s2.notified.contains(tk)
        &&& s2.owner[tk] < n
        &&& ph(s2, s2.owner[tk]) == (Ph::Asleep { tk })
    } by {
        if s.list.contains(tk) {
            let o = s.owner[tk];
            if o == t {
                // A sleeper that steps either stays put or leaves the list.
                assert(ph(s, t) == (Ph::Asleep { tk }));
            }
        }
    }
    assert forall|t1: nat| t1 < n implies match #[trigger] ph(s2, t1) {
        Ph::Asleep { tk } => tk < s2.next_tk && s2.owner[tk] == t1,
        Ph::Notify { tk } => tk < s2.next_tk && !s2.list.contains(tk),
        _ => true,
    } by {
        if t1 != t {
            assert(ph(s2, t1) == ph(s, t1));
            match ph(s, t1) {
                Ph::Asleep { tk } => {
                    if ph(s, t) is Check && s.word == 2 {
                        assert(tk != s.next_tk);
                    }
                },
                Ph::Notify { tk } => {
                    if s2.list.contains(tk) {
                        assert(s.list.contains(tk) || tk >= s.next_tk);
                    }
                },
                _ => {},
            }
        }
    }
    assert forall|t1: nat| t1 < n implies match #[trigger] ph(s2, t1) {
        Ph::Asleep { tk } => !s2.list.contains(tk) && !s2.notified.contains(tk)
            ==> exists|u: nat| u < n && #[trigger] ph(s2, u) == (Ph::Notify { tk }),
        _ => true,
    } by {
        match ph(s2, t1) {
            Ph::Asleep { tk } => {
                if !s2.list.contains(tk) && !s2.notified.contains(tk) {
                    if t1 == t {
                        // Only `Check` puts a thread to sleep, and on the list.
                        assert(ph(s, t) == (Ph::Asleep { tk }));
                        assert(!s.list.contains(tk));
                    }
                    assert(ph(s, t1) == (Ph::Asleep { tk }));
                    if s.list.contains(tk) {
                        // Taken off by an unparker (which now notifies it)
                        // or by its own timeout (then it is not asleep).
                        match ph(s, t) {
                            Ph::Unpark => {
                                let tk2 = choose|tk2: nat| s.list.contains(tk2) && s2 == (St { list: s.list.remove(tk2), ..go(s, t, Ph::Notify { tk: tk2 }) });
                                assert(tk2 == tk);
                                assert(ph(s2, t) == (Ph::Notify { tk }));
                            },
                            _ => {},
                        }
                    } else {
                        let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::Notify { tk });
                        assert(u != t);
                        assert(ph(s2, u) == (Ph::Notify { tk }));
                    }
                }
            },
            _ => {},
        }
    }
    // No lost wakeups.
    if !s2.list.is_empty() && s2.word != 2 {
        lemma_no_lost_wakeup(s, n, t, s2);
    }
}

proof fn lemma_no_lost_wakeup(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        !s2.list.is_empty(),
        s2.word != 2,
    ensures
        exists|u: nat| u < n && #[trigger] committed(s2, u),
{
    let x = s2.list.choose();
    assert(s2.list.contains(x));
    match ph(s, t) {
        Ph::Unpark => {
            let tk = choose|tk: nat| s.list.contains(tk) && s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Notify { tk }) });
            let w = s.owner[tk];
            assert(w != t);
            assert(ph(s2, w) == ph(s, w));
            assert(committed(s2, w));
        },
        Ph::Swap => {
            assert(false);
        },
        Ph::Asleep { tk } => {
            if ph(s2, t) == Ph::Swap {
                assert(committed(s2, t));
            } else {
                // The list only lost `tk` or nothing, so it was nonempty.
                assert(s.list.contains(x));
                assert(!s.list.is_empty());
                let u = choose|u: nat| u < n && #[trigger] committed(s, u);
                if u == t {
                    assert(s2 == s);
                    assert(committed(s2, u));
                } else {
                    assert(ph(s2, u) == ph(s, u));
                    if let Ph::Asleep { tk: tku } = ph(s, u) {
                        assert(!s2.list.contains(tku));
                    }
                    assert(committed(s2, u));
                }
            }
        },
        _ => if !committed(s2, t) {
            assert(s.list.contains(x));
            assert(!s.list.is_empty());
            assert(s.word != 2);
            let u = choose|u: nat| u < n && #[trigger] committed(s, u);
            assert(u != t);
            assert(ph(s2, u) == ph(s, u));
            if let Ph::Asleep { tk: tku } = ph(s, u) {
                assert(!s2.list.contains(tku));
            }
            assert(committed(s2, u));
        },
    }
}

pub proof fn lemma_inv(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(i), n),
    decreases i,
{
    if i == 0 {
        lemma_init(ex(0), n);
    } else {
        lemma_inv(ex, sched, n, (i - 1) as nat);
        assert(sched((i - 1) as nat) < n && step(ex((i - 1) as nat), sched((i - 1) as nat), ex(i)));
        lemma_step(ex((i - 1) as nat), n, sched((i - 1) as nat), ex(i));
    }
}

/// Someone holds the lock at or after `j`.
pub open spec fn held_after(ex: spec_fn(nat) -> St, n: nat, j: nat) -> bool {
    exists|k: nat| k >= j && #[trigger] crit(ex(k), n)
}

/// The hypothesis the liveness proof refutes: nobody holds the lock at or
/// after `i`.
pub open spec fn nobody_after(ex: spec_fn(nat) -> St, n: nat, i: nat) -> bool {
    forall|j: nat| j >= i ==> !crit(#[trigger] ex(j), n)
}

/// What the proof needs about one step: the invariant, and the frame.
proof fn lemma_at(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, m: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(m), n),
        inv(ex(m + 1), n),
        sched(m) < n,
        step(ex(m), sched(m), ex(m + 1)),
        forall|u: nat| u < n && u != sched(m) ==> #[trigger] ex(m + 1).th[u as int] == ex(m).th[u as int],
        forall|tk: nat| ex(m).notified.contains(tk) ==> #[trigger] ex(m + 1).notified.contains(tk),
        forall|tk: nat| #[trigger] ex(m + 1).list.contains(tk) ==> ex(m).list.contains(tk) || tk >= ex(m).next_tk,
{
    lemma_inv(ex, sched, n, m);
    lemma_inv(ex, sched, n, m + 1);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step_frame(ex(m), n, sched(m), ex(m + 1));
}

/// `t`'s phase and deadline flag stay put until `t` steps, at `k`.
proof fn lemma_until_step(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, j: nat) -> (k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
    ensures
        k >= j,
        sched(k) == t,
        ex(k).th[t as int] == ex(j).th[t as int],
{
    let k = lemma_next_step(sched, n, t, j);
    let f = |m: nat| ex(m).th[t as int];
    assert forall|m: nat| j <= m < k && #[trigger] sched(m) != t implies f(m + 1) == f(m) by {
        lemma_at(ex, sched, n, m);
    }
    lemma_frame(sched, f, t, j, k);
    k
}

/// A thread about to CAS or swap takes the lock at its next step, since
/// the word stays 0 while nobody holds the lock.
proof fn lemma_active(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) is Fast || ph(ex(j), t) is SpinCas || ph(ex(j), t) is Swap,
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    assert(!crit(ex(k), n));
    assert(ex(k).word == 0);
    assert(ph(ex(k + 1), t) == Ph::Crit);
    assert(crit(ex(k + 1), n));
}

proof fn lemma_spin(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) is Spin,
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    assert(!crit(ex(k), n));
    lemma_active(ex, sched, n, i, t, k + 1);
}

proof fn lemma_check(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) is Check,
        !timed(ex(j), t),
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    assert(!crit(ex(k), n));
    lemma_active(ex, sched, n, i, t, k + 1);
}

/// A notified sleeper retries at its next step.
proof fn lemma_awake(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat, tk: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) == (Ph::Asleep { tk }),
        ex(j).notified.contains(tk),
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_notified_stays(ex, sched, n, tk, j, k);
    lemma_at(ex, sched, n, k);
    lemma_active(ex, sched, n, i, t, k + 1);
}

proof fn lemma_notified_stays(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, tk: nat, j: nat, k: nat)
    requires
        run(ex, sched, n),
        j <= k,
        ex(j).notified.contains(tk),
    ensures
        ex(k).notified.contains(tk),
    decreases k - j,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        lemma_notified_stays(ex, sched, n, tk, j + 1, k);
    }
}

/// A sleeper already taken off the list is woken: its waker sets the flag
/// at its next step, and the sleeper cannot go anywhere before that except
/// to retry.
proof fn lemma_pending(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat, tk: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) == (Ph::Asleep { tk }),
        !ex(j).list.contains(tk),
    ensures
        false,
{
    lemma_at(ex, sched, n, j);
    if ex(j).notified.contains(tk) {
        lemma_awake(ex, sched, n, i, t, j, tk);
    }
    let u = choose|u: nat| u < n && #[trigger] ph(ex(j), u) == (Ph::Notify { tk });
    let k = lemma_until_step(ex, sched, n, u, j);
    lemma_sleeps_until(ex, sched, n, i, t, tk, j, j, k);
    lemma_at(ex, sched, n, k);
    assert(u != t);
    assert(ph(ex(k + 1), t) == (Ph::Asleep { tk }));
    assert(ex(k + 1).notified.contains(tk));
    lemma_awake(ex, sched, n, i, t, k + 1, tk);
}

/// Until `k`, a sleeper off the list stays asleep and off the list (any
/// other move leads to a contradiction).
proof fn lemma_sleeps_until(
    ex: spec_fn(nat) -> St,
    sched: spec_fn(nat) -> nat,
    n: nat,
    i: nat,
    t: nat,
    tk: nat,
    j: nat,
    m: nat,
    k: nat,
)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        i <= j <= m <= k,
        ph(ex(m), t) == (Ph::Asleep { tk }),
        !ex(m).list.contains(tk),
    ensures
        ph(ex(k), t) == (Ph::Asleep { tk }),
        !ex(k).list.contains(tk),
    decreases k - m,
{
    if m < k {
        lemma_at(ex, sched, n, m);
        if ex(m).notified.contains(tk) {
            lemma_awake(ex, sched, n, i, t, m, tk);
        }
        assert(tk < ex(m).next_tk);
        if sched(m) == t {
            if ph(ex(m + 1), t) is Swap {
                lemma_active(ex, sched, n, i, t, m + 1);
            }
            assert(ex(m + 1) == ex(m));
        }
        lemma_sleeps_until(ex, sched, n, i, t, tk, j, m + 1, k);
    }
}

/// While a deadline-free sleeper is on the list, an unparker takes some
/// sleeper off it at its next step, and that sleeper is then woken.
proof fn lemma_unpark(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat, tk0: nat, u: nat, j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t0 < n,
        u < n,
        j >= i,
        ph(ex(j), t0) == (Ph::Asleep { tk: tk0 }),
        !timed(ex(j), t0),
        ex(j).list.contains(tk0),
        ph(ex(j), u) == Ph::Unpark,
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, u, j);
    lemma_listed_until(ex, sched, n, i, t0, tk0, j, k);
    lemma_at(ex, sched, n, k);
    let s = ex(k);
    let s2 = ex(k + 1);
    assert(s.list.contains(tk0));
    let tk = choose|tk: nat| s.list.contains(tk) && s2 == (St { list: s.list.remove(tk), ..go(s, u, Ph::Notify { tk }) });
    let w = s.owner[tk];
    assert(w != u);
    assert(ph(s2, w) == (Ph::Asleep { tk }));
    lemma_pending(ex, sched, n, i, w, k + 1, tk);
}

/// A deadline-free sleeper stays asleep on the list until `k`, unless it is
/// taken off it, which leads to a contradiction.
proof fn lemma_listed_until(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat, tk0: nat, m: nat, k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t0 < n,
        i <= m <= k,
        ph(ex(m), t0) == (Ph::Asleep { tk: tk0 }),
        !timed(ex(m), t0),
        ex(m).list.contains(tk0),
    ensures
        ph(ex(k), t0) == (Ph::Asleep { tk: tk0 }),
        !timed(ex(k), t0),
        ex(k).list.contains(tk0),
    decreases k - m,
{
    if m < k {
        lemma_at(ex, sched, n, m);
        if sched(m) == t0 {
            assert(!ex(m).notified.contains(tk0));
            assert(ex(m + 1) == ex(m));
        }
        assert(ph(ex(m + 1), t0) == (Ph::Asleep { tk: tk0 }));
        if !ex(m + 1).list.contains(tk0) {
            lemma_pending(ex, sched, n, i, t0, m + 1, tk0);
        }
        lemma_listed_until(ex, sched, n, i, t0, tk0, m + 1, k);
    }
}

proof fn lemma_asleep(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat, j: nat, tk0: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t0 < n,
        j >= i,
        ph(ex(j), t0) == (Ph::Asleep { tk: tk0 }),
        !timed(ex(j), t0),
    ensures
        false,
{
    lemma_at(ex, sched, n, j);
    let s = ex(j);
    if !s.list.contains(tk0) {
        lemma_pending(ex, sched, n, i, t0, j, tk0);
    }
    assert(!crit(s, n));
    assert(s.word == 0);
    assert(!s.list.is_empty());
    let u = choose|u: nat| u < n && #[trigger] committed(s, u);
    match ph(s, u) {
        Ph::Unpark => lemma_unpark(ex, sched, n, i, t0, tk0, u, j),
        Ph::Swap => lemma_active(ex, sched, n, i, u, j),
        Ph::Asleep { tk } => lemma_pending(ex, sched, n, i, u, j, tk),
        _ => {},
    }
}

/// Deadlock freedom: in a fair execution, a thread waiting in `lock()` at
/// time `i` (with no deadline) sees the lock held by some thread, possibly
/// itself, at some time `j >= i`.
pub proof fn theorem_deadlock_free(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t0 < n,
        waiting(ph(ex(i), t0)),
        !timed(ex(i), t0),
    ensures
        held_after(ex, n, i),
{
    if !held_after(ex, n, i) {
        assert(nobody_after(ex, n, i));
        match ph(ex(i), t0) {
            Ph::Fast | Ph::SpinCas { .. } | Ph::Swap => lemma_active(ex, sched, n, i, t0, i),
            Ph::Spin { .. } => lemma_spin(ex, sched, n, i, t0, i),
            Ph::Check => lemma_check(ex, sched, n, i, t0, i),
            Ph::Asleep { tk } => lemma_asleep(ex, sched, n, i, t0, i, tk),
            _ => {},
        }
    }
}

/// So a waiter that never gets the lock sees it taken infinitely often:
/// the lock is never stuck.
pub proof fn corollary_never_stuck(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t0 < n,
        forall|j: nat| j >= i ==> waiting(#[trigger] ph(ex(j), t0)) && !timed(ex(j), t0),
    ensures
        forall|j: nat| j >= i ==> #[trigger] held_after(ex, n, j),
{
    assert forall|j: nat| j >= i implies #[trigger] held_after(ex, n, j) by {
        assert(waiting(ph(ex(j), t0)) && !timed(ex(j), t0));
        theorem_deadlock_free(ex, sched, n, j, t0);
    }
}

} // verus!

verus! {

/// The hypotheses are satisfiable: with every thread idle forever under a
/// round-robin schedule, `run` and `fair` both hold.
pub proof fn lemma_nonvacuous(s0: St, n: nat)
    requires
        init(s0, n),
        n > 0,
    ensures
        run(|i: nat| s0, |i: nat| i % n, n),
        fair(|i: nat| i % n, n),
{
    lemma_round_robin_fair(n);
    let ex = |i: nat| s0;
    let sched = |i: nat| i % n;
    assert forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1)) by {
        let t = i % n;
        assert(s0.th[t as int].ph == Ph::Idle);
    }
}

/// The model as `crate::model::Model` takes it: `src/mutex.rs` holds one
/// and is verified to follow it.
pub struct P;

impl crate::model::Protocol for P {
    type St = St;
    type Th = Th;

    open spec fn init(s: St, n: nat) -> bool {
        init(s, n)
    }

    open spec fn step(s: St, t: nat, s2: St) -> bool {
        step(s, t, s2)
    }

    open spec fn inv(s: St, n: nat) -> bool {
        inv(s, n)
    }

    open spec fn threads(s: St) -> Seq<Th> {
        s.th
    }

    open spec fn idle(th: Th) -> bool {
        th.ph == Ph::Idle
    }

    proof fn lemma_init(s: St, n: nat) {
        lemma_init(s, n);
        assert forall|t: int| 0 <= t < n implies (#[trigger] s.th[t]).ph == Ph::Idle by {}
    }

    proof fn lemma_step(s: St, n: nat, t: nat, s2: St) {
        lemma_step(s, n, t, s2);
        lemma_step_frame(s, n, t, s2);
        assert forall|u: int| 0 <= u < n && u != t implies #[trigger] s2.th[u] == s.th[u] by {
            assert(s2.th[(u as nat) as int] == s.th[(u as nat) as int]);
        }
    }

    proof fn lemma_len(s: St, n: nat) {
    }
}

} // verus!
