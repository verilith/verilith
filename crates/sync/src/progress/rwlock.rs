//! The reader-writer lock never deadlocks: while a thread waits for it
//! without a deadline, some thread holds it at some later point.
//!
//! The model is `read`, `write`, their slow paths, `unlock_read`,
//! `unlock_write`, `downgrade` and the global parking lot, one step per
//! atomic access to the lock word and one per bucket critical section, as
//! for the mutex (see `super::mutex`). The lock word is kept as its fields
//! (writer bit, the two parking hints, reader count) rather than as bits;
//! `TRUST.md` gives the correspondence.
//!
//! The parking hints are what makes this lock subtler than the mutex: a
//! waiting writer sets "writer waiting", which holds off new readers, and
//! a waiter that sets "parked" relies on whoever clears it to wake every
//! sleeper. The proof shows the hints are never left set with nobody to
//! clear them, and that a sleeper is never left on the list with "parked"
//! clear and nobody about to wake it:
//!
//! - the writer bit is set only while a writer holds the lock, and the
//!   reader count is exactly the number of threads holding a read lock;
//! - the hints are set only while someone holds the lock or the last
//!   reader out is about to clear them;
//! - **no lost wakeups**: while anyone sleeps on the list, "parked" is set
//!   or some thread is about to wake every sleeper.
//!
//! `theorem_deadlock_free` then follows: if nobody ever held the lock
//! again, the threads finishing an unlock would wake everyone and go idle,
//! the word would settle at 0 with nobody asleep, and the next load by the
//! waiting thread would see a free lock and take it.
//!
//! As with the mutex, this is deadlock freedom, not starvation freedom:
//! writers can starve each other, and a stream of writers can starve
//! readers (the "writer waiting" hint is what keeps readers from starving
//! writers). A thread must not wait for the lock while it holds it, which
//! the model builds in by giving each thread one lock operation at a time.
use super::trace::*;
use vstd::prelude::*;

verus! {

/// The lock word: bit 0 `w`, bit 1 `pk`, bit 2 `ww`, bits 3.. `rc`.
pub struct Word {
    pub w: bool,
    pub pk: bool,
    pub ww: bool,
    pub rc: nat,
}

pub open spec fn zero() -> Word {
    Word { w: false, pk: false, ww: false, rc: 0 }
}

/// `s & BLOCKS_READ != 0`
pub open spec fn blocks_read(x: Word) -> bool {
    x.w || x.ww
}

/// `s & WRITER != 0 || s >> 3 != 0`
pub open spec fn blocks_write(x: Word) -> bool {
    x.w || x.rc != 0
}

pub enum Ph {
    Idle,
    /// In `read_slow` (`wr` false) or `write_slow` (`wr` true), about to
    /// load the word; `left` is how many more snoozes the backoff allows.
    Load { wr: bool, left: nat },
    /// Saw `s`, free for this kind of lock; about to CAS from `s`.
    Cas { wr: bool, s: Word, left: nat },
    /// Saw `s`, blocked; about to CAS the parking hints into `s`.
    Flag { wr: bool, s: Word, left: nat },
    /// In `park`, about to lock the bucket and re-check.
    Check { wr: bool, left: nat },
    /// Asleep in `park` with waiter ticket `tk`.
    Asleep { wr: bool, tk: nat, left: nat },
    RCrit,
    WCrit,
    /// The last reader left with a hint set; about to clear both hints.
    Clear,
    /// About to take every sleeper off the list (`unpark_all`'s bucket
    /// section). `rd`: this thread holds a read lock (after `downgrade`).
    Unpark { rd: bool },
    /// Setting the `notified` flag of each sleeper in `woken`, in order.
    Notify { rd: bool, woken: Seq<nat> },
}

pub struct Th {
    pub ph: Ph,
    pub timed: bool,
}

pub struct St {
    pub word: Word,
    pub th: Seq<Th>,
    pub list: Set<nat>,
    pub owner: Map<nat, nat>,
    pub notified: Set<nat>,
    pub next_tk: nat,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.word == zero()
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

pub open spec fn go(s: St, t: nat, p: Ph) -> St {
    St { th: s.th.update(t as int, Th { ph: p, timed: s.th[t as int].timed }), ..s }
}

pub open spec fn gow(s: St, t: nat, p: Ph, w: Word) -> St {
    St { word: w, ..go(s, t, p) }
}

/// `woken` holds exactly the tickets in `list`.
pub open spec fn lists(woken: Seq<nat>, list: Set<nat>) -> bool {
    forall|tk: nat| #[trigger] woken.contains(tk) <==> list.contains(tk)
}

/// One step of thread `t`.
pub open spec fn step(s: St, t: nat, s2: St) -> bool {
    let x = s.word;
    match ph(s, t) {
        // Call `read`/`try_read*` (start at the first load) or
        // `write`/`try_write*` (start at the fast-path CAS from 0).
        Ph::Idle => s2 == s || exists|b: bool, left: nat|
            s2 == (St { th: s.th.update(t as int, Th { ph: Ph::Load { wr: false, left }, timed: b }), ..s })
            || s2 == (St { th: s.th.update(t as int, Th { ph: Ph::Cas { wr: true, s: zero(), left }, timed: b }), ..s }),
        Ph::Load { wr, left } => {
            let free = if wr { !blocks_write(x) } else { !blocks_read(x) };
            let hinted = if wr { x.pk && x.ww } else { x.pk };
            if free {
                s2 == go(s, t, Ph::Cas { wr, s: x, left })
            } else if timed(s, t) && s2 == go(s, t, Ph::Idle) {
                // `try_read`/`try_write` fail at once.
                true
            } else if !x.pk && left > 0 {
                s2 == go(s, t, Ph::Load { wr, left: (left - 1) as nat })
            } else if !hinted {
                s2 == go(s, t, Ph::Flag { wr, s: x, left })
            } else {
                s2 == go(s, t, Ph::Check { wr, left })
            }
        },
        // `cas_read(s)` adds a reader; `cas_write(s)` sets the writer bit,
        // keeping the hints. On failure: spin and reload, or give up.
        Ph::Cas { wr, s: c, left } => if x == c {
            if wr {
                s2 == gow(s, t, Ph::WCrit, Word { w: true, ..x })
            } else {
                s2 == gow(s, t, Ph::RCrit, Word { rc: x.rc + 1, ..x })
            }
        } else {
            s2 == go(s, t, Ph::Load { wr, left }) || (timed(s, t) && s2 == go(s, t, Ph::Idle))
        },
        // `cas_flags(s, PARKED)` for readers, `cas_flags(s, FLAGS)` for
        // writers; the result is ignored and the loop reloads.
        Ph::Flag { wr, s: c, left } => if x == c {
            s2 == gow(s, t, Ph::Load { wr, left }, Word { pk: true, ww: x.ww || wr, ..x })
        } else {
            s2 == go(s, t, Ph::Load { wr, left })
        },
        // `park`'s bucket section: sleep only if still blocked and the
        // parked hint is still set.
        Ph::Check { wr, left } => {
            let blocked = if wr { blocks_write(x) } else { blocks_read(x) };
            if blocked && x.pk {
                s2 == (St {
                    list: s.list.insert(s.next_tk),
                    owner: s.owner.insert(s.next_tk, t),
                    next_tk: s.next_tk + 1,
                    ..go(s, t, Ph::Asleep { wr, tk: s.next_tk, left })
                })
            } else {
                s2 == go(s, t, Ph::Load { wr, left }) || (timed(s, t) && s2 == go(s, t, Ph::Idle))
            }
        },
        Ph::Asleep { wr, tk, left } => if s.notified.contains(tk) {
            s2 == go(s, t, Ph::Load { wr, left })
        } else if !timed(s, t) {
            s2 == s
        } else if s.list.contains(tk) {
            s2 == s || s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Idle) })
        } else {
            s2 == s || s2 == go(s, t, Ph::Load { wr, left })
        },
        // `unlock_read`: `fetch_sub(ONE_READER)`, then if this was the
        // last reader and a hint was set, clear the hints and wake all.
        Ph::RCrit => {
            let x2 = Word { rc: (x.rc - 1) as nat, ..x };
            if x.rc == 1 && (x.pk || x.ww) {
                s2 == gow(s, t, Ph::Clear, x2)
            } else {
                s2 == gow(s, t, Ph::Idle, x2)
            }
        },
        // `unlock_write` (swap 0, wake all if a hint was set) or
        // `downgrade` (`fetch_add(ONE_READER - WRITER)`, wake all if parked).
        Ph::WCrit => {
            ||| s2 == gow(s, t, if x.pk || x.ww { Ph::Unpark { rd: false } } else { Ph::Idle }, zero())
            ||| s2 == gow(s, t, if x.pk { Ph::Unpark { rd: true } } else { Ph::RCrit }, Word { w: false, rc: x.rc + 1, ..x })
        },
        // `clear_flags`: `fetch_and(NOT_FLAGS)`.
        Ph::Clear => s2 == gow(s, t, Ph::Unpark { rd: false }, Word { pk: false, ww: false, ..x }),
        Ph::Unpark { rd } => exists|woken: Seq<nat>|
            #[trigger] lists(woken, s.list)
            && s2 == (St { list: Set::empty(), ..go(s, t, Ph::Notify { rd, woken }) }),
        Ph::Notify { rd, woken } => if woken.len() == 0 {
            s2 == go(s, t, if rd { Ph::RCrit } else { Ph::Idle })
        } else {
            s2 == (St { notified: s.notified.insert(woken[0]), ..go(s, t, Ph::Notify { rd, woken: woken.drop_first() }) })
        },
    }
}

pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

pub open spec fn holds_read(p: Ph) -> bool {
    match p {
        Ph::RCrit => true,
        Ph::Unpark { rd } => rd,
        Ph::Notify { rd, .. } => rd,
        _ => false,
    }
}

pub open spec fn holds(p: Ph) -> bool {
    holds_read(p) || p == Ph::WCrit
}

/// Finishing an unlock: clearing hints or waking sleepers, holding nothing.
pub open spec fn post(p: Ph) -> bool {
    match p {
        Ph::Clear => true,
        Ph::Unpark { rd } => !rd,
        Ph::Notify { rd, .. } => !rd,
        _ => false,
    }
}

pub open spec fn waiting(p: Ph) -> bool {
    match p {
        Ph::Load { .. } | Ph::Cas { .. } | Ph::Flag { .. } | Ph::Check { .. } | Ph::Asleep { .. } => true,
        _ => false,
    }
}

pub open spec fn crit(s: St, n: nat) -> bool {
    exists|t: nat| t < n && #[trigger] holds(ph(s, t))
}

/// The number of threads holding a read lock.
pub open spec fn nreaders(th: Seq<Th>) -> nat
    decreases th.len(),
{
    if th.len() == 0 {
        0
    } else {
        nreaders(th.drop_last()) + if holds_read(th.last().ph) { 1nat } else { 0nat }
    }
}

pub open spec fn waking(s: St, u: nat) -> bool {
    ph(s, u) is Clear || ph(s, u) is Unpark
}

pub open spec fn inv(s: St, n: nat) -> bool {
    &&& s.th.len() == n
    &&& s.word.w ==> exists|t: nat| t < n && #[trigger] ph(s, t) == Ph::WCrit
    &&& s.word.rc == nreaders(s.th)
    // A writer holds the lock alone.
    &&& forall|t: nat| t < n && #[trigger] ph(s, t) == Ph::WCrit ==> s.word.w && s.word.rc == 0
    &&& forall|t: nat, u: nat| t < n && u < n && #[trigger] ph(s, t) == Ph::WCrit && #[trigger] ph(s, u) == Ph::WCrit ==> t == u
    // The hints are set only while someone holds the lock or is about to
    // clear them.
    &&& (s.word.pk || s.word.ww) ==> s.word.w || s.word.rc > 0 || exists|u: nat| u < n && #[trigger] ph(s, u) == Ph::Clear
    &&& forall|tk: nat| #[trigger] s.list.contains(tk) ==> {
        &&& tk < s.next_tk
        &&& !s.notified.contains(tk)
        &&& s.owner[tk] < n
        &&& ph(s, s.owner[tk]) is Asleep
        &&& ph(s, s.owner[tk])->Asleep_tk == tk
    }
    &&& forall|tk: nat| #[trigger] s.notified.contains(tk) ==> tk < s.next_tk
    &&& forall|t: nat| t < n ==> match #[trigger] ph(s, t) {
        Ph::Asleep { tk, .. } => tk < s.next_tk && s.owner[tk] == t,
        Ph::Notify { woken, .. } => forall|tk: nat| #[trigger] woken.contains(tk) ==> tk < s.next_tk && !s.list.contains(tk),
        Ph::Flag { wr, s: c, .. } => if wr { blocks_write(c) } else { blocks_read(c) },
        Ph::Cas { wr, s: c, .. } => if wr { !blocks_write(c) } else { !blocks_read(c) },
        _ => true,
    }
    // A sleeper taken off the list but not yet notified has a waker.
    &&& forall|t: nat| t < n ==> match #[trigger] ph(s, t) {
        Ph::Asleep { tk, .. } => !s.list.contains(tk) && !s.notified.contains(tk)
            ==> exists|u: nat| u < n && #[trigger] ph(s, u) is Notify && ph(s, u)->Notify_woken.contains(tk),
        _ => true,
    }
    // No lost wakeups.
    &&& !s.list.is_empty() ==> s.word.pk || exists|u: nat| u < n && #[trigger] waking(s, u)
}

// ---------------------------------------------------------------------
// Counting readers.

proof fn lemma_nreaders_update(th: Seq<Th>, t: int, x: Th)
    requires
        0 <= t < th.len(),
    ensures
        nreaders(th.update(t, x)) as int == nreaders(th) as int
            - (if holds_read(th[t].ph) { 1int } else { 0int })
            + (if holds_read(x.ph) { 1int } else { 0int }),
    decreases th.len(),
{
    let th2 = th.update(t, x);
    if t == th.len() - 1 {
        assert(th2.drop_last() =~= th.drop_last());
    } else {
        assert(th2.drop_last() =~= th.drop_last().update(t, x));
        lemma_nreaders_update(th.drop_last(), t, x);
    }
}

proof fn lemma_nreaders_zero(th: Seq<Th>)
    requires
        forall|t: int| 0 <= t < th.len() ==> !holds_read(#[trigger] th[t].ph),
    ensures
        nreaders(th) == 0,
    decreases th.len(),
{
    if th.len() > 0 {
        assert forall|t: int| 0 <= t < th.drop_last().len() implies !holds_read(#[trigger] th.drop_last()[t].ph) by {
            assert(th.drop_last()[t] == th[t]);
        }
        lemma_nreaders_zero(th.drop_last());
        assert(!holds_read(th[th.len() - 1].ph));
    }
}

proof fn lemma_nreaders_pos(th: Seq<Th>, t: int)
    requires
        0 <= t < th.len(),
        holds_read(th[t].ph),
    ensures
        nreaders(th) >= 1,
    decreases th.len(),
{
    if t < th.len() - 1 {
        assert(th.drop_last()[t] == th[t]);
        lemma_nreaders_pos(th.drop_last(), t);
    }
}

// ---------------------------------------------------------------------
// The invariant.

proof fn lemma_init(s: St, n: nat)
    requires
        init(s, n),
    ensures
        inv(s, n),
{
    assert forall|t: nat| t < n implies #[trigger] ph(s, t) == Ph::Idle by {
        assert(s.th[t as int].ph == Ph::Idle);
    }
    lemma_nreaders_zero(s.th);
}

proof fn lemma_step_frame(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.th.len() == n,
        s2.th == s.th.update(t as int, s2.th[t as int]),
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        timed(s2, t) == timed(s, t) || ph(s, t) == Ph::Idle,
        forall|tk: nat| s.notified.contains(tk) ==> #[trigger] s2.notified.contains(tk),
        forall|tk: nat| #[trigger] s2.list.contains(tk) ==> s.list.contains(tk) || tk >= s.next_tk,
        s2.next_tk >= s.next_tk,
        // Only a holder's step can make a thread a holder or a finisher.
        !holds(ph(s, t)) && !post(ph(s, t)) && (holds(ph(s2, t)) || post(ph(s2, t))) ==> ph(s, t) is Cas,
        post(ph(s2, t)) ==> post(ph(s, t)) || holds(ph(s, t)),
{
    assert(s2.th =~= s.th.update(t as int, s2.th[t as int]));
}

proof fn lemma_step(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        inv(s2, n),
{
    lemma_step_frame(s, n, t, s2);
    lemma_step_word(s, n, t, s2);
    lemma_step_tickets(s, n, t, s2);
    lemma_step_wake(s, n, t, s2);
}

proof fn lemma_step_word(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.word.w ==> exists|t: nat| t < n && #[trigger] ph(s2, t) == Ph::WCrit,
        s2.word.rc == nreaders(s2.th),
        forall|t: nat| t < n && #[trigger] ph(s2, t) == Ph::WCrit ==> s2.word.w && s2.word.rc == 0,
        forall|t: nat, u: nat| t < n && u < n && #[trigger] ph(s2, t) == Ph::WCrit && #[trigger] ph(s2, u) == Ph::WCrit ==> t == u,
        (s2.word.pk || s2.word.ww) ==> s2.word.w || s2.word.rc > 0 || exists|u: nat| u < n && #[trigger] ph(s2, u) == Ph::Clear,
{
    lemma_step_frame(s, n, t, s2);
    lemma_nreaders_update(s.th, t as int, s2.th[t as int]);
    let x = s.word;
    let x2 = s2.word;
    // Reader count.
    if ph(s, t) is RCrit {
        lemma_nreaders_pos(s.th, t as int);
    }
    match ph(s, t) {
        Ph::WCrit => {
            assert(!holds_read(ph(s, t)));
            if s2.word.w == false && s2.word.rc == x.rc + 1 {
                assert(holds_read(ph(s2, t)));
            } else {
                assert(s2.word == zero());
                assert(!holds_read(ph(s2, t)));
                assert(x.rc == 0);
            }
        },
        Ph::Notify { rd, woken } => {
            assert(holds_read(ph(s, t)) == holds_read(ph(s2, t)));
        },
        Ph::Unpark { rd } => {
            assert(holds_read(ph(s, t)) == holds_read(ph(s2, t)));
        },
        _ => {},
    }
    // A writer is alone.
    if ph(s, t) is Cas && ph(s2, t) == Ph::WCrit {
        assert(!x.w && x.rc == 0);
        assert forall|u: nat| u < n && u != t implies #[trigger] ph(s, u) != Ph::WCrit by {}
        assert forall|u: nat| u < n && u != t implies !holds_read(#[trigger] ph(s, u)) by {
            if holds_read(ph(s, u)) {
                lemma_nreaders_pos(s.th, u as int);
            }
        }
    }
    assert forall|u: nat| u < n && #[trigger] ph(s2, u) == Ph::WCrit implies s2.word.w && s2.word.rc == 0 by {
        if u != t {
            assert(ph(s, u) == Ph::WCrit);
            if ph(s, t) is RCrit {
                lemma_nreaders_pos(s.th, t as int);
            }
            if ph(s, t) == Ph::WCrit {
                assert(false);
            }
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) == Ph::WCrit && #[trigger] ph(s2, v) == Ph::WCrit implies u == v by {
        if u != t && v != t {
            assert(ph(s, u) == Ph::WCrit && ph(s, v) == Ph::WCrit);
        } else if u == t && v != t {
            assert(ph(s, v) == Ph::WCrit);
            assert(x.w);
        } else if v == t && u != t {
            assert(ph(s, u) == Ph::WCrit);
            assert(x.w);
        }
    }
    if ph(s, t) is Cas && ph(s2, t) == Ph::RCrit {
        assert forall|u: nat| u < n implies #[trigger] ph(s, u) != Ph::WCrit by {}
    }
    if ph(s, t) is RCrit {
        assert forall|u: nat| u < n implies #[trigger] ph(s, u) != Ph::WCrit by {}
    }
    // Writer bit.
    if x2.w {
        if ph(s2, t) != Ph::WCrit {
            let h = choose|h: nat| h < n && #[trigger] ph(s, h) == Ph::WCrit;
            if h == t {
                assert(!x2.w);
            }
            assert(ph(s2, h) == Ph::WCrit);
        }
    }
    // Hints.
    if (x2.pk || x2.ww) && !x2.w && x2.rc == 0 {
        if ph(s2, t) != Ph::Clear {
            match ph(s, t) {
                Ph::Flag { wr, s: c, left } => {
                    if x == c {
                        // A writer sets the hints only while the lock is
                        // held; a reader adds `pk` to a word that already
                        // has `ww` (or the writer bit).
                        assert(x.ww);
                    }
                },
                Ph::RCrit => {},
                _ => {},
            }
            assert(x.pk || x.ww);
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == Ph::Clear;
            if u == t {
                assert(false);
            }
            assert(ph(s2, u) == Ph::Clear);
        }
    }
}

proof fn lemma_step_tickets(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        forall|tk: nat| #[trigger] s2.list.contains(tk) ==> {
            &&& tk < s2.next_tk
            &&& !s2.notified.contains(tk)
            &&& s2.owner[tk] < n
            &&& ph(s2, s2.owner[tk]) is Asleep
            &&& ph(s2, s2.owner[tk])->Asleep_tk == tk
        },
        forall|tk: nat| #[trigger] s2.notified.contains(tk) ==> tk < s2.next_tk,
        forall|t: nat| t < n ==> match #[trigger] ph(s2, t) {
            Ph::Asleep { tk, .. } => tk < s2.next_tk && s2.owner[tk] == t,
            Ph::Notify { woken, .. } => forall|tk: nat| #[trigger] woken.contains(tk) ==> tk < s2.next_tk && !s2.list.contains(tk),
            Ph::Flag { wr, s: c, .. } => if wr { blocks_write(c) } else { blocks_read(c) },
            Ph::Cas { wr, s: c, .. } => if wr { !blocks_write(c) } else { !blocks_read(c) },
            _ => true,
        },
        forall|t: nat| t < n ==> match #[trigger] ph(s2, t) {
            Ph::Asleep { tk, .. } => !s2.list.contains(tk) && !s2.notified.contains(tk)
                ==> exists|u: nat| u < n && #[trigger] ph(s2, u) is Notify && ph(s2, u)->Notify_woken.contains(tk),
            _ => true,
        },
{
    lemma_step_frame(s, n, t, s2);
    assert forall|tk: nat| #[trigger] s2.notified.contains(tk) implies tk < s2.next_tk by {
        if !s.notified.contains(tk) {
            let w0 = ph(s, t)->Notify_woken;
            assert(w0.contains(w0[0]));
        }
    }
    assert forall|tk: nat| #[trigger] s2.list.contains(tk) implies {
        &&& tk < s2.next_tk
        &&& !s2.notified.contains(tk)
        &&& s2.owner[tk] < n
        &&& ph(s2, s2.owner[tk]) is Asleep
        &&& ph(s2, s2.owner[tk])->Asleep_tk == tk
    } by {
        if s.list.contains(tk) {
            if s.owner[tk] == t {
                assert(ph(s, t) is Asleep);
            }
            if ph(s, t) is Notify {
                assert(!ph(s, t)->Notify_woken.contains(tk));
                if ph(s, t)->Notify_woken.len() > 0 {
                    assert(ph(s, t)->Notify_woken.contains(ph(s, t)->Notify_woken[0]));
                }
            }
        }
    }
    assert forall|t1: nat| t1 < n implies match #[trigger] ph(s2, t1) {
        Ph::Asleep { tk, .. } => tk < s2.next_tk && s2.owner[tk] == t1,
        Ph::Notify { woken, .. } => forall|tk: nat| #[trigger] woken.contains(tk) ==> tk < s2.next_tk && !s2.list.contains(tk),
        Ph::Flag { wr, s: c, .. } => if wr { blocks_write(c) } else { blocks_read(c) },
        Ph::Cas { wr, s: c, .. } => if wr { !blocks_write(c) } else { !blocks_read(c) },
        _ => true,
    } by {
        if t1 == t {
            match ph(s2, t) {
                Ph::Notify { woken, .. } => {
                    assert forall|tk: nat| #[trigger] woken.contains(tk) implies tk < s2.next_tk && !s2.list.contains(tk) by {
                        if let Ph::Notify { woken: w0, .. } = ph(s, t) {
                            let k = choose|k: int| 0 <= k < woken.len() && woken[k] == tk;
                            assert(w0[k + 1] == tk);
                            assert(w0.contains(tk));
                        }
                    }
                },
                _ => {},
            }
        } else {
            assert(ph(s2, t1) == ph(s, t1));
            match ph(s, t1) {
                Ph::Asleep { tk, .. } => {
                    if ph(s, t) is Check {
                        assert(tk != s.next_tk);
                    }
                },
                Ph::Notify { woken, .. } => {
                    assert forall|tk: nat| #[trigger] woken.contains(tk) implies tk < s2.next_tk && !s2.list.contains(tk) by {
                        if s2.list.contains(tk) {
                            assert(s.list.contains(tk) || tk >= s.next_tk);
                        }
                    }
                },
                _ => {},
            }
        }
    }
    assert forall|t1: nat| t1 < n implies match #[trigger] ph(s2, t1) {
        Ph::Asleep { tk, .. } => !s2.list.contains(tk) && !s2.notified.contains(tk)
            ==> exists|u: nat| u < n && #[trigger] ph(s2, u) is Notify && ph(s2, u)->Notify_woken.contains(tk),
        _ => true,
    } by {
        lemma_pending_waker(s, n, t, s2, t1);
    }
}

proof fn lemma_step_wake(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        !s2.list.is_empty() ==> s2.word.pk || exists|u: nat| u < n && #[trigger] waking(s2, u),
{
    lemma_step_frame(s, n, t, s2);
    let x = s.word;
    let x2 = s2.word;
    if !s2.list.is_empty() && !x2.pk {
        let y = s2.list.choose();
        assert(s2.list.contains(y));
        if !(exists|u: nat| u < n && #[trigger] waking(s2, u)) {
            assert(s.list.contains(y));
            assert(!s.list.is_empty());
            match ph(s, t) {
                Ph::Unpark { .. } => {
                    assert(s2.list.is_empty());
                },
                Ph::Clear => {
                    assert(waking(s2, t));
                },
                Ph::WCrit => {
                    if x.pk {
                        assert(waking(s2, t));
                    }
                },
                _ => {},
            }
            assert(x.pk || x.pk == x2.pk);
            if x.pk {
                assert(ph(s, t) is WCrit || ph(s, t) is Clear);
            }
            let u = choose|u: nat| u < n && #[trigger] waking(s, u);
            assert(u != t);
            assert(ph(s2, u) == ph(s, u));
            assert(waking(s2, u));
        }
    }
}

proof fn lemma_pending_waker(s: St, n: nat, t: nat, s2: St, t1: nat)
    requires
        inv(s, n),
        t < n,
        t1 < n,
        step(s, t, s2),
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        forall|tk: nat| s.notified.contains(tk) ==> #[trigger] s2.notified.contains(tk),
    ensures
        match ph(s2, t1) {
            Ph::Asleep { tk, .. } => !s2.list.contains(tk) && !s2.notified.contains(tk)
                ==> exists|u: nat| u < n && #[trigger] ph(s2, u) is Notify && ph(s2, u)->Notify_woken.contains(tk),
            _ => true,
        },
{
    match ph(s2, t1) {
        Ph::Asleep { tk, .. } => {
            if !s2.list.contains(tk) && !s2.notified.contains(tk) {
                if t1 == t {
                    assert(ph(s, t) is Asleep);
                    assert(ph(s, t)->Asleep_tk == tk);
                }
                assert(ph(s, t1) is Asleep && ph(s, t1)->Asleep_tk == tk);
                if s.list.contains(tk) {
                    if let Ph::Unpark { rd } = ph(s, t) {
                        assert(ph(s2, t) is Notify && ph(s2, t)->Notify_woken.contains(tk));
                    }
                } else {
                    assert(!s.notified.contains(tk));
                    let u = choose|u: nat| u < n && #[trigger] ph(s, u) is Notify && ph(s, u)->Notify_woken.contains(tk);
                    if u == t {
                        let w0 = ph(s, t)->Notify_woken;
                        assert(w0.len() > 0);
                        if w0[0] == tk {
                            assert(s2.notified.contains(tk));
                        } else {
                            let k = choose|k: int| 0 <= k < w0.len() && w0[k] == tk;
                            assert(k > 0);
                            assert(w0.drop_first()[k - 1] == tk);
                            assert(ph(s2, t)->Notify_woken.contains(tk));
                        }
                    } else {
                        assert(ph(s2, u) == ph(s, u));
                    }
                }
            }
        },
        _ => {},
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

proof fn lemma_at(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, m: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(m), n),
        inv(ex(m + 1), n),
        sched(m) < n,
        step(ex(m), sched(m), ex(m + 1)),
        forall|u: nat| u < n && u != sched(m) ==> #[trigger] ex(m + 1).th[u as int] == ex(m).th[u as int],
        timed(ex(m + 1), sched(m)) == timed(ex(m), sched(m)) || ph(ex(m), sched(m)) == Ph::Idle,
        forall|tk: nat| ex(m).notified.contains(tk) ==> #[trigger] ex(m + 1).notified.contains(tk),
        !holds(ph(ex(m), sched(m))) && !post(ph(ex(m), sched(m))) && (holds(ph(ex(m + 1), sched(m))) || post(ph(ex(m + 1), sched(m))))
            ==> ph(ex(m), sched(m)) is Cas,
        post(ph(ex(m + 1), sched(m))) ==> post(ph(ex(m), sched(m))) || holds(ph(ex(m), sched(m))),
{
    lemma_inv(ex, sched, n, m);
    lemma_inv(ex, sched, n, m + 1);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step_frame(ex(m), n, sched(m), ex(m + 1));
}

// ---------------------------------------------------------------------
// Liveness.

pub open spec fn held_after(ex: spec_fn(nat) -> St, n: nat, j: nat) -> bool {
    exists|k: nat| k >= j && #[trigger] crit(ex(k), n)
}

pub open spec fn nobody_after(ex: spec_fn(nat) -> St, n: nat, i: nat) -> bool {
    forall|j: nat| j >= i ==> !crit(#[trigger] ex(j), n)
}

proof fn lemma_no_holder(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, j: nat)
    requires
        run(ex, sched, n),
        nobody_after(ex, n, i),
        j >= i,
    ensures
        !ex(j).word.w,
        ex(j).word.rc == 0,
        forall|t: nat| t < n ==> !holds(#[trigger] ph(ex(j), t)),
{
    lemma_inv(ex, sched, n, j);
    assert(!crit(ex(j), n));
    assert forall|t: int| 0 <= t < ex(j).th.len() implies !holds_read(#[trigger] ex(j).th[t].ph) by {
        assert(!holds(ph(ex(j), t as nat)));
    }
    lemma_nreaders_zero(ex(j).th);
    if ex(j).word.w {
        let h = choose|h: nat| h < n && #[trigger] ph(ex(j), h) == Ph::WCrit;
        assert(holds(ph(ex(j), h)));
    }
}

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

/// Not finishing an unlock at or after `k`.
pub open spec fn calm(ex: spec_fn(nat) -> St) -> spec_fn(nat, nat) -> bool {
    |t: nat, m: nat| !post(ph(ex(m), t))
}

/// With nobody holding the lock, a thread that is not finishing an unlock
/// never starts finishing one.
proof fn lemma_stays_calm(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, k: nat, m: nat)
    requires
        run(ex, sched, n),
        nobody_after(ex, n, i),
        t < n,
        i <= k <= m,
        !post(ph(ex(k), t)),
    ensures
        !post(ph(ex(m), t)),
    decreases m - k,
{
    if k < m {
        lemma_at(ex, sched, n, k);
        lemma_no_holder(ex, sched, n, i, k);
        lemma_no_holder(ex, sched, n, i, k + 1);
        lemma_stays_calm(ex, sched, n, i, t, k + 1, m);
    }
}

proof fn lemma_calm_from(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, k: nat)
    requires
        run(ex, sched, n),
        nobody_after(ex, n, i),
        t < n,
        i <= k,
        !post(ph(ex(k), t)),
    ensures
        eventually_always(calm(ex), t, i),
{
    assert forall|m: nat| m >= k implies #[trigger] calm(ex)(t, m) by {
        lemma_stays_calm(ex, sched, n, i, t, k, m);
    }
    assert(holds_from(calm(ex), t, k));
}

/// A thread finishing an unlock finishes it.
proof fn lemma_finishes(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        t < n,
        i <= j,
    ensures
        eventually_always(calm(ex), t, i),
    decreases
            (match ph(ex(j), t) {
                Ph::Clear => 1,
                _ => 0nat,
            }),
            (match ph(ex(j), t) {
                Ph::Unpark { .. } => 1,
                _ => 0nat,
            }),
            (match ph(ex(j), t) {
                Ph::Notify { woken, .. } => woken.len() + 1,
                _ => 0nat,
            }),
{
    if !post(ph(ex(j), t)) {
        lemma_calm_from(ex, sched, n, i, t, j);
    } else {
        let k = lemma_until_step(ex, sched, n, t, j);
        lemma_at(ex, sched, n, k);
        lemma_no_holder(ex, sched, n, i, k + 1);
        assert(ph(ex(k), t) == ph(ex(j), t));
        lemma_finishes(ex, sched, n, i, t, k + 1);
    }
}

/// After some time nobody is finishing an unlock, the word is 0 and the
/// list is empty, for good.
proof fn lemma_settles(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat) -> (k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
    ensures
        k >= i,
        forall|m: nat| m >= k ==> (#[trigger] ex(m)).word == zero() && ex(m).list.is_empty(),
        forall|t: nat, m: nat| t < n && m >= k ==> !post(#[trigger] ph(ex(m), t)),
{
    assert forall|t: nat| t < n implies #[trigger] eventually_always(calm(ex), t, i) by {
        lemma_finishes(ex, sched, n, i, t, i);
    }
    let k = lemma_all_eventually(calm(ex), n, i);
    assert forall|t: nat, m: nat| t < n && m >= k implies !post(#[trigger] ph(ex(m), t)) by {
        assert(calm(ex)(t, m));
    }
    assert forall|m: nat| m >= k implies (#[trigger] ex(m)).word == zero() && ex(m).list.is_empty() by {
        lemma_inv(ex, sched, n, m);
        lemma_no_holder(ex, sched, n, i, m);
        let s = ex(m);
        if exists|u: nat| u < n && #[trigger] ph(s, u) == Ph::Clear {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == Ph::Clear;
            assert(post(ph(s, u)));
        }
        if exists|u: nat| u < n && #[trigger] waking(s, u) {
            let u = choose|u: nat| u < n && #[trigger] waking(s, u);
            assert(post(ph(s, u)) || holds(ph(s, u)));
        }
    }
    k
}

/// After the lock settles, a thread waiting without a deadline takes it
/// within four of its own steps.
proof fn lemma_takes(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, k0: nat, t: nat, j: nat, fuel: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        nobody_after(ex, n, i),
        forall|m: nat| m >= k0 ==> (#[trigger] ex(m)).word == zero() && ex(m).list.is_empty(),
        forall|t: nat, m: nat| t < n && m >= k0 ==> !post(#[trigger] ph(ex(m), t)),
        k0 >= i,
        t < n,
        j >= k0,
        waiting(ph(ex(j), t)),
        !timed(ex(j), t),
        fuel == (match ph(ex(j), t) {
            Ph::Cas { s, .. } => if s == zero() { 0nat } else { 4 },
            Ph::Load { .. } => 1,
            Ph::Flag { .. } | Ph::Check { .. } | Ph::Asleep { .. } => 2,
            _ => 5,
        }),
    ensures
        false,
    decreases fuel,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    let s = ex(k);
    assert(s.word == zero());
    assert(ph(s, t) == ph(ex(j), t));
    if let Ph::Asleep { tk, .. } = ph(s, t) {
        // The list is empty, so the sleeper was taken off it, and every
        // waker has finished: it has been notified.
        assert(!s.list.contains(tk));
        if !s.notified.contains(tk) {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) is Notify && ph(s, u)->Notify_woken.contains(tk);
            lemma_no_holder(ex, sched, n, i, k);
            assert(!holds(ph(s, u)));
            assert(post(ph(s, u)));
        }
    }
    if ph(ex(k + 1), t) is Idle {
        assert(false);
    }
    if holds(ph(ex(k + 1), t)) {
        lemma_no_holder(ex, sched, n, i, k + 1);
    }
    assert(!timed(ex(k + 1), t));
    assert(ex(k + 1).word == zero());
    match ph(s, t) {
        Ph::Cas { s: c, .. } => {
            if c == zero() {
                assert(holds(ph(ex(k + 1), t)));
            }
            assert(ph(ex(k + 1), t) is Load);
        },
        Ph::Load { .. } => {
            assert(ph(ex(k + 1), t) is Cas);
            assert(ph(ex(k + 1), t)->Cas_s == zero());
        },
        Ph::Flag { s: c, .. } => {
            assert(ph(ex(k + 1), t) is Load);
        },
        Ph::Check { .. } => {
            assert(ph(ex(k + 1), t) is Load);
        },
        _ => {
            assert(ph(s, t) is Asleep);
            assert(ph(ex(k + 1), t) is Load);
        },
    }
    lemma_takes(ex, sched, n, i, k0, t, k + 1, (match ph(ex(k + 1), t) {
        Ph::Cas { s, .. } => if s == zero() { 0nat } else { 4 },
        Ph::Load { .. } => 1,
        Ph::Flag { .. } | Ph::Check { .. } | Ph::Asleep { .. } => 2,
        _ => 5,
    }));
}

/// A waiting thread without a deadline is still waiting while nobody holds
/// the lock.
proof fn lemma_still_waiting(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, m: nat)
    requires
        run(ex, sched, n),
        nobody_after(ex, n, i),
        t < n,
        m >= i,
        waiting(ph(ex(i), t)),
        !timed(ex(i), t),
    ensures
        waiting(ph(ex(m), t)),
        !timed(ex(m), t),
    decreases m - i,
{
    if m > i {
        lemma_still_waiting(ex, sched, n, i, t, (m - 1) as nat);
        let p = (m - 1) as nat;
        lemma_at(ex, sched, n, p);
        lemma_no_holder(ex, sched, n, i, m);
        assert(!holds(ph(ex(m), t)));
    }
}

/// Deadlock freedom: in a fair execution, a thread waiting in `read()` or
/// `write()` at time `i` (with no deadline) sees the lock held by some
/// thread, possibly itself, at some time `j >= i`.
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
        let k0 = lemma_settles(ex, sched, n, i);
        lemma_still_waiting(ex, sched, n, i, t0, k0);
        lemma_takes(ex, sched, n, i, k0, t0, k0, (match ph(ex(k0), t0) {
            Ph::Cas { s, .. } => if s == zero() { 0nat } else { 4 },
            Ph::Load { .. } => 1,
            Ph::Flag { .. } | Ph::Check { .. } | Ph::Asleep { .. } => 2,
            _ => 5,
        }));
    }
}

/// A waiter that never gets the lock sees it taken infinitely often.
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

} // verus!
