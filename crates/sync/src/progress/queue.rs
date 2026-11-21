//! The MPMC queue is lock-free under fair scheduling: while any thread is
//! inside `push` or `pop`, some `push` or `pop` returns.
//!
//! The model is `ArrayQueue::push` and `pop` (Vyukov's bounded queue as
//! crossbeam implements it), one step per atomic access: the head and tail
//! loads and CASes, the stamp loads and stores, and the read-modify-writes
//! that confirm "full" or "empty". Positions are kept unpacked (the code
//! packs lap and index into one word, an order-preserving bijection the
//! safety proof handles with `pk`), and a slot's stamp is kept as a rank:
//! `2p` means "free for position `p`", `2p + 1` "holds the value pushed at
//! `p`". The code's stamp comparisons map one to one onto rank comparisons:
//! `stamp == tail` is rank `2t`, `stamp == tail + 1 - one_lap` is rank
//! `2(t - cap) + 1`, `stamp == head + 1` is rank `2h + 1`, and
//! `stamp == head` is rank `2h`.
//!
//! The model is sequentially consistent. The code's loads are relaxed or
//! acquire, so a thread can read an old value of head, tail or a stamp;
//! that only makes it retry, and once no thread writes any more it reads
//! the last values, which is what fairness of the memory system (every
//! store eventually becomes visible to every thread, as on all hardware
//! Rust targets) gives. `TRUST.md` ("Progress") discusses this.
//!
//! `len` is modeled too: it loads the tail, the head and the tail again,
//! and retries only if the tail moved in between.
//!
//! [`theorem_lock_free`]: in every fair execution, if some thread is in
//! `push`, `pop` or `len` at time `i`, some call returns at some step
//! `j >= i`.
//! A thread that has claimed a position (won the CAS) finishes in one more
//! step, which is also why the queue is not lock-free in the strict sense
//! (a claimant that is never scheduled again blocks the threads behind it
//! on its slot); fairness rules that out. If no call ever returned, nobody
//! would win a CAS, so head, tail and every stamp would freeze, and then
//! the next attempt of any thread would win its CAS or confirm a full or
//! empty queue. Individual threads can still starve (lose every CAS).
use super::trace::*;
use vstd::prelude::*;

verus! {

pub enum Ph {
    Idle,
    /// `push`: about to load the tail.
    PLoad,
    /// About to load the stamp of slot `a % cap`, with `tail == a`.
    PStamp { a: nat },
    /// About to CAS the tail from `a` to `a + 1`.
    PCas { a: nat },
    /// The slot holds the previous lap's value: about to load the head.
    PHead { a: nat },
    /// The head looked like `a - cap`: about to confirm with a
    /// read-modify-write (`fetch_add(0)`).
    PConfirm { a: nat },
    /// Claimed position `a`: about to write the value and store the stamp.
    PWrite { a: nat },
    /// `pop`: about to load the head.
    QLoad,
    QStamp { a: nat },
    QCas { a: nat },
    /// The slot waits for the push at `a`: about to load the tail.
    QTail { a: nat },
    QConfirm { a: nat },
    /// Claimed position `a`: about to read the value and store the stamp.
    QRead { a: nat },
    /// `len`: about to load the tail ...
    LTail,
    /// ... then the head, having seen tail `a` ...
    LHead { a: nat },
    /// ... then the tail again; it returns if the tail is still `a`.
    LTail2 { a: nat },
}

pub struct St {
    pub cap: nat,
    pub head: nat,
    pub tail: nat,
    /// Stamp ranks, one per slot.
    pub st: Seq<nat>,
    pub th: Seq<Ph>,
    /// Calls returned so far (a ghost counter).
    pub done: nat,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.cap > 0
    &&& s.head == 0
    &&& s.tail == 0
    &&& s.st.len() == s.cap
    &&& forall|k: int| 0 <= k < s.cap ==> #[trigger] s.st[k] == 2 * k
    &&& s.th.len() == n
    &&& forall|t: int| 0 <= t < n ==> #[trigger] s.th[t] == Ph::Idle
}

pub open spec fn ph(s: St, t: nat) -> Ph {
    s.th[t as int]
}

pub open spec fn rank(s: St, a: nat) -> nat {
    s.st[(a % s.cap) as int]
}

pub open spec fn go(s: St, t: nat, p: Ph) -> St {
    St { th: s.th.update(t as int, p), ..s }
}

/// Return from the call.
pub open spec fn ret(s: St, t: nat) -> St {
    St { done: s.done + 1, ..go(s, t, Ph::Idle) }
}

pub open spec fn step(s: St, t: nat, s2: St) -> bool {
    match ph(s, t) {
        Ph::Idle => s2 == s || s2 == go(s, t, Ph::PLoad) || s2 == go(s, t, Ph::QLoad) || s2 == go(s, t, Ph::LTail),
        Ph::LTail => s2 == go(s, t, Ph::LHead { a: s.tail }),
        Ph::LHead { a } => s2 == go(s, t, Ph::LTail2 { a }),
        Ph::LTail2 { a } => if s.tail == a { s2 == ret(s, t) } else { s2 == go(s, t, Ph::LTail) },
        Ph::PLoad => s2 == go(s, t, Ph::PStamp { a: s.tail }),
        Ph::PStamp { a } => {
            let r = rank(s, a);
            if r == 2 * a {
                s2 == go(s, t, Ph::PCas { a })
            } else if a >= s.cap && r == 2 * (a - s.cap) + 1 {
                s2 == go(s, t, Ph::PHead { a })
            } else {
                s2 == go(s, t, Ph::PLoad)
            }
        },
        // On failure the CAS returns the current tail, and the loop goes
        // on with it.
        Ph::PCas { a } => if s.tail == a {
            s2 == (St { tail: a + 1, ..go(s, t, Ph::PWrite { a }) })
        } else {
            s2 == go(s, t, Ph::PStamp { a: s.tail })
        },
        Ph::PHead { a } => s2 == go(s, t, if s.head + s.cap == a { Ph::PConfirm { a } } else { Ph::PLoad }),
        Ph::PConfirm { a } => if s.head + s.cap == a {
            s2 == ret(s, t)
        } else {
            s2 == go(s, t, Ph::PLoad)
        },
        Ph::PWrite { a } => s2 == (St { st: s.st.update((a % s.cap) as int, 2 * a + 1), ..ret(s, t) }),
        Ph::QLoad => s2 == go(s, t, Ph::QStamp { a: s.head }),
        Ph::QStamp { a } => {
            let r = rank(s, a);
            if r == 2 * a + 1 {
                s2 == go(s, t, Ph::QCas { a })
            } else if r == 2 * a {
                s2 == go(s, t, Ph::QTail { a })
            } else {
                s2 == go(s, t, Ph::QLoad)
            }
        },
        Ph::QCas { a } => if s.head == a {
            s2 == (St { head: a + 1, ..go(s, t, Ph::QRead { a }) })
        } else {
            s2 == go(s, t, Ph::QStamp { a: s.head })
        },
        Ph::QTail { a } => s2 == go(s, t, if s.tail == a { Ph::QConfirm { a } } else { Ph::QLoad }),
        Ph::QConfirm { a } => if s.tail == a {
            s2 == ret(s, t)
        } else {
            s2 == go(s, t, Ph::QLoad)
        },
        Ph::QRead { a } => s2 == (St { st: s.st.update((a % s.cap) as int, 2 * (a + s.cap)), ..ret(s, t) }),
    }
}

pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

pub open spec fn writing(s: St, n: nat, p: nat) -> bool {
    exists|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p })
}

pub open spec fn reading(s: St, n: nat, p: nat) -> bool {
    exists|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: p })
}

/// What slot `p % cap` holds, for each position `p` in the window
/// `[head, head + cap)`.
pub open spec fn window(s: St, n: nat, p: nat) -> bool {
    let r = rank(s, p);
    if p < s.tail {
        r == 2 * p + 1 || (r == 2 * p && writing(s, n, p))
    } else {
        r == 2 * p || (p >= s.cap && r == 2 * (p - s.cap) + 1 && reading(s, n, (p - s.cap) as nat))
    }
}

pub open spec fn inv(s: St, n: nat) -> bool {
    &&& s.cap > 0
    &&& s.st.len() == s.cap
    &&& s.th.len() == n
    &&& s.head <= s.tail <= s.head + s.cap
    &&& forall|p: nat| s.head <= p < s.head + s.cap ==> #[trigger] window(s, n, p)
    &&& forall|u: nat| u < n ==> match #[trigger] ph(s, u) {
        Ph::PWrite { a } => s.head <= a < s.tail && rank(s, a) == 2 * a,
        Ph::QRead { a } => a < s.head && s.tail <= a + s.cap && rank(s, a) == 2 * a + 1,
        // What a thread saw stays true: stamps only grow, and so do head
        // and tail.
        Ph::PCas { a } => a <= s.tail && rank(s, a) >= 2 * a,
        Ph::QCas { a } => a <= s.head && rank(s, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s.tail,
        Ph::QStamp { a } => a <= s.head,
        _ => true,
    }
    &&& forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s, u) is PWrite && #[trigger] ph(s, v) is PWrite
        && ph(s, u)->PWrite_a == ph(s, v)->PWrite_a ==> u == v
    &&& forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s, u) is QRead && #[trigger] ph(s, v) is QRead
        && ph(s, u)->QRead_a == ph(s, v)->QRead_a ==> u == v
}

// ---------------------------------------------------------------------
// Arithmetic on slot indices.

/// Two positions less than `cap` apart use different slots.
proof fn lemma_slots_differ(p: nat, q: nat, cap: nat)
    requires
        cap > 0,
        p < q < p + cap,
    ensures
        p % cap != q % cap,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, cap as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q as int, cap as int);
    if p % cap == q % cap {
        assert((q - p) as int == cap * (q as int / cap as int - p as int / cap as int)) by (nonlinear_arith)
            requires
                p as int == cap * (p as int / cap as int) + p % cap,
                q as int == cap * (q as int / cap as int) + q % cap,
                p % cap == q % cap;
        assert(false) by (nonlinear_arith)
            requires
                (q - p) as int == cap * (q as int / cap as int - p as int / cap as int),
                0 < q - p < cap,
                cap > 0;
    }
}

proof fn lemma_slot_shift(p: nat, cap: nat)
    requires
        cap > 0,
    ensures
        (p + cap) % cap == p % cap,
{
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(p as int, cap as int);
}

/// The window position of a slot that position `a` uses.
proof fn lemma_window_pos(s: St, n: nat, a: nat) -> (p: nat)
    requires
        inv(s, n),
        s.head <= a + s.cap,
        a < s.head + s.cap || a == s.head + s.cap,
    ensures
        s.head <= p < s.head + s.cap,
        p % s.cap == a % s.cap,
        p == (if a == s.head + s.cap { s.head } else if a >= s.head { a } else { a + s.cap }),
{
    if a == s.head + s.cap {
        lemma_slot_shift(s.head, s.cap);
        s.head
    } else if a >= s.head {
        a
    } else {
        lemma_slot_shift(a, s.cap);
        a + s.cap
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
    assert forall|p: nat| s.head <= p < s.head + s.cap implies #[trigger] window(s, n, p) by {
        vstd::arithmetic::div_mod::lemma_small_mod(p, s.cap);
        assert(s.st[p as int] == 2 * p);
    }
    assert forall|u: nat| u < n implies #[trigger] ph(s, u) == Ph::Idle by {
        assert(s.th[u as int] == Ph::Idle);
    }
}

proof fn lemma_step(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        inv(s2, n),
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] ph(s2, u) == ph(s, u),
        s2.done >= s.done,
        (s2.head != s.head || s2.tail != s.tail || s2.st != s.st) ==> ph(s2, t) is PWrite || ph(s2, t) is QRead || s2.done > s.done,
        ph(s, t) is PWrite || ph(s, t) is QRead ==> s2.done > s.done,
{
    let cap = s.cap;
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    match ph(s, t) {
        Ph::PCas { a } => {
            if s.tail == a {
                // The slot is free for `a`: it is in the window at `a`, and
                // its rank is at least `2a`.
                if a == s.head + cap {
                    let p = lemma_window_pos(s, n, a);
                    assert(window(s, n, p));
                    assert(false);
                }
                let p = lemma_window_pos(s, n, a);
                assert(p == a);
                assert(window(s, n, a));
                assert(rank(s, a) == 2 * a);
                lemma_claim_push(s, n, t, s2, a);
            } else {
                lemma_local(s, n, t, s2);
            }
        },
        Ph::QCas { a } => {
            if s.head == a {
                if a == s.tail {
                    assert(window(s, n, a));
                    assert(false);
                }
                assert(window(s, n, a));
                assert(rank(s, a) == 2 * a + 1);
                lemma_claim_pop(s, n, t, s2, a);
            } else {
                lemma_local(s, n, t, s2);
            }
        },
        Ph::PWrite { a } => lemma_write(s, n, t, s2, a),
        Ph::QRead { a } => lemma_read(s, n, t, s2, a),
        _ => lemma_local(s, n, t, s2),
    }
}

/// Steps that change only the stepping thread's phase (and maybe `done`).
proof fn lemma_local(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
        s2.head == s.head,
        s2.tail == s.tail,
        s2.st == s.st,
        !(ph(s, t) is PWrite || ph(s, t) is QRead),
    ensures
        inv(s2, n),
{
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    assert forall|p: nat| s2.head <= p < s2.head + s2.cap implies #[trigger] window(s2, n, p) by {
        assert(window(s, n, p));
        if p < s.tail && rank(s, p) == 2 * p {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
            assert(u != t);
            assert(ph(s2, u) == ph(s, u));
        }
        if p >= s.tail && rank(s, p) != 2 * p {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - s.cap) as nat });
            assert(u != t);
            assert(ph(s2, u) == ph(s, u));
        }
    }
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::PWrite { a } => s2.head <= a < s2.tail && rank(s2, a) == 2 * a,
        Ph::QRead { a } => a < s2.head && s2.tail <= a + s2.cap && rank(s2, a) == 2 * a + 1,
        Ph::PCas { a } => a <= s2.tail && rank(s2, a) >= 2 * a,
        Ph::QCas { a } => a <= s2.head && rank(s2, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s2.tail,
        Ph::QStamp { a } => a <= s2.head,
        _ => true,
    } by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
        }
    }
}

proof fn lemma_claim_push(s: St, n: nat, t: nat, s2: St, a: nat)
    requires
        inv(s, n),
        t < n,
        ph(s, t) == (Ph::PCas { a }),
        s.tail == a,
        a < s.head + s.cap,
        rank(s, a) == 2 * a,
        s2 == (St { tail: a + 1, ..go(s, t, Ph::PWrite { a }) }),
    ensures
        inv(s2, n),
{
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    assert(ph(s2, t) == (Ph::PWrite { a }));
    assert forall|p: nat| s2.head <= p < s2.head + s2.cap implies #[trigger] window(s2, n, p) by {
        assert(window(s, n, p));
        if p == a {
            assert(writing(s2, n, a));
        } else {
            if p < s.tail && rank(s, p) == 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
            if p >= s.tail && rank(s, p) != 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - s.cap) as nat });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
        }
    }
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::PWrite { a } => s2.head <= a < s2.tail && rank(s2, a) == 2 * a,
        Ph::QRead { a } => a < s2.head && s2.tail <= a + s2.cap && rank(s2, a) == 2 * a + 1,
        Ph::PCas { a } => a <= s2.tail && rank(s2, a) >= 2 * a,
        Ph::QCas { a } => a <= s2.head && rank(s2, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s2.tail,
        Ph::QStamp { a } => a <= s2.head,
        _ => true,
    } by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
            if let Ph::QRead { a: q } = ph(s, u) {
                // A pop in flight on `a`'s slot would have kept it from
                // looking free.
                if q + s.cap == a {
                    lemma_slot_shift(q, s.cap);
                    assert(rank(s, a) == rank(s, q));
                    assert(false);
                }
                assert(s2.tail <= q + s2.cap);
                assert(rank(s2, q) == rank(s, q));
            }
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is PWrite && #[trigger] ph(s2, v) is PWrite
        && ph(s2, u)->PWrite_a == ph(s2, v)->PWrite_a implies u == v by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
        }
        if v != t {
            assert(ph(s2, v) == ph(s, v));
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is QRead && #[trigger] ph(s2, v) is QRead
        && ph(s2, u)->QRead_a == ph(s2, v)->QRead_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
    }
}

proof fn lemma_claim_pop(s: St, n: nat, t: nat, s2: St, a: nat)
    requires
        inv(s, n),
        t < n,
        ph(s, t) == (Ph::QCas { a }),
        s.head == a,
        a < s.tail,
        rank(s, a) == 2 * a + 1,
        s2 == (St { head: a + 1, ..go(s, t, Ph::QRead { a }) }),
    ensures
        inv(s2, n),
{
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    assert(ph(s2, t) == (Ph::QRead { a }));
    lemma_slot_shift(a, s.cap);
    assert forall|p: nat| s2.head <= p < s2.head + s2.cap implies #[trigger] window(s2, n, p) by {
        if p == a + s.cap {
            assert(rank(s2, p) == rank(s, a));
            assert(reading(s2, n, a));
        } else {
            assert(window(s, n, p));
            if p < s.tail && rank(s, p) == 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
            if p >= s.tail && rank(s, p) != 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - s.cap) as nat });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
        }
    }
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::PWrite { a } => s2.head <= a < s2.tail && rank(s2, a) == 2 * a,
        Ph::QRead { a } => a < s2.head && s2.tail <= a + s2.cap && rank(s2, a) == 2 * a + 1,
        Ph::PCas { a } => a <= s2.tail && rank(s2, a) >= 2 * a,
        Ph::QCas { a } => a <= s2.head && rank(s2, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s2.tail,
        Ph::QStamp { a } => a <= s2.head,
        _ => true,
    } by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
            if let Ph::PWrite { a: p } = ph(s, u) {
                // A push in flight on `a` would have kept it from looking
                // full.
                assert(p != a);
            }
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is QRead && #[trigger] ph(s2, v) is QRead
        && ph(s2, u)->QRead_a == ph(s2, v)->QRead_a implies u == v by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
        }
        if v != t {
            assert(ph(s2, v) == ph(s, v));
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is PWrite && #[trigger] ph(s2, v) is PWrite
        && ph(s2, u)->PWrite_a == ph(s2, v)->PWrite_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
    }
}

proof fn lemma_write(s: St, n: nat, t: nat, s2: St, a: nat)
    requires
        inv(s, n),
        t < n,
        ph(s, t) == (Ph::PWrite { a }),
        step(s, t, s2),
    ensures
        inv(s2, n),
{
    let cap = s.cap;
    let k = a % cap;
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    // Only `a`'s slot changes, and `a` is the only window position on it.
    assert forall|p: nat| s2.head <= p < s2.head + s2.cap implies #[trigger] window(s2, n, p) by {
        assert(window(s, n, p));
        if p != a {
            if p < a { lemma_slots_differ(p, a, cap); } else { lemma_slots_differ(a, p, cap); }
            assert(rank(s2, p) == rank(s, p));
            if p < s.tail && rank(s, p) == 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
            if p >= s.tail && rank(s, p) != 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - s.cap) as nat });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
        }
    }
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::PWrite { a } => s2.head <= a < s2.tail && rank(s2, a) == 2 * a,
        Ph::QRead { a } => a < s2.head && s2.tail <= a + s2.cap && rank(s2, a) == 2 * a + 1,
        Ph::PCas { a } => a <= s2.tail && rank(s2, a) >= 2 * a,
        Ph::QCas { a } => a <= s2.head && rank(s2, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s2.tail,
        Ph::QStamp { a } => a <= s2.head,
        _ => true,
    } by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
            match ph(s, u) {
                Ph::PWrite { a: b } => {
                    assert(b != a);
                    if b < a { lemma_slots_differ(b, a, cap); } else { lemma_slots_differ(a, b, cap); }
                },
                Ph::QRead { a: b } => {
                    if b + cap < a { lemma_slots_differ(b + cap, a, cap); } else if b + cap > a { lemma_slots_differ(a, b + cap, cap); }
                    lemma_slot_shift(b, cap);
                },
                Ph::PCas { a: b } => {
                    if b % cap == k {
                        assert(rank(s2, b) == 2 * a + 1);
                    }
                },
                Ph::QCas { a: b } => {
                    if b % cap == k {
                        assert(rank(s2, b) == 2 * a + 1);
                    }
                },
                _ => {},
            }
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is PWrite && #[trigger] ph(s2, v) is PWrite
        && ph(s2, u)->PWrite_a == ph(s2, v)->PWrite_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is QRead && #[trigger] ph(s2, v) is QRead
        && ph(s2, u)->QRead_a == ph(s2, v)->QRead_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
    }
}

proof fn lemma_read(s: St, n: nat, t: nat, s2: St, a: nat)
    requires
        inv(s, n),
        t < n,
        ph(s, t) == (Ph::QRead { a }),
        step(s, t, s2),
    ensures
        inv(s2, n),
{
    let cap = s.cap;
    let k = a % cap;
    lemma_slot_shift(a, cap);
    assert forall|u: nat| u < n && u != t implies #[trigger] ph(s2, u) == ph(s, u) by {}
    let w = a + cap;
    assert forall|p: nat| s2.head <= p < s2.head + s2.cap implies #[trigger] window(s2, n, p) by {
        assert(window(s, n, p));
        if p != w {
            if p < w { lemma_slots_differ(p, w, cap); } else { lemma_slots_differ(w, p, cap); }
            assert(rank(s2, p) == rank(s, p));
            if p < s.tail && rank(s, p) == 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
            if p >= s.tail && rank(s, p) != 2 * p {
                let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - s.cap) as nat });
                assert(u != t);
                assert(ph(s2, u) == ph(s, u));
            }
        } else {
            assert(rank(s2, p) == 2 * p);
            if p < s.tail {
                assert(false);
            }
        }
    }
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::PWrite { a } => s2.head <= a < s2.tail && rank(s2, a) == 2 * a,
        Ph::QRead { a } => a < s2.head && s2.tail <= a + s2.cap && rank(s2, a) == 2 * a + 1,
        Ph::PCas { a } => a <= s2.tail && rank(s2, a) >= 2 * a,
        Ph::QCas { a } => a <= s2.head && rank(s2, a) >= 2 * a + 1,
        Ph::PStamp { a } => a <= s2.tail,
        Ph::QStamp { a } => a <= s2.head,
        _ => true,
    } by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
            match ph(s, u) {
                Ph::PWrite { a: b } => {
                    if b < w { lemma_slots_differ(b, w, cap); } else { assert(false); }
                },
                Ph::QRead { a: b } => {
                    assert(b != a);
                    if b < a { lemma_slots_differ(b, a, cap); } else { lemma_slots_differ(a, b, cap); }
                },
                Ph::PCas { a: b } => {
                    if b % cap == k {
                        assert(rank(s2, b) == 2 * (a + cap));
                        assert(b <= s.tail);
                    }
                },
                Ph::QCas { a: b } => {
                    if b % cap == k {
                        assert(rank(s2, b) == 2 * (a + cap));
                        assert(b <= s.head);
                    }
                },
                _ => {},
            }
        }
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is PWrite && #[trigger] ph(s2, v) is PWrite
        && ph(s2, u)->PWrite_a == ph(s2, v)->PWrite_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
    }
    assert forall|u: nat, v: nat| u < n && v < n && #[trigger] ph(s2, u) is QRead && #[trigger] ph(s2, v) is QRead
        && ph(s2, u)->QRead_a == ph(s2, v)->QRead_a implies u == v by {
        assert(ph(s2, u) == ph(s, u));
        assert(ph(s2, v) == ph(s, v));
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
        forall|u: nat| u < n && u != sched(m) ==> #[trigger] ph(ex(m + 1), u) == ph(ex(m), u),
        ex(m + 1).done >= ex(m).done,
        (ex(m + 1).head != ex(m).head || ex(m + 1).tail != ex(m).tail || ex(m + 1).st != ex(m).st)
            ==> ph(ex(m + 1), sched(m)) is PWrite || ph(ex(m + 1), sched(m)) is QRead || ex(m + 1).done > ex(m).done,
        ph(ex(m), sched(m)) is PWrite || ph(ex(m), sched(m)) is QRead ==> ex(m + 1).done > ex(m).done,
{
    lemma_inv(ex, sched, n, m);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step(ex(m), n, sched(m), ex(m + 1));
}

// ---------------------------------------------------------------------
// Liveness.

/// Some call returns at step `j`.
pub open spec fn returns(ex: spec_fn(nat) -> St, j: nat) -> bool {
    ex(j + 1).done > ex(j).done
}

pub open spec fn none_after(ex: spec_fn(nat) -> St, i: nat) -> bool {
    forall|j: nat| j >= i ==> !#[trigger] returns(ex, j)
}

pub open spec fn ctx(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat) -> bool {
    &&& run(ex, sched, n)
    &&& fair(sched, n)
    &&& none_after(ex, i)
}

proof fn lemma_until_step(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, j: nat) -> (k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
    ensures
        k >= j,
        sched(k) == t,
        ph(ex(k), t) == ph(ex(j), t),
{
    let k = lemma_next_step(sched, n, t, j);
    let f = |m: nat| ph(ex(m), t);
    assert forall|m: nat| j <= m < k && #[trigger] sched(m) != t implies f(m + 1) == f(m) by {
        lemma_at(ex, sched, n, m);
    }
    lemma_frame(sched, f, t, j, k);
    k
}

/// A claimant returns at its next step.
proof fn lemma_no_claimant(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        ctx(ex, sched, n, i),
        t < n,
        j >= i,
        ph(ex(j), t) is PWrite || ph(ex(j), t) is QRead,
    ensures
        false,
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    assert(returns(ex, k));
}

/// With no returns, head, tail and the stamps never change after `i`.
proof fn lemma_frozen(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, j: nat)
    requires
        ctx(ex, sched, n, i),
        j >= i,
    ensures
        ex(j).head == ex(i).head,
        ex(j).tail == ex(i).tail,
        ex(j).st == ex(i).st,
        ex(j).cap == ex(i).cap,
    decreases j - i,
{
    if j > i {
        let m = (j - 1) as nat;
        lemma_frozen(ex, sched, n, i, m);
        lemma_at(ex, sched, n, m);
        assert(!returns(ex, m));
        if ph(ex(j), sched(m)) is PWrite || ph(ex(j), sched(m)) is QRead {
            lemma_no_claimant(ex, sched, n, i, sched(m), j);
        }
    }
}

/// How many of its own steps a thread needs to return, with head `h`,
/// tail `t` and stamps frozen (and no claimant in flight).
pub open spec fn fuel(s: St, p: Ph) -> nat {
    let h = s.head;
    let t = s.tail;
    match p {
        Ph::PWrite { .. } | Ph::QRead { .. } => 0,
        Ph::PConfirm { a } => if h + s.cap == a { 0 } else { 4 },
        Ph::PHead { a } => if h + s.cap == a { 1 } else { 4 },
        Ph::PCas { a } => if a == t { 0 } else { 3 },
        Ph::PStamp { a } => if a == t { 2 } else { 5 },
        Ph::PLoad => 3,
        Ph::QConfirm { a } => if t == a { 0 } else { 4 },
        Ph::QTail { a } => if t == a { 1 } else { 4 },
        Ph::QCas { a } => if a == h { 0 } else { 3 },
        Ph::QStamp { a } => if a == h { 2 } else { 5 },
        Ph::QLoad => 3,
        Ph::LTail2 { a } => if a == t { 0 } else { 4 },
        Ph::LHead { a } => if a == t { 1 } else { 5 },
        Ph::LTail => 2,
        Ph::Idle => 0,
    }
}

proof fn lemma_finishes(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat, j: nat)
    requires
        ctx(ex, sched, n, i),
        t < n,
        j >= i,
        !(ph(ex(j), t) is Idle),
    ensures
        false,
    decreases fuel(ex(i), ph(ex(j), t)),
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    lemma_frozen(ex, sched, n, i, k);
    lemma_frozen(ex, sched, n, i, k + 1);
    let s = ex(k);
    let s2 = ex(k + 1);
    assert(!returns(ex, k));
    if ph(s2, t) is PWrite || ph(s2, t) is QRead {
        lemma_no_claimant(ex, sched, n, i, t, k + 1);
    }
    let h = s.head;
    let tl = s.tail;
    let cap = s.cap;
    // With nothing in flight, every window slot is settled: full below the
    // tail, free from it on.
    assert forall|p: nat| h <= p < h + cap implies #[trigger] rank(s, p) == (if p < tl { 2 * p + 1 } else { 2 * p }) by {
        assert(window(s, n, p));
        if p < tl && rank(s, p) == 2 * p {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::PWrite { a: p });
            lemma_no_claimant(ex, sched, n, i, u, k);
        }
        if p >= tl && rank(s, p) != 2 * p {
            let u = choose|u: nat| u < n && #[trigger] ph(s, u) == (Ph::QRead { a: (p - cap) as nat });
            lemma_no_claimant(ex, sched, n, i, u, k);
        }
    }
    match ph(s, t) {
        Ph::PStamp { a } => {
            if a == tl {
                let p = lemma_window_pos(s, n, a);
                assert(rank(s, p) == rank(s, a));
                if tl < h + cap {
                    assert(ph(s2, t) == (Ph::PCas { a }));
                } else {
                    assert(ph(s2, t) == (Ph::PHead { a }));
                }
            }
        },
        Ph::QStamp { a } => {
            if a == h {
                assert(rank(s, a) == (if h < tl { 2 * h + 1 } else { 2 * h }));
            }
        },
        _ => {},
    }
    lemma_finishes(ex, sched, n, i, t, k + 1);
}

/// Lock-freedom under fair scheduling: if a thread is in `push` or `pop`
/// at time `i`, some call returns at some step `j >= i`.
pub proof fn theorem_lock_free(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t0: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t0 < n,
        !(ph(ex(i), t0) is Idle),
    ensures
        exists|j: nat| j >= i && #[trigger] returns(ex, j),
{
    if !exists|j: nat| j >= i && #[trigger] returns(ex, j) {
        assert(none_after(ex, i));
        lemma_finishes(ex, sched, n, i, t0, i);
    }
}

/// The hypotheses are satisfiable.
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
        assert(s0.th[t as int] == Ph::Idle);
    }
}

} // verus!
