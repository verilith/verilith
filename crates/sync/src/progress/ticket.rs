//! The fair lock is starvation-free: a thread that has asked for it gets
//! it.
//!
//! The model is `fair::Lock` (`src/fair.rs`), a ticket lock, one step per
//! atomic access: taking a ticket (`fetch_add` on `next`), loading
//! `serving` while waiting, and the unlock (`fetch_add` on `serving`).
//! The critical section itself touches neither counter, so it is not a
//! step; that every holder unlocks is built in, as in the other models:
//! a holder's next step is its unlock. The critical sections the crate
//! runs under this lock (a parking-lot bucket's, a channel waiter list's)
//! are verified code that Verus proves terminates.
//!
//! What is proved (`theorem_starvation_free`): in every fair execution,
//! every thread that is waiting at time `i` holds the lock at some time
//! `j >= i`. This is the property the other progress proofs used to
//! assume of `std`'s mutex, which does not have it (it lets threads
//! barge).
//!
//! The proof: the tickets `serving .. next` belong to distinct threads,
//! each waiting or (for `serving` only) holding. The thread with ticket
//! `serving` either holds the lock, and its next step releases it, or is
//! waiting, and its next step finds `serving` equal to its ticket and
//! takes the lock. Either way `serving` grows, and a waiter's ticket is
//! at most `next - 1`, so it is reached after finitely many such rounds.
//!
//! `lemma_bound` also gives what the code needs to let both counters wrap
//! around: fewer tickets are outstanding than there are threads.
use super::trace::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/// Where a thread is in the lock protocol.
pub enum Ph {
    /// Not inside `lock` or `unlock`.
    Idle,
    /// Holds ticket `tk` and waits for `serving` to reach it.
    Wait { tk: nat },
    /// Holds the lock, with ticket `tk`.
    Crit { tk: nat },
}

pub struct Th {
    pub ph: Ph,
}

pub struct St {
    /// The next ticket to hand out.
    pub next: nat,
    /// The ticket allowed in.
    pub serving: nat,
    pub th: Seq<Th>,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.next == 0
    &&& s.serving == 0
    &&& s.th.len() == n
    &&& forall|t: int| 0 <= t < n ==> (#[trigger] s.th[t]).ph == Ph::Idle
}

pub open spec fn ph(s: St, t: nat) -> Ph {
    s.th[t as int].ph
}

/// Thread `t` moves to phase `p`.
pub open spec fn go(s: St, t: nat, p: Ph) -> St {
    St { th: s.th.update(t as int, Th { ph: p }), ..s }
}

/// One step of thread `t`.
pub open spec fn step(s: St, t: nat, s2: St) -> bool {
    match ph(s, t) {
        // Call `lock` (its `fetch_add` on `next`), or do nothing.
        Ph::Idle => s2 == s || s2 == (St { next: s.next + 1, ..go(s, t, Ph::Wait { tk: s.next }) }),
        // A load of `serving`.
        Ph::Wait { tk } => if s.serving == tk {
            s2 == go(s, t, Ph::Crit { tk })
        } else {
            s2 == s
        },
        // `unlock`'s `fetch_add` on `serving`.
        Ph::Crit { tk } => s2 == (St { serving: s.serving + 1, ..go(s, t, Ph::Idle) }),
    }
}

/// An execution: `ex(0)` is initial and step `i` is taken by `sched(i)`.
pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

/// The ticket a thread holds, if it is waiting or holding the lock.
pub open spec fn ticket(p: Ph) -> Option<nat> {
    match p {
        Ph::Idle => None,
        Ph::Wait { tk } => Some(tk),
        Ph::Crit { tk } => Some(tk),
    }
}

/// Some thread holds ticket `tk`.
pub open spec fn has_owner(s: St, n: nat, tk: nat) -> bool {
    exists|t: nat| t < n && #[trigger] ticket(ph(s, t)) == Some(tk)
}

pub open spec fn inv(s: St, n: nat) -> bool {
    &&& s.th.len() == n
    &&& s.serving <= s.next
    // Waiters hold outstanding tickets; only `serving`'s holder is in.
    &&& forall|t: nat| t < n ==> match #[trigger] ph(s, t) {
        Ph::Idle => true,
        Ph::Wait { tk } => s.serving <= tk < s.next,
        Ph::Crit { tk } => tk == s.serving && tk < s.next,
    }
    // Tickets are not shared.
    &&& forall|t: nat, u: nat| t < n && u < n && t != u && #[trigger] ticket(ph(s, t)) is Some
        ==> ticket(ph(s, t)) != #[trigger] ticket(ph(s, u))
    // Every outstanding ticket has its thread.
    &&& forall|tk: nat| s.serving <= tk < s.next ==> #[trigger] has_owner(s, n, tk)
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

/// Only `t`'s own step changes `t`'s phase; the counters only grow, and
/// `serving` grows only by `serving`'s holder's unlock.
pub proof fn lemma_step_frame(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        s2.next >= s.next,
        s2.serving == s.serving || (s2.serving == s.serving + 1 && ph(s, t) == (Ph::Crit { tk: s.serving })),
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
    assert forall|u: nat| u < n implies match #[trigger] ph(s2, u) {
        Ph::Idle => true,
        Ph::Wait { tk } => s2.serving <= tk < s2.next,
        Ph::Crit { tk } => tk == s2.serving && tk < s2.next,
    } by {
        if u != t {
            assert(s2.th[u as int] == s.th[u as int]);
            if let Ph::Wait { tk } = ph(s, u) {
                if ph(s, t) is Crit {
                    // `t`'s ticket was `serving`, so `u`'s is past it.
                    assert(ticket(ph(s, t)) != ticket(ph(s, u)));
                }
            }
            if let Ph::Crit { tk } = ph(s, u) {
                if ph(s, t) is Crit {
                    assert(ticket(ph(s, t)) != ticket(ph(s, u)));
                }
            }
        }
    }
    assert forall|a: nat, b: nat| a < n && b < n && a != b && #[trigger] ticket(ph(s2, a)) is Some
        implies ticket(ph(s2, a)) != #[trigger] ticket(ph(s2, b)) by {
        if a != t && b != t {
            assert(s2.th[a as int] == s.th[a as int]);
            assert(s2.th[b as int] == s.th[b as int]);
            assert(ticket(ph(s, a)) != ticket(ph(s, b)));
        } else if a == t {
            assert(s2.th[b as int] == s.th[b as int]);
            if ph(s, t) is Idle {
                // A fresh ticket: everyone else's is below `next`.
                match ph(s, b) {
                    Ph::Wait { tk } => {},
                    Ph::Crit { tk } => {},
                    Ph::Idle => {},
                }
            } else {
                assert(ticket(ph(s, t)) != ticket(ph(s, b)));
            }
        } else {
            assert(s2.th[a as int] == s.th[a as int]);
            if ph(s, t) is Idle {
                match ph(s, a) {
                    Ph::Wait { tk } => {},
                    Ph::Crit { tk } => {},
                    Ph::Idle => {},
                }
            } else {
                assert(ticket(ph(s, a)) != ticket(ph(s, t)));
            }
        }
    }
    assert forall|tk: nat| s2.serving <= tk < s2.next implies #[trigger] has_owner(s2, n, tk) by {
        if tk == s.next && s2.next == s.next + 1 {
            assert(ticket(ph(s2, t)) == Some(tk));
        } else {
            assert(s.serving <= tk < s.next);
            assert(has_owner(s, n, tk));
            let u = choose|u: nat| u < n && #[trigger] ticket(ph(s, u)) == Some(tk);
            if u == t {
                // `t` kept its ticket: it went from waiting to holding,
                // or stood still. (An unlock gives up only `serving`,
                // which is now below `tk`.)
                assert(ticket(ph(s2, t)) == Some(tk));
            } else {
                assert(s2.th[u as int] == s.th[u as int]);
                assert(ticket(ph(s2, u)) == Some(tk));
            }
        }
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

/// Fewer tickets are outstanding than there are threads, since each
/// belongs to a different one. The code relies on this to let both
/// counters wrap around at `2^64`.
pub proof fn lemma_bound(s: St, n: nat)
    requires
        inv(s, n),
    ensures
        s.next - s.serving <= n,
{
    let x = set_int_range(s.serving as int, s.next as int);
    let f = |tk: int| (choose|t: nat| t < n && #[trigger] ticket(ph(s, t)) == Some(tk as nat)) as int;
    lemma_int_range(s.serving as int, s.next as int);
    lemma_int_range(0, n as int);
    assert forall|a: int, b: int| x.contains(a) && x.contains(b) && #[trigger] f(a) == #[trigger] f(b) implies a == b by {
        assert(has_owner(s, n, a as nat));
        assert(has_owner(s, n, b as nat));
        let ta = choose|t: nat| t < n && #[trigger] ticket(ph(s, t)) == Some(a as nat);
        let tb = choose|t: nat| t < n && #[trigger] ticket(ph(s, t)) == Some(b as nat);
        assert(ticket(ph(s, ta)) == Some(a as nat));
        assert(ticket(ph(s, tb)) == Some(b as nat));
    }
    assert(x.injective_on(f));
    lemma_map_size(x, x.map(f), f);
    assert forall|t: int| #[trigger] x.map(f).contains(t) implies set_int_range(0, n as int).contains(t) by {
        let tk = choose|tk: int| x.contains(tk) && f(tk) == t;
        assert(has_owner(s, n, tk as nat));
        let u = choose|u: nat| u < n && #[trigger] ticket(ph(s, u)) == Some(tk as nat);
        assert(ticket(ph(s, u)) == Some(tk as nat));
    }
    lemma_len_subset(x.map(f), set_int_range(0, n as int));
}

} // verus!

verus! {

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
        ex(m + 1).serving == ex(m).serving || (ex(m + 1).serving == ex(m).serving + 1 && ph(ex(m), sched(m)) == (Ph::Crit { tk: ex(m).serving })),
{
    lemma_inv(ex, sched, n, m);
    lemma_inv(ex, sched, n, m + 1);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step_frame(ex(m), n, sched(m), ex(m + 1));
}

/// `t`'s phase stays put until `t` steps, at `k`.
proof fn lemma_until_step(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, j: nat) -> (k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
    ensures
        k >= j,
        sched(k) == t,
        ex(k).th[t as int] == ex(j).th[t as int],
        forall|m: nat| j <= m <= k ==> #[trigger] ex(m).th[t as int] == ex(j).th[t as int],
        forall|m: nat| j <= m < k ==> #[trigger] sched(m) != t,
{
    let k = lemma_next_step(sched, n, t, j);
    let f = |m: nat| ex(m).th[t as int];
    assert forall|m: nat| j <= m < k && #[trigger] sched(m) != t implies f(m + 1) == f(m) by {
        lemma_at(ex, sched, n, m);
    }
    assert forall|m: nat| j <= m <= k implies #[trigger] ex(m).th[t as int] == ex(j).th[t as int] by {
        lemma_frame(sched, f, t, j, m);
    }
    k
}

/// While a thread holds ticket `serving` and has not stepped, `serving`
/// stays put: only `serving`'s holder can move it, and that is this
/// thread.
proof fn lemma_serving_still(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, j: nat, k: nat)
    requires
        run(ex, sched, n),
        t < n,
        j <= k,
        ticket(ph(ex(j), t)) == Some(ex(j).serving),
        forall|m: nat| j <= m <= k ==> #[trigger] ex(m).th[t as int] == ex(j).th[t as int],
        forall|m: nat| j <= m < k ==> #[trigger] sched(m) != t,
    ensures
        ex(k).serving == ex(j).serving,
    decreases k - j,
{
    if j < k {
        lemma_serving_still(ex, sched, n, t, j, (k - 1) as nat);
        let m = (k - 1) as nat;
        lemma_at(ex, sched, n, m);
        assert(ex(m).th[t as int] == ex(j).th[t as int]);
        if ex(k).serving != ex(m).serving {
            // The stepping thread held ticket `serving`, and so does `t`.
            let u = sched(m);
            assert(sched(m) != t);
            assert(ticket(ph(ex(m), u)) == Some(ex(m).serving));
            assert(ticket(ph(ex(m), t)) == Some(ex(m).serving));
        }
    }
}

/// `serving` grows past its current value: its ticket's thread takes the
/// lock (if it has not) and then releases it.
proof fn lemma_advance(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat) -> (j: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        ex(i).serving < ex(i).next,
    ensures
        j > i,
        ex(j).serving == ex(i).serving + 1,
        forall|m: nat| i <= m <= j ==> #[trigger] ex(m).serving <= ex(i).serving + 1,
{
    lemma_at(ex, sched, n, i);
    let s = ex(i).serving;
    assert(has_owner(ex(i), n, s));
    let u = choose|u: nat| u < n && #[trigger] ticket(ph(ex(i), u)) == Some(s);
    assert(ticket(ph(ex(i), u)) == Some(s));
    let k = lemma_until_step(ex, sched, n, u, i);
    lemma_serving_still(ex, sched, n, u, i, k);
    assert forall|m: nat| i <= m <= k implies #[trigger] ex(m).serving <= s + 1 by {
        lemma_serving_still(ex, sched, n, u, i, m);
    }
    lemma_at(ex, sched, n, k);
    if ph(ex(k), u) is Crit {
        assert(ex(k + 1).serving == s + 1);
        k + 1
    } else {
        // It was waiting: this step lets it in.
        assert(ph(ex(k + 1), u) == (Ph::Crit { tk: s }));
        assert(ex(k + 1).serving == s);
        let k2 = lemma_until_step(ex, sched, n, u, k + 1);
        lemma_serving_still(ex, sched, n, u, k + 1, k2);
        assert forall|m: nat| i <= m <= k2 implies #[trigger] ex(m).serving <= s + 1 by {
            if m > k {
                lemma_serving_still(ex, sched, n, u, k + 1, m);
            }
        }
        lemma_at(ex, sched, n, k2);
        assert(ex(k2 + 1).serving == s + 1);
        k2 + 1
    }
}

/// The lock is held by `t` at some time at or after `i`.
pub open spec fn gets_in(ex: spec_fn(nat) -> St, t: nat, i: nat) -> bool {
    exists|j: nat| j >= i && #[trigger] ph(ex(j), t) is Crit
}

/// A waiter keeps its ticket until it gets in.
proof fn lemma_waits(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, tk: nat, i: nat, m: nat)
    requires
        run(ex, sched, n),
        t < n,
        i <= m,
        ph(ex(i), t) == (Ph::Wait { tk }),
        !gets_in(ex, t, i),
    ensures
        ph(ex(m), t) == (Ph::Wait { tk }),
    decreases m - i,
{
    if i < m {
        lemma_waits(ex, sched, n, t, tk, i, (m - 1) as nat);
        lemma_at(ex, sched, n, (m - 1) as nat);
        if !(ph(ex(m), t) == (Ph::Wait { tk })) {
            assert(ph(ex(m), t) is Crit);
        }
    }
}

proof fn lemma_wait(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, tk: nat, i: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
        ph(ex(i), t) == (Ph::Wait { tk }),
    ensures
        gets_in(ex, t, i),
    decreases tk - ex(i).serving,
{
    lemma_at(ex, sched, n, i);
    if !gets_in(ex, t, i) {
        if ex(i).serving == tk {
            // `serving` stays at `tk` until `t` steps, and then it is in.
            let k = lemma_until_step(ex, sched, n, t, i);
            lemma_serving_still(ex, sched, n, t, i, k);
            lemma_at(ex, sched, n, k);
            assert(ph(ex(k + 1), t) is Crit);
            assert(gets_in(ex, t, i));
        } else {
            let j = lemma_advance(ex, sched, n, i);
            lemma_waits(ex, sched, n, t, tk, i, j);
            lemma_at(ex, sched, n, j);
            lemma_wait(ex, sched, n, t, tk, j);
            let j2 = choose|j2: nat| j2 >= j && #[trigger] ph(ex(j2), t) is Crit;
            assert(gets_in(ex, t, i));
        }
    }
}

/// Starvation freedom: in a fair execution, a thread inside `lock()` at
/// time `i` holds the lock at some time `j >= i`.
pub proof fn theorem_starvation_free(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
        ph(ex(i), t) is Wait,
    ensures
        gets_in(ex, t, i),
{
    if let Ph::Wait { tk } = ph(ex(i), t) {
        lemma_wait(ex, sched, n, t, tk, i);
    }
}

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

/// The model as `crate::model::Model` takes it: `src/fair.rs` holds one
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
