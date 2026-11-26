//! Cloning a channel handle is lock-free: while a thread is cloning, some
//! clone or drop on the same side takes effect.
//!
//! The model is the handle count of one side of a channel
//! (`chan_sync::Chan::add_handle` and `drop_handle`), one step per atomic
//! access: a clone loads the count and then retries a compare-and-swap
//! from the value it last saw to one more, taking the value the failed
//! CAS returned each time; a drop is one `fetch_sub`. The count's atomic
//! is sequentially consistent, so a load or a failed CAS returns the
//! current value. `done` counts the updates that took effect.
//!
//! What is proved (`theorem_lock_free`): in every fair execution, if a
//! thread is cloning at time `i`, `done` grows at some time `j >= i`. A
//! clone's CAS fails only if the count changed since the clone saw it,
//! and the count changes only by an update that took effect.
//!
//! Not proved, because it is false: that every clone succeeds. Other
//! clones and drops on the same side can win every race.
use super::trace::*;
use vstd::prelude::*;

verus! {

/// Where a thread is.
pub enum Ph {
    /// Not cloning.
    Idle,
    /// Cloning, about to CAS the count from `seen` to `seen + 1`.
    Cas { seen: nat },
}

pub struct Th {
    pub ph: Ph,
}

pub struct St {
    /// The handle count.
    pub count: nat,
    /// How many clones and drops have taken effect.
    pub done: nat,
    pub th: Seq<Th>,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.done == 0
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
        // Nothing; a clone's first load; or a whole drop (its
        // `fetch_sub`, which needs a handle to drop).
        Ph::Idle => s2 == s || s2 == go(s, t, Ph::Cas { seen: s.count })
            || (s.count > 0 && s2 == (St { count: (s.count - 1) as nat, done: s.done + 1, ..s })),
        // The CAS: it succeeds, and the clone returns, or it fails and
        // returns the current count, the next try's expected value.
        Ph::Cas { seen } => if s.count == seen {
            s2 == (St { count: s.count + 1, done: s.done + 1, ..go(s, t, Ph::Idle) })
        } else {
            s2 == go(s, t, Ph::Cas { seen: s.count })
        },
    }
}

/// An execution: `ex(0)` is initial and step `i` is taken by `sched(i)`.
pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

pub open spec fn inv(s: St, n: nat) -> bool {
    s.th.len() == n
}

/// Only `t`'s own step changes `t`'s phase, `done` never shrinks, and the
/// count changes only when `done` grows.
pub proof fn lemma_step_frame(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        inv(s2, n),
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        s2.done >= s.done,
        s2.done == s.done ==> s2.count == s.count,
{
}

proof fn lemma_inv(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(i), n),
    decreases i,
{
    if i > 0 {
        lemma_inv(ex, sched, n, (i - 1) as nat);
        assert(sched((i - 1) as nat) < n && step(ex((i - 1) as nat), sched((i - 1) as nat), ex(i)));
        lemma_step_frame(ex((i - 1) as nat), n, sched((i - 1) as nat), ex(i));
    }
}

proof fn lemma_at(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, m: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(m), n),
        sched(m) < n,
        step(ex(m), sched(m), ex(m + 1)),
        forall|u: nat| u < n && u != sched(m) ==> #[trigger] ex(m + 1).th[u as int] == ex(m).th[u as int],
        ex(m + 1).done >= ex(m).done,
        ex(m + 1).done == ex(m).done ==> ex(m + 1).count == ex(m).count,
{
    lemma_inv(ex, sched, n, m);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step_frame(ex(m), n, sched(m), ex(m + 1));
}

/// Some update takes effect at or after `i`.
pub open spec fn progress(ex: spec_fn(nat) -> St, i: nat) -> bool {
    exists|j: nat| j >= i && #[trigger] ex(j).done > ex(i).done
}

/// If no update takes effect from `i` to `k`, the count stays put.
proof fn lemma_still(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, k: nat)
    requires
        run(ex, sched, n),
        i <= k,
        !progress(ex, i),
    ensures
        ex(k).done == ex(i).done,
        ex(k).count == ex(i).count,
    decreases k - i,
{
    if i < k {
        lemma_still(ex, sched, n, i, (k - 1) as nat);
        lemma_at(ex, sched, n, (k - 1) as nat);
        if ex(k).done != ex(i).done {
            assert(ex(k).done > ex(i).done);
        }
    }
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
{
    let k = lemma_next_step(sched, n, t, j);
    let f = |m: nat| ex(m).th[t as int];
    assert forall|m: nat| j <= m < k && #[trigger] sched(m) != t implies f(m + 1) == f(m) by {
        lemma_at(ex, sched, n, m);
    }
    lemma_frame(sched, f, t, j, k);
    k
}

/// Lock freedom: in a fair execution, while a thread is cloning at time
/// `i`, some clone or drop takes effect at some time `j >= i`.
pub proof fn theorem_lock_free(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, t: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
        ph(ex(i), t) is Cas,
    ensures
        progress(ex, i),
{
    if !progress(ex, i) {
        // The next try fails only if the count moved since `t` saw it,
        // and then `t` sees the current count; the try after that
        // succeeds.
        let k = lemma_until_step(ex, sched, n, t, i);
        lemma_still(ex, sched, n, i, k);
        assert(ph(ex(k), t) == ph(ex(i), t));
        lemma_at(ex, sched, n, k);
        lemma_still(ex, sched, n, i, k + 1);
        if ex(k + 1).done == ex(i).done {
            assert(ph(ex(k + 1), t) == (Ph::Cas { seen: ex(k).count }));
            let k2 = lemma_until_step(ex, sched, n, t, k + 1);
            lemma_still(ex, sched, n, i, k2);
            assert(ph(ex(k2), t) == ph(ex(k + 1), t));
            lemma_at(ex, sched, n, k2);
            assert(ex(k2 + 1).done == ex(k2).done + 1);
            assert(ex(k2 + 1).done > ex(i).done);
        }
        assert(ex(k + 1).done > ex(i).done || ex(k + 1).done == ex(i).done);
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

/// The model as `crate::model::Model` takes it: `src/chan_sync.rs` holds
/// one for each side's count and is verified to follow it.
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
        assert forall|t: int| 0 <= t < n implies (#[trigger] s.th[t]).ph == Ph::Idle by {}
    }

    proof fn lemma_step(s: St, n: nat, t: nat, s2: St) {
        lemma_step_frame(s, n, t, s2);
        assert forall|u: int| 0 <= u < n && u != t implies #[trigger] s2.th[u] == s.th[u] by {
            assert(s2.th[(u as nat) as int] == s.th[(u as nat) as int]);
        }
    }

    proof fn lemma_len(s: St, n: nat) {
    }
}

} // verus!
