//! Infinite executions, fair schedules, and the two facts every progress
//! proof here uses: a thread's next step comes, and until then nothing it
//! alone controls changes.
use vstd::prelude::*;

verus! {

/// Thread `t` takes a step at or after time `i`.
pub open spec fn steps_after(sched: spec_fn(nat) -> nat, t: nat, i: nat) -> bool {
    exists|j: nat| j >= i && #[trigger] sched(j) == t
}

/// Every thread `t < n` takes a step at or after every point in time.
pub open spec fn fair(sched: spec_fn(nat) -> nat, n: nat) -> bool {
    forall|t: nat, i: nat| t < n ==> #[trigger] steps_after(sched, t, i)
}

proof fn lemma_first(sched: spec_fn(nat) -> nat, t: nat, i: nat, j: nat) -> (k: nat)
    requires
        i <= j,
        sched(j) == t,
    ensures
        i <= k <= j,
        sched(k) == t,
        forall|m: nat| i <= m < k ==> #[trigger] sched(m) != t,
    decreases j - i,
{
    if sched(i) == t {
        i
    } else {
        lemma_first(sched, t, i + 1, j)
    }
}

/// The first step of thread `t` at or after `i`.
pub proof fn lemma_next_step(sched: spec_fn(nat) -> nat, n: nat, t: nat, i: nat) -> (k: nat)
    requires
        fair(sched, n),
        t < n,
    ensures
        k >= i,
        sched(k) == t,
        forall|m: nat| i <= m < k ==> #[trigger] sched(m) != t,
{
    assert(steps_after(sched, t, i));
    let j = choose|j: nat| j >= i && #[trigger] sched(j) == t;
    lemma_first(sched, t, i, j)
}

/// A value that only `t`'s own steps change is the same at `k` as at `i`
/// when `t` takes no step in between.
pub proof fn lemma_frame<A>(sched: spec_fn(nat) -> nat, f: spec_fn(nat) -> A, t: nat, i: nat, k: nat)
    requires
        i <= k,
        forall|m: nat| i <= m < k ==> #[trigger] sched(m) != t,
        forall|m: nat| i <= m < k && #[trigger] sched(m) != t ==> f(m + 1) == f(m),
    ensures
        f(k) == f(i),
    decreases k - i,
{
    if i < k {
        assert(sched(i) != t);
        assert(f(i + 1) == f(i));
        lemma_frame(sched, f, t, i + 1, k);
    }
}

} // verus!

verus! {

/// `P(t, m)` holds for every `m >= k`.
pub open spec fn holds_from(p: spec_fn(nat, nat) -> bool, t: nat, k: nat) -> bool {
    forall|m: nat| m >= k ==> #[trigger] p(t, m)
}

/// Thread `t` satisfies `P` for good from some time `k >= i` on.
pub open spec fn eventually_always(p: spec_fn(nat, nat) -> bool, t: nat, i: nat) -> bool {
    exists|k: nat| k >= i && #[trigger] holds_from(p, t, k)
}

/// If each of `n` threads eventually satisfies `P` for good, there is one
/// time after which all of them do.
pub proof fn lemma_all_eventually(p: spec_fn(nat, nat) -> bool, n: nat, i: nat) -> (k: nat)
    requires
        forall|t: nat| t < n ==> #[trigger] eventually_always(p, t, i),
    ensures
        k >= i,
        forall|t: nat, m: nat| t < n && m >= k ==> #[trigger] p(t, m),
    decreases n,
{
    if n == 0 {
        i
    } else {
        let k0 = lemma_all_eventually(p, (n - 1) as nat, i);
        let t = (n - 1) as nat;
        assert(eventually_always(p, t, i));
        let kt = choose|k: nat| k >= i && #[trigger] holds_from(p, t, k);
        let k = if k0 >= kt { k0 } else { kt };
        assert forall|t1: nat, m: nat| t1 < n && m >= k implies #[trigger] p(t1, m) by {
            if t1 == t {
                assert(holds_from(p, t, kt));
            }
        }
        k
    }
}

} // verus!

verus! {

/// Round-robin scheduling is fair, so the theorems' hypotheses can hold.
pub proof fn lemma_round_robin_fair(n: nat)
    requires
        n > 0,
    ensures
        fair(|i: nat| i % n, n),
{
    let sched = |i: nat| i % n;
    assert forall|t: nat, i: nat| t < n implies #[trigger] steps_after(sched, t, i) by {
        let j: nat = n * i + t;
        assert(n * i >= i) by (nonlinear_arith)
            requires n > 0;
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(i as int, t as int, n as int);
        vstd::arithmetic::div_mod::lemma_small_mod(t, n);
        assert(sched(j) == t);
    }
}

} // verus!
