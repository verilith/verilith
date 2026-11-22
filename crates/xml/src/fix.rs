//! The least fixed point of a system of Horn clauses over `n` items, in
//! time linear in its size: item `k` holds when `local[k]` does and every
//! item in `deps[k]` holds. Which entities may be referred to in attribute
//! values and in content are such systems (`ent.rs`), whose spec, `oka_seq`
//! and `okc_seq`, applies the clauses level by level: `hlev(d)` is what
//! holds through chains of at most `d` items.
//!
//! `ex_hfix` computes `hlev(n)`, which is every level from `n` on
//! (`lemma_hlev_settled`), with a worklist (Kahn's algorithm): it counts
//! each item's dependencies that are not yet known to hold, and marks an
//! item when its count reaches zero. Every dependency is counted once and
//! discounted once, so the work is linear in `n` and the dependencies.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// Every element of `s` is an index of `p` at which `p` holds.
pub open spec fn all_in(s: Seq<int>, p: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < p.len() && p[s[i]]
}

/// Every dependency is one of the `n` items.
pub open spec fn deps_wf(n: int, deps: Seq<Seq<int>>) -> bool {
    &&& deps.len() == n
    &&& forall|k: int, i: int| 0 <= k < n && 0 <= i < deps[k].len() ==> 0 <= #[trigger] deps[k][i] < n
}

/// One application of the clauses to `prev`.
pub open spec fn hstep(local: Seq<bool>, deps: Seq<Seq<int>>, prev: Seq<bool>) -> Seq<bool> {
    Seq::new(local.len(), |k: int| local[k] && all_in(deps[k], prev))
}

/// What holds through chains of at most `d` items.
pub open spec fn hlev(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat) -> Seq<bool>
    decreases d,
{
    if d == 0 {
        Seq::new(local.len(), |k: int| false)
    } else {
        hstep(local, deps, hlev(local, deps, (d - 1) as nat))
    }
}

/// How many of `p` hold.
pub open spec fn cnt(p: Seq<bool>) -> nat
    decreases p.len(),
{
    if p.len() == 0 {
        0
    } else {
        cnt(p.drop_last()) + if p.last() {
            1nat
        } else {
            0nat
        }
    }
}

/// How many times `j` is in `s`.
pub open spec fn occ(s: Seq<int>, j: int) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        occ(s.drop_last(), j) + if s.last() == j {
            1nat
        } else {
            0nat
        }
    }
}

/// How many elements of `s` are not marked in `p`.
pub open spec fn unp(s: Seq<int>, p: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        unp(s.drop_last(), p) + if p[s.last()] {
            0nat
        } else {
            1nat
        }
    }
}

/// `p` holds wherever `q` does... the other way round: `p` is below `q`.
pub open spec fn below(p: Seq<bool>, q: Seq<bool>) -> bool {
    p.len() == q.len() && forall|k: int| 0 <= k < p.len() && #[trigger] p[k] ==> q[k]
}

// ---------------------------------------------------------------------------
// The levels: monotone, and settled by level n
// ---------------------------------------------------------------------------

pub proof fn lemma_hlev_len(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat)
    ensures
        hlev(local, deps, d).len() == local.len(),
    decreases d,
{
    if d > 0 {
        lemma_hlev_len(local, deps, (d - 1) as nat);
    }
}

/// `hstep` is monotone.
pub proof fn lemma_hstep_mono(local: Seq<bool>, deps: Seq<Seq<int>>, p: Seq<bool>, q: Seq<bool>)
    requires
        below(p, q),
    ensures
        below(hstep(local, deps, p), hstep(local, deps, q)),
{
    assert forall|k: int| 0 <= k < local.len() && #[trigger] hstep(local, deps, p)[k] implies hstep(
        local,
        deps,
        q,
    )[k] by {
        assert forall|i: int| 0 <= i < deps[k].len() implies 0 <= #[trigger] deps[k][i] < q.len() && q[deps[k][i]] by {
            assert(all_in(deps[k], p));
            assert(p[deps[k][i]]);
        }
    }
}

/// Each level is below the next.
pub proof fn lemma_hlev_mono(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat)
    ensures
        below(hlev(local, deps, d), hlev(local, deps, d + 1)),
    decreases d,
{
    lemma_hlev_len(local, deps, d);
    lemma_hlev_len(local, deps, d + 1);
    if d > 0 {
        lemma_hlev_mono(local, deps, (d - 1) as nat);
        lemma_hstep_mono(local, deps, hlev(local, deps, (d - 1) as nat), hlev(local, deps, d));
    }
}

/// Each level is below every later one.
pub proof fn lemma_hlev_mono_le(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat, e: nat)
    requires
        d <= e,
    ensures
        below(hlev(local, deps, d), hlev(local, deps, e)),
    decreases e - d,
{
    lemma_hlev_len(local, deps, d);
    if d < e {
        lemma_hlev_mono(local, deps, d);
        lemma_hlev_mono_le(local, deps, d + 1, e);
    }
}

/// Once a level is the one before, so is every later level.
pub proof fn lemma_hlev_fixed_from(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat, m: nat)
    requires
        hlev(local, deps, d + 1) == hlev(local, deps, d),
    ensures
        hlev(local, deps, d + m) == hlev(local, deps, d),
    decreases m,
{
    if m > 0 {
        lemma_hlev_fixed_from(local, deps, d, (m - 1) as nat);
        assert(hlev(local, deps, d + m) == hstep(local, deps, hlev(local, deps, (d + m - 1) as nat)));
    }
}

pub proof fn lemma_cnt_le(p: Seq<bool>)
    ensures
        cnt(p) <= p.len(),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_cnt_le(p.drop_last());
    }
}

/// Below means no more, and fewer unless equal.
pub proof fn lemma_cnt_below(p: Seq<bool>, q: Seq<bool>)
    requires
        below(p, q),
    ensures
        cnt(p) <= cnt(q),
        p != q ==> cnt(p) < cnt(q),
    decreases p.len(),
{
    if p.len() > 0 {
        let (p1, q1) = (p.drop_last(), q.drop_last());
        assert(below(p1, q1));
        lemma_cnt_below(p1, q1);
        if p != q && p1 == q1 {
            assert(p.last() != q.last()) by {
                if p.last() == q.last() {
                    assert forall|i: int| 0 <= i < p.len() implies p[i] == q[i] by {
                        if i < p.len() - 1 {
                            assert(p1[i] == p[i] && q1[i] == q[i]);
                        }
                    }
                    assert(p =~= q);
                }
            }
        }
    } else {
        assert(p =~= q);
    }
}

/// Unless the levels have settled, level `d` holds for at least `d` items.
proof fn lemma_hlev_grows(local: Seq<bool>, deps: Seq<Seq<int>>, d: nat)
    requires
        forall|e: nat| e < d ==> hlev(local, deps, e + 1) != #[trigger] hlev(local, deps, e),
    ensures
        cnt(hlev(local, deps, d)) >= d,
    decreases d,
{
    if d > 0 {
        let e = (d - 1) as nat;
        lemma_hlev_grows(local, deps, e);
        lemma_hlev_mono(local, deps, e);
        assert(hlev(local, deps, e + 1) != hlev(local, deps, e));
        lemma_cnt_below(hlev(local, deps, e), hlev(local, deps, d));
    }
}

/// Level `n` is every later level: the clauses' least fixed point.
pub proof fn lemma_hlev_settled(local: Seq<bool>, deps: Seq<Seq<int>>, m: nat)
    ensures
        hlev(local, deps, local.len() + m) == hlev(local, deps, local.len()),
{
    let n = local.len();
    if exists|e: nat| e <= n && hlev(local, deps, e + 1) == #[trigger] hlev(local, deps, e) {
        let e = choose|e: nat| e <= n && hlev(local, deps, e + 1) == #[trigger] hlev(local, deps, e);
        lemma_hlev_fixed_from(local, deps, e, (n - e) as nat);
        lemma_hlev_fixed_from(local, deps, e, (n + m - e) as nat);
    } else {
        lemma_hlev_grows(local, deps, n + 1);
        lemma_hlev_len(local, deps, n + 1);
        lemma_cnt_le(hlev(local, deps, n + 1));
    }
}

// ---------------------------------------------------------------------------
// Counting lemmas
// ---------------------------------------------------------------------------

pub proof fn lemma_occ_push(s: Seq<int>, v: int, j: int)
    ensures
        occ(s.push(v), j) == occ(s, j) + if v == j {
            1nat
        } else {
            0nat
        },
{
    assert(s.push(v).drop_last() =~= s);
}

pub proof fn lemma_occ_take(s: Seq<int>, t: int, j: int)
    requires
        0 <= t < s.len(),
    ensures
        occ(s.subrange(0, t + 1), j) == occ(s.subrange(0, t), j) + if s[t] == j {
            1nat
        } else {
            0nat
        },
{
    assert(s.subrange(0, t + 1).drop_last() =~= s.subrange(0, t));
}

pub proof fn lemma_occ_le_unp(s: Seq<int>, p: Seq<bool>, j: int)
    requires
        0 <= j < p.len(),
        !p[j],
    ensures
        occ(s, j) <= unp(s, p),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_occ_le_unp(s.drop_last(), p, j);
    }
}

/// Marking `j` discounts its occurrences.
pub proof fn lemma_unp_mark(s: Seq<int>, p: Seq<bool>, j: int)
    requires
        0 <= j < p.len(),
        !p[j],
    ensures
        unp(s, p.update(j, true)) + occ(s, j) == unp(s, p),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_unp_mark(s.drop_last(), p, j);
    }
}

/// When the only unmarked elements of `s` are the occurrences of `j`,
/// every element is marked or is `j`.
pub proof fn lemma_unp_only(s: Seq<int>, p: Seq<bool>, j: int)
    requires
        unp(s, p) == occ(s, j),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < p.len(),
        0 <= j < p.len(),
        !p[j],
    ensures
        forall|i: int| 0 <= i < s.len() ==> p[#[trigger] s[i]] || s[i] == j,
    decreases s.len(),
{
    if s.len() > 0 {
        let s1 = s.drop_last();
        lemma_occ_le_unp(s1, p, j);
        assert forall|i: int| 0 <= i < s1.len() implies 0 <= #[trigger] s1[i] < p.len() by {
            assert(s1[i] == s[i]);
        }
        lemma_unp_only(s1, p, j);
        assert forall|i: int| 0 <= i < s.len() implies p[#[trigger] s[i]] || s[i] == j by {
            if i < s1.len() {
                assert(s1[i] == s[i]);
            }
        }
    }
}

/// No unmarked element means every element is marked.
pub proof fn lemma_unp_zero(s: Seq<int>, p: Seq<bool>)
    ensures
        unp(s, p) == 0 <==> forall|i: int| 0 <= i < s.len() ==> p[#[trigger] s[i]],
    decreases s.len(),
{
    if s.len() > 0 {
        let s1 = s.drop_last();
        lemma_unp_zero(s1, p);
        if unp(s, p) == 0 {
            assert forall|i: int| 0 <= i < s.len() implies p[#[trigger] s[i]] by {
                if i < s1.len() {
                    assert(s1[i] == s[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < s.len() ==> p[#[trigger] s[i]] {
            assert forall|i: int| 0 <= i < s1.len() implies p[#[trigger] s1[i]] by {
                assert(s1[i] == s[i]);
            }
            assert(p[s[s.len() - 1]]);
        }
    }
}

pub proof fn lemma_cnt_mark(p: Seq<bool>, j: int)
    requires
        0 <= j < p.len(),
        !p[j],
    ensures
        cnt(p.update(j, true)) == cnt(p) + 1,
    decreases p.len(),
{
    let q = p.update(j, true);
    if j == p.len() - 1 {
        assert(q.drop_last() =~= p.drop_last());
    } else {
        assert(q.drop_last() =~= p.drop_last().update(j, true));
        lemma_cnt_mark(p.drop_last(), j);
    }
}

pub proof fn lemma_occ_prefix_le(s: Seq<int>, t: int, j: int)
    requires
        0 <= t <= s.len(),
    ensures
        occ(s.subrange(0, t), j) <= occ(s, j),
    decreases s.len() - t,
{
    if t < s.len() {
        lemma_occ_take(s, t, j);
        lemma_occ_prefix_le(s, t + 1, j);
    } else {
        assert(s.subrange(0, t) =~= s);
    }
}

/// With nothing marked, every element counts.
pub proof fn lemma_unp_none(s: Seq<int>, p: Seq<bool>)
    requires
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < p.len() && !p[s[i]],
    ensures
        unp(s, p) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let s1 = s.drop_last();
        assert forall|i: int| 0 <= i < s1.len() implies 0 <= #[trigger] s1[i] < p.len() && !p[s1[i]] by {
            assert(s1[i] == s[i]);
        }
        lemma_unp_none(s1, p);
        assert(!p[s[s.len() - 1]]);
    }
}

pub proof fn lemma_cnt_pos(p: Seq<bool>, q: int)
    requires
        0 <= q < p.len(),
        p[q],
    ensures
        cnt(p) >= 1,
    decreases p.len(),
{
    if q < p.len() - 1 {
        assert(p.drop_last()[q] == p[q]);
        lemma_cnt_pos(p.drop_last(), q);
    }
}

pub proof fn lemma_push_contains(s: Seq<usize>, v: usize, x: usize)
    ensures
        s.push(v).contains(x) == (s.contains(x) || x == v),
{
    if s.contains(x) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(s.push(v)[i] == x);
    }
    if x == v {
        assert(s.push(v)[s.len() as int] == x);
    }
    if s.push(v).contains(x) {
        let i = choose|i: int| 0 <= i < s.push(v).len() && s.push(v)[i] == x;
        if i < s.len() {
            assert(s[i] == x);
        }
    }
}

pub proof fn lemma_push_nodup(s: Seq<usize>, v: usize)
    requires
        s.no_duplicates(),
        !s.contains(v),
    ensures
        s.push(v).no_duplicates(),
{
    let t = s.push(v);
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        if i < s.len() && j < s.len() {
            assert(t[i] == s[i] && t[j] == s[j]);
        } else if i < s.len() {
            assert(t[i] == s[i]);
        } else if j < s.len() {
            assert(t[j] == s[j]);
        }
    }
}

pub proof fn lemma_pop_contains(s: Seq<usize>, x: usize)
    requires
        s.no_duplicates(),
        s.len() > 0,
    ensures
        s.drop_last().no_duplicates(),
        s.drop_last().contains(x) == (s.contains(x) && x != s.last()),
{
    let t = s.drop_last();
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        assert(t[i] == s[i] && t[j] == s[j]);
    }
    if t.contains(x) {
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        assert(s[i] == x);
        assert(s[i] != s[s.len() - 1]);
    }
    if s.contains(x) && x != s.last() {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(t[i] == x);
    }
}

/// When the worklist is empty, everything the clauses give is done.
proof fn lemma_complete(local: Seq<bool>, ds: Seq<Seq<int>>, done: Seq<bool>, d: nat)
    requires
        deps_wf(local.len() as int, ds),
        done.len() == local.len(),
        forall|q: int| 0 <= q < local.len() && local[q] && !#[trigger] done[q] ==> unp(ds[q], done) > 0,
    ensures
        forall|q: int| 0 <= q < local.len() && #[trigger] hlev(local, ds, d)[q] ==> done[q],
    decreases d,
{
    if d > 0 {
        lemma_complete(local, ds, done, (d - 1) as nat);
        let prev = hlev(local, ds, (d - 1) as nat);
        assert forall|q: int| 0 <= q < local.len() && #[trigger] hlev(local, ds, d)[q] implies done[q] by {
            assert(hlev(local, ds, d) == hstep(local, ds, prev));
            assert(all_in(ds[q], prev));
            assert forall|i: int| 0 <= i < ds[q].len() implies done[#[trigger] ds[q][i]] by {
                assert(prev[ds[q][i]]);
            }
            lemma_unp_zero(ds[q], done);
        }
    }
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

pub open spec fn deps_view(deps: Seq<Vec<usize>>) -> Seq<Seq<int>> {
    deps.map_values(|v: Vec<usize>| v@.map_values(|x: usize| x as int))
}

/// The dependants of `j` recorded in `rev`, as numbers.
pub open spec fn rv(rev: Seq<Vec<usize>>, j: int) -> Seq<int> {
    rev[j]@.map_values(|x: usize| x as int)
}

/// The state of the worklist: `done` the items known to hold, `proc` those
/// whose dependants have been discounted, `pend[k]` the dependencies of `k`
/// not yet discounted, and `work` the items done but not processed.
pub open spec fn kahn_inv(
    local: Seq<bool>,
    ds: Seq<Seq<int>>,
    rev: Seq<Vec<usize>>,
    pend: Seq<usize>,
    done: Seq<bool>,
    proc: Seq<bool>,
    work: Seq<usize>,
) -> bool {
    let n = local.len();
    &&& deps_wf(n as int, ds)
    &&& rev.len() == n && pend.len() == n && done.len() == n && proc.len() == n
    &&& forall|j: int, k: int| 0 <= j < n && 0 <= k < n ==> #[trigger] occ(rv(rev, j), k) == occ(ds[k], j)
    &&& forall|j: int, t: int| 0 <= j < n && 0 <= t < rev[j]@.len() ==> #[trigger] rev[j]@[t] < n
    &&& forall|k: int| 0 <= k < n ==> #[trigger] pend[k] == unp(ds[k], proc)
    &&& forall|k: int| 0 <= k < n && #[trigger] done[k] ==> local[k]
    &&& forall|k: int| 0 <= k < n && #[trigger] proc[k] ==> done[k]
    &&& forall|k: int| 0 <= k < n && local[k] && !#[trigger] done[k] ==> pend[k] > 0
    &&& forall|k: int| 0 <= k < n && #[trigger] done[k] ==> hlev(local, ds, cnt(done))[k]
    &&& work.no_duplicates()
    &&& forall|t: int| 0 <= t < work.len() ==> #[trigger] work[t] < n && done[work[t] as int] && !proc[work[t] as int]
    &&& forall|k: int| 0 <= k < n && #[trigger] done[k] && !proc[k] ==> work.contains(k as usize)
}

/// Marking `k`, all of whose dependencies are done, keeps every done
/// item within the level of the new count.
proof fn lemma_mark_level(local: Seq<bool>, ds: Seq<Seq<int>>, done: Seq<bool>, k: int)
    requires
        deps_wf(local.len() as int, ds),
        done.len() == local.len(),
        0 <= k < local.len(),
        local[k],
        !done[k],
        forall|i: int| 0 <= i < ds[k].len() ==> done[#[trigger] ds[k][i]],
        forall|q: int| 0 <= q < local.len() && #[trigger] done[q] ==> hlev(local, ds, cnt(done))[q],
    ensures
        forall|q: int|
            0 <= q < local.len() && #[trigger] done.update(k, true)[q] ==> hlev(local, ds, cnt(done.update(k, true)))[q],
{
    let c = cnt(done);
    lemma_cnt_mark(done, k);
    lemma_hlev_mono(local, ds, c);
    lemma_hlev_len(local, ds, c);
    lemma_hlev_len(local, ds, c + 1);
    let prev = hlev(local, ds, c);
    assert(hlev(local, ds, c + 1) == hstep(local, ds, prev));
    assert(all_in(ds[k], prev)) by {
        assert forall|i: int| 0 <= i < ds[k].len() implies 0 <= #[trigger] ds[k][i] < prev.len() && prev[ds[k][i]] by {
            assert(done[ds[k][i]]);
        }
    }
    assert forall|q: int|
        0 <= q < local.len() && #[trigger] done.update(k, true)[q] implies hlev(local, ds, cnt(done.update(k, true)))[q] by {
        if q != k {
            assert(done[q]);
            assert(below(hlev(local, ds, c), hlev(local, ds, c + 1)));
        }
    }
}

/// `hlev(local, deps, n)`: which of the `n` items hold.
#[verifier::spinoff_prover]
#[verifier::rlimit(600)]
pub fn ex_hfix(local: &Vec<bool>, deps: &Vec<Vec<usize>>) -> (r: Vec<bool>)
    requires
        deps@.len() == local@.len(),
        forall|k: int, i: int| 0 <= k < deps@.len() && 0 <= i < deps@[k]@.len() ==> #[trigger] deps@[k]@[i] < local@.len(),
    ensures
        r@ == hlev(local@, deps_view(deps@), local@.len() as nat),
{
    let n = local.len();
    let ghost ds = deps_view(deps@);
    proof {
        assert forall|k: int, i: int| 0 <= k < n && 0 <= i < ds[k].len() implies 0 <= #[trigger] ds[k][i] < n by {
            assert(ds[k][i] == deps@[k]@[i] as int);
        }
    }
    // The dependants of each item, once per occurrence.
    let mut rev: Vec<Vec<usize>> = Vec::new();
    while rev.len() < n
        invariant
            rev@.len() <= n,
            forall|j: int| 0 <= j < rev@.len() ==> (#[trigger] rev@[j])@.len() == 0,
        decreases n - rev@.len(),
    {
        rev.push(Vec::new());
    }
    proof {
        assert forall|j: int, q: int| 0 <= j < n && 0 <= q < n implies #[trigger] occ(rv(rev@, j), q) == 0 by {
            assert(rv(rev@, j) =~= Seq::<int>::empty());
        }
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == local@.len() == deps@.len(),
            ds == deps_view(deps@),
            deps_wf(n as int, ds),
            rev@.len() == n,
            forall|j: int, t: int| 0 <= j < n && 0 <= t < rev@[j]@.len() ==> #[trigger] rev@[j]@[t] < n,
            forall|j: int, q: int|
                0 <= j < n && 0 <= q < n ==> #[trigger] occ(rv(rev@, j), q) == if q < k {
                    occ(ds[q], j)
                } else {
                    0nat
                },
        decreases n - k,
    {
        let dk = &deps[k];
        let mut i: usize = 0;
        proof {
            assert(dk@.map_values(|x: usize| x as int) == ds[k as int]);
        }
        while i < dk.len()
            invariant
                k < n,
                i <= dk@.len(),
                n == local@.len() == deps@.len(),
                dk == deps@[k as int],
                ds == deps_view(deps@),
                ds[k as int] == dk@.map_values(|x: usize| x as int),
                deps_wf(n as int, ds),
                rev@.len() == n,
                forall|j: int, t: int| 0 <= j < n && 0 <= t < rev@[j]@.len() ==> #[trigger] rev@[j]@[t] < n,
                forall|j: int, q: int|
                    0 <= j < n && 0 <= q < n ==> #[trigger] occ(rv(rev@, j), q) == if q < k {
                        occ(ds[q], j)
                    } else if q == k {
                        occ(ds[k as int].subrange(0, i as int), j)
                    } else {
                        0nat
                    },
            decreases dk@.len() - i,
        {
            let x = dk[i];
            proof {
                assert(ds[k as int][i as int] == x as int);
                assert(x < n);
            }
            let ghost old_rev = rev@;
            rev[x].push(k);
            proof {
                assert forall|j: int| 0 <= j < n && j != x as int implies rev@[j] == old_rev[j] by {}
                assert(rev@[x as int]@ == old_rev[x as int]@.push(k));
                assert forall|j: int, t: int| 0 <= j < n && 0 <= t < rev@[j]@.len() implies #[trigger] rev@[j]@[t] < n by {
                    if j == x as int {
                        if t < old_rev[j]@.len() {
                            assert(rev@[j]@[t] == old_rev[j]@[t]);
                        }
                    }
                }
                assert forall|j: int, q: int| 0 <= j < n && 0 <= q < n implies #[trigger] occ(rv(rev@, j), q) == if q < k {
                    occ(ds[q], j)
                } else if q == k {
                    occ(ds[k as int].subrange(0, i + 1), j)
                } else {
                    0nat
                } by {
                    lemma_occ_take(ds[k as int], i as int, j);
                    if j == x as int {
                        assert(rv(rev@, j) =~= rv(old_rev, j).push(k as int));
                        lemma_occ_push(rv(old_rev, j), k as int, q);
                    } else {
                        assert(rv(rev@, j) == rv(old_rev, j));
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(ds[k as int].subrange(0, dk@.len() as int) =~= ds[k as int]);
        }
        k = k + 1;
    }
    // Counts, and the items that hold with no dependency.
    let ghost none = Seq::new(n as nat, |q: int| false);
    let mut pend: Vec<usize> = Vec::new();
    let mut done: Vec<bool> = Vec::new();
    let mut work: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == local@.len() == deps@.len(),
            ds == deps_view(deps@),
            deps_wf(n as int, ds),
            none == Seq::new(n as nat, |q: int| false),
            pend@.len() == k && done@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] pend@[q] == unp(ds[q], none),
            forall|q: int| 0 <= q < k ==> #[trigger] done@[q] == (local@[q] && ds[q].len() == 0),
            work@.no_duplicates(),
            forall|t: int| 0 <= t < work@.len() ==> #[trigger] work@[t] < k && done@[work@[t] as int],
            forall|q: int| 0 <= q < k && #[trigger] done@[q] ==> work@.contains(q as usize),
        decreases n - k,
    {
        let c = deps[k].len();
        proof {
            assert(ds[k as int].len() == c);
            assert forall|i: int| 0 <= i < ds[k as int].len() implies 0 <= #[trigger] ds[k as int][i] < none.len()
                && !none[ds[k as int][i]] by {}
            lemma_unp_none(ds[k as int], none);
        }
        pend.push(c);
        let h = local[k] && c == 0;
        done.push(h);
        let ghost w0 = work@;
        if h {
            proof {
                if w0.contains(k) {
                    let t = choose|t: int| 0 <= t < w0.len() && w0[t] == k;
                    assert(w0[t] < k);
                }
                lemma_push_nodup(w0, k);
            }
            work.push(k);
        }
        proof {
            assert forall|q: int| 0 <= q < k + 1 && #[trigger] done@[q] implies work@.contains(q as usize) by {
                if h {
                    lemma_push_contains(w0, k, q as usize);
                }
            }
        }
        k = k + 1;
    }
    let ghost mut proc = none;
    proof {
        let d0 = done@;
        lemma_hlev_len(local@, ds, 0);
        lemma_hlev_len(local@, ds, 1);
        assert(hlev(local@, ds, 1) == hstep(local@, ds, hlev(local@, ds, 0)));
        assert forall|q: int| 0 <= q < n && #[trigger] d0[q] implies hlev(local@, ds, cnt(d0))[q] by {
            lemma_cnt_pos(d0, q);
            lemma_hlev_mono_le(local@, ds, 1, cnt(d0));
            assert(all_in(ds[q], hlev(local@, ds, 0)));
        }
        assert(kahn_inv(local@, ds, rev@, pend@, done@, proc, work@));
    }
    while work.len() > 0
        invariant
            n == local@.len() == deps@.len(),
            ds == deps_view(deps@),
            kahn_inv(local@, ds, rev@, pend@, done@, proc, work@),
        decreases 2 * (n - cnt(done@)) + work@.len(),
    {
        proof {
            lemma_cnt_le(done@);
        }
        let ghost m0 = 2 * (n - cnt(done@)) + work@.len();
        let ghost w0 = work@;
        proof {
            assert(kahn_inv(local@, ds, rev@, pend@, done@, proc, w0));
        }
        let j = match work.pop() {
            Some(j) => j,
            None => {
                return done;
            },
        };
        proof {
            assert(j == w0.last());
            assert(work@ == w0.drop_last());
            assert(w0[w0.len() - 1] == j);
            assert(done@[j as int] && !proc[j as int]);
            lemma_pop_contains(w0, j);
            assert forall|t2: int| 0 <= t2 < work@.len() implies #[trigger] work@[t2] < n && done@[work@[t2] as int]
                && !proc[work@[t2] as int] && work@[t2] != j by {
                assert(work@[t2] == w0[t2]);
                if work@[t2] == j {
                    assert(work@.contains(j));
                }
            }
            assert forall|q: int| 0 <= q < n && #[trigger] done@[q] && !proc[q] && q != j implies work@.contains(q as usize) by {
                assert(w0.contains(q as usize));
                lemma_pop_contains(w0, q as usize);
            }
        }
        let rj = &rev[j];
        let mut t: usize = 0;
        while t < rj.len()
            invariant
                n == local@.len() == deps@.len(),
                ds == deps_view(deps@),
                deps_wf(n as int, ds),
                rev@.len() == n && pend@.len() == n && done@.len() == n && proc.len() == n,
                j < n,
                rj == rev@[j as int],
                t <= rj@.len(),
                forall|j2: int, k2: int| 0 <= j2 < n && 0 <= k2 < n ==> #[trigger] occ(rv(rev@, j2), k2) == occ(ds[k2], j2),
                forall|j2: int, t2: int| 0 <= j2 < n && 0 <= t2 < rev@[j2]@.len() ==> #[trigger] rev@[j2]@[t2] < n,
                forall|q: int| 0 <= q < n ==> #[trigger] pend@[q] + occ(rv(rev@, j as int).subrange(0, t as int), q) == unp(ds[q], proc),
                forall|q: int| 0 <= q < n && #[trigger] done@[q] ==> local@[q],
                forall|q: int| 0 <= q < n && #[trigger] proc[q] ==> done@[q],
                done@[j as int] && !proc[j as int],
                forall|q: int| 0 <= q < n && local@[q] && !#[trigger] done@[q] ==> pend@[q] > 0,
                forall|q: int| 0 <= q < n && #[trigger] done@[q] ==> hlev(local@, ds, cnt(done@))[q],
                work@.no_duplicates(),
                forall|t2: int| 0 <= t2 < work@.len() ==> #[trigger] work@[t2] < n && done@[work@[t2] as int] && !proc[work@[t2] as int] && work@[t2] != j,
                forall|q: int| 0 <= q < n && #[trigger] done@[q] && !proc[q] && q != j ==> work@.contains(q as usize),
                cnt(done@) <= n,
                2 * (n - cnt(done@)) + work@.len() < m0,
            decreases rj@.len() - t,
        {
            let q = rj[t];
            proof {
                let rs = rv(rev@, j as int);
                assert(rs[t as int] == q as int);
                lemma_occ_take(rs, t as int, q as int);
                lemma_occ_prefix_le(rs, t + 1, q as int);
                lemma_occ_le_unp(ds[q as int], proc, j as int);
                assert forall|q2: int| 0 <= q2 < n implies occ(rs.subrange(0, t + 1), q2) == occ(rs.subrange(0, t as int), q2)
                    + if q2 == q as int {
                    1nat
                } else {
                    0nat
                } by {
                    lemma_occ_take(rs, t as int, q2);
                }
            }
            let p = pend[q] - 1;
            pend.set(q, p);
            if p == 0 && local[q] && !done[q] {
                proof {
                    let rs = rv(rev@, j as int);
                    // Every dependency of `q` is processed, or is `j`, which is done.
                    assert(unp(ds[q as int], proc) == occ(ds[q as int], j as int));
                    assert forall|i: int| 0 <= i < ds[q as int].len() implies 0 <= #[trigger] ds[q as int][i] < proc.len() by {}
                    lemma_unp_only(ds[q as int], proc, j as int);
                    assert forall|i: int| 0 <= i < ds[q as int].len() implies done@[#[trigger] ds[q as int][i]] by {}
                    lemma_mark_level(local@, ds, done@, q as int);
                    lemma_cnt_mark(done@, q as int);
                    if work@.contains(q) {
                        let t2 = choose|t2: int| 0 <= t2 < work@.len() && work@[t2] == q;
                        assert(done@[work@[t2] as int]);
                    }
                    lemma_push_nodup(work@, q);
                }
                let ghost w1 = work@;
                done.set(q, true);
                work.push(q);
                proof {
                    assert forall|q2: int| 0 <= q2 < n && #[trigger] done@[q2] && !proc[q2] && q2 != j implies work@.contains(
                        q2 as usize,
                    ) by {
                        lemma_push_contains(w1, q, q2 as usize);
                    }
                    lemma_cnt_le(done@);
                }
            }
            t = t + 1;
        }
        proof {
            let rs = rv(rev@, j as int);
            assert(rs.subrange(0, rj@.len() as int) =~= rs);
            let p2 = proc.update(j as int, true);
            assert forall|q: int| 0 <= q < n implies #[trigger] pend@[q] == unp(ds[q], p2) by {
                lemma_unp_mark(ds[q], proc, j as int);
            }
            proc = p2;
            assert forall|q: int| 0 <= q < n && #[trigger] done@[q] && !proc[q] implies work@.contains(q as usize) by {}
            assert(kahn_inv(local@, ds, rev@, pend@, done@, proc, work@));
        }
    }
    proof {
        // The worklist is empty: done is processed, and nothing more holds.
        let dn = done@;
        assert(proc =~= dn) by {
            assert forall|q: int| 0 <= q < n implies proc[q] == dn[q] by {
                if dn[q] && !proc[q] {
                    assert(work@.contains(q as usize));
                }
            }
        }
        assert forall|q: int| 0 <= q < n && local@[q] && !#[trigger] dn[q] implies unp(ds[q], dn) > 0 by {}
        lemma_complete(local@, ds, dn, n as nat);
        lemma_cnt_le(dn);
        lemma_hlev_mono_le(local@, ds, cnt(dn), n as nat);
        lemma_hlev_len(local@, ds, n as nat);
        assert(dn =~= hlev(local@, ds, n as nat));
    }
    done
}

} // verus!

verus! {

/// The dependencies of an item that does not hold by itself do not matter.
pub proof fn lemma_hlev_deps(local: Seq<bool>, ds: Seq<Seq<int>>, es: Seq<Seq<int>>, d: nat)
    requires
        ds.len() == local.len() && es.len() == local.len(),
        forall|k: int| 0 <= k < local.len() && local[k] ==> #[trigger] ds[k] == es[k],
    ensures
        hlev(local, ds, d) == hlev(local, es, d),
    decreases d,
{
    if d > 0 {
        lemma_hlev_deps(local, ds, es, (d - 1) as nat);
        let prev = hlev(local, ds, (d - 1) as nat);
        assert(hstep(local, ds, prev) =~= hstep(local, es, prev));
    }
}

/// `all_in` of a concatenation.
pub proof fn lemma_all_in_add(a: Seq<int>, b: Seq<int>, p: Seq<bool>)
    ensures
        all_in(a + b, p) == (all_in(a, p) && all_in(b, p)),
{
    let c = a + b;
    if all_in(a, p) && all_in(b, p) {
        assert forall|i: int| 0 <= i < c.len() implies 0 <= #[trigger] c[i] < p.len() && p[c[i]] by {
            if i < a.len() {
                assert(c[i] == a[i]);
            } else {
                assert(c[i] == b[i - a.len()]);
            }
        }
    }
    if all_in(c, p) {
        assert forall|i: int| 0 <= i < a.len() implies 0 <= #[trigger] a[i] < p.len() && p[a[i]] by {
            assert(c[i] == a[i]);
        }
        assert forall|i: int| 0 <= i < b.len() implies 0 <= #[trigger] b[i] < p.len() && p[b[i]] by {
            assert(c[a.len() + i] == b[i]);
        }
    }
}

} // verus!
