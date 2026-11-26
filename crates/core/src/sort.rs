//! A verified merge sort of positions.
//!
//! [`order_by`] puts the positions `0..n` in the order a caller's
//! comparison gives: the result is a permutation of `0..n` in which each
//! position compares `le` the next. The comparison is a closure over
//! positions, so the keys can be anything the caller can compare: integers,
//! byte strings, paths. It must be total (of any two positions, one is `le`
//! the other); it need not be transitive for the result to be sorted
//! neighbour by neighbour.
//!
//! The sort is top-down and stable, takes `n log n` comparisons, and
//! allocates two vectors of `n` positions, once.
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// Each element is `le` the next.
pub open spec fn sorted_by(s: Seq<usize>, le: spec_fn(usize, usize) -> bool) -> bool {
    forall|k: int| 0 <= k < s.len() - 1 ==> le(#[trigger] s[k], s[k + 1])
}

/// Every element is below `n`.
pub open spec fn below(s: Seq<usize>, n: nat) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] < n
}

/// `0, 1, ..., n - 1`.
pub open spec fn upto(n: nat) -> Seq<usize> {
    Seq::new(n, |i: int| i as usize)
}

/// Of any two positions below `n`, one is `le` the other.
pub open spec fn total(le: spec_fn(usize, usize) -> bool, n: nat) -> bool {
    forall|i: usize, j: usize| i < n && j < n ==> #[trigger] le(i, j) || le(j, i)
}

/// `f` can be called on any two positions below `n`, and computes `le`.
pub open spec fn computes<F: Fn(usize, usize) -> bool>(
    f: &F,
    le: spec_fn(usize, usize) -> bool,
    n: nat,
) -> bool {
    &&& forall|i: usize, j: usize| i < n && j < n ==> #[trigger] f.requires((i, j))
    &&& forall|i: usize, j: usize, r: bool| #[trigger] f.ensures((i, j), r) ==> r == le(i, j)
}

proof fn lemma_sorted_push(s: Seq<usize>, x: usize, le: spec_fn(usize, usize) -> bool)
    requires
        sorted_by(s, le),
        s.len() > 0 ==> le(s.last(), x),
    ensures
        sorted_by(s.push(x), le),
{
    let t = s.push(x);
    assert forall|k: int| 0 <= k < t.len() - 1 implies le(#[trigger] t[k], t[k + 1]) by {
        assert(t[k] == s[k]);
        if k + 1 < s.len() {
            assert(t[k + 1] == s[k + 1]);
        }
    }
}

/// The positions `0..n`, ordered by `f`, which computes `le`: a permutation
/// of `0..n` in which each position is `le` the next. Stable: positions
/// that compare `le` both ways keep their order.
pub fn order_by<F: Fn(usize, usize) -> bool>(
    n: usize,
    f: &F,
    Ghost(le): Ghost<spec_fn(usize, usize) -> bool>,
) -> (r: Vec<usize>)
    requires
        computes(f, le, n as nat),
        total(le, n as nat),
    ensures
        r@.len() == n,
        r@.to_multiset() == upto(n as nat).to_multiset(),
        below(r@, n as nat),
        sorted_by(r@, le),
{
    let mut v: Vec<usize> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@ == upto(i as nat),
        decreases n - i,
    {
        v.push(i);
        i += 1;
        proof {
            assert(v@ =~= upto(i as nat));
        }
    }
    let mut t: Vec<usize> = Vec::with_capacity(n);
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    msort(&mut v, &mut t, 0, n, f, Ghost(le), Ghost(n as nat));
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    v
}

/// Sorts `v[lo..hi]`, using `t` as scratch.
fn msort<F: Fn(usize, usize) -> bool>(
    v: &mut Vec<usize>,
    t: &mut Vec<usize>,
    lo: usize,
    hi: usize,
    f: &F,
    Ghost(le): Ghost<spec_fn(usize, usize) -> bool>,
    Ghost(n): Ghost<nat>,
)
    requires
        lo <= hi <= old(v)@.len(),
        below(old(v)@, n),
        computes(f, le, n),
        total(le, n),
    ensures
        final(v)@.len() == old(v)@.len(),
        below(final(v)@, n),
        forall|j: int|
            0 <= j < old(v)@.len() && !(lo <= j < hi) ==> #[trigger] final(v)@[j] == old(v)@[j],
        final(v)@.subrange(lo as int, hi as int).to_multiset() == old(v)@.subrange(
            lo as int,
            hi as int,
        ).to_multiset(),
        sorted_by(final(v)@.subrange(lo as int, hi as int), le),
    decreases hi - lo,
{
    if hi - lo <= 1 {
        return;
    }
    let ghost v0 = v@;
    let mid = lo + (hi - lo) / 2;
    msort(v, t, lo, mid, f, Ghost(le), Ghost(n));
    let ghost v1 = v@;
    msort(v, t, mid, hi, f, Ghost(le), Ghost(n));
    let ghost v2 = v@;
    proof {
        assert(v1.subrange(mid as int, hi as int) =~= v0.subrange(mid as int, hi as int));
        assert(v2.subrange(lo as int, mid as int) =~= v1.subrange(lo as int, mid as int));
    }
    merge(v, t, lo, mid, hi, f, Ghost(le), Ghost(n));
    proof {
        let l0 = v0.subrange(lo as int, mid as int);
        let r0 = v0.subrange(mid as int, hi as int);
        let l2 = v2.subrange(lo as int, mid as int);
        let r2 = v2.subrange(mid as int, hi as int);
        assert(v0.subrange(lo as int, hi as int) =~= l0 + r0);
        assert(v2.subrange(lo as int, hi as int) =~= l2 + r2);
        vstd::seq_lib::lemma_multiset_commutative(l0, r0);
        vstd::seq_lib::lemma_multiset_commutative(l2, r2);
    }
}

/// Merges the sorted runs `v[lo..mid]` and `v[mid..hi]` in place, through
/// `t`.
fn merge<F: Fn(usize, usize) -> bool>(
    v: &mut Vec<usize>,
    t: &mut Vec<usize>,
    lo: usize,
    mid: usize,
    hi: usize,
    f: &F,
    Ghost(le): Ghost<spec_fn(usize, usize) -> bool>,
    Ghost(n): Ghost<nat>,
)
    requires
        lo <= mid <= hi <= old(v)@.len(),
        below(old(v)@, n),
        sorted_by(old(v)@.subrange(lo as int, mid as int), le),
        sorted_by(old(v)@.subrange(mid as int, hi as int), le),
        computes(f, le, n),
        total(le, n),
    ensures
        final(v)@.len() == old(v)@.len(),
        below(final(v)@, n),
        forall|j: int|
            0 <= j < old(v)@.len() && !(lo <= j < hi) ==> #[trigger] final(v)@[j] == old(v)@[j],
        final(v)@.subrange(lo as int, hi as int).to_multiset() == old(v)@.subrange(
            lo as int,
            hi as int,
        ).to_multiset(),
        sorted_by(final(v)@.subrange(lo as int, hi as int), le),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms;

    let ghost v0 = v@;
    let ghost va = v0.subrange(lo as int, mid as int);
    let ghost vb = v0.subrange(mid as int, hi as int);
    t.clear();
    let mut i: usize = lo;
    let mut j: usize = mid;
    proof {
        assert(t@ =~= Seq::<usize>::empty());
        assert(va.take(0) =~= Seq::<usize>::empty());
        assert(vb.take(0) =~= Seq::<usize>::empty());
        assert(t@.to_multiset() =~= va.take(0).to_multiset().add(vb.take(0).to_multiset()));
    }
    while i < mid || j < hi
        invariant
            lo <= i <= mid <= j <= hi <= v@.len(),
            v@ == v0,
            va == v0.subrange(lo as int, mid as int),
            vb == v0.subrange(mid as int, hi as int),
            below(v0, n),
            sorted_by(va, le),
            sorted_by(vb, le),
            computes(f, le, n),
            total(le, n),
            t@.len() == (i - lo) + (j - mid),
            t@.to_multiset() == va.take(i - lo).to_multiset().add(vb.take(j - mid).to_multiset()),
            below(t@, n),
            sorted_by(t@, le),
            t@.len() > 0 && i < mid ==> le(t@.last(), v0[i as int]),
            t@.len() > 0 && j < hi ==> le(t@.last(), v0[j as int]),
        decreases (mid - i) + (hi - j),
    {
        let ghost t0 = t@;
        let take_a = if i < mid && j < hi {
            let x = v[i];
            let y = v[j];
            let c = f(x, y);
            proof {
                if !c {
                    assert(le(x, y) || le(y, x));
                }
            }
            c
        } else {
            i < mid
        };
        if take_a {
            let x = v[i];
            t.push(x);
            proof {
                let k = i - lo;
                assert(va[k] == x);
                assert(va.take(k + 1) =~= va.take(k).push(x));
                t0.to_multiset_ensures();
                va.take(k).to_multiset_ensures();
                lemma_sorted_push(t0, x, le);
                assert(t@.to_multiset() =~= va.take(k + 1).to_multiset().add(
                    vb.take(j - mid).to_multiset(),
                ));
                if i + 1 < mid {
                    assert(va[k + 1] == v0[i + 1]);
                    assert(le(va[k], va[k + 1]));
                }
            }
            i += 1;
        } else {
            let y = v[j];
            t.push(y);
            proof {
                let k = j - mid;
                assert(vb[k] == y);
                assert(vb.take(k + 1) =~= vb.take(k).push(y));
                t0.to_multiset_ensures();
                vb.take(k).to_multiset_ensures();
                lemma_sorted_push(t0, y, le);
                assert(t@.to_multiset() =~= va.take(i - lo).to_multiset().add(
                    vb.take(k + 1).to_multiset(),
                ));
                if j + 1 < hi {
                    assert(vb[k + 1] == v0[j + 1]);
                    assert(le(vb[k], vb[k + 1]));
                }
            }
            j += 1;
        }
    }
    proof {
        assert(va.take(i - lo) =~= va);
        assert(vb.take(j - mid) =~= vb);
        assert(v0.subrange(lo as int, hi as int) =~= va + vb);
        vstd::seq_lib::lemma_multiset_commutative(va, vb);
    }
    let m = t.len();
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            m == t@.len(),
            m == hi - lo,
            hi <= v0.len(),
            v@.len() == v0.len(),
            below(v0, n),
            below(t@, n),
            forall|j: int| 0 <= j < v0.len() && !(lo <= j < lo + k) ==> #[trigger] v@[j] == v0[j],
            forall|j: int| 0 <= j < k ==> #[trigger] v@[lo + j] == t@[j],
        decreases m - k,
    {
        v.set(lo + k, t[k]);
        k += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < m implies v@.subrange(lo as int, hi as int)[j] == t@[j] by {
            assert(v@[lo + j] == t@[j]);
        }
        assert(v@.subrange(lo as int, hi as int) =~= t@);
        assert forall|j: int| 0 <= j < v@.len() implies #[trigger] v@[j] < n by {
            if lo <= j < hi {
                assert(v@[lo + (j - lo)] == t@[j - lo]);
            } else {
                assert(v@[j] == v0[j]);
            }
        }
    }
}

} // verus!
