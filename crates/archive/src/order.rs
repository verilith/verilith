//! An order on paths, used by the planner to find duplicates and symbolic
//! link prefixes in one pass over a sorted list. Nothing here is trusted:
//! the order is a proof device, and the safety theorems do not mention it.
use crate::policy::*;
use vstd::prelude::*;

verus! {

/// Bytes `a` sort before `b`, comparing from index `i`.
pub open spec fn blt_from(a: Seq<u8>, b: Seq<u8>, i: int) -> bool
    decreases a.len() - i,
{
    if i < 0 || i >= b.len() {
        false
    } else if i >= a.len() {
        true
    } else if a[i] < b[i] {
        true
    } else if a[i] > b[i] {
        false
    } else {
        blt_from(a, b, i + 1)
    }
}

pub open spec fn blt(a: Seq<u8>, b: Seq<u8>) -> bool {
    blt_from(a, b, 0)
}

/// Path `p` sorts before `q`, comparing components from index `i`.
pub open spec fn plt_from(p: Path, q: Path, i: int) -> bool
    decreases p.len() - i,
{
    if i < 0 || i >= q.len() {
        false
    } else if i >= p.len() {
        true
    } else if blt(p[i], q[i]) {
        true
    } else if p[i] == q[i] {
        plt_from(p, q, i + 1)
    } else {
        false
    }
}

pub open spec fn plt(p: Path, q: Path) -> bool {
    plt_from(p, q, 0)
}

pub proof fn lemma_blt_irrefl(a: Seq<u8>, i: int)
    requires
        0 <= i,
    ensures
        !blt_from(a, a, i),
    decreases a.len() - i,
{
    if i < a.len() {
        lemma_blt_irrefl(a, i + 1);
    }
}

pub proof fn lemma_blt_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, i: int)
    requires
        0 <= i,
        blt_from(a, b, i),
        blt_from(b, c, i),
    ensures
        blt_from(a, c, i),
    decreases a.len() - i,
{
    if i < a.len() && a[i] == b[i] && b[i] == c[i] {
        lemma_blt_trans(a, b, c, i + 1);
    }
}

pub proof fn lemma_blt_asym(a: Seq<u8>, b: Seq<u8>)
    ensures
        !(blt(a, b) && blt(b, a)),
{
    if blt(a, b) && blt(b, a) {
        lemma_blt_trans(a, b, a, 0);
        lemma_blt_irrefl(a, 0);
    }
}

pub proof fn lemma_plt_irrefl(p: Path, i: int)
    requires
        0 <= i,
    ensures
        !plt_from(p, p, i),
    decreases p.len() - i,
{
    if i < p.len() {
        lemma_blt_irrefl(p[i], 0);
        lemma_plt_irrefl(p, i + 1);
    }
}

pub proof fn lemma_plt_trans(p: Path, q: Path, r: Path, i: int)
    requires
        0 <= i,
        plt_from(p, q, i),
        plt_from(q, r, i),
    ensures
        plt_from(p, r, i),
    decreases p.len() - i,
{
    if i < p.len() {
        if blt(p[i], q[i]) && blt(q[i], r[i]) {
            lemma_blt_trans(p[i], q[i], r[i], 0);
        } else if p[i] == q[i] && q[i] == r[i] {
            lemma_plt_trans(p, q, r, i + 1);
        }
    }
}

/// `q` is the first `q.len()` components of `p`.
pub open spec fn is_prefix(q: Path, p: Path) -> bool {
    q.len() <= p.len() && forall|k: int| 0 <= k < q.len() ==> q[k] == p[k]
}

/// A proper prefix sorts first.
pub proof fn lemma_prefix_lt(q: Path, p: Path, i: int)
    requires
        is_prefix(q, p),
        q.len() < p.len(),
        0 <= i <= q.len(),
    ensures
        plt_from(q, p, i),
    decreases q.len() - i,
{
    if i < q.len() {
        lemma_blt_irrefl(q[i], 0);
        lemma_prefix_lt(q, p, i + 1);
    }
}

/// Everything sorted between a path and one of its extensions is an
/// extension too.
pub proof fn lemma_between(q: Path, r: Path, p: Path, i: int)
    requires
        is_prefix(q, p),
        0 <= i <= q.len(),
        i <= r.len(),
        forall|k: int| 0 <= k < i ==> q[k] == r[k],
        q == r || plt_from(q, r, i),
        r == p || plt_from(r, p, i),
    ensures
        is_prefix(q, r),
    decreases q.len() - i,
{
    if q == r || r == p {
    } else if i < q.len() {
        lemma_blt_asym(q[i], r[i]);
        lemma_blt_irrefl(q[i], 0);
        assert(q[i] == p[i]);
        assert(q[i] == r[i]);
        lemma_between(q, r, p, i + 1);
    }
}

/// In a list sorted by adjacent pairs, earlier sorts before later.
pub proof fn lemma_sorted(ps: Seq<Path>, a: int, c: int)
    requires
        forall|k: int| 0 <= k < ps.len() - 1 ==> plt(#[trigger] ps[k], ps[k + 1]),
        0 <= a < c < ps.len(),
    ensures
        plt(ps[a], ps[c]),
    decreases c - a,
{
    if a + 1 < c {
        lemma_sorted(ps, a + 1, c);
        assert(plt(ps[a], ps[a + 1]));
        lemma_plt_trans(ps[a], ps[a + 1], ps[c], 0);
    }
}

} // verus!
