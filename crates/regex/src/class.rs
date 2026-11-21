//! Sets of code points as sorted ranges.
use crate::data::*;
use vstd::prelude::*;

verus! {

pub struct Class {
    /// Sorted; `lo <= hi`; a gap of at least one code point between ranges.
    pub r: Vec<(u32, u32)>,
}

/// The ranges are in increasing order, do not overlap, and hold only
/// code points.
pub open spec fn wf_ranges(r: Seq<(u32, u32)>) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < r.len() ==> (#[trigger] r[a]).1 < (#[trigger] r[b]).0
    &&& forall|a: int| 0 <= a < r.len() ==> (#[trigger] r[a]).0 <= r[a].1 <= MAXCP
}

/// Replacing the ranges `j0..j1` by one range that covers them and
/// `lo..=hi` adds exactly `lo..=hi`.
proof fn lemma_merge(rr: Seq<(u32, u32)>, o: Seq<(u32, u32)>, lo: u32, hi: u32, nlo: u32, nhi: u32, j0: int, j1: int)
    requires
        wf_ranges(rr),
        0 <= j0 <= j1 <= rr.len(),
        o == rr.subrange(0, j0).push((nlo, nhi)) + rr.subrange(j1, rr.len() as int),
        nlo <= lo <= hi <= nhi <= MAXCP,
        forall|k: int| 0 <= k < j0 ==> (#[trigger] rr[k]).1 < nlo,
        forall|k: int| j1 <= k < rr.len() ==> (#[trigger] rr[k]).0 > nhi,
        forall|c: u32|
            #[trigger] inr(c, nlo, nhi) <==> (lo <= c <= hi || exists|k: int|
                j0 <= k < j1 && (#[trigger] rr[k]).0 <= c <= rr[k].1),
    ensures
        wf_ranges(o),
        cs_ranges(o) == cs_union(cs_ranges(rr), cs_range(lo, hi)),
{
    let n = rr.len() as int;
    assert(o.len() == j0 + 1 + (n - j1));
    assert forall|k: int| 0 <= k < o.len() implies #[trigger] o[k] == (if k < j0 {
        rr[k]
    } else if k == j0 {
        (nlo, nhi)
    } else {
        rr[k - j0 - 1 + j1]
    }) by {}
    assert forall|a: int, b: int| 0 <= a < b < o.len() implies (#[trigger] o[a]).1 < (#[trigger] o[b]).0 by {
        if b < j0 {
            assert(rr[a].1 < rr[b].0);
        } else if b == j0 {
            assert(rr[a].1 < nlo);
        } else if a < j0 {
            assert(rr[a].1 < rr[b - j0 - 1 + j1].0);
        } else if a == j0 {
            assert(rr[b - j0 - 1 + j1].0 > nhi);
        } else {
            assert(rr[a - j0 - 1 + j1].1 < rr[b - j0 - 1 + j1].0);
        }
    }
    assert forall|a: int| 0 <= a < o.len() implies (#[trigger] o[a]).0 <= o[a].1 <= MAXCP by {
        if a < j0 {
            assert(rr[a].0 <= rr[a].1);
        } else if a > j0 {
            assert(rr[a - j0 - 1 + j1].0 <= rr[a - j0 - 1 + j1].1);
        }
    }
    let want = cs_union(cs_ranges(rr), cs_range(lo, hi));
    assert forall|c: u32| cs_ranges(o).contains(c) == want.contains(c) by {
        assert(inr(c, nlo, nhi) == (nlo <= c <= nhi));
        if cs_ranges(o).contains(c) {
            let m = choose|m: int| 0 <= m < o.len() && (#[trigger] o[m]).0 <= c <= o[m].1;
            if m < j0 {
                assert(rr[m].0 <= c <= rr[m].1);
            } else if m == j0 {
                if !(lo <= c <= hi) {
                    let k = choose|k: int| j0 <= k < j1 && (#[trigger] rr[k]).0 <= c <= rr[k].1;
                    assert(rr[k].0 <= c <= rr[k].1);
                }
            } else {
                assert(rr[m - j0 - 1 + j1].0 <= c <= rr[m - j0 - 1 + j1].1);
            }
        }
        if want.contains(c) {
            if lo <= c <= hi {
                assert(o[j0].0 <= c <= o[j0].1);
            } else {
                let k = choose|k: int| 0 <= k < rr.len() && (#[trigger] rr[k]).0 <= c <= rr[k].1;
                if k < j0 {
                    assert(o[k].0 <= c <= o[k].1);
                } else if k < j1 {
                    assert(nlo <= c <= nhi);
                    assert(o[j0].0 <= c <= o[j0].1);
                } else {
                    assert(o[k - j1 + j0 + 1].0 <= c <= o[k - j1 + j0 + 1].1);
                }
            }
        }
    }
    assert(cs_ranges(o) =~= want);
}

/// `lo <= c <= hi`.
pub open spec fn inr(c: u32, lo: u32, hi: u32) -> bool {
    lo <= c <= hi
}

impl Class {
    /// The ranges are in increasing order and do not overlap.
    pub open spec fn wf(&self) -> bool {
        wf_ranges(self.r@)
    }

    /// The code points in the class.
    pub open spec fn set(&self) -> ISet<u32> {
        cs_ranges(self.r@)
    }

    pub fn contains(&self, c: u32) -> (res: bool)
        requires
            self.wf(),
        ensures
            res == self.set().contains(c),
    {
        self.contains_c(c).0
    }

    /// `contains`, with the number of loop iterations it took.
    pub fn contains_c(&self, c: u32) -> (res: (bool, Ghost<nat>))
        requires
            self.wf(),
        ensures
            res.0 == self.set().contains(c),
            res.1@ <= 64,
    {
        let mut lo = 0usize;
        let mut hi = self.r.len();
        let ghost len = self.r@.len() as int;
        let ghost mut it: nat = 0;
        proof {
            vstd::arithmetic::power2::lemma2_to64();
        }
        while lo < hi
            invariant
                self.wf(),
                lo <= hi <= self.r@.len(),
                len == self.r@.len(),
                len <= usize::MAX,
                it <= 64,
                (hi - lo) * vstd::arithmetic::power2::pow2(it) <= len,
                forall|k: int| 0 <= k < lo ==> (#[trigger] self.r@[k]).1 < c,
                forall|k: int| hi <= k < self.r@.len() ==> (#[trigger] self.r@[k]).1 >= c,
            decreases hi - lo,
        {
            let m = lo + (hi - lo) / 2;
            let ghost w = hi - lo;
            let ghost lo0 = lo;
            let ghost hi0 = hi;
            if self.r[m].1 < c {
                assert forall|k: int| 0 <= k < m + 1 implies (#[trigger] self.r@[k]).1 < c by {
                    if k < m {
                        assert(self.r@[k].1 < self.r@[m as int].0);
                    }
                }
                lo = m + 1;
            } else {
                assert forall|k: int| m <= k < self.r@.len() implies (#[trigger] self.r@[k]).1 >= c by {
                    if k > m {
                        assert(self.r@[m as int].1 < self.r@[k].0);
                    }
                }
                hi = m;
            }
            proof {
                use vstd::arithmetic::power2::*;
                let w2 = hi - lo;
                let pw = pow2(it) as int;
                assert(2 * w2 <= w);
                lemma_pow2_unfold(it + 1);
                lemma_pow2_pos(it);
                assert(pow2(it + 1) == 2 * pw);
                assert(w2 * (2 * pw) <= w * pw) by (nonlinear_arith)
                    requires
                        2 * w2 <= w,
                        pw > 0,
                        w2 >= 0,
                ;
                assert(pw <= w * pw) by (nonlinear_arith)
                    requires
                        w >= 1,
                        pw > 0,
                ;
                if it >= 64 {
                    lemma2_to64();
                    if it > 64 {
                        lemma_pow2_strictly_increases(64, it);
                    }
                    assert(false);
                }
                it = it + 1;
            }
        }
        let res = lo < self.r.len() && self.r[lo].0 <= c;
        proof {
            if res {
                assert(self.r@[lo as int].0 <= c <= self.r@[lo as int].1);
            } else if self.set().contains(c) {
                let k = choose|k: int| 0 <= k < self.r@.len() && (#[trigger] self.r@[k]).0 <= c <= self.r@[k].1;
                if k > lo {
                    assert(self.r@[lo as int].1 < self.r@[k].0);
                }
            }
        }
        (res, Ghost(it))
    }

    pub fn new() -> (r: Class)
        ensures
            r.wf(),
            r.set() == ISet::<u32>::empty(),
            r.r@.len() == 0,
    {
        let r = Class { r: Vec::new() };
        assert(r.set() =~= ISet::<u32>::empty());
        r
    }

    pub fn dup(&self) -> (r: Class)
        ensures
            r.r@ == self.r@,
    {
        let mut out: Vec<(u32, u32)> = Vec::new();
        let n = self.r.len();
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == self.r@.len(),
                out@ == self.r@.subrange(0, i as int),
            decreases n - i,
        {
            out.push(self.r[i]);
            assert(self.r@.subrange(0, i + 1) =~= self.r@.subrange(0, i as int).push(self.r@[i as int]));
            i += 1;
        }
        assert(self.r@.subrange(0, n as int) =~= self.r@);
        Class { r: out }
    }

    /// Adds `lo..=hi`.
    pub fn add(&mut self, lo: u32, hi: u32)
        requires
            old(self).wf(),
            hi <= MAXCP,
        ensures
            final(self).wf(),
            final(self).set() == cs_union(old(self).set(), cs_range(lo, hi)),
    {
        let ghost s0 = self.set();
        if lo > hi {
            assert(s0 =~= cs_union(s0, cs_range(lo, hi)));
            return ;
        }
        let ghost rr = self.r@;
        let n = self.r.len();
        let mut out: Vec<(u32, u32)> = Vec::new();
        let mut i = 0;
        // Ranges entirely before `lo`, and not touching it.
        while i < n && self.r[i].1 < lo && lo - self.r[i].1 > 1
            invariant
                i <= n,
                n == rr.len(),
                self.r@ == rr,
                old(self).wf(),
                rr == old(self).r@,
                out@ == rr.subrange(0, i as int),
                forall|k: int| 0 <= k < i ==> (#[trigger] rr[k]).1 + 1 < lo,
            decreases n - i,
        {
            out.push(self.r[i]);
            assert(rr.subrange(0, i + 1) =~= rr.subrange(0, i as int).push(rr[i as int]));
            i += 1;
        }
        let ghost j0 = i as int;
        let mut nlo = lo;
        let mut nhi = hi;
        assert forall|k: int| j0 <= k < n implies (#[trigger] rr[k]).1 + 1 >= lo by {
            if k > j0 {
                assert(rr[j0].1 < rr[k].0);
            }
        }
        // Ranges overlapping or touching.
        while i < n && (self.r[i].0 <= nhi || self.r[i].0 - nhi == 1)
            invariant
                j0 <= i <= n,
                n == rr.len(),
                self.r@ == rr,
                old(self).wf(),
                rr == old(self).r@,
                out@ == rr.subrange(0, j0),
                nlo <= lo <= hi <= nhi <= MAXCP,
                forall|k: int| j0 <= k < n ==> (#[trigger] rr[k]).1 + 1 >= lo,
                forall|k: int| 0 <= k < j0 ==> (#[trigger] rr[k]).1 < nlo,
                forall|c: u32|
                    #[trigger] inr(c, nlo, nhi) <==> (lo <= c <= hi || exists|k: int|
                        j0 <= k < i && (#[trigger] rr[k]).0 <= c <= rr[k].1),
            decreases n - i,
        {
            let ghost nlo0 = nlo;
            let ghost nhi0 = nhi;
            let a = self.r[i].0;
            let b = self.r[i].1;
            if a < nlo {
                nlo = a;
            }
            if b > nhi {
                nhi = b;
            }
            assert forall|k: int| 0 <= k < j0 implies (#[trigger] rr[k]).1 < nlo by {
                assert(rr[k].1 < rr[i as int].0);
            }
            assert forall|c: u32|
                #[trigger] inr(c, nlo, nhi) <==> (lo <= c <= hi || exists|k: int|
                    j0 <= k < i + 1 && (#[trigger] rr[k]).0 <= c <= rr[k].1) by {
                assert(inr(c, nlo0, nhi0) == (nlo0 <= c <= nhi0));
                if nlo <= c <= nhi {
                    if nlo0 <= c <= nhi0 {
                        if !(lo <= c <= hi) {
                            let k = choose|k: int| j0 <= k < i && (#[trigger] rr[k]).0 <= c <= rr[k].1;
                            assert(j0 <= k < i + 1 && rr[k].0 <= c <= rr[k].1);
                        }
                    } else {
                        assert(rr[i as int].0 <= c <= rr[i as int].1);
                    }
                }
                if exists|k: int| j0 <= k < i + 1 && (#[trigger] rr[k]).0 <= c <= rr[k].1 {
                    let k = choose|k: int| j0 <= k < i + 1 && (#[trigger] rr[k]).0 <= c <= rr[k].1;
                    if k < i {
                        assert(nlo0 <= c <= nhi0);
                    }
                }
            }
            i += 1;
        }
        let ghost j1 = i as int;
        assert forall|k: int| j1 <= k < n implies (#[trigger] rr[k]).0 > nhi by {
            if k > j1 {
                assert(rr[j1].1 < rr[k].0);
            }
        }
        out.push((nlo, nhi));
        while i < n
            invariant
                0 <= j0 <= j1 <= i <= n,
                n == rr.len(),
                self.r@ == rr,
                out@ == rr.subrange(0, j0).push((nlo, nhi)) + rr.subrange(j1, i as int),
            decreases n - i,
        {
            out.push(self.r[i]);
            assert(rr.subrange(j1, i + 1) =~= rr.subrange(j1, i as int).push(rr[i as int]));
            assert(out@ =~= rr.subrange(0, j0).push((nlo, nhi)) + rr.subrange(j1, i + 1));
            i += 1;
        }
        assert(rr.subrange(j1, n as int) =~= rr.subrange(j1, i as int));
        self.r = out;
        proof {
            lemma_merge(rr, self.r@, lo, hi, nlo, nhi, j0, j1);
        }
    }

    /// Adds the ranges `rs`.
    pub fn add_ranges(&mut self, rs: &[(u32, u32)])
        requires
            old(self).wf(),
            forall|k: int| 0 <= k < rs@.len() ==> (#[trigger] rs@[k]).1 <= MAXCP,
        ensures
            final(self).wf(),
            final(self).set() == cs_union(old(self).set(), cs_ranges(rs@)),
    {
        let ghost s0 = self.set();
        let n = rs.len();
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == rs@.len(),
                forall|k: int| 0 <= k < rs@.len() ==> (#[trigger] rs@[k]).1 <= MAXCP,
                self.wf(),
                self.set() == cs_union(s0, cs_ranges(rs@.subrange(0, i as int))),
            decreases n - i,
        {
            let ghost s1 = self.set();
            let ghost pre = rs@.subrange(0, i as int);
            let ghost nxt = rs@.subrange(0, i + 1);
            self.add(rs[i].0, rs[i].1);
            proof {
                let want = cs_union(s0, cs_ranges(nxt));
                assert forall|c: u32| self.set().contains(c) == want.contains(c) by {
                    if cs_ranges(nxt).contains(c) {
                        let k = choose|k: int| 0 <= k < nxt.len() && (#[trigger] nxt[k]).0 <= c <= nxt[k].1;
                        if k < i {
                            assert(pre[k].0 <= c <= pre[k].1);
                        }
                    }
                    if cs_ranges(pre).contains(c) {
                        let k = choose|k: int| 0 <= k < pre.len() && (#[trigger] pre[k]).0 <= c <= pre[k].1;
                        assert(nxt[k].0 <= c <= nxt[k].1);
                    }
                    if rs@[i as int].0 <= c <= rs@[i as int].1 {
                        assert(nxt[i as int].0 <= c <= nxt[i as int].1);
                    }
                }
                assert(self.set() =~= want);
            }
            i += 1;
        }
        assert(rs@.subrange(0, n as int) =~= rs@);
    }

    /// Adds every code point of `o`.
    pub fn add_class(&mut self, o: &Class)
        requires
            old(self).wf(),
            o.wf(),
        ensures
            final(self).wf(),
            final(self).set() == cs_union(old(self).set(), o.set()),
    {
        let ghost s0 = self.set();
        let n = o.r.len();
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == o.r@.len(),
                o.wf(),
                self.wf(),
                forall|c: u32|
                    #[trigger] self.set().contains(c) <==> (s0.contains(c) || exists|k: int|
                        0 <= k < i && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1),
            decreases n - i,
        {
            let ghost s1 = self.set();
            self.add(o.r[i].0, o.r[i].1);
            assert forall|c: u32|
                #[trigger] self.set().contains(c) <==> (s0.contains(c) || exists|k: int|
                    0 <= k < i + 1 && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1) by {
                assert(s1.contains(c) <==> (s0.contains(c) || exists|k: int|
                    0 <= k < i && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1));
                if s1.contains(c) && !s0.contains(c) {
                    let k = choose|k: int| 0 <= k < i && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1;
                    assert(0 <= k < i + 1 && o.r@[k].0 <= c <= o.r@[k].1);
                }
                if exists|k: int| 0 <= k < i + 1 && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1 {
                    let k = choose|k: int| 0 <= k < i + 1 && (#[trigger] o.r@[k]).0 <= c <= o.r@[k].1;
                    if k < i {
                        assert(s1.contains(c));
                    }
                }
                if o.r@[i as int].0 <= c <= o.r@[i as int].1 {
                    assert(0 <= i < i + 1 && o.r@[i as int].0 <= c <= o.r@[i as int].1);
                }
            }
            i += 1;
        }
        assert forall|c: u32| self.set().contains(c) == cs_union(s0, o.set()).contains(c) by {}
        assert(self.set() =~= cs_union(s0, o.set()));
    }

    /// The code points not in the class.
    pub fn negate(&self) -> (out: Class)
        requires
            self.wf(),
        ensures
            out.wf(),
            out.set() == cs_neg(self.set()),
    {
        let mut out: Vec<(u32, u32)> = Vec::new();
        let ghost rr = self.r@;
        let n = self.r.len();
        let mut next: u32 = 0;
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == rr.len(),
                rr == self.r@,
                self.wf(),
                next <= MAXCP + 1,
                forall|k: int| 0 <= k < i ==> (#[trigger] rr[k]).1 < next,
                forall|k: int| i <= k < n ==> (#[trigger] rr[k]).0 >= next,
                forall|k: int| 0 <= k < out@.len() ==> (#[trigger] out@[k]).0 <= out@[k].1 < next,
                forall|a: int, b: int| 0 <= a < b < out@.len() ==> (#[trigger] out@[a]).1 < (#[trigger] out@[b]).0,
                forall|c: u32|
                    #[trigger] cs_ranges(out@).contains(c) <==> (c < next && forall|k: int|
                        0 <= k < i ==> !((#[trigger] rr[k]).0 <= c <= rr[k].1)),
            decreases n - i,
        {
            let a = self.r[i].0;
            let b = self.r[i].1;
            let ghost o0 = out@;
            let ghost next0 = next;
            if next < a {
                out.push((next, a - 1));
            }
            next = b + 1;
            proof {
                let o1 = out@;
                assert forall|k: int| i + 1 <= k < n implies (#[trigger] rr[k]).0 >= next by {
                    assert(rr[i as int].1 < rr[k].0);
                }
                assert forall|c: u32|
                    #[trigger] cs_ranges(o1).contains(c) <==> (c < next && forall|k: int|
                        0 <= k < i + 1 ==> !((#[trigger] rr[k]).0 <= c <= rr[k].1)) by {
                    let lhs0 = cs_ranges(o0).contains(c);
                    let rhs0 = c < next0 && forall|k: int| 0 <= k < i ==> !((#[trigger] rr[k]).0 <= c <= rr[k].1);
                    assert(lhs0 <==> rhs0);
                    if exists|k: int| 0 <= k < o1.len() && (#[trigger] o1[k]).0 <= c <= o1[k].1 {
                        let k = choose|k: int| 0 <= k < o1.len() && (#[trigger] o1[k]).0 <= c <= o1[k].1;
                        if k < o0.len() {
                            assert(o0[k].0 <= c <= o0[k].1);
                            assert(lhs0);
                            assert(c < next0);
                        } else {
                            assert forall|kk: int| 0 <= kk < i implies !((#[trigger] rr[kk]).0 <= c <= rr[kk].1) by {}
                        }
                    }
                    if c < next && forall|k: int| 0 <= k < i + 1 ==> !((#[trigger] rr[k]).0 <= c <= rr[k].1) {
                        assert(!(rr[i as int].0 <= c <= rr[i as int].1));
                        if c < next0 {
                            assert(rhs0);
                            let k = choose|k: int| 0 <= k < o0.len() && (#[trigger] o0[k]).0 <= c <= o0[k].1;
                            assert(o1[k].0 <= c <= o1[k].1);
                        } else {
                            assert(next0 <= c < a);
                            assert(o1[o1.len() - 1].0 <= c <= o1[o1.len() - 1].1);
                        }
                    }
                }
            }
            i += 1;
        }
        let ghost o0 = out@;
        if next <= MAXCP {
            out.push((next, MAXCP));
        }
        let res = Class { r: out };
        proof {
            let o1 = res.r@;
            let want = cs_neg(self.set());
            assert forall|c: u32| res.set().contains(c) == want.contains(c) by {
                let lhs0 = cs_ranges(o0).contains(c);
                let rhs0 = c < next && forall|k: int| 0 <= k < n ==> !((#[trigger] rr[k]).0 <= c <= rr[k].1);
                assert(lhs0 <==> rhs0);
                if res.set().contains(c) {
                    let k = choose|k: int| 0 <= k < o1.len() && (#[trigger] o1[k]).0 <= c <= o1[k].1;
                    if k < o0.len() {
                        assert(o0[k].0 <= c <= o0[k].1);
                        assert(lhs0);
                    } else {
                        assert forall|kk: int| 0 <= kk < n implies !((#[trigger] rr[kk]).0 <= c <= rr[kk].1) by {}
                    }
                    if self.set().contains(c) {
                        let kk = choose|kk: int| 0 <= kk < rr.len() && (#[trigger] rr[kk]).0 <= c <= rr[kk].1;
                        assert(false);
                    }
                }
                if want.contains(c) {
                    assert forall|kk: int| 0 <= kk < n implies !((#[trigger] rr[kk]).0 <= c <= rr[kk].1) by {
                        if rr[kk].0 <= c <= rr[kk].1 {
                            assert(self.set().contains(c));
                        }
                    }
                    if c < next {
                        assert(rhs0);
                        let k = choose|k: int| 0 <= k < o0.len() && (#[trigger] o0[k]).0 <= c <= o0[k].1;
                        assert(o1[k].0 <= c <= o1[k].1);
                    } else {
                        assert(o1[o1.len() - 1].0 <= c <= o1[o1.len() - 1].1);
                    }
                }
            }
            assert(res.set() =~= want);
        }
        res
    }

    /// The class with every code point that case-folds like a member.
    pub fn fold(&self) -> (out: Class)
        requires
            self.wf(),
        ensures
            out.wf(),
            out.set() == cs_fold(self.set()),
    {
        let mut out = self.dup();
        let ghost s0 = self.set();
        assert(out.set() =~= s0);
        let mut k: usize = 0;
        while k < NFOLD
            invariant
                k <= NFOLD,
                self.wf(),
                s0 == self.set(),
                out.wf(),
                forall|c: u32|
                    #[trigger] out.set().contains(c) <==> (s0.contains(c) || (c <= MAXCP && exists|j: int|
                        j < k && #[trigger] folds_to(s0, j, c))),
            decreases NFOLD - k,
        {
            let ghost o0 = out.set();
            let a = fold_a_at(k);
            let b = fold_b_at(k);
            let hit = b <= MAXCP && self.contains(a);
            if hit {
                out.add(b, b);
            }
            assert forall|c: u32|
                #[trigger] out.set().contains(c) <==> (s0.contains(c) || (c <= MAXCP && exists|j: int|
                    j < k + 1 && #[trigger] folds_to(s0, j, c))) by {
                assert(o0.contains(c) <==> (s0.contains(c) || (c <= MAXCP && exists|j: int|
                    j < k && #[trigger] folds_to(s0, j, c))));
                if o0.contains(c) && !s0.contains(c) {
                    let j = choose|j: int| j < k && #[trigger] folds_to(s0, j, c);
                    assert(j < k + 1 && folds_to(s0, j, c));
                }
                if hit && c == b {
                    assert(folds_to(s0, k as int, c));
                }
                if c <= MAXCP && exists|j: int| j < k + 1 && #[trigger] folds_to(s0, j, c) {
                    let j = choose|j: int| j < k + 1 && #[trigger] folds_to(s0, j, c);
                    if j < k {
                        assert(o0.contains(c));
                    }
                }
            }
            k += 1;
        }
        assert forall|c: u32| out.set().contains(c) == cs_fold(s0).contains(c) by {
            if cs_fold(s0).contains(c) && !s0.contains(c) {
                let j = choose|j: int| #[trigger] folds_to(s0, j, c);
                assert(j < k && folds_to(s0, j, c));
            }
        }
        assert(out.set() =~= cs_fold(s0));
        out
    }

    /// Unicode group `g` of the tables.
    pub fn group(g: usize) -> (out: Class)
        requires
            g < NGROUPS,
        ensures
            out.wf(),
            out.set() == cs_group(g as int),
    {
        let mut out = Class::new();
        let lo = group_off_at(g) as usize;
        let hi0 = group_off_at(g + 1) as usize;
        let hi = if hi0 < NRANGES {
            hi0
        } else {
            NRANGES
        };
        let mut i = lo;
        while i < hi
            invariant
                lo <= i,
                hi <= NRANGES,
                hi <= hi0,
                lo == group_off(g as int),
                hi0 == group_off(g + 1),
                hi == hi0 || hi == NRANGES,
                out.wf(),
                forall|c: u32|
                    out.set().contains(c) <==> exists|j: int| j < i && #[trigger] in_group_range(g as int, j, c),
            decreases hi - i,
        {
            let ghost o0 = out.set();
            let a = group_lo_at(i);
            let b = group_hi_at(i);
            if b <= MAXCP {
                out.add(a, b);
            }
            assert forall|c: u32|
                out.set().contains(c) <==> exists|j: int| j < i + 1 && #[trigger] in_group_range(g as int, j, c) by {
                if o0.contains(c) {
                    let j = choose|j: int| j < i && #[trigger] in_group_range(g as int, j, c);
                    assert(j < i + 1 && in_group_range(g as int, j, c));
                }
                if b <= MAXCP && a <= c <= b {
                    assert(in_group_range(g as int, i as int, c));
                }
                if exists|j: int| j < i + 1 && #[trigger] in_group_range(g as int, j, c) {
                    let j = choose|j: int| j < i + 1 && #[trigger] in_group_range(g as int, j, c);
                    if j < i {
                        assert(o0.contains(c));
                    }
                }
            }
            i += 1;
        }
        proof {
            let want = cs_group(g as int);
            assert forall|c: u32| out.set().contains(c) == want.contains(c) by {
                if want.contains(c) {
                    let j = choose|j: int| #[trigger] in_group_range(g as int, j, c);
                    assert(j < i && in_group_range(g as int, j, c));
                }
            }
            assert(out.set() =~= want);
        }
        out
    }
}

/// The index of the Unicode group named `name`.
pub fn find_group(name: &[u8]) -> (r: Option<usize>)
    ensures
        match find_group_from(name@, 0) {
            Some(g) => r == Some(g as usize) && 0 <= g < NGROUPS,
            None => r is None,
        },
{
    let mut g: usize = 0;
    while g < NGROUPS
        invariant
            g <= NGROUPS,
            find_group_from(name@, 0) == find_group_from(name@, g as int),
        decreases NGROUPS - g,
    {
        let a = name_off_at(g) as usize;
        let b = name_off_at(g + 1) as usize;
        if a <= b && b <= NNAMEBYTES && b - a == name.len() {
            let mut k = 0;
            while k < name.len() && name_byte_at(a + k) == name[k]
                invariant
                    k <= name@.len(),
                    b - a == name@.len(),
                    a <= b <= NNAMEBYTES,
                    forall|j: int| 0 <= j < k ==> name_byte(a + j) == name@[j],
                decreases name@.len() - k,
            {
                k += 1;
            }
            if k == name.len() {
                assert(group_name(g as int) =~= name@);
                return Some(g);
            }
            assert(group_name(g as int)[k as int] != name@[k as int]);
        }
        g += 1;
    }
    None
}

} // verus!
