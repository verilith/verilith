//! Sets of stream offsets as sorted, disjoint, half-open ranges: what a
//! sender has had acknowledged, or must send again.
//!
//! Proven: [`RangeSet::insert`] and [`RangeSet::remove`] are set union and
//! difference on `RangeSet::view`; ranges stay sorted, non-empty and
//! separated by gaps (adjacent ones are merged).
use vstd::prelude::*;

verus! {

/// Ascending, non-empty, with a gap between neighbours.
pub open spec fn wf_seq(s: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].0 < s[i].1
    &&& forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i].1 < #[trigger] s[j].0
}

/// `x` is in one of the ranges.
pub open spec fn covers(s: Seq<(u64, u64)>, x: int) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] s[i].0 <= x < s[i].1
}

pub open spec fn ins_pre(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64, a: u64, b: u64) -> bool {
    &&& wf_seq(s)
    &&& a < b
    &&& 0 <= i <= j <= s.len()
    &&& forall|k: int| 0 <= k < i ==> #[trigger] s[k].1 < a
    &&& i < s.len() ==> s[i].1 >= a
    &&& forall|k: int| i <= k < j ==> #[trigger] s[k].0 <= b
    &&& j < s.len() ==> s[j].0 > b
    &&& lo == if i < j && s[i].0 < a { s[i].0 } else { a }
    &&& hi == if i < j && s[j - 1].1 > b { s[j - 1].1 } else { b }
}

pub open spec fn ins_out(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64) -> Seq<(u64, u64)> {
    s.subrange(0, i).push((lo, hi)) + s.subrange(j, s.len() as int)
}

proof fn lemma_ins_index(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64, a: u64, b: u64)
    requires
        ins_pre(s, i, j, lo, hi, a, b),
    ensures
        ins_out(s, i, j, lo, hi).len() == i + 1 + (s.len() - j),
        forall|q: int| 0 <= q < i ==> #[trigger] ins_out(s, i, j, lo, hi)[q] == s[q],
        ins_out(s, i, j, lo, hi)[i] == (lo, hi),
        forall|q: int| j <= q < s.len() ==> #[trigger] ins_out(s, i, j, lo, hi)[q - j + i + 1] == s[q],
        lo < hi,
        lo <= a,
        b <= hi,
        i < j ==> lo <= s[i].0 && s[j - 1].1 <= hi,
{
    let o = ins_out(s, i, j, lo, hi);
    assert forall|q: int| j <= q < s.len() implies #[trigger] o[q - j + i + 1] == s[q] by {}
    if i < j {
        if i < j - 1 {
            assert(s[i].1 < s[j - 1].0);
        }
    }
}

proof fn lemma_insert_sorted(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64, a: u64, b: u64)
    requires
        ins_pre(s, i, j, lo, hi, a, b),
    ensures
        wf_seq(ins_out(s, i, j, lo, hi)),
{
    lemma_ins_index(s, i, j, lo, hi, a, b);
    let o = ins_out(s, i, j, lo, hi);
    let m = i;
    let n = s.len() as int;
    assert forall|q: int| 0 <= q < o.len() implies #[trigger] o[q].0 < o[q].1 by {
        if q > m {
            assert(o[q] == s[q - m - 1 + j]);
        }
    }
    assert forall|p: int, q: int| 0 <= p < q < o.len() implies #[trigger] o[p].1 < #[trigger] o[q].0 by {
        if q < m {
        } else if q == m {
            assert(s[p].1 < a);
            if i < j {
                assert(s[p].1 < s[i].0);
            }
        } else {
            let q0 = q - m - 1 + j;
            assert(o[q] == s[q0]);
            if q0 > j {
                assert(s[j].0 < s[q0].0);
            }
            if p == m {
                if i < j {
                    assert(s[j - 1].1 < s[q0].0);
                }
            } else if p < m {
                assert(s[p].1 < s[q0].0);
            } else {
                let p0 = p - m - 1 + j;
                assert(o[p] == s[p0]);
                assert(s[p0].1 < s[q0].0);
            }
        }
    }
}

proof fn lemma_insert_covers(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64, a: u64, b: u64)
    requires
        ins_pre(s, i, j, lo, hi, a, b),
    ensures
        forall|x: int| covers(ins_out(s, i, j, lo, hi), x) == (covers(s, x) || (a <= x < b)),
{
    lemma_ins_index(s, i, j, lo, hi, a, b);
    let o = ins_out(s, i, j, lo, hi);
    let m = i;
    assert forall|x: int| covers(o, x) == (covers(s, x) || (a <= x < b)) by {
        if covers(s, x) {
            let t = choose|t: int| 0 <= t < s.len() && #[trigger] s[t].0 <= x < s[t].1;
            if t < i {
                assert(o[t].0 <= x < o[t].1);
            } else if t >= j {
                assert(o[t - j + m + 1] == s[t]);
                assert(o[t - j + m + 1].0 <= x < o[t - j + m + 1].1);
            } else {
                if t > i {
                    assert(s[i].0 < s[t].0);
                }
                if t < j - 1 {
                    assert(s[t].1 < s[j - 1].0);
                }
                assert(o[m].0 <= x < o[m].1);
            }
        }
        if a <= x < b {
            assert(o[m].0 <= x < o[m].1);
        }
        if covers(o, x) {
            let t = choose|t: int| 0 <= t < o.len() && #[trigger] o[t].0 <= x < o[t].1;
            if t < m {
                assert(s[t].0 <= x < s[t].1);
            } else if t > m {
                let t0 = t - m - 1 + j;
                assert(o[t] == s[t0]);
                assert(s[t0].0 <= x < s[t0].1);
            } else if !(a <= x < b) {
                if x < a {
                    assert(s[i].0 <= x < s[i].1);
                } else {
                    assert(s[j - 1].0 <= x < s[j - 1].1);
                }
            }
        }
    }
}

proof fn lemma_insert(s: Seq<(u64, u64)>, i: int, j: int, lo: u64, hi: u64, a: u64, b: u64)
    requires
        ins_pre(s, i, j, lo, hi, a, b),
    ensures
        wf_seq(ins_out(s, i, j, lo, hi)),
        forall|x: int| covers(ins_out(s, i, j, lo, hi), x) == (covers(s, x) || (a <= x < b)),
{
    lemma_insert_sorted(s, i, j, lo, hi, a, b);
    lemma_insert_covers(s, i, j, lo, hi, a, b);
}

pub open spec fn rem_pre(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64) -> bool {
    &&& wf_seq(s)
    &&& a < b
    &&& 0 <= i <= j <= s.len()
    &&& forall|k: int| 0 <= k < i ==> #[trigger] s[k].1 <= a
    &&& i < s.len() ==> s[i].1 > a
    &&& forall|k: int| i <= k < j ==> #[trigger] s[k].0 < b
    &&& j < s.len() ==> s[j].0 >= b
}

pub open spec fn rem_mid(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64) -> Seq<(u64, u64)> {
    let l: Seq<(u64, u64)> = if i < j && s[i].0 < a { seq![(s[i].0, a)] } else { Seq::empty() };
    let r: Seq<(u64, u64)> = if i < j && s[j - 1].1 > b { seq![(b, s[j - 1].1)] } else { Seq::empty() };
    l + r
}

pub open spec fn rem_out(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64) -> Seq<(u64, u64)> {
    s.subrange(0, i) + rem_mid(s, i, j, a, b) + s.subrange(j, s.len() as int)
}

proof fn lemma_rem_index(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64)
    requires
        rem_pre(s, i, j, a, b),
    ensures
        ({
            let o = rem_out(s, i, j, a, b);
            let mid = rem_mid(s, i, j, a, b);
            let ml = mid.len() as int;
            &&& o.len() == i + ml + (s.len() - j)
            &&& forall|q: int| 0 <= q < i ==> #[trigger] o[q] == s[q]
            &&& forall|q: int| 0 <= q < ml ==> #[trigger] o[i + q] == mid[q]
            &&& forall|q: int| j <= q < s.len() ==> #[trigger] o[q - j + i + ml] == s[q]
            &&& forall|q: int| 0 <= q < ml ==> #[trigger] mid[q].0 < mid[q].1
            &&& forall|q: int| 0 <= q < ml ==> a <= #[trigger] mid[q].0 || mid[q].1 <= a
            &&& ml == (if i < j && s[i].0 < a { 1int } else { 0 }) + (if i < j && s[j - 1].1 > b { 1int } else { 0 })
        }),
        i < j ==> s[i].0 <= s[j - 1].0 && s[i].1 <= s[j - 1].1,
{
    let o = rem_out(s, i, j, a, b);
    let mid = rem_mid(s, i, j, a, b);
    let ml = mid.len() as int;
    assert forall|q: int| 0 <= q < ml implies #[trigger] o[i + q] == mid[q] by {}
    assert forall|q: int| j <= q < s.len() implies #[trigger] o[q - j + i + ml] == s[q] by {}
    if i < j - 1 {
        assert(s[i].1 < s[j - 1].0);
    }
}

proof fn lemma_remove_sorted(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64)
    requires
        rem_pre(s, i, j, a, b),
    ensures
        wf_seq(rem_out(s, i, j, a, b)),
{
    lemma_rem_index(s, i, j, a, b);
    let o = rem_out(s, i, j, a, b);
    let mid = rem_mid(s, i, j, a, b);
    let m = i;
    let ml = mid.len() as int;
    let left = i < j && s[i].0 < a;
    let right = i < j && s[j - 1].1 > b;
    if left {
        assert(mid[0] == (s[i].0, a));
    }
    if right {
        assert(mid[ml - 1] == (b, s[j - 1].1));
    }
    assert forall|q: int| 0 <= q < o.len() implies #[trigger] o[q].0 < o[q].1 by {
        if m <= q < m + ml {
            assert(o[q] == mid[q - m]);
        } else if q >= m + ml {
            assert(o[q] == s[q - m - ml + j]);
        }
    }
    assert forall|p: int, q: int| 0 <= p < q < o.len() implies #[trigger] o[p].1 < #[trigger] o[q].0 by {
        if q < m {
        } else if q < m + ml {
            assert(o[q] == mid[q - m]);
            if p < m {
                assert(s[p].1 < s[i].0);
            } else {
                assert(o[p] == mid[p - m]);
                assert(left && right && p == m && q == m + 1);
            }
        } else {
            let q0 = q - m - ml + j;
            assert(o[q] == s[q0]);
            if q0 > j {
                assert(s[j].0 < s[q0].0);
            }
            if p < m {
                assert(s[p].1 < s[q0].0);
            } else if p < m + ml {
                assert(o[p] == mid[p - m]);
                if i < j {
                    assert(s[j - 1].1 < s[q0].0);
                }
            } else {
                let p0 = p - m - ml + j;
                assert(o[p] == s[p0]);
                assert(s[p0].1 < s[q0].0);
            }
        }
    }
}

proof fn lemma_remove_covers(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64)
    requires
        rem_pre(s, i, j, a, b),
    ensures
        forall|x: int| covers(rem_out(s, i, j, a, b), x) == (covers(s, x) && !(a <= x < b)),
{
    lemma_rem_index(s, i, j, a, b);
    let o = rem_out(s, i, j, a, b);
    let mid = rem_mid(s, i, j, a, b);
    let m = i;
    let ml = mid.len() as int;
    let left = i < j && s[i].0 < a;
    let right = i < j && s[j - 1].1 > b;
    if left {
        assert(mid[0] == (s[i].0, a));
    }
    if right {
        assert(mid[ml - 1] == (b, s[j - 1].1));
    }
    assert forall|x: int| covers(o, x) == (covers(s, x) && !(a <= x < b)) by {
        if covers(s, x) && !(a <= x < b) {
            let t = choose|t: int| 0 <= t < s.len() && #[trigger] s[t].0 <= x < s[t].1;
            if t < i {
                assert(o[t].0 <= x < o[t].1);
            } else if t >= j {
                assert(o[t - j + m + ml] == s[t]);
                assert(o[t - j + m + ml].0 <= x < o[t - j + m + ml].1);
            } else if x < a {
                if t > i {
                    assert(s[i].1 < s[t].0);
                }
                assert(o[m] == mid[0]);
                assert(o[m].0 <= x < o[m].1);
            } else {
                if t < j - 1 {
                    assert(s[t].1 < s[j - 1].0);
                }
                assert(o[m + ml - 1] == mid[ml - 1]);
                assert(o[m + ml - 1].0 <= x < o[m + ml - 1].1);
            }
        }
        if covers(o, x) {
            let t = choose|t: int| 0 <= t < o.len() && #[trigger] o[t].0 <= x < o[t].1;
            if t < m {
                assert(s[t].0 <= x < s[t].1);
            } else if t >= m + ml {
                let t0 = t - m - ml + j;
                assert(o[t] == s[t0]);
                assert(s[t0].0 <= x < s[t0].1);
            } else {
                assert(o[t] == mid[t - m]);
                if left && t == m {
                    assert(s[i].0 <= x < s[i].1);
                } else {
                    assert(mid[t - m] == (b, s[j - 1].1));
                    assert(s[j - 1].0 <= x < s[j - 1].1);
                }
            }
        }
    }
}

proof fn lemma_remove(s: Seq<(u64, u64)>, i: int, j: int, a: u64, b: u64)
    requires
        rem_pre(s, i, j, a, b),
    ensures
        wf_seq(rem_out(s, i, j, a, b)),
        forall|x: int| covers(rem_out(s, i, j, a, b), x) == (covers(s, x) && !(a <= x < b)),
{
    lemma_remove_sorted(s, i, j, a, b);
    lemma_remove_covers(s, i, j, a, b);
}

/// Ranges of offsets.
pub struct RangeSet {
    v: Vec<(u64, u64)>,
}

impl RangeSet {
    pub closed spec fn ranges(&self) -> Seq<(u64, u64)> {
        self.v@
    }

    pub open spec fn wf(&self) -> bool {
        wf_seq(self.ranges())
    }

    /// The offsets in the set.
    pub open spec fn view(&self) -> ISet<int> {
        ISet::new(|x: int| covers(self.ranges(), x))
    }

    /// The empty set.
    pub fn new() -> (r: RangeSet)
        ensures
            r.wf(),
            r.view() == ISet::<int>::empty(),
    {
        let r = RangeSet { v: Vec::new() };
        assert(r.view() =~= ISet::<int>::empty());
        r
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.view() == ISet::<int>::empty()),
    {
        proof {
            if self.v.len() > 0 {
                let x = self.v@[0].0 as int;
                assert(self.view().contains(x));
            } else {
                assert(self.view() =~= ISet::<int>::empty());
            }
        }
        self.v.len() == 0
    }

    /// Ranges held (the memory used).
    pub fn len(&self) -> (r: usize)
        ensures
            r == self.ranges().len(),
    {
        self.v.len()
    }

    /// The lowest range: `[a, b)` is in the set, nothing below `a` is,
    /// and `b` is not.
    pub fn first(&self) -> (r: Option<(u64, u64)>)
        requires
            self.wf(),
        ensures
            r is None <==> self.view() == ISet::<int>::empty(),
            r matches Some((a, b)) ==> {
                &&& a < b
                &&& forall|x: int| a <= x < b ==> self.view().contains(x)
                &&& !self.view().contains(b as int)
                &&& forall|x: int| x < a ==> !self.view().contains(x)
            },
    {
        if self.v.len() == 0 {
            proof {
                assert(self.view() =~= ISet::<int>::empty());
            }
            return None;
        }
        let (a, b) = self.v[0];
        proof {
            let s = self.v@;
            assert(self.view().contains(a as int));
            assert forall|x: int| a <= x < b implies self.view().contains(x) by {
                assert(s[0].0 <= x < s[0].1);
            }
            assert forall|x: int| x < a implies !self.view().contains(x) by {
                if covers(s, x) {
                    let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i].0 <= x < s[i].1;
                    if i > 0 {
                        assert(s[0].1 < s[i].0);
                    }
                }
            }
            if covers(s, b as int) {
                let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i].0 <= b < s[i].1;
                if i > 0 {
                    assert(s[0].1 < s[i].0);
                }
            }
        }
        Some((a, b))
    }

    /// Adds `[a, b)`.
    pub fn insert(&mut self, a: u64, b: u64)
        requires
            old(self).wf(),
            a < b,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().union(ISet::new(|x: int| a <= x < b)),
    {
        let n = self.v.len();
        let mut i = 0;
        while i < n && self.v[i].1 < a
            invariant
                0 <= i <= n == self.v.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] self.v@[k].1 < a,
            decreases n - i,
        {
            i = i + 1;
        }
        let mut j = i;
        while j < n && self.v[j].0 <= b
            invariant
                i <= j <= n == self.v.len(),
                forall|k: int| i <= k < j ==> #[trigger] self.v@[k].0 <= b,
            decreases n - j,
        {
            j = j + 1;
        }
        let (lo, hi) = if i < j {
            let l = if self.v[i].0 < a { self.v[i].0 } else { a };
            let h = if self.v[j - 1].1 > b { self.v[j - 1].1 } else { b };
            (l, h)
        } else {
            (a, b)
        };
        let ghost s = self.v@;
        let mut out: Vec<(u64, u64)> = Vec::new();
        let mut k = 0;
        while k < i
            invariant
                0 <= k <= i <= n == s.len(),
                self.v@ == s,
                out@ == s.subrange(0, k as int),
            decreases i - k,
        {
            out.push(self.v[k]);
            k = k + 1;
            proof {
                assert(out@ =~= s.subrange(0, k as int));
            }
        }
        out.push((lo, hi));
        let mut k = j;
        while k < n
            invariant
                i <= j <= k <= n == s.len(),
                self.v@ == s,
                out@ == s.subrange(0, i as int).push((lo, hi)) + s.subrange(j as int, k as int),
            decreases n - k,
        {
            out.push(self.v[k]);
            k = k + 1;
            proof {
                assert(out@ =~= s.subrange(0, i as int).push((lo, hi)) + s.subrange(j as int, k as int));
            }
        }
        proof {
            assert(out@ =~= ins_out(s, i as int, j as int, lo, hi));
            lemma_insert(s, i as int, j as int, lo, hi, a, b);
        }
        self.v = out;
        proof {
            assert(final(self).view() =~= old(self).view().union(ISet::new(|x: int| a <= x < b)));
        }
    }

    /// Removes `[a, b)`.
    pub fn remove(&mut self, a: u64, b: u64)
        requires
            old(self).wf(),
            a < b,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().difference(ISet::new(|x: int| a <= x < b)),
    {
        let n = self.v.len();
        let mut i = 0;
        while i < n && self.v[i].1 <= a
            invariant
                0 <= i <= n == self.v.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] self.v@[k].1 <= a,
            decreases n - i,
        {
            i = i + 1;
        }
        let mut j = i;
        while j < n && self.v[j].0 < b
            invariant
                i <= j <= n == self.v.len(),
                forall|k: int| i <= k < j ==> #[trigger] self.v@[k].0 < b,
            decreases n - j,
        {
            j = j + 1;
        }
        let ghost s = self.v@;
        let left = i < j && self.v[i].0 < a;
        let right = i < j && self.v[j - 1].1 > b;
        let mut out: Vec<(u64, u64)> = Vec::new();
        let mut k = 0;
        while k < i
            invariant
                0 <= k <= i <= n == s.len(),
                self.v@ == s,
                out@ == s.subrange(0, k as int),
            decreases i - k,
        {
            out.push(self.v[k]);
            k = k + 1;
            proof {
                assert(out@ =~= s.subrange(0, k as int));
            }
        }
        let ghost mid: Seq<(u64, u64)> = Seq::empty();
        if left {
            out.push((self.v[i].0, a));
            proof {
                mid = mid.push((s[i as int].0, a));
            }
        }
        if right {
            out.push((b, self.v[j - 1].1));
            proof {
                mid = mid.push((b, s[j - 1].1));
            }
        }
        proof {
            assert(out@ =~= s.subrange(0, i as int) + mid);
        }
        let mut k = j;
        while k < n
            invariant
                i <= j <= k <= n == s.len(),
                self.v@ == s,
                out@ == s.subrange(0, i as int) + mid + s.subrange(j as int, k as int),
            decreases n - k,
        {
            out.push(self.v[k]);
            k = k + 1;
            proof {
                assert(out@ =~= s.subrange(0, i as int) + mid + s.subrange(j as int, k as int));
            }
        }
        proof {
            assert(mid =~= rem_mid(s, i as int, j as int, a, b));
            assert(out@ =~= rem_out(s, i as int, j as int, a, b));
            lemma_remove(s, i as int, j as int, a, b);
        }
        self.v = out;
        proof {
            assert(final(self).view() =~= old(self).view().difference(ISet::new(|x: int| a <= x < b)));
        }
    }

    /// Whether `[a, b)` is all in the set.
    pub fn contains(&self, a: u64, b: u64) -> (r: bool)
        requires
            self.wf(),
            a < b,
        ensures
            r == (forall|x: int| a <= x < b ==> self.view().contains(x)),
    {
        let n = self.v.len();
        let mut i = 0;
        while i < n && self.v[i].1 <= a
            invariant
                0 <= i <= n == self.v.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] self.v@[k].1 <= a,
            decreases n - i,
        {
            i = i + 1;
        }
        let r = i < n && self.v[i].0 <= a && b <= self.v[i].1;
        proof {
            let s = self.v@;
            if !r {
                // `a` itself, or the first gap past it, is missing.
                if i < n && s[i as int].0 <= a {
                    let x = s[i as int].1 as int;
                    assert(a <= x < b);
                    if covers(s, x) {
                        let t = choose|t: int| 0 <= t < s.len() && #[trigger] s[t].0 <= x < s[t].1;
                        if t < i {
                            assert(s[t].1 <= a);
                        } else if t > i {
                            assert(s[i as int].1 < s[t].0);
                        }
                    }
                    assert(!self.view().contains(x));
                } else {
                    if covers(s, a as int) {
                        let t = choose|t: int| 0 <= t < s.len() && #[trigger] s[t].0 <= a < s[t].1;
                        if t < i {
                        } else if t > i {
                            assert(s[i as int].0 < s[t].0);
                        }
                    }
                    assert(!self.view().contains(a as int));
                }
            } else {
                assert forall|x: int| a <= x < b implies self.view().contains(x) by {
                    assert(s[i as int].0 <= x < s[i as int].1);
                }
            }
        }
        r
    }

    /// Adds `[a, b)` less the offsets in `other`.
    pub fn insert_except(&mut self, a: u64, b: u64, other: &RangeSet)
        requires
            old(self).wf(),
            other.wf(),
            a < b,
        ensures
            final(self).wf(),
            forall|x: int| #[trigger] final(self).view().contains(x) == ((old(self).view().contains(x) || (
            a <= x < b)) && !(a <= x < b && other.view().contains(x))),
    {
        self.insert(a, b);
        let ghost u = self.view();
        let n = other.v.len();
        let mut k = 0;
        while k < n
            invariant
                0 <= k <= n == other.v@.len(),
                a < b,
                self.wf(),
                forall|x: int| #[trigger] self.view().contains(x) == (u.contains(x) && !(a <= x < b && covers(other.v@.subrange(0, k as int), x))),
            decreases n - k,
        {
            let (s, e) = other.v[k];
            let lo = if s > a { s } else { a };
            let hi = if e < b { e } else { b };
            let ghost before = self.view();
            if lo < hi {
                self.remove(lo, hi);
            }
            proof {
                let o1 = other.v@.subrange(0, k as int);
                let o2 = other.v@.subrange(0, k + 1);
                assert forall|x: int| #[trigger] self.view().contains(x) == (u.contains(x) && !(a <= x < b && covers(o2, x))) by {
                    if covers(o2, x) {
                        let t = choose|t: int| 0 <= t < o2.len() && #[trigger] o2[t].0 <= x < o2[t].1;
                        if t < k {
                            assert(o1[t] == o2[t]);
                            assert(covers(o1, x));
                        }
                    }
                    if covers(o1, x) {
                        let t = choose|t: int| 0 <= t < o1.len() && #[trigger] o1[t].0 <= x < o1[t].1;
                        assert(o1[t] == o2[t]);
                        assert(covers(o2, x));
                    }
                    if s <= x < e {
                        assert(o2[k as int] == (s, e));
                        assert(covers(o2, x));
                    }
                    if covers(o2, x) && !covers(o1, x) {
                        let t = choose|t: int| 0 <= t < o2.len() && #[trigger] o2[t].0 <= x < o2[t].1;
                        assert(t == k);
                    }
                }
            }
            k = k + 1;
        }
        proof {
            assert(other.v@.subrange(0, n as int) =~= other.v@);
            assert forall|x: int| other.view().contains(x) == covers(other.v@, x) by {}
        }
    }

    /// Empties the set.
    pub fn clear(&mut self)
        ensures
            final(self).wf(),
            final(self).view() == ISet::<int>::empty(),
    {
        self.v.clear();
        proof {
            assert(final(self).view() =~= ISet::<int>::empty());
        }
    }
}

} // verus!
