//! Received packet numbers (RFC 9000 §12.3, §13.2): duplicate detection
//! and the ranges an ACK frame reports, for one packet number space.
//!
//! Proven, after any sequence of calls:
//!
//! - the tracked ranges hold only packet numbers that were received, so
//!   an ACK frame built by [`Received::ack_fields`] acknowledges nothing
//!   else (§13.1: "MUST NOT acknowledge packets it has not received"), and
//!   decodes, through `frame::AckRanges`, back to exactly those ranges;
//! - a packet number received before is always a duplicate
//!   ([`Received::is_dup`]), so no packet is processed twice (§12.3);
//! - at most [`MAX_RANGES`] ranges are kept: when one more is needed the
//!   oldest is dropped, and every packet number below it is from then on
//!   treated as a duplicate (§13.2.3 allows this).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::spec::ack_ranges_wf;

verus! {

/// The most ranges kept.
pub const MAX_RANGES: usize = 32;

/// Packet numbers are below 2^62 (§12.3).
pub const PN_LIMIT: u64 = 0x4000_0000_0000_0000;

/// `x` is in one of the inclusive ranges `rs`.
pub open spec fn holds(rs: Seq<(u64, u64)>, x: int) -> bool {
    exists|i: int| 0 <= i < rs.len() && #[trigger] rs[i].0 <= x <= rs[i].1
}

/// Ascending, disjoint, not adjacent, below [`PN_LIMIT`].
pub open spec fn sorted(rs: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i].0 <= rs[i].1 < PN_LIMIT
    &&& forall|i: int, j: int| 0 <= i < j < rs.len() ==> #[trigger] rs[i].1 + 1 < #[trigger] rs[j].0
}

/// The last `k` ranges, newest first: the order of an ACK frame.
pub open spec fn desc(rs: Seq<(u64, u64)>, k: int) -> Seq<(u64, u64)> {
    Seq::new(k as nat, |j: int| rs[rs.len() - 1 - j])
}

/// The ranges `frame::AckRanges::next` returns for the (Gap, ACK Range
/// Length) pairs `g` after a range whose smallest number is `s`.
pub open spec fn gap_abs(g: Seq<(u64, u64)>, s: u64) -> Seq<(u64, u64)>
    decreases g.len(),
{
    if g.len() == 0 {
        Seq::empty()
    } else {
        let hi = s - g[0].0 - 2;
        let lo = hi - g[0].1;
        seq![(lo as u64, hi as u64)] + gap_abs(g.drop_first(), lo as u64)
    }
}

/// The packet numbers an ACK frame with these fields acknowledges.
pub open spec fn ack_has(largest: u64, first: u64, g: Seq<(u64, u64)>, x: int) -> bool {
    (largest - first <= x <= largest) || holds(gap_abs(g, (largest - first) as u64), x)
}

/// The gaps between consecutive descending ranges `t`.
pub open spec fn gaps_of(t: Seq<(u64, u64)>, g: Seq<(u64, u64)>) -> bool {
    &&& t.len() == g.len() + 1
    &&& forall|m: int| 0 <= m < g.len() ==> #[trigger] g[m] == ((t[m].0 - t[m + 1].1 - 2) as u64, (t[m + 1].1 - t[m + 1].0) as u64)
}

/// Descending, not adjacent, below [`PN_LIMIT`].
pub open spec fn desc_ok(t: Seq<(u64, u64)>) -> bool {
    &&& forall|m: int| 0 <= m < t.len() ==> #[trigger] t[m].0 <= t[m].1 < PN_LIMIT
    &&& forall|m: int| 0 <= m < t.len() - 1 ==> #[trigger] t[m + 1].1 + 2 <= t[m].0
}

proof fn lemma_gaps(t: Seq<(u64, u64)>, g: Seq<(u64, u64)>)
    requires
        gaps_of(t, g),
        desc_ok(t),
    ensures
        ack_ranges_wf(g, t[0].0),
        gap_abs(g, t[0].0) == t.drop_first(),
    decreases g.len(),
{
    if g.len() > 0 {
        let t2 = t.drop_first();
        let g2 = g.drop_first();
        assert(g[0] == ((t[0].0 - t[1].1 - 2) as u64, (t[1].1 - t[1].0) as u64));
        assert(t[0].0 <= t[0].1 < PN_LIMIT && t[1].0 <= t[1].1 < PN_LIMIT && t[1].1 + 2 <= t[0].0);
        assert forall|m: int| 0 <= m < g2.len() implies #[trigger] g2[m] == ((t2[m].0 - t2[m + 1].1 - 2) as u64, (
        t2[m + 1].1 - t2[m + 1].0) as u64) by {
            assert(g[m + 1] == ((t[m + 1].0 - t[m + 2].1 - 2) as u64, (t[m + 2].1 - t[m + 2].0) as u64));
        }
        assert forall|m: int| 0 <= m < t2.len() implies #[trigger] t2[m].0 <= t2[m].1 < PN_LIMIT by {
            assert(t[m + 1].0 <= t[m + 1].1 < PN_LIMIT);
        }
        assert forall|m: int| 0 <= m < t2.len() - 1 implies #[trigger] t2[m + 1].1 + 2 <= t2[m].0 by {
            let m1 = m + 1;
            assert(t[m1 + 1].1 + 2 <= t[m1].0);
        }
        lemma_gaps(t2, g2);
        assert(t2[0] == t[1]);
        let hi = (t[0].0 - g[0].0 - 2) as u64;
        let lo = (hi - g[0].1) as u64;
        assert(hi == t[1].1 && lo == t[1].0);
        assert(gap_abs(g, t[0].0) == seq![(lo, hi)] + gap_abs(g2, lo));
        assert(gap_abs(g, t[0].0) =~= seq![t[1]] + t2.drop_first());
        assert(t.drop_first() =~= seq![t[1]] + t2.drop_first());
    }
}

/// The packet numbers received in one packet number space.
pub struct Received {
    rs: Vec<(u64, u64)>,
    floor: u64,
    largest_time: u64,
    pending: u64,
    immediate: bool,
    received: Ghost<Set<int>>,
}

impl Received {
    /// The tracked ranges, ascending.
    pub closed spec fn ranges(&self) -> Seq<(u64, u64)> {
        self.rs@
    }

    /// Packet numbers below this are duplicates.
    pub closed spec fn floor(&self) -> u64 {
        self.floor
    }

    /// Every packet number received.
    pub closed spec fn received(&self) -> Set<int> {
        self.received@
    }

    /// The tracked ranges are sorted, at most [`MAX_RANGES`], above the
    /// floor; they hold only received numbers and every received number
    /// above the floor.
    pub closed spec fn inv(&self) -> bool {
        &&& sorted(self.rs@)
        &&& self.rs@.len() <= MAX_RANGES
        &&& self.rs@.len() > 0 ==> self.rs@[0].0 >= self.floor
        &&& self.floor <= PN_LIMIT
        &&& forall|x: int| holds(self.rs@, x) ==> #[trigger] self.received@.contains(x)
        &&& forall|x: int| #[trigger] self.received@.contains(x) ==> holds(self.rs@, x) || x < self.floor
    }

    /// Nothing received yet.
    pub fn new() -> (r: Received)
        ensures
            r.inv(),
            r.received() == Set::<int>::empty(),
            r.floor() == 0,
    {
        Received { rs: Vec::new(), floor: 0, largest_time: 0, pending: 0, immediate: false, received: Ghost(Set::empty()) }
    }

    /// Whether `pn` must be discarded as a duplicate: it was received
    /// before, or is below the oldest range kept.
    pub fn is_dup(&self, pn: u64) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == (pn < self.floor() || holds(self.ranges(), pn as int)),
            self.received().contains(pn as int) ==> r,
            r ==> self.received().contains(pn as int) || pn < self.floor(),
    {
        if pn < self.floor {
            return true;
        }
        let mut i = self.rs.len();
        while i > 0
            invariant
                self.inv(),
                i <= self.rs@.len(),
                forall|j: int| i <= j < self.rs@.len() ==> !(#[trigger] self.rs@[j].0 <= pn <= self.rs@[j].1),
            decreases i,
        {
            let (lo, hi) = self.rs[i - 1];
            if lo <= pn && pn <= hi {
                return true;
            }
            if hi < pn {
                assert forall|j: int| 0 <= j < self.rs@.len() implies !(#[trigger] self.rs@[j].0 <= pn <= self.rs@[j].1) by {
                    if j < i - 1 {
                        assert(self.rs@[j].1 + 1 < self.rs@[i - 1].0);
                        assert(self.rs@[i - 1].0 <= self.rs@[i - 1].1);
                    }
                }
                return false;
            }
            i = i - 1;
        }
        false
    }

    /// The largest packet number received, if any range is kept.
    pub fn largest(&self) -> (r: Option<u64>)
        requires
            self.inv(),
        ensures
            self.ranges().len() == 0 ==> r is None,
            self.ranges().len() > 0 ==> r == Some(self.ranges().last().1),
    {
        if self.rs.len() == 0 {
            None
        } else {
            Some(self.rs[self.rs.len() - 1].1)
        }
    }

    /// When the largest packet number was received.
    pub fn largest_time(&self) -> u64 {
        self.largest_time
    }

    /// Whether an ACK frame should be sent now rather than within
    /// max_ack_delay (§13.2.1, §13.2.2): two or more ack-eliciting packets
    /// arrived since the last one, or an ack-eliciting packet arrived out
    /// of order.
    pub fn ack_now(&self) -> bool {
        self.pending >= 2 || self.immediate
    }

    /// Whether ack-eliciting packets arrived since the last ACK frame.
    pub fn ack_pending(&self) -> bool {
        self.pending > 0
    }

    /// An ACK frame was sent.
    pub fn on_ack_sent(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).ranges() == old(self).ranges(),
            final(self).floor() == old(self).floor(),
            final(self).received() == old(self).received(),
    {
        self.pending = 0;
        self.immediate = false;
    }

    /// Packet `pn`, not a duplicate, was received and authenticated at
    /// `now`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    pub fn insert(&mut self, pn: u64, now: u64, eliciting: bool)
        requires
            old(self).inv(),
            pn < PN_LIMIT,
            pn >= old(self).floor(),
            !holds(old(self).ranges(), pn as int),
        ensures
            final(self).inv(),
            final(self).received() == old(self).received().insert(pn as int),
            final(self).floor() >= old(self).floor(),
            forall|x: int| #[trigger] holds(final(self).ranges(), x) == ((holds(old(self).ranges(), x) || x == pn) && x >= final(self).floor()),
    {
        let ghost old_rs = self.rs@;
        let len = self.rs.len();
        // Ranges before index i end below pn; ranges from i start above it.
        let mut i = len;
        while i > 0 && self.rs[i - 1].0 > pn
            invariant
                self.rs@ == old_rs,
                len == old_rs.len(),
                i <= len,
                forall|j: int| i <= j < len ==> #[trigger] old_rs[j].0 > pn,
            decreases i,
        {
            i = i - 1;
        }
        proof {
            if i > 0 {
                if old_rs[i - 1].1 >= pn {
                    assert(old_rs[i - 1].0 <= pn <= old_rs[i - 1].1);
                }
            }
        }
        let largest = len == 0 || i == len;
        let left = i > 0 && self.rs[i - 1].1 + 1 == pn;
        let right = i < len && pn + 1 == self.rs[i].0;
        if eliciting {
            if self.pending < u64::MAX {
                self.pending = self.pending + 1;
            }
            // §13.2.1: out of order, or with packets missing below it.
            if !largest || !left {
                self.immediate = true;
            }
        }
        if largest {
            self.largest_time = now;
        }
        if left && right {
            let hi = self.rs[i].1;
            let lo = self.rs[i - 1].0;
            self.rs.set(i - 1, (lo, hi));
            self.rs.remove(i);
        } else if left {
            let lo = self.rs[i - 1].0;
            self.rs.set(i - 1, (lo, pn));
        } else if right {
            let hi = self.rs[i].1;
            self.rs.set(i, (pn, hi));
        } else {
            self.rs.insert(i, (pn, pn));
        }
        self.received = Ghost(self.received@.insert(pn as int));
        let ghost mid = self.rs@;
        proof {
            lemma_layout(old_rs, mid, pn, i as int, left, right);
            lemma_insert_sorted(old_rs, mid, pn, i as int, left, right);
            lemma_insert_holds(old_rs, mid, pn, i as int, left, right);
        }
        if self.rs.len() > MAX_RANGES {
            let (_, hi) = self.rs.remove(0);
            self.floor = hi + 1;
            proof {
                lemma_drop(mid, self.rs@);
            }
        } else {
            proof {
                lemma_above(mid);
                assert(mid.len() > 0);
                if old_rs.len() > 0 {
                    assert(old_rs[0].0 <= old_rs[0].1);
                }
            }
        }
        proof {
            assert forall|x: int| #[trigger] self.received@.contains(x) implies holds(self.rs@, x) || x < self.floor by {
                if x != pn && old(self).received@.contains(x) {
                    assert(holds(old_rs, x) || x < old(self).floor);
                }
            }
        }
    }

    /// The fields of an ACK frame (§19.3) for the `n` newest ranges:
    /// Largest Acknowledged, First ACK Range, and the (Gap, ACK Range
    /// Length) pairs appended to `gaps`. Everything it acknowledges was
    /// received.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(50)]
    pub fn ack_fields(&self, n: usize, gaps: &mut Vec<(u64, u64)>) -> (r: (u64, u64))
        requires
            self.inv(),
            self.ranges().len() > 0,
            n >= 1,
            old(gaps)@.len() == 0,
        ensures
            ({
                let k = if n < self.ranges().len() { n as int } else { self.ranges().len() as int };
                let t = desc(self.ranges(), k);
                &&& r.0 == t[0].1 && r.1 == t[0].1 - t[0].0
                &&& ack_ranges_wf(final(gaps)@, (r.0 - r.1) as u64)
                &&& gap_abs(final(gaps)@, (r.0 - r.1) as u64) == t.drop_first()
            }),
            r.0 < PN_LIMIT,
            r.1 <= r.0,
            forall|x: int| #[trigger] ack_has(r.0, r.1, final(gaps)@, x) ==> self.received().contains(x),
    {
        let len = self.rs.len();
        let k = if n < len { n } else { len };
        let ghost t = desc(self.rs@, k as int);
        let (lo0, hi0) = self.rs[len - 1];
        assert(t[0] == self.rs@[len - 1]);
        let mut j: usize = 1;
        while j < k
            invariant
                self.inv(),
                len == self.rs@.len(),
                1 <= j <= k <= len,
                t == desc(self.rs@, k as int),
                gaps@.len() == j - 1,
                forall|m: int| 0 <= m < gaps@.len() ==> #[trigger] gaps@[m] == ((t[m].0 - t[m + 1].1 - 2) as u64, (t[m + 1].1 - t[m + 1].0) as u64),
            decreases k - j,
        {
            let (lo, hi) = self.rs[len - 1 - j];
            let prev = self.rs[len - j].0;
            assert(t[j - 1] == self.rs@[len - j] && t[j as int] == self.rs@[len - 1 - j]);
            assert(self.rs@[len - 1 - j].1 + 1 < self.rs@[len - j].0);
            assert(self.rs@[len - 1 - j].0 <= self.rs@[len - 1 - j].1);
            gaps.push((prev - hi - 2, hi - lo));
            j = j + 1;
        }
        proof {
            assert forall|m: int| 0 <= m < t.len() implies #[trigger] t[m].0 <= t[m].1 < PN_LIMIT by {
                assert(t[m] == self.rs@[len - 1 - m]);
            }
            assert forall|m: int| 0 <= m < t.len() - 1 implies #[trigger] t[m + 1].1 + 2 <= t[m].0 by {
                assert(t[m] == self.rs@[len - 1 - m] && t[m + 1] == self.rs@[len - 2 - m]);
            }
            lemma_gaps(t, gaps@);
            assert(self.rs@[len - 1].0 <= self.rs@[len - 1].1 < PN_LIMIT);
            assert forall|x: int| #[trigger] ack_has(hi0, (hi0 - lo0) as u64, gaps@, x) implies self.received@.contains(x) by {
                if lo0 <= x <= hi0 {
                    assert(self.rs@[len - 1].0 <= x <= self.rs@[len - 1].1);
                } else {
                    let d = t.drop_first();
                    let m = choose|m: int| 0 <= m < d.len() && #[trigger] d[m].0 <= x <= d[m].1;
                    assert(d[m] == self.rs@[len - 2 - m]);
                    assert(self.rs@[len - 2 - m].0 <= x <= self.rs@[len - 2 - m].1);
                }
                assert(holds(self.rs@, x));
            }
        }
        (hi0, hi0 - lo0)
    }
}

/// The new range's index.
pub open spec fn at_of(i: int, left: bool) -> int {
    if left { i - 1 } else { i }
}

/// The old index of new range `k`, other than the new range's.
pub open spec fn src_of(k: int, at: int, left: bool, right: bool) -> int {
    if k < at {
        k
    } else if left && right {
        k + 1
    } else if !left && !right {
        k - 1
    } else {
        k
    }
}

/// `n` is `o` with `pn` added at index `i`, merged with its neighbours as
/// `left` and `right` say.
pub open spec fn layout(o: Seq<(u64, u64)>, n: Seq<(u64, u64)>, pn: u64, i: int, left: bool, right: bool) -> bool {
    let at = at_of(i, left);
    &&& sorted(o)
    &&& pn < PN_LIMIT
    &&& 0 <= i <= o.len()
    &&& i > 0 ==> o[i - 1].1 < pn
    &&& forall|j: int| i <= j < o.len() ==> #[trigger] o[j].0 > pn
    &&& left == (i > 0 && o[i - 1].1 + 1 == pn)
    &&& right == (i < o.len() && pn + 1 == o[i].0)
    &&& n.len() == o.len() + 1 - (if left { 1int } else { 0 }) - (if right { 1int } else { 0 })
    &&& 0 <= at < n.len()
    &&& n[at] == (if left { o[i - 1].0 } else { pn }, if right { o[i].1 } else { pn })
    &&& forall|k: int| 0 <= k < n.len() && k != at ==> 0 <= src_of(k, at, left, right) < o.len()
        && #[trigger] n[k] == o[src_of(k, at, left, right)]
}

proof fn lemma_layout(o: Seq<(u64, u64)>, n: Seq<(u64, u64)>, pn: u64, i: int, left: bool, right: bool)
    requires
        sorted(o),
        pn < PN_LIMIT,
        0 <= i <= o.len(),
        i > 0 ==> o[i - 1].1 < pn,
        forall|j: int| i <= j < o.len() ==> #[trigger] o[j].0 > pn,
        left == (i > 0 && o[i - 1].1 + 1 == pn),
        right == (i < o.len() && pn + 1 == o[i].0),
        left && right ==> n == o.update(i - 1, (o[i - 1].0, o[i].1)).remove(i),
        left && !right ==> n == o.update(i - 1, (o[i - 1].0, pn)),
        !left && right ==> n == o.update(i, (pn, o[i].1)),
        !left && !right ==> n == o.insert(i, (pn, pn)),
    ensures
        layout(o, n, pn, i, left, right),
{
    let at = at_of(i, left);
    if left && right {
        let u = o.update(i - 1, (o[i - 1].0, o[i].1));
        assert forall|k: int| 0 <= k < n.len() && k != at implies 0 <= src_of(k, at, left, right) < o.len()
            && #[trigger] n[k] == o[src_of(k, at, left, right)] by {
            if k < i {
                assert(n[k] == u[k]);
            } else {
                assert(n[k] == u[k + 1]);
            }
        }
    } else if !left && !right {
        assert forall|k: int| 0 <= k < n.len() && k != at implies 0 <= src_of(k, at, left, right) < o.len()
            && #[trigger] n[k] == o[src_of(k, at, left, right)] by {}
    }
}

proof fn lemma_insert_sorted(o: Seq<(u64, u64)>, n: Seq<(u64, u64)>, pn: u64, i: int, left: bool, right: bool)
    requires
        layout(o, n, pn, i, left, right),
    ensures
        sorted(n),
        n.len() <= o.len() + 1,
        n.len() > 0,
        o.len() > 0 ==> n[0].0 >= o[0].0 || n[0].0 == pn,
{
    let at = at_of(i, left);
    let len = o.len() as int;
    assert forall|k: int| 0 <= k < n.len() implies #[trigger] n[k].0 <= n[k].1 < PN_LIMIT by {
        if k != at {
            assert(n[k] == o[src_of(k, at, left, right)]);
        } else {
            if left {
                assert(o[i - 1].0 <= o[i - 1].1);
            }
            if right {
                assert(o[i].0 <= o[i].1 < PN_LIMIT);
            }
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < n.len() implies #[trigger] n[a].1 + 1 < #[trigger] n[b].0 by {
        let sa = src_of(a, at, left, right);
        let sb = src_of(b, at, left, right);
        if a != at && b != at {
            assert(n[a] == o[sa] && n[b] == o[sb]);
            assert(o[sa].1 + 1 < o[sb].0);
        } else if a == at {
            assert(n[b] == o[sb]);
            assert(o[sb].0 > pn);
            if right {
                assert(sb > i);
                assert(o[i].1 + 1 < o[sb].0);
            } else if sb == i {
                assert(o[i].0 != pn + 1);
            }
        } else {
            assert(n[a] == o[sa]);
            if left {
                assert(sa < i - 1);
                assert(o[sa].1 + 1 < o[i - 1].0);
            } else if sa == i - 1 {
                assert(o[i - 1].1 + 1 != pn);
            } else {
                assert(o[sa].1 + 1 < o[i - 1].0);
                assert(o[i - 1].0 <= o[i - 1].1);
            }
        }
    }
    if len > 0 {
        if at == 0 {
            if left {
                assert(i == 1);
            }
        } else {
            assert(n[0] == o[0]);
        }
    }
}

proof fn lemma_insert_holds(o: Seq<(u64, u64)>, n: Seq<(u64, u64)>, pn: u64, i: int, left: bool, right: bool)
    requires
        layout(o, n, pn, i, left, right),
    ensures
        forall|x: int| #[trigger] holds(n, x) == (holds(o, x) || x == pn),
{
    let at = at_of(i, left);
    assert forall|x: int| #[trigger] holds(n, x) == (holds(o, x) || x == pn) by {
        if holds(n, x) {
            let k = choose|k: int| 0 <= k < n.len() && #[trigger] n[k].0 <= x <= n[k].1;
            if k != at {
                let sk = src_of(k, at, left, right);
                assert(n[k] == o[sk]);
                assert(o[sk].0 <= x <= o[sk].1);
            } else if x < pn {
                assert(o[i - 1].0 <= x <= o[i - 1].1);
            } else if x > pn {
                assert(o[i].0 <= x <= o[i].1);
            }
        }
        if x == pn {
            assert(n[at].0 <= x <= n[at].1);
        }
        if holds(o, x) {
            let j = choose|j: int| 0 <= j < o.len() && #[trigger] o[j].0 <= x <= o[j].1;
            if left && j == i - 1 {
                assert(n[at].0 <= x <= n[at].1);
            } else if right && j == i {
                assert(n[at].0 <= x <= n[at].1);
            } else {
                let k = if j < at { j } else if left && right { j - 1 } else if !left && !right { j + 1 } else { j };
                assert(k != at && 0 <= k < n.len() && src_of(k, at, left, right) == j);
                assert(n[k] == o[j]);
                assert(n[k].0 <= x <= n[k].1);
            }
        }
    }
}

/// Every number in sorted ranges is at least the first one's start.
proof fn lemma_above(rs: Seq<(u64, u64)>)
    requires
        sorted(rs),
    ensures
        forall|x: int| holds(rs, x) ==> x >= rs[0].0,
{
    assert forall|x: int| holds(rs, x) implies x >= rs[0].0 by {
        let j = choose|j: int| 0 <= j < rs.len() && #[trigger] rs[j].0 <= x <= rs[j].1;
        if j > 0 {
            assert(rs[0].1 + 1 < rs[j].0);
            assert(rs[0].0 <= rs[0].1);
        }
    }
}

/// Dropping the oldest range.
proof fn lemma_drop(m: Seq<(u64, u64)>, n: Seq<(u64, u64)>)
    requires
        sorted(m),
        m.len() > 0,
        n == m.remove(0),
    ensures
        sorted(n),
        forall|x: int| #[trigger] holds(n, x) == (holds(m, x) && x >= m[0].1 + 1),
        n.len() > 0 ==> n[0].0 >= m[0].1 + 1,
        m[0].1 + 1 <= PN_LIMIT,
        m[0].0 <= m[0].1,
{
    assert(m[0].0 <= m[0].1 < PN_LIMIT);
    assert forall|k: int| 0 <= k < n.len() implies #[trigger] n[k] == m[k + 1] by {}
    assert forall|x: int| #[trigger] holds(n, x) == (holds(m, x) && x >= m[0].1 + 1) by {
        if holds(n, x) {
            let j = choose|j: int| 0 <= j < n.len() && #[trigger] n[j].0 <= x <= n[j].1;
            assert(n[j] == m[j + 1]);
            assert(m[0].1 + 1 < m[j + 1].0);
        }
        if holds(m, x) && x >= m[0].1 + 1 {
            let j = choose|j: int| 0 <= j < m.len() && #[trigger] m[j].0 <= x <= m[j].1;
            assert(j != 0);
            assert(n[j - 1] == m[j]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < n.len() implies #[trigger] n[a].1 + 1 < #[trigger] n[b].0 by {
        assert(n[a] == m[a + 1] && n[b] == m[b + 1]);
    }
    assert forall|a: int| 0 <= a < n.len() implies #[trigger] n[a].0 <= n[a].1 < PN_LIMIT by {
        assert(n[a] == m[a + 1]);
    }
    if n.len() > 0 {
        assert(n[0] == m[1]);
        assert(m[0].1 + 1 < m[1].0);
    }
}

} // verus!
