//! Sent packets, acknowledgments and loss detection in one packet number
//! space (RFC 9002 §6, Appendix A), proven.
//!
//! [`Sent`] records every packet sent in a space, in packet number order,
//! from the oldest one still outstanding. Packet numbers are never
//! skipped, so the packet numbered `pn` is at a fixed offset, and an ACK
//! frame costs time proportional to the packets it acknowledges, not to
//! the packets in flight. The theorems:
//!
//! - **packet numbers** are handed out in order, each once (`on_sent`),
//!   and stop before `2^62` (§12.3: a packet number is never reused);
//! - **acknowledgments** (`on_ack`): an ACK frame that acknowledges a
//!   packet number never sent is PROTOCOL_VIOLATION (RFC 9000 §13.1), and
//!   otherwise exactly the outstanding packets in its ranges become
//!   acknowledged, every other packet keeps its state, and the caller is
//!   handed exactly those packets, each once;
//! - **loss** (`detect_lost`, §6.1): exactly the outstanding packets sent
//!   before the largest acknowledged that are `kPacketThreshold` (3) or
//!   more packets older than it, or were sent `loss_delay` or longer ago,
//!   are declared lost ([`lost_rule`]), each handed to the caller once;
//!   the loss timer it returns is the earliest time another packet would
//!   meet the time threshold. Persistent congestion (§7.6.2) is reported
//!   only when two ack-eliciting packets declared lost in the call were
//!   sent at least the given duration apart with every packet between
//!   them lost as well;
//! - **bytes in flight** (§2, §B.2): the count is always the sum of the
//!   sizes of the outstanding in-flight packets ([`flight`]), so
//!   congestion control (`cc.rs`) sees exactly what the network holds.
//!
//! Times are microseconds on the caller's clock.
use vstd::prelude::*;

verus! {

/// PROTOCOL_VIOLATION (RFC 9000 §20.1).
pub const PROTOCOL_VIOLATION: u64 = 0x0a;

/// kPacketThreshold (§6.1.1).
pub const PACKET_THRESHOLD: u64 = 3;

/// The state of a packet sent.
pub const OUTSTANDING: u8 = 0;
/// See [`OUTSTANDING`].
pub const ACKED: u8 = 1;
/// See [`OUTSTANDING`].
pub const LOST: u8 = 2;

/// The largest packet number (RFC 9000 §12.3: `2^62 - 1`).
pub const PN_LIMIT: u64 = 0x4000_0000_0000_0000;

/// A packet sent.
#[derive(Clone, Copy, Debug)]
pub struct Packet {
    /// When it was sent.
    pub time: u64,
    /// Its size in bytes (the UDP payload it took).
    pub size: u32,
    /// The caller's: what was in it, to resend or forget.
    pub token: u64,
    /// It carries a frame other than ACK, PADDING or CONNECTION_CLOSE
    /// (RFC 9002 §2).
    pub eliciting: bool,
    /// It counts towards bytes in flight (§2): ack-eliciting or padded.
    pub in_flight: bool,
    /// [`OUTSTANDING`], [`ACKED`] or [`LOST`].
    pub state: u8,
}

/// The bytes a packet adds to bytes in flight.
pub open spec fn weight(p: Packet) -> nat {
    if p.state == OUTSTANDING && p.in_flight {
        p.size as nat
    } else {
        0
    }
}

/// Bytes in flight: the outstanding in-flight packets' sizes.
pub open spec fn flight(s: Seq<Packet>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        flight(s.drop_last()) + weight(s.last())
    }
}

proof fn lemma_flight_push(s: Seq<Packet>, p: Packet)
    ensures
        flight(s.push(p)) == flight(s) + weight(p),
{
    assert(s.push(p).drop_last() =~= s);
}

proof fn lemma_flight_update(s: Seq<Packet>, j: int, p: Packet)
    requires
        0 <= j < s.len(),
    ensures
        flight(s.update(j, p)) + weight(s[j]) == flight(s) + weight(p),
    decreases s.len(),
{
    if j == s.len() - 1 {
        assert(s.update(j, p).drop_last() =~= s.drop_last());
    } else {
        lemma_flight_update(s.drop_last(), j, p);
        assert(s.update(j, p).drop_last() =~= s.drop_last().update(j, p));
    }
}

proof fn lemma_flight_skip(s: Seq<Packet>)
    requires
        s.len() > 0,
    ensures
        flight(s) == weight(s[0]) + flight(s.skip(1)),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.skip(1) =~= Seq::<Packet>::empty());
        assert(s.drop_last() =~= Seq::<Packet>::empty());
    } else {
        lemma_flight_skip(s.drop_last());
        assert(s.drop_last().skip(1) =~= s.skip(1).drop_last());
    }
}

proof fn lemma_flight_bound(s: Seq<Packet>)
    ensures
        flight(s) <= s.len() * 0xffff_ffff,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_flight_bound(s.drop_last());
    }
}

/// An ACK frame's ranges, as packet numbers: `(smallest, largest)` pairs,
/// largest first, each below the one before with a gap (RFC 9000 §19.3.1).
pub open spec fn ranges_ok(rs: Seq<(u64, u64)>) -> bool {
    &&& rs.len() > 0
    &&& forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).0 <= rs[i].1
    &&& forall|i: int| 1 <= i < rs.len() ==> (#[trigger] rs[i]).1 + 1 < rs[i - 1].0
}

/// What `ack_range(lo, hi)` does, from packets `s1` (the first numbered
/// `b`) and `done` list `d1` to `s2` and `d2`.
pub open spec fn range_post(lo: int, hi: int, b: int, s1: Seq<Packet>, d1: Seq<Done>, s2: Seq<Packet>, d2: Seq<Done>) -> bool {
    &&& s2.len() == s1.len()
    &&& d2.len() >= d1.len()
    &&& d2.take(d1.len() as int) == d1
    &&& d2.len() <= d1.len() + s1.len()
    &&& forall|i: int|
        0 <= i < s1.len() ==> #[trigger] s2[i] == (Packet {
            state: if s1[i].state == OUTSTANDING && lo <= b + i <= hi { ACKED } else { s1[i].state },
            ..s1[i]
        })
    &&& forall|k: int|
        d1.len() <= k < d2.len() ==> {
            let p = (#[trigger] d2[k]).pn as int;
            &&& lo <= p <= hi
            &&& b <= p < b + s1.len()
            &&& s1[p - b] == d2[k].packet
            &&& d2[k].packet.state == OUTSTANDING
        }
    &&& forall|k: int, l: int| d1.len() <= k < l < d2.len() ==> (#[trigger] d2[k]).pn > (#[trigger] d2[l]).pn
    &&& forall|i: int|
        0 <= i < s1.len() && s1[i].state == OUTSTANDING && lo <= b + i <= hi ==> exists|k: int|
            d1.len() <= k < d2.len() && (#[trigger] d2[k]).pn == b + i
}

/// `on_ack`'s loop: after the first `j` ranges, from packets `v0` and
/// `done` list `d0`, the packets are `cur` and the list `d`.
#[verifier::opaque]
pub open spec fn ack_inv(rs: Seq<(u64, u64)>, j: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>, cur: Seq<Packet>, d: Seq<Done>) -> bool {
    &&& cur.len() == v0.len()
    &&& d0.len() <= d.len() <= d0.len() + v0.len()
    &&& d.take(d0.len() as int) == d0
    &&& forall|i: int|
        0 <= i < v0.len() ==> #[trigger] cur[i] == (Packet {
            state: if v0[i].state == OUTSTANDING && hit_before(rs, j, b0 + i) { ACKED } else { v0[i].state },
            ..v0[i]
        })
    &&& forall|k: int|
        d0.len() <= k < d.len() ==> {
            let p = (#[trigger] d[k]).pn as int;
            &&& b0 <= p < b0 + v0.len()
            &&& v0[p - b0] == d[k].packet
            &&& d[k].packet.state == OUTSTANDING
            &&& hit_before(rs, j, p)
            &&& j > 0 ==> p >= rs[j - 1].0
        }
    &&& j == 0 ==> d.len() == d0.len()
    &&& forall|k: int, l: int| d0.len() <= k < l < d.len() ==> (#[trigger] d[k]).pn > (#[trigger] d[l]).pn
    &&& forall|i: int|
        0 <= i < v0.len() && v0[i].state == OUTSTANDING && hit_before(rs, j, b0 + i) ==> exists|k: int|
            d0.len() <= k < d.len() && (#[trigger] d[k]).pn == b0 + i
}

proof fn lemma_ack_start(rs: Seq<(u64, u64)>, b0: int, v0: Seq<Packet>, d0: Seq<Done>)
    ensures
        ack_inv(rs, 0, b0, v0, d0, v0, d0),
{
    reveal(ack_inv);
    assert(d0.take(d0.len() as int) =~= d0);
    assert forall|i: int| 0 <= i < v0.len() implies #[trigger] v0[i] == (Packet {
        state: if v0[i].state == OUTSTANDING && hit_before(rs, 0, b0 + i) { ACKED } else { v0[i].state },
        ..v0[i]
    }) by {}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_ack_step(
    rs: Seq<(u64, u64)>,
    j: int,
    b0: int,
    v0: Seq<Packet>,
    d0: Seq<Done>,
    s1: Seq<Packet>,
    d1: Seq<Done>,
    s2: Seq<Packet>,
    d2: Seq<Done>,
)
    requires
        ranges_ok(rs),
        0 <= j < rs.len(),
        ack_inv(rs, j, b0, v0, d0, s1, d1),
        range_post(rs[j].0 as int, rs[j].1 as int, b0, s1, d1, s2, d2),
    ensures
        ack_inv(rs, j + 1, b0, v0, d0, s2, d2),
{
    reveal(ack_inv);
    let lo = rs[j].0 as int;
    let hi = rs[j].1 as int;
    assert forall|q: int| 0 <= q < j implies hi + 1 < (#[trigger] rs[q]).0 by {
        lemma_ranges_order(rs, q, j);
    }
    assert forall|p: int| hit_before(rs, j + 1, p) == (hit_before(rs, j, p) || (lo <= p <= hi)) by {
        if lo <= p <= hi {
            assert(rs[j].0 <= p <= rs[j].1);
        }
        if hit_before(rs, j + 1, p) && !(lo <= p <= hi) {
            let q = choose|q: int| 0 <= q < j + 1 && (#[trigger] rs[q]).0 <= p <= rs[q].1;
            assert(q < j);
        }
    }
    assert(d2.take(d0.len() as int) =~= d1.take(d0.len() as int));
    assert forall|k: int| 0 <= k < d1.len() implies #[trigger] d2[k] == d1[k] by {
        assert(d2.take(d1.len() as int)[k] == d2[k]);
    }
    // States.
    assert forall|i: int| 0 <= i < v0.len() implies #[trigger] s2[i] == (Packet {
        state: if v0[i].state == OUTSTANDING && hit_before(rs, j + 1, b0 + i) { ACKED } else { v0[i].state },
        ..v0[i]
    }) by {
        assert(s1[i] == (Packet {
            state: if v0[i].state == OUTSTANDING && hit_before(rs, j, b0 + i) { ACKED } else { v0[i].state },
            ..v0[i]
        }));
        if hit_before(rs, j, b0 + i) {
            let q = choose|q: int| 0 <= q < j && (#[trigger] rs[q]).0 <= b0 + i <= rs[q].1;
            assert(hi + 1 < rs[q].0);
        }
    }
    // The list.
    assert forall|k: int| d0.len() <= k < d2.len() implies {
        let p = (#[trigger] d2[k]).pn as int;
        &&& b0 <= p < b0 + v0.len()
        &&& v0[p - b0] == d2[k].packet
        &&& d2[k].packet.state == OUTSTANDING
        &&& hit_before(rs, j + 1, p)
        &&& p >= rs[j].0
    } by {
        let p = d2[k].pn as int;
        if k < d1.len() {
            assert(d2[k] == d1[k]);
            if j > 0 {
                lemma_ranges_order(rs, j - 1, j);
            }
        } else {
            assert(s1[p - b0] == d2[k].packet);
            assert(s1[p - b0].state == OUTSTANDING);
            assert(p - b0 < s1.len());
            assert(s1[p - b0] == (Packet {
                state: if v0[p - b0].state == OUTSTANDING && hit_before(rs, j, b0 + (p - b0)) { ACKED } else { v0[p - b0].state },
                ..v0[p - b0]
            }));
            assert(rs[j].0 <= p <= rs[j].1);
        }
    }
    assert forall|k: int, l: int| d0.len() <= k < l < d2.len() implies (#[trigger] d2[k]).pn > (#[trigger] d2[l]).pn by {
        if l < d1.len() {
            assert(d2[k] == d1[k] && d2[l] == d1[l]);
        } else if k < d1.len() {
            assert(d2[k] == d1[k]);
            if j > 0 {
                lemma_ranges_order(rs, j - 1, j);
            }
        }
    }
    let nd = d2.skip(d0.len() as int);
    assert forall|k: int, l: int| 0 <= k < l < nd.len() implies (#[trigger] nd[k]).pn > (#[trigger] nd[l]).pn by {
        assert(nd[k] == d2[d0.len() + k] && nd[l] == d2[d0.len() + l]);
        assert(d2[d0.len() + k].pn > d2[d0.len() + l].pn);
    }
    assert forall|k: int| 0 <= k < nd.len() implies b0 <= (#[trigger] nd[k]).pn < b0 + v0.len() by {
        assert(nd[k] == d2[d0.len() + k]);
    }
    lemma_desc_count(nd, b0, b0 + v0.len());
    assert forall|i: int| 0 <= i < v0.len() && v0[i].state == OUTSTANDING && hit_before(rs, j + 1, b0 + i) implies exists|k: int|
        d0.len() <= k < d2.len() && (#[trigger] d2[k]).pn == b0 + i by {
        if hit_before(rs, j, b0 + i) {
            let k = choose|k: int| d0.len() <= k < d1.len() && (#[trigger] d1[k]).pn == b0 + i;
            assert(d2[k] == d1[k]);
        } else {
            assert(s1[i].state == OUTSTANDING);
            let k = choose|k: int| d1.len() <= k < d2.len() && (#[trigger] d2[k]).pn == b0 + i;
            assert(d0.len() <= k);
        }
    }
}

/// What `on_ack(rs)` does, from packets `v0` (the first numbered `b0`)
/// and `done` list `d0` to packets `v1` (the first numbered `b1`) and
/// list `d`:
///
/// - each packet is acknowledged iff it was outstanding and is in a
///   range, and keeps its state otherwise; only packets no longer
///   outstanding are dropped, from the front;
/// - `d` gets exactly the packets newly acknowledged, each once.
pub open spec fn ack_post(rs: Seq<(u64, u64)>, b0: int, v0: Seq<Packet>, d0: Seq<Done>, b1: int, v1: Seq<Packet>, d: Seq<Done>) -> bool {
    let nd = d.skip(d0.len() as int);
    &&& d.len() >= d0.len()
    &&& d.take(d0.len() as int) == d0
    &&& b1 >= b0
    &&& v1.len() == v0.len() - (b1 - b0)
    &&& forall|i: int|
        0 <= i < v0.len() ==> {
            let after = if (#[trigger] v0[i]).state == OUTSTANDING && in_ranges(rs, b0 + i) {
                ACKED
            } else {
                v0[i].state
            };
            &&& i >= b1 - b0 ==> v1[i - (b1 - b0)] == (Packet { state: after, ..v0[i] })
            &&& i < b1 - b0 ==> after != OUTSTANDING
        }
    &&& forall|k: int|
        0 <= k < nd.len() ==> {
            let pn = (#[trigger] nd[k]).pn as int;
            &&& b0 <= pn < b0 + v0.len()
            &&& v0[pn - b0] == nd[k].packet
            &&& nd[k].packet.state == OUTSTANDING
            &&& in_ranges(rs, pn)
        }
    &&& forall|k: int, l: int| 0 <= k < l < nd.len() ==> (#[trigger] nd[k]).pn != (#[trigger] nd[l]).pn
    &&& forall|i: int|
        0 <= i < v0.len() && v0[i].state == OUTSTANDING && in_ranges(rs, b0 + i) ==> exists|k: int|
            0 <= k < nd.len() && (#[trigger] nd[k]).pn == b0 + i
}

#[verifier::spinoff_prover]
proof fn lemma_ack_end(rs: Seq<(u64, u64)>, b0: int, v0: Seq<Packet>, d0: Seq<Done>, mid: Seq<Packet>, d: Seq<Done>, b1: int, v1: Seq<Packet>)
    requires
        ack_inv(rs, rs.len() as int, b0, v0, d0, mid, d),
        b0 <= b1 <= b0 + mid.len(),
        v1 == mid.skip(b1 - b0),
        forall|i: int| 0 <= i < b1 - b0 ==> (#[trigger] mid[i]).state != OUTSTANDING,
    ensures
        ack_post(rs, b0, v0, d0, b1, v1, d),
{
    reveal(ack_inv);
    let n = rs.len() as int;
    assert forall|p: int| in_ranges(rs, p) == hit_before(rs, n, p) by {}
    let nd = d.skip(d0.len() as int);
    assert forall|k: int| 0 <= k < nd.len() implies #[trigger] nd[k] == d[d0.len() + k] by {}
    assert forall|i: int| 0 <= i < v0.len() implies {
            let after = if (#[trigger] v0[i]).state == OUTSTANDING && in_ranges(rs, b0 + i) {
                ACKED
            } else {
                v0[i].state
            };
            &&& i >= b1 - b0 ==> v1[i - (b1 - b0)] == (Packet { state: after, ..v0[i] })
            &&& i < b1 - b0 ==> after != OUTSTANDING
        } by {
        assert(mid[i] == (Packet {
            state: if v0[i].state == OUTSTANDING && hit_before(rs, n, b0 + i) { ACKED } else { v0[i].state },
            ..v0[i]
        }));
        if i >= b1 - b0 {
            assert(v1[i - (b1 - b0)] == mid[i]);
        }
    }
    assert forall|k: int, l: int| 0 <= k < l < nd.len() implies (#[trigger] nd[k]).pn != (#[trigger] nd[l]).pn by {
        assert(d[d0.len() + k].pn > d[d0.len() + l].pn);
    }
    assert forall|i: int| 0 <= i < v0.len() && v0[i].state == OUTSTANDING && in_ranges(rs, b0 + i) implies exists|k: int|
            0 <= k < nd.len() && (#[trigger] nd[k]).pn == b0 + i by {
        let k = choose|k: int| d0.len() <= k < d.len() && (#[trigger] d[k]).pn == b0 + i;
        assert(nd[k - d0.len()] == d[k]);
    }
}

/// What loss detection found.
#[derive(Clone, Copy, Debug)]
pub struct Loss {
    /// When the next packet would be lost by the time threshold, for the
    /// loss timer (§6.1.2, `loss_time`).
    pub timer: Option<u64>,
    /// Persistent congestion (§7.6), as `detect_lost` states it.
    pub persistent: bool,
}

/// When a packet sent at `p.time` meets the time threshold (saturating).
pub open spec fn deadline(p: Packet, delay: int) -> int {
    if p.time + delay > u64::MAX {
        u64::MAX as int
    } else {
        p.time + delay
    }
}

/// A packet after loss detection.
pub open spec fn lost_state(p: Packet, pn: int, lg: int, now: int, delay: int) -> Packet {
    if lost_rule(p, pn, lg, now, delay) {
        Packet { state: LOST, ..p }
    } else {
        p
    }
}

/// An outstanding packet below the largest acknowledged that is not lost
/// yet: the loss timer waits for it.
pub open spec fn candidate(p: Packet, pn: int, lg: int, now: int, delay: int) -> bool {
    p.state == OUTSTANDING && pn < lg && !lost_rule(p, pn, lg, now, delay)
}

/// What `detect_lost` does, from packets `v0` (the first numbered `b0`)
/// and `done` list `d0` to `v1` (the first numbered `b1`) and `d`, with
/// largest acknowledged `lg`: each packet becomes `lost_state`, only
/// packets no longer outstanding are dropped, and `d` gets exactly the
/// packets newly lost, in order.
pub open spec fn loss_post(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>, b1: int, v1: Seq<Packet>, d: Seq<Done>) -> bool {
    let nd = d.skip(d0.len() as int);
    &&& d.len() >= d0.len()
    &&& d.take(d0.len() as int) == d0
    &&& b1 >= b0
    &&& v1.len() == v0.len() - (b1 - b0)
    &&& forall|i: int|
        0 <= i < v0.len() ==> {
            let after = lost_state(#[trigger] v0[i], b0 + i, lg, now, delay);
            &&& i >= b1 - b0 ==> v1[i - (b1 - b0)] == after
            &&& i < b1 - b0 ==> after.state != OUTSTANDING
        }
    &&& forall|k: int|
        0 <= k < nd.len() ==> {
            let pn = (#[trigger] nd[k]).pn as int;
            &&& b0 <= pn < b0 + v0.len()
            &&& v0[pn - b0] == nd[k].packet
            &&& lost_rule(nd[k].packet, pn, lg, now, delay)
        }
    &&& forall|k: int, l: int| 0 <= k < l < nd.len() ==> (#[trigger] nd[k]).pn < (#[trigger] nd[l]).pn
    &&& forall|i: int|
        0 <= i < v0.len() && lost_rule(v0[i], b0 + i, lg, now, delay) ==> exists|k: int|
            0 <= k < nd.len() && (#[trigger] nd[k]).pn == b0 + i
}

/// The loss timer is the earliest deadline of the packets it waits for.
pub open spec fn timer_post(t: Option<u64>, lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>) -> bool {
    &&& t matches Some(x) ==> exists|i: int|
        0 <= i < v0.len() && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) && deadline(v0[i], delay) == x
    &&& forall|i: int|
        0 <= i < v0.len() && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) ==> (t matches Some(x) && x
            <= deadline(v0[i], delay))
}

#[verifier::opaque]
pub open spec fn loss_inv(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>, c: int, cur: Seq<Packet>, d: Seq<Done>) -> bool {
    &&& cur.len() == v0.len()
    &&& d0.len() <= d.len() <= d0.len() + (c - b0)
    &&& d.take(d0.len() as int) == d0
    &&& forall|i: int|
        0 <= i < v0.len() ==> #[trigger] cur[i] == if b0 + i < c {
            lost_state(v0[i], b0 + i, lg, now, delay)
        } else {
            v0[i]
        }
    &&& forall|k: int|
        d0.len() <= k < d.len() ==> {
            let p = (#[trigger] d[k]).pn as int;
            &&& b0 <= p < c
            &&& p < b0 + v0.len()
            &&& v0[p - b0] == d[k].packet
            &&& lost_rule(d[k].packet, p, lg, now, delay)
        }
    &&& forall|k: int, l: int| d0.len() <= k < l < d.len() ==> (#[trigger] d[k]).pn < (#[trigger] d[l]).pn
    &&& forall|i: int|
        0 <= i < v0.len() && b0 + i < c && lost_rule(v0[i], b0 + i, lg, now, delay) ==> exists|k: int|
            d0.len() <= k < d.len() && (#[trigger] d[k]).pn == b0 + i
}

#[verifier::opaque]
pub open spec fn timer_inv(t: Option<u64>, lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, c: int) -> bool {
    &&& t matches Some(x) ==> exists|i: int|
        0 <= i < v0.len() && b0 + i < c && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) && deadline(v0[i], delay)
            == x
    &&& forall|i: int|
        0 <= i < v0.len() && b0 + i < c && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) ==> (t matches Some(x)
            && x <= deadline(v0[i], delay))
}

proof fn lemma_loss_start(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>)
    ensures
        loss_inv(lg, now, delay, b0, v0, d0, b0, v0, d0),
        timer_inv(None, lg, now, delay, b0, v0, b0),
{
    reveal(loss_inv);
    reveal(timer_inv);
    assert(d0.take(d0.len() as int) =~= d0);
}

proof fn lemma_loss_none(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>)
    requires
        lg <= b0,
    ensures
        loss_post(lg, now, delay, b0, v0, d0, b0, v0, d0),
        timer_post(None, lg, now, delay, b0, v0),
{
    assert(d0.take(d0.len() as int) =~= d0);
    assert(v0.skip(0) =~= v0);
    assert forall|i: int| 0 <= i < v0.len() implies lost_state(#[trigger] v0[i], b0 + i, lg, now, delay) == v0[i] by {}
}

proof fn lemma_loss_at(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>, c: int, cur: Seq<Packet>, d: Seq<Done>)
    requires
        loss_inv(lg, now, delay, b0, v0, d0, c, cur, d),
        b0 <= c < b0 + v0.len(),
    ensures
        cur[c - b0] == v0[c - b0],
        cur.len() == v0.len(),
        d.len() <= d0.len() + (c - b0),
        d.len() >= d0.len(),
{
    reveal(loss_inv);
    assert(cur[c - b0] == v0[c - b0]);
}

proof fn lemma_loss_keep(lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, d0: Seq<Done>, c: int, cur: Seq<Packet>, d: Seq<Done>)
    requires
        loss_inv(lg, now, delay, b0, v0, d0, c, cur, d),
        b0 <= c < b0 + v0.len(),
        !lost_rule(v0[c - b0], c, lg, now, delay),
    ensures
        loss_inv(lg, now, delay, b0, v0, d0, c + 1, cur, d),
{
    reveal(loss_inv);
    assert forall|i: int| 0 <= i < v0.len() implies #[trigger] cur[i] == if b0 + i < c + 1 {
        lost_state(v0[i], b0 + i, lg, now, delay)
    } else {
        v0[i]
    } by {
        if b0 + i == c {
            assert(cur[i] == v0[i]);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_loss_lost(
    lg: int,
    now: int,
    delay: int,
    b0: int,
    v0: Seq<Packet>,
    d0: Seq<Done>,
    c: int,
    cur: Seq<Packet>,
    d: Seq<Done>,
    cur2: Seq<Packet>,
    d2: Seq<Done>,
)
    requires
        loss_inv(lg, now, delay, b0, v0, d0, c, cur, d),
        b0 <= c < b0 + v0.len(),
        0 <= c < PN_LIMIT,
        lost_rule(cur[c - b0], c, lg, now, delay),
        cur2 == cur.update(c - b0, Packet { state: LOST, ..cur[c - b0] }),
        d2 == d.push(Done { pn: c as u64, packet: cur[c - b0] }),
    ensures
        loss_inv(lg, now, delay, b0, v0, d0, c + 1, cur2, d2),
{
    reveal(loss_inv);
    assert(cur[c - b0] == v0[c - b0]);
    assert(d2.take(d0.len() as int) =~= d.take(d0.len() as int));
    assert forall|k: int| 0 <= k < d.len() implies #[trigger] d2[k] == d[k] by {}
    assert forall|i: int| 0 <= i < v0.len() implies #[trigger] cur2[i] == if b0 + i < c + 1 {
        lost_state(v0[i], b0 + i, lg, now, delay)
    } else {
        v0[i]
    } by {
        if b0 + i != c {
            assert(cur2[i] == cur[i]);
        }
    }
    assert forall|k: int, l: int| d0.len() <= k < l < d2.len() implies (#[trigger] d2[k]).pn < (#[trigger] d2[l]).pn by {
        if l == d.len() {
            assert(d2[k] == d[k]);
        } else {
            assert(d2[k] == d[k] && d2[l] == d[l]);
        }
    }
    assert forall|i: int| 0 <= i < v0.len() && b0 + i < c + 1 && lost_rule(v0[i], b0 + i, lg, now, delay) implies exists|k: int|
            d0.len() <= k < d2.len() && (#[trigger] d2[k]).pn == b0 + i by {
        if b0 + i == c {
            assert(d2[d.len() as int].pn == c);
        } else {
            let k = choose|k: int| d0.len() <= k < d.len() && (#[trigger] d[k]).pn == b0 + i;
            assert(d2[k] == d[k]);
        }
    }
}

proof fn lemma_timer_skip(t: Option<u64>, lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, c: int)
    requires
        timer_inv(t, lg, now, delay, b0, v0, c),
        b0 <= c < b0 + v0.len(),
        !candidate(v0[c - b0], c, lg, now, delay),
    ensures
        timer_inv(t, lg, now, delay, b0, v0, c + 1),
{
    reveal(timer_inv);
    if t is Some {
        let i = choose|i: int| 0 <= i < v0.len() && b0 + i < c && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) && deadline(v0[i], delay) == t.unwrap();
        assert(b0 + i < c + 1);
    }
}

proof fn lemma_timer_add(t: Option<u64>, t2: Option<u64>, lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, c: int)
    requires
        timer_inv(t, lg, now, delay, b0, v0, c),
        b0 <= c < b0 + v0.len(),
        delay >= 0,
        candidate(v0[c - b0], c, lg, now, delay),
        t2 == Some(match t {
            Some(x) => if x <= deadline(v0[c - b0], delay) { x } else { deadline(v0[c - b0], delay) as u64 },
            None => deadline(v0[c - b0], delay) as u64,
        }),
    ensures
        timer_inv(t2, lg, now, delay, b0, v0, c + 1),
{
    reveal(timer_inv);
    let j = c - b0;
    assert(0 <= deadline(v0[j], delay) <= u64::MAX) by {
        assert(v0[j].time >= 0);
    }

    match t {
        Some(x) => {
            let i = choose|i: int| 0 <= i < v0.len() && b0 + i < c && candidate(#[trigger] v0[i], b0 + i, lg, now, delay) && deadline(v0[i], delay) == x;
            if x <= deadline(v0[j], delay) {
                assert(b0 + i < c + 1);
            } else {
                assert(candidate(v0[j], b0 + j, lg, now, delay));
            }
        },
        None => {
            assert(candidate(v0[j], b0 + j, lg, now, delay));
        },
    }
}

proof fn lemma_timer_end(t: Option<u64>, lg: int, now: int, delay: int, b0: int, v0: Seq<Packet>, c: int)
    requires
        timer_inv(t, lg, now, delay, b0, v0, c),
        c >= lg,
    ensures
        timer_post(t, lg, now, delay, b0, v0),
{
    reveal(timer_inv);
}

#[verifier::spinoff_prover]
proof fn lemma_loss_end(
    lg: int,
    now: int,
    delay: int,
    b0: int,
    v0: Seq<Packet>,
    d0: Seq<Done>,
    c: int,
    mid: Seq<Packet>,
    d: Seq<Done>,
    b1: int,
    v1: Seq<Packet>,
)
    requires
        loss_inv(lg, now, delay, b0, v0, d0, c, mid, d),
        c >= lg,
        b0 <= b1 <= b0 + mid.len(),
        v1 == mid.skip(b1 - b0),
        forall|i: int| 0 <= i < b1 - b0 ==> (#[trigger] mid[i]).state != OUTSTANDING,
    ensures
        loss_post(lg, now, delay, b0, v0, d0, b1, v1, d),
{
    reveal(loss_inv);
    let nd = d.skip(d0.len() as int);
    assert forall|k: int| 0 <= k < nd.len() implies #[trigger] nd[k] == d[d0.len() + k] by {}
    assert forall|i: int| 0 <= i < v0.len() implies {
        let after = lost_state(#[trigger] v0[i], b0 + i, lg, now, delay);
        &&& i >= b1 - b0 ==> v1[i - (b1 - b0)] == after
        &&& i < b1 - b0 ==> after.state != OUTSTANDING
    } by {
        assert(mid[i] == if b0 + i < c { lost_state(v0[i], b0 + i, lg, now, delay) } else { v0[i] });
        if i >= b1 - b0 {
            assert(v1[i - (b1 - b0)] == mid[i]);
        }
    }
    assert forall|k: int, l: int| 0 <= k < l < nd.len() implies (#[trigger] nd[k]).pn < (#[trigger] nd[l]).pn by {
        assert(d[d0.len() + k].pn < d[d0.len() + l].pn);
    }
    assert forall|i: int| 0 <= i < v0.len() && lost_rule(v0[i], b0 + i, lg, now, delay) implies exists|k: int|
            0 <= k < nd.len() && (#[trigger] nd[k]).pn == b0 + i by {
        let k = choose|k: int| d0.len() <= k < d.len() && (#[trigger] d[k]).pn == b0 + i;
        assert(nd[k - d0.len()] == d[k]);
    }
}

/// Strictly decreasing packet numbers in `[a, b)` are at most `b - a`.
proof fn lemma_desc_count(d: Seq<Done>, a: int, b: int)
    requires
        forall|k: int, l: int| 0 <= k < l < d.len() ==> (#[trigger] d[k]).pn > (#[trigger] d[l]).pn,
        forall|k: int| 0 <= k < d.len() ==> a <= (#[trigger] d[k]).pn < b,
    ensures
        d.len() <= if b > a { b - a } else { 0 },
    decreases d.len(),
{
    if d.len() > 0 {
        let e = d.drop_last();
        let last = d.len() - 1;
        let m = d[last].pn as int;
        assert forall|k: int| 0 <= k < e.len() implies a <= #[trigger] e[k].pn as int by {
            assert(e[k] == d[k]);
        }
        assert forall|k: int| 0 <= k < e.len() implies #[trigger] e[k].pn as int > m by {
            assert(e[k] == d[k]);
            assert(d[k].pn > d[last].pn);
        }
        assert forall|k: int, l: int| 0 <= k < l < e.len() implies (#[trigger] e[k]).pn > (#[trigger] e[l]).pn by {
            assert(e[k] == d[k] && e[l] == d[l]);
        }
        assert forall|k: int| 0 <= k < e.len() implies m + 1 <= (#[trigger] e[k]).pn < b by {
            assert(e[k] == d[k]);
            assert(e[k].pn as int > m);
        }
        assert(a <= m < b);
        lemma_desc_count(e, m + 1, b);
    }
}

/// Ranges further down are below: `rs[j]` is below `rs[q]` for `q < j`.
proof fn lemma_ranges_order(rs: Seq<(u64, u64)>, q: int, j: int)
    requires
        ranges_ok(rs),
        0 <= q < j < rs.len(),
    ensures
        rs[j].1 + 1 < rs[q].0,
        rs[j].1 < rs[q].1,
    decreases j - q,
{
    assert(rs[j].1 + 1 < rs[j - 1].0);
    if q < j - 1 {
        lemma_ranges_order(rs, q, j - 1);
        assert(rs[j - 1].0 <= rs[j - 1].1);
    }
}

/// `pn` is in one of the first `j` ranges.
pub open spec fn hit_before(rs: Seq<(u64, u64)>, j: int, pn: int) -> bool {
    exists|q: int| 0 <= q < j && (#[trigger] rs[q]).0 <= pn <= rs[q].1
}

/// `pn` is in one of the ranges.
pub open spec fn in_ranges(rs: Seq<(u64, u64)>, pn: int) -> bool {
    exists|i: int| 0 <= i < rs.len() && (#[trigger] rs[i]).0 <= pn <= rs[i].1
}

/// §6.1: an outstanding packet sent before the largest acknowledged one
/// is lost once it is `kPacketThreshold` packets older, or was sent
/// `delay` or longer before `now`.
pub open spec fn lost_rule(p: Packet, pn: int, largest: int, now: int, delay: int) -> bool {
    &&& p.state == OUTSTANDING
    &&& pn < largest
    &&& (pn + PACKET_THRESHOLD <= largest || p.time + delay <= now)
}

/// A packet acknowledged or declared lost, with its number.
#[derive(Clone, Copy, Debug)]
pub struct Done {
    /// Its packet number.
    pub pn: u64,
    /// The packet, as it was before.
    pub packet: Packet,
}

/// What an ACK frame told.
#[derive(Clone, Copy, Debug)]
pub struct AckInfo {
    /// The largest packet it acknowledged was newly acknowledged: its send
    /// time, for an RTT sample (§5.1), and whether it was ack-eliciting.
    pub largest_new: Option<(u64, bool)>,
    /// A newly acknowledged packet was ack-eliciting.
    pub eliciting: bool,
}

/// The packets sent in one packet number space.
pub struct Sent {
    pkts: Vec<Packet>,
    /// `pkts[start..]` are the packets numbered `base..next`.
    start: usize,
    base: u64,
    next: u64,
    largest_acked: Option<u64>,
    in_flight: u64,
    /// Outstanding ack-eliciting packets, and when the last was sent.
    eliciting: u64,
    last_eliciting: u64,
}

impl Sent {
    /// The packets, `[i]` numbered `base() + i`.
    pub closed spec fn view(&self) -> Seq<Packet> {
        self.pkts@.subrange(self.start as int, self.pkts@.len() as int)
    }

    /// The number of the oldest packet kept.
    pub closed spec fn base(&self) -> nat {
        self.base as nat
    }

    /// The number the next packet gets.
    pub closed spec fn next(&self) -> nat {
        self.next as nat
    }

    /// The largest packet number acknowledged.
    pub closed spec fn largest(&self) -> Option<u64> {
        self.largest_acked
    }

    /// Bytes in flight.
    pub closed spec fn bytes(&self) -> nat {
        self.in_flight as nat
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.core()
        &&& self.view().len() > 0 ==> self.view()[0].state == OUTSTANDING
    }

    /// `inv` but for the front: in the middle of `on_ack` and
    /// `detect_lost`, before `drain`.
    closed spec fn core(&self) -> bool {
        let v = self.view();
        &&& self.start <= self.pkts@.len()
        &&& self.next as nat == self.base as nat + v.len()
        &&& self.next <= PN_LIMIT
        &&& self.in_flight as nat == flight(v)
        &&& forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).state <= LOST
        &&& self.largest_acked matches Some(l) ==> l < self.next
        &&& self.pkts@.len() < 0x1_0000_0000
        &&& self.eliciting <= v.len()
    }

    /// No packets sent.
    pub fn new() -> (r: Sent)
        ensures
            r.inv(),
            r@.len() == 0,
            r.next() == 0,
            r.bytes() == 0,
            r.largest() is None,
    {
        let r = Sent { pkts: Vec::new(), start: 0, base: 0, next: 0, largest_acked: None, in_flight: 0, eliciting: 0, last_eliciting: 0 };
        assert(r@ =~= Seq::<Packet>::empty());
        r
    }

    /// Bytes in flight.
    pub fn bytes_in_flight(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.bytes(),
    {
        self.in_flight
    }

    /// The number the next packet gets.
    pub fn next_pn(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.next(),
    {
        self.next
    }

    /// The largest packet number acknowledged.
    pub fn largest_acked(&self) -> (r: Option<u64>)
        ensures
            r == self.largest(),
    {
        self.largest_acked
    }

    /// Whether an ack-eliciting packet may be outstanding, and when the
    /// last one was sent (for the PTO, §6.2.1).
    pub fn eliciting_in_flight(&self) -> (r: Option<u64>) {
        if self.eliciting > 0 {
            Some(self.last_eliciting)
        } else {
            None
        }
    }

    /// Records a packet sent now and returns its number; `None` once
    /// packet numbers are used up (the connection must close) or too many
    /// are outstanding.
    pub fn on_sent(&mut self, time: u64, size: u32, eliciting: bool, in_flight: bool, token: u64) -> (r: Option<u64>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).base() == old(self).base(),
            final(self).largest() == old(self).largest(),
            match r {
                Some(pn) => {
                    &&& pn == old(self).next()
                    &&& final(self).next() == pn + 1
                    &&& final(self)@ == old(self)@.push(
                        Packet { time, size, token, eliciting, in_flight, state: OUTSTANDING },
                    )
                    &&& final(self).bytes() == old(self).bytes() + if in_flight { size as nat } else { 0 }
                },
                None => *final(self) == *old(self),
            },
    {
        if self.next >= PN_LIMIT - 1 || self.pkts.len() >= 0xffff_0000 {
            return None;
        }
        let p = Packet { time, size, token, eliciting, in_flight, state: OUTSTANDING };
        let add: u64 = if in_flight { size as u64 } else { 0 };
        proof {
            lemma_flight_bound(self@);
            assert(self.in_flight as nat <= self@.len() * 0xffff_ffff);
            assert(self@.len() * 0xffff_ffff <= 0x1_0000_0000 * 0xffff_ffff) by (nonlinear_arith)
                requires
                    self@.len() <= 0x1_0000_0000,
            ;
        }
        let ghost v0 = self@;
        if self.start == self.pkts.len() {
            // Nothing kept: the new packet is the oldest.
            self.base = self.next;
        }
        self.pkts.push(p);
        self.in_flight = self.in_flight + add;
        if eliciting {
            self.eliciting = self.eliciting + 1;
            self.last_eliciting = time;
        }
        let pn = self.next;
        self.next = self.next + 1;
        proof {
            assert(self@ =~= v0.push(p));
            lemma_flight_push(v0, p);
        }
        Some(pn)
    }

    /// Drops the packets at the front that are no longer outstanding.
    fn drain(&mut self)
        requires
            old(self).core(),
        ensures
            final(self).inv(),
            final(self).next() == old(self).next(),
            final(self).largest() == old(self).largest(),
            final(self).bytes() == old(self).bytes(),
            final(self).base() >= old(self).base(),
            // What is dropped was not outstanding; the rest is unchanged.
            final(self)@ == old(self)@.skip(final(self).base() - old(self).base()),
            forall|i: int| 0 <= i < final(self).base() - old(self).base() ==> (#[trigger] old(self)@[i]).state
                != OUTSTANDING,
    {
        let ghost v0 = self@;
        while self.start < self.pkts.len() && self.pkts[self.start].state != OUTSTANDING
            invariant
                self.start <= self.pkts@.len(),
                self.next as nat == self.base as nat + self@.len(),
                self.next == old(self).next,
                self.next <= PN_LIMIT,
                self.base >= old(self).base,
                self.in_flight == old(self).in_flight,
                self.in_flight as nat == flight(self@),
                self.pkts@ == old(self).pkts@,
                self.base - old(self).base <= v0.len(),
                self@ == v0.skip(self.base - old(self).base),
                forall|i: int| 0 <= i < self.base - old(self).base ==> (#[trigger] v0[i]).state != OUTSTANDING,
                forall|i: int| 0 <= i < self@.len() ==> (#[trigger] self@[i]).state <= LOST,
                self.eliciting == old(self).eliciting,
                self.largest_acked == old(self).largest_acked,
                self.pkts@.len() < 0x1_0000_0000,
            decreases self.pkts@.len() - self.start,
        {
            let ghost v = self@;
            let ghost d = self.base - old(self).base;
            proof {
                lemma_flight_skip(v);
                assert(v[0] == self.pkts@[self.start as int]);
                assert(v[0] == v0[d]);
            }
            self.start = self.start + 1;
            self.base = self.base + 1;
            proof {
                assert(self@ =~= v.skip(1));
                assert(v0.skip(d + 1) =~= v0.skip(d).skip(1));
            }
        }
        if self.eliciting > (self.pkts.len() - self.start) as u64 {
            // Only an upper bound is kept (packets left the count when
            // they were acknowledged or lost); never more than are left.
            self.eliciting = (self.pkts.len() - self.start) as u64;
        }
        // Reclaim the space once most of the vector is dropped packets.
        if self.start >= 4096 && self.start >= self.pkts.len() / 2 {
            let mut v: Vec<Packet> = Vec::with_capacity(self.pkts.len() - self.start + 64);
            let mut i = self.start;
            while i < self.pkts.len()
                invariant
                    self.start <= i <= self.pkts@.len(),
                    v@ == self.pkts@.subrange(self.start as int, i as int),
                decreases self.pkts@.len() - i,
            {
                v.push(self.pkts[i]);
                proof {
                    assert(v@ =~= self.pkts@.subrange(self.start as int, i + 1));
                }
                i = i + 1;
            }
            let ghost before = self@;
            self.pkts = v;
            self.start = 0;
            assert(self@ =~= before);
        }
    }

    /// Acknowledges packet `pn`, if outstanding, handing it to `done`.
    fn ack_one(&mut self, pn: u64, done: &mut Vec<Done>, info: &mut AckInfo, largest: bool)
        requires
            old(self).core(),
            old(self).base() <= pn < old(self).next(),
            old(done)@.len() < usize::MAX,
        ensures
            final(self).core(),
            final(self).base() == old(self).base(),
            final(self).next() == old(self).next(),
            final(self).largest() == old(self).largest(),
            ({
                let i = pn - old(self).base();
                let p = old(self)@[i];
                if p.state == OUTSTANDING {
                    &&& final(self)@ == old(self)@.update(i, Packet { state: ACKED, ..p })
                    &&& final(done)@ == old(done)@.push(Done { pn, packet: p })
                } else {
                    &&& final(self)@ == old(self)@
                    &&& final(done)@ == old(done)@
                }
            }),
    {
        let idx = self.start + (pn - self.base) as usize;
        let p = self.pkts[idx];
        if p.state != OUTSTANDING {
            return;
        }
        let ghost v = self@;
        let mut q = p;
        q.state = ACKED;
        self.pkts.set(idx, q);
        proof {
            assert(self@ =~= v.update(pn - self.base, q));
            lemma_flight_update(v, pn - self.base, q);
        }
        if p.in_flight {
            self.in_flight = self.in_flight - p.size as u64;
        }
        if p.eliciting {
            info.eliciting = true;
            if self.eliciting > 0 {
                self.eliciting = self.eliciting - 1;
            }
        }
        if largest {
            info.largest_new = Some((p.time, p.eliciting));
        }
        done.push(Done { pn, packet: p });
    }

    /// Acknowledges the outstanding packets numbered `lo..=hi`, largest
    /// first.
    fn ack_range(&mut self, lo: u64, hi: u64, done: &mut Vec<Done>, info: &mut AckInfo, first: bool)
        requires
            old(self).core(),
            lo <= hi < old(self).next(),
            old(done)@.len() + old(self)@.len() <= usize::MAX,
        ensures
            final(self).core(),
            final(self).base() == old(self).base(),
            final(self).next() == old(self).next(),
            final(self).largest() == old(self).largest(),
            range_post(lo as int, hi as int, old(self).base() as int, old(self)@, old(done)@, final(self)@, final(done)@),
    {
        if hi < self.base {
            proof {
                assert(done@.take(done@.len() as int) =~= done@);
                assert forall|i: int| 0 <= i < self@.len() implies #[trigger] self@[i] == (Packet { state: self@[i].state, ..self@[i] }) by {}
            }
            return;
        }
        let ghost v0 = self@;
        let ghost d0 = done@;
        let ghost b0 = self.base as int;
        let from = if lo > self.base { lo } else { self.base };
        let mut c = hi + 1;
        while c > from
            invariant
                self.core(),
                self.base == b0,
                b0 <= from <= c <= hi + 1,
                from >= lo,
                lo <= hi,
                hi < self.next,
                self.next == old(self).next,
                self.largest_acked == old(self).largest_acked,
                self@.len() == v0.len(),
                d0 == old(done)@,
                v0 == old(self)@,
                d0.len() <= done@.len() <= d0.len() + (hi + 1 - c),
                hi + 1 - from <= v0.len(),
                d0.len() + v0.len() <= usize::MAX,
                done@.take(d0.len() as int) == d0,
                forall|i: int|
                    0 <= i < v0.len() ==> #[trigger] self@[i] == (Packet {
                        state: if v0[i].state == OUTSTANDING && c <= b0 + i <= hi { ACKED } else { v0[i].state },
                        ..v0[i]
                    }),
                forall|k: int|
                    d0.len() <= k < done@.len() ==> {
                        let p = (#[trigger] done@[k]).pn as int;
                        &&& c <= p <= hi
                        &&& v0[p - b0] == done@[k].packet
                        &&& done@[k].packet.state == OUTSTANDING
                    },
                forall|k: int, l: int|
                    d0.len() <= k < l < done@.len() ==> (#[trigger] done@[k]).pn > (#[trigger] done@[l]).pn,
                forall|i: int|
                    0 <= i < v0.len() && v0[i].state == OUTSTANDING && c <= b0 + i <= hi ==> exists|k: int|
                        d0.len() <= k < done@.len() && (#[trigger] done@[k]).pn == b0 + i,
            decreases c - from,
        {
            c = c - 1;
            let ghost dd = done@;
            let ghost ss = self@;
            self.ack_one(c, done, info, first && c == hi);
            proof {
                assert(done@.take(d0.len() as int) =~= dd.take(d0.len() as int));
                assert forall|i: int| 0 <= i < v0.len() && v0[i].state == OUTSTANDING && c <= b0 + i <= hi implies exists|k: int|
                        d0.len() <= k < done@.len() && (#[trigger] done@[k]).pn == b0 + i by {
                    if b0 + i == c {
                        assert(done@[done@.len() - 1].pn == c);
                    } else {
                        let k = choose|k: int| d0.len() <= k < dd.len() && (#[trigger] dd[k]).pn == b0 + i;
                        assert(done@[k] == dd[k]);
                    }
                }
            }
        }
    }

    /// An ACK frame's ranges `rs` (largest first). Every outstanding packet
    /// in them becomes acknowledged and is appended to `done`; bytes in
    /// flight drop by those in flight. `Err(PROTOCOL_VIOLATION)`, and
    /// nothing changed, if it acknowledges a packet never sent.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    pub fn on_ack(&mut self, rs: &[(u64, u64)], done: &mut Vec<Done>) -> (r: Result<AckInfo, u64>)
        requires
            old(self).inv(),
            ranges_ok(rs@),
            old(done)@.len() + 2 * old(self)@.len() <= usize::MAX,
        ensures
            final(self).inv(),
            final(self).next() == old(self).next(),
            r is Err ==> *final(self) == *old(self) && final(done)@ == old(done)@,
            r is Err <==> rs@[0].1 >= old(self).next(),
            r is Ok ==> final(self).largest() == Some(
                match old(self).largest() {
                    Some(l) => if l > rs@[0].1 { l } else { rs@[0].1 },
                    None => rs@[0].1,
                },
            ),
            r is Ok ==> ack_post(rs@, old(self).base() as int, old(self)@, old(done)@, final(self).base() as int, final(self)@, final(done)@),
    {
        if rs[0].1 >= self.next {
            return Err(PROTOCOL_VIOLATION);
        }
        let ghost v0 = self@;
        let ghost b0 = self.base as int;
        let ghost d0 = done@;
        let mut info = AckInfo { largest_new: None, eliciting: false };
        let n = rs.len();
        let mut j: usize = 0;
        proof {
            lemma_ack_start(rs@, b0, v0, d0);
        }
        while j < n
            invariant
                self.core(),
                ranges_ok(rs@),
                n == rs@.len(),
                j <= n,
                self.base == b0,
                self.next == old(self).next,
                self.largest_acked == old(self).largest_acked,
                self@.len() == v0.len(),
                d0 == old(done)@,
                d0.len() + 2 * v0.len() <= usize::MAX,
                rs@[0].1 < self.next,
                ack_inv(rs@, j as int, b0, v0, d0, self@, done@),
            decreases n - j,
        {
            let (lo, hi) = rs[j];
            proof {
                reveal(ack_inv);
                if j > 0 {
                    lemma_ranges_order(rs@, 0, j as int);
                }
            }
            let ghost s1 = self@;
            let ghost d1 = done@;
            self.ack_range(lo, hi, done, &mut info, j == 0);
            proof {
                lemma_ack_step(rs@, j as int, b0, v0, d0, s1, d1, self@, done@);
            }
            j = j + 1;
        }
        let top = rs[0].1;
        self.largest_acked = match self.largest_acked {
            Some(l) => if l > top { Some(l) } else { Some(top) },
            None => Some(top),
        };
        let ghost mid = self@;
        self.drain();
        proof {
            lemma_ack_end(rs@, b0, v0, d0, mid, done@, self.base as int, self@);
        }
        Ok(info)
    }

    /// Loss detection (§6.1, Appendix A.10) at time `now` with
    /// `loss_delay` (§6.1.2, from the RTT): every packet [`lost_rule`]
    /// says is lost becomes [`LOST`] and is appended to `done`, in packet
    /// number order; bytes in flight drop by those in flight.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    pub fn detect_lost(&mut self, now: u64, loss_delay: u64, pc_duration: u64, done: &mut Vec<Done>) -> (r: Loss)
        requires
            old(self).inv(),
            old(done)@.len() + old(self)@.len() <= usize::MAX,
        ensures
            final(self).inv(),
            final(self).next() == old(self).next(),
            final(self).largest() == old(self).largest(),
            loss_post(
                match old(self).largest() {
                    Some(l) => l as int,
                    None => -1,
                },
                now as int,
                loss_delay as int,
                old(self).base() as int,
                old(self)@,
                old(done)@,
                final(self).base() as int,
                final(self)@,
                final(done)@,
            ),
            timer_post(
                r.timer,
                match old(self).largest() {
                    Some(l) => l as int,
                    None => -1,
                },
                now as int,
                loss_delay as int,
                old(self).base() as int,
                old(self)@,
            ),
            // Persistent congestion only with two ack-eliciting packets
            // lost in this call, `pc_duration` apart, and every packet
            // between them lost in it too.
            r.persistent ==> exists|k: int, l: int|
                old(done)@.len() <= k < l < final(done)@.len() && (#[trigger] final(done)@[k]).packet.eliciting && (
                #[trigger] final(done)@[l]).packet.eliciting && final(done)@[l].packet.time >= final(done)@[k].packet.time
                    + pc_duration && final(done)@[l].pn - final(done)@[k].pn == l - k,
    {
        let ghost v0 = self@;
        let ghost d0 = done@;
        let ghost b0 = self.base as int;
        let largest: u64 = match self.largest_acked {
            Some(l) => l,
            None => {
                proof {
                    assert(done@.take(d0.len() as int) =~= d0);
                    assert(self@.skip(0) =~= self@);
                    lemma_loss_none(-1, now as int, loss_delay as int, b0, v0, d0);
                    assert(self.base == b0);
                }
                return Loss { timer: None, persistent: false };
            },
        };
        let ghost lg = largest as int;
        if largest <= self.base {
            proof {
                assert(done@.take(d0.len() as int) =~= d0);
                assert(self@.skip(0) =~= self@);
                lemma_loss_none(lg, now as int, loss_delay as int, b0, v0, d0);
            }
            return Loss { timer: None, persistent: false };
        }
        proof {
            lemma_loss_start(lg, now as int, loss_delay as int, b0, v0, d0);
        }
        let mut timer: Option<u64> = None;
        let mut persistent = false;
        // The current run of packets lost in this call, as the index in
        // `done` where it starts and the send time of its first
        // ack-eliciting packet.
        let mut run_first: Option<u64> = None;
        let mut run_open = false;
        let ghost mut run_k: int = 0;
        let ghost mut run_e: int = 0;
        let mut c = self.base;
        while c < largest
            invariant
                self.core(),
                self.base == b0,
                self.next == old(self).next,
                self.largest_acked == old(self).largest_acked,
                self.largest_acked == Some(largest),
                largest < self.next,
                b0 <= c <= largest,
                self@.len() == v0.len(),
                d0 == old(done)@,
                d0.len() + v0.len() <= usize::MAX,
                c < b0 + v0.len() + 1,
                lg == largest as int,
                loss_inv(lg, now as int, loss_delay as int, b0, v0, d0, c as int, self@, done@),
                timer_inv(timer, lg, now as int, loss_delay as int, b0, v0, c as int),
                run_open ==> d0.len() <= run_k < done@.len() && done@[done@.len() - 1].pn == c - 1 && done@[done@.len()
                    - 1].pn - done@[run_k].pn == done@.len() - 1 - run_k,
                run_first matches Some(t) ==> run_open && run_k <= run_e < done@.len() && done@[run_e].packet.eliciting
                    && done@[run_e].packet.time == t && done@[run_e].pn - done@[run_k].pn == run_e - run_k,
                persistent ==> exists|k: int, l: int|
                    d0.len() <= k < l < done@.len() && (#[trigger] done@[k]).packet.eliciting && (
                    #[trigger] done@[l]).packet.eliciting && done@[l].packet.time >= done@[k].packet.time + pc_duration
                        && done@[l].pn - done@[k].pn == l - k,
            decreases largest - c,
        {
            let idx = self.start + (c - self.base) as usize;
            let p = self.pkts[idx];
            let ghost s1 = self@;
            let ghost d1 = done@;
            let ghost t1 = timer;
            proof {
                lemma_loss_at(lg, now as int, loss_delay as int, b0, v0, d0, c as int, s1, d1);
                assert(p == s1[c - b0]);
            }
            if p.state != OUTSTANDING {
                run_open = false;
                run_first = None;
                proof {
                    lemma_loss_keep(lg, now as int, loss_delay as int, b0, v0, d0, c as int, s1, d1);
                    lemma_timer_skip(timer, lg, now as int, loss_delay as int, b0, v0, c as int);
                }
            } else {
                let by_time = now >= loss_delay && p.time <= now - loss_delay;
                if largest - c >= PACKET_THRESHOLD || by_time {
                    let mut q = p;
                    q.state = LOST;
                    self.pkts.set(idx, q);
                    proof {
                        assert(self@ =~= s1.update(c - b0, q));
                        lemma_flight_update(s1, c - b0, q);
                    }
                    if p.in_flight {
                        self.in_flight = self.in_flight - p.size as u64;
                    }
                    if p.eliciting && self.eliciting > 0 {
                        self.eliciting = self.eliciting - 1;
                    }
                    done.push(Done { pn: c, packet: p });
                    proof {
                        assert(s1[c - b0].state == OUTSTANDING);
                        assert((c as int) < lg);
                        assert(c + PACKET_THRESHOLD <= lg || s1[c - b0].time + loss_delay <= now);
                        lemma_loss_lost(lg, now as int, loss_delay as int, b0, v0, d0, c as int, s1, d1, self@, done@);
                        lemma_timer_skip(timer, lg, now as int, loss_delay as int, b0, v0, c as int);
                    }
                    let ghost kk = done@.len() - 1;
                    if !run_open {
                        run_open = true;
                        proof {
                            run_k = kk;
                        }
                    }
                    if p.eliciting {
                        match run_first {
                            Some(t) => {
                                if p.time >= t && p.time - t >= pc_duration {
                                    persistent = true;
                                    proof {
                                        assert(done@[run_e] == d1[run_e]);
                                        assert(done@[run_k] == d1[run_k]);
                                    }
                                }
                            },
                            None => {
                                run_first = Some(p.time);
                                proof {
                                    run_e = kk;
                                }
                            },
                        }
                    }
                    proof {
                        assert forall|k: int| 0 <= k < d1.len() implies done@[k] == d1[k] by {}
                    }
                } else {
                    // Not lost yet: when it will be, by time.
                    let t = if p.time > u64::MAX - loss_delay { u64::MAX } else { p.time + loss_delay };
                    timer = match timer {
                        Some(x) => if x <= t { Some(x) } else { Some(t) },
                        None => Some(t),
                    };
                    run_open = false;
                    run_first = None;
                    proof {
                        lemma_loss_keep(lg, now as int, loss_delay as int, b0, v0, d0, c as int, s1, d1);
                        lemma_timer_add(t1, timer, lg, now as int, loss_delay as int, b0, v0, c as int);
                    }
                }
            }
            c = c + 1;
        }
        let ghost mid = self@;
        self.drain();
        proof {
            lemma_loss_end(lg, now as int, loss_delay as int, b0, v0, d0, c as int, mid, done@, self.base as int, self@);
            lemma_timer_end(timer, lg, now as int, loss_delay as int, b0, v0, c as int);
        }
        Loss { timer, persistent }
    }

    /// Forgets every packet, as when this space's keys are discarded
    /// (§6.4): they leave bytes in flight without being acknowledged or
    /// lost. Packet numbers go on from where they were.
    pub fn discard(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@.len() == 0,
            final(self).bytes() == 0,
            final(self).next() == old(self).next(),
            final(self).largest() == old(self).largest(),
    {
        self.pkts = Vec::new();
        self.start = 0;
        self.base = self.next;
        self.in_flight = 0;
        self.eliciting = 0;
        assert(self@ =~= Seq::<Packet>::empty());
    }

    /// The tokens of up to `max` outstanding ack-eliciting packets, oldest
    /// first: what a probe (§6.2.4) may send again.
    pub fn outstanding(&self, max: usize, out: &mut Vec<u64>)
        requires
            self.inv(),
    {
        let mut i = self.start;
        let mut n: usize = 0;
        while i < self.pkts.len() && n < max
            invariant
                self.start <= i <= self.pkts@.len(),
            decreases self.pkts@.len() - i,
        {
            let p = self.pkts[i];
            if p.state == OUTSTANDING && p.eliciting {
                out.push(p.token);
                n = n + 1;
            }
            i = i + 1;
        }
    }
}

} // verus!