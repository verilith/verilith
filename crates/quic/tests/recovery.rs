//! Loss recovery end to end: a sender's `Sent` and a receiver's `Received`
//! over a lossy, reordering path, with the ACK frames encoded and parsed
//! in between, plus the RFC 9002 arithmetic on known values.
use std::collections::BTreeSet;
use verilith_quic::cc::NewReno;
use verilith_quic::frame::{self, Ack, Frame};
use verilith_quic::recv::Received;
use verilith_quic::rtt::{self, Rtt};
use verilith_quic::sent::{self, Sent};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// The receiver's ACK frame, encoded and parsed back, as the descending
/// ranges `Sent::on_ack` takes.
fn ack_ranges(r: &Received, n: usize) -> Vec<(u64, u64)> {
    let mut gaps = Vec::new();
    let (largest, first) = r.ack_fields(n, &mut gaps);
    let mut raw = Vec::new();
    for (g, l) in &gaps {
        verilith_quic::varint::write(&mut raw, *g);
        verilith_quic::varint::write(&mut raw, *l);
    }
    let f = Frame::Ack(Ack { largest, delay: 0, first, count: gaps.len() as u64, raw: &raw, ecn: None });
    let mut b = Vec::new();
    frame::encode(&f, &mut b);
    let (f, end) = frame::parse(&b, 0).expect("parses");
    assert_eq!(end, b.len());
    let Frame::Ack(a) = f else { panic!("not an ACK") };
    let mut out = vec![(a.largest - a.first, a.largest)];
    let mut it = a.ranges();
    while let Some(rg) = it.next() {
        out.push(rg);
    }
    out
}

#[test]
fn lossy_path() {
    for seed in 1..40u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let mut s = Sent::new();
        let mut r = Received::new();
        let mut delivered = BTreeSet::new();
        let mut acked = BTreeSet::new();
        let mut lost = BTreeSet::new();
        let mut path: Vec<(u64, u64)> = Vec::new(); // (arrival, pn)
        let mut now = 0u64;
        for _ in 0..3000 {
            now += 100;
            if rng.next() % 3 != 0 {
                let pn = s.on_sent(now, 1200, true, true, 0).expect("sent");
                if rng.next() % 10 != 0 {
                    path.push((now + 5_000 + rng.next() % 3_000, pn));
                }
            }
            // Arrivals, in any order.
            path.sort();
            while let Some(&(t, pn)) = path.first() {
                if t > now {
                    break;
                }
                path.remove(0);
                if !r.is_dup(pn) {
                    r.insert(pn, now, true);
                    assert!(delivered.insert(pn), "processed twice");
                }
            }
            if r.ack_now() && r.largest().is_some() {
                let rs = ack_ranges(&r, 1 + (rng.next() % 40) as usize);
                r.on_ack_sent();
                for &(lo, hi) in &rs {
                    for pn in lo..=hi {
                        assert!(delivered.contains(&pn), "acknowledged {pn}, never received");
                    }
                }
                let mut done = Vec::new();
                s.on_ack(&rs, &mut done).expect("valid ACK");
                for d in &done {
                    assert!(delivered.contains(&d.pn));
                    assert!(acked.insert(d.pn), "acknowledged twice");
                }
                let mut done = Vec::new();
                s.detect_lost(now, 9_000, u64::MAX, &mut done);
                for d in &done {
                    assert!(lost.insert(d.pn), "lost twice");
                    assert!(!acked.contains(&d.pn));
                }
            }
        }
        let flight: u64 = (0..s.next_pn()).filter(|p| !acked.contains(p) && !lost.contains(p)).count() as u64 * 1200;
        assert_eq!(s.bytes_in_flight(), flight);
        assert!(!acked.is_empty() && !lost.is_empty());
    }
}

#[test]
fn received_ranges_are_bounded() {
    let mut r = Received::new();
    // Every other packet: one range each.
    for pn in (0..200u64).step_by(2) {
        assert!(!r.is_dup(pn));
        r.insert(pn, 0, true);
    }
    let rs = ack_ranges(&r, usize::MAX);
    assert_eq!(rs.len(), verilith_quic::recv::MAX_RANGES);
    assert_eq!(rs[0], (198, 198));
    // Dropped ranges are duplicates from then on, and so are kept ones.
    assert!(r.is_dup(0) && r.is_dup(1) && r.is_dup(198));
    assert!(!r.is_dup(197) && !r.is_dup(199));
    r.insert(197, 0, true);
    assert_eq!(ack_ranges(&r, 1), vec![(196, 198)]);
}

#[test]
fn sent_packets_lost_by_threshold() {
    let mut s = Sent::new();
    for t in 0..10 {
        s.on_sent(t, 1000, true, true, t).unwrap();
    }
    let mut done = Vec::new();
    // Packet 9 acknowledged: 0..=6 are 3 or more behind it.
    s.on_ack(&[(9, 9)], &mut done).unwrap();
    assert_eq!(done.len(), 1);
    let mut done = Vec::new();
    let loss = s.detect_lost(10, 1_000_000, u64::MAX, &mut done);
    let pns: Vec<u64> = done.iter().map(|d| d.pn).collect();
    assert_eq!(pns, [0, 1, 2, 3, 4, 5, 6]);
    assert!(loss.timer.is_some());
    assert!(!loss.persistent);
    assert_eq!(s.bytes_in_flight(), 2000);
    assert!(matches!(s.on_ack(&[(10, 10)], &mut Vec::new()), Err(sent::PROTOCOL_VIOLATION)));
}

#[test]
fn rtt_examples() {
    let mut r = Rtt::new();
    assert_eq!(r.pto(0), 333_000 + 4 * 166_500);
    r.update(100_000, 0, 25_000, false);
    assert_eq!((r.smoothed, r.var, r.min), (100_000, 50_000, 100_000));
    // A larger sample, with an ACK delay that is subtracted.
    r.update(140_000, 20_000, 25_000, true);
    assert_eq!(r.smoothed, (7 * 100_000 + 120_000) / 8);
    assert_eq!(r.var, (3 * 50_000 + 20_000) / 4);
    // An ACK delay that would go below min_rtt is not subtracted.
    let s = r.smoothed;
    r.update(105_000, 20_000, 25_000, true);
    assert_eq!(r.smoothed, (7 * s + 105_000) / 8);
    assert_eq!(r.loss_delay(), {
        let m = r.smoothed.max(r.latest);
        m + m / 8
    });
    assert_eq!(r.persistent(25_000), 3 * r.pto(25_000));
    assert_eq!(rtt::backoff(1000, 3), 8000);
    assert_eq!(rtt::backoff(u64::MAX / 2 + 1, 2), u64::MAX);
}

#[test]
fn new_reno() {
    let mut c = NewReno::new(1200);
    assert_eq!(c.cwnd, 12_000);
    assert!(c.can_send(10_800, 1200) && !c.can_send(10_801, 1200));
    // Slow start: the window grows by the bytes acknowledged.
    c.on_ack(1, 1200, false);
    assert_eq!(c.cwnd, 13_200);
    // A loss halves it once; more losses from before then do nothing.
    c.on_congestion(5, 100);
    assert_eq!((c.cwnd, c.ssthresh), (6_600, Some(6_600)));
    c.on_congestion(50, 200);
    c.on_ack(99, 1200, false);
    assert_eq!(c.cwnd, 6_600);
    // Congestion avoidance: one datagram per window acknowledged.
    for _ in 0..5 {
        c.on_ack(101, 1200, false);
    }
    assert_eq!(c.cwnd, 6_600);
    c.on_ack(101, 1200, false);
    assert_eq!(c.cwnd, 7_800);
    c.on_persistent();
    assert_eq!(c.cwnd, 2_400);
    // Never below the minimum.
    c.on_congestion(1000, 2000);
    assert_eq!(c.cwnd, 2_400);
}
