//! `sendq::SendState` and `ranges::RangeSet` against simple references.
use std::collections::BTreeSet;
use verilith_quic::ranges::RangeSet;
use verilith_quic::sendq::SendState;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn range_set_is_a_set() {
    for seed in 1..300u64 {
        let mut r = Rng(seed);
        let mut s = RangeSet::new();
        let mut m = BTreeSet::new();
        for _ in 0..60 {
            let a = r.next() % 200;
            let b = a + 1 + r.next() % 30;
            match r.next() % 3 {
                0 => {
                    s.insert(a, b);
                    m.extend(a..b);
                }
                1 => {
                    s.remove(a, b);
                    for x in a..b {
                        m.remove(&x);
                    }
                }
                _ => assert_eq!(s.contains(a, b), (a..b).all(|x| m.contains(&x))),
            }
            assert_eq!(s.first().map(|(a, _)| a), m.iter().next().copied());
        }
    }
}

#[test]
fn send_state_sends_everything_once_acknowledged() {
    for seed in 1..200u64 {
        let mut r = Rng(seed);
        let mut s = SendState::new();
        let total = 1 + r.next() % 5000;
        assert!(s.write(total));
        s.set_fin();
        let mut acked = BTreeSet::new();
        let mut inflight: Vec<(u64, u64, bool)> = Vec::new();
        let mut rounds = 0;
        while !s.all_acked() {
            rounds += 1;
            assert!(rounds < 100_000, "seed {seed}");
            if let Some((o, n, f)) = s.next(1 + r.next() % 700, u64::MAX) {
                assert!(o + n <= total && (!f || o + n == total));
                assert!((o..o + n).all(|x| !acked.contains(&x)));
                s.sent(o, n, f);
                inflight.push((o, n, f));
            }
            if !inflight.is_empty() && r.next() % 2 == 0 {
                let (o, n, f) = inflight.swap_remove((r.next() % inflight.len() as u64) as usize);
                if r.next() % 4 == 0 {
                    s.on_lost(o, n, f);
                } else {
                    let before = s.base();
                    let k = s.on_ack(o, n, f);
                    acked.extend(o..o + n);
                    assert_eq!(s.base(), before + k);
                    assert!((0..s.base()).all(|x| acked.contains(&x)));
                    assert!(!acked.contains(&s.base()));
                }
            }
        }
        assert_eq!(acked.len() as u64, total);
    }
}
