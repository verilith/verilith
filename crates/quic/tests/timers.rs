//! `timers`: the idle timeout without overflow, and `next` against `due`.
use verilith_quic::timers::{due, idle_timeout, next, pto_deadline, Due, Timers};

#[test]
fn idle_timeout_takes_the_smaller_and_never_overflows() {
    assert_eq!(idle_timeout(0, 0, 1000), None);
    assert_eq!(idle_timeout(30_000, 0, 1000), Some(30_000_000));
    assert_eq!(idle_timeout(30_000, 10_000, 1000), Some(10_000_000));
    // At least three PTOs.
    assert_eq!(idle_timeout(1, 0, 1_000_000), Some(3_000_000));
    // A peer's max_idle_timeout can be up to 2^62 - 1 ms.
    assert_eq!(idle_timeout(0, (1 << 62) - 1, 1000), Some(u64::MAX));
}

#[test]
fn something_is_due_when_next_says() {
    struct R(u64);
    impl R {
        fn r(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn o(&mut self) -> Option<u64> {
            if self.r() % 2 == 0 { Some(self.r() % 1000) } else { None }
        }
    }
    let mut g = R(0x2545f4914f6cdd1d);
    for _ in 0..20000 {
        let g = &mut g;
        let last = [g.o(), g.o(), g.o()];
        let pto = pto_deadline(&last, &[g.r() % 100, g.r() % 100, g.r() % 100], (g.r() % 4) as u32);
        let t = Timers { idle: g.o(), loss: [g.o(), g.o(), g.o()], pto, can_send: g.r() % 4 != 0, ack: g.o() };
        let Some(n) = next(&t) else { continue };
        let d = due(&t, n);
        assert!(!matches!(d, Due::Nothing) || t.ack == Some(n));
        if n > 0 {
            assert!(matches!(due(&t, n - 1), Due::Nothing));
        }
    }
}
