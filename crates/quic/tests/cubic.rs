//! CUBIC's window over time: slow start, the 0.7 back-off, the concave
//! climb back to W_max in about K, and the convex probing past it.
use verilith_quic::cubic::Cubic;

const MDS: u64 = 1200;
const RTT: u64 = 20_000;

/// Acknowledges one window's worth of datagrams sent at `sent`, at `now`.
fn ack_window(c: &mut Cubic, sent: u64, now: u64) {
    for _ in 0..c.cwnd / MDS {
        c.on_ack(sent, MDS, false, now, RTT);
    }
}

#[test]
fn slow_start_then_back_off() {
    let mut c = Cubic::new(MDS);
    assert_eq!(c.cwnd, 12_000);
    ack_window(&mut c, 0, RTT);
    assert_eq!(c.cwnd, 24_000);
    c.on_congestion(RTT, 2 * RTT);
    assert_eq!(c.cwnd, 16_800);
    assert_eq!(c.ssthresh, Some(16_800));
    assert_eq!(c.w_max, 24_000);
    // Packets sent before the reduction neither grow nor reduce it again.
    c.on_ack(RTT, MDS, false, 3 * RTT, RTT);
    c.on_congestion(RTT, 3 * RTT);
    assert_eq!(c.cwnd, 16_800);
}

#[test]
fn climbs_back_to_w_max_in_about_k() {
    let mut c = Cubic::new(MDS);
    // A large window, as after a long slow start: 1000 datagrams.
    c.cwnd = 1000 * MDS;
    c.w_est = c.cwnd;
    c.on_congestion(0, 0);
    assert_eq!(c.cwnd, 700 * MDS);
    let mut now = 0;
    let mut reached = None;
    while now < 60_000_000 {
        now += RTT;
        let before = c.cwnd;
        ack_window(&mut c, now - RTT + 1, now);
        assert!(c.cwnd >= before);
        if reached.is_none() && c.cwnd >= 1000 * MDS {
            reached = Some(now);
        }
    }
    // K = ∛(300 / 0.4) ≈ 9.09 s; the window is aimed one RTT ahead.
    let k = c.k as f64 / 1024.0;
    assert!((k - 9.09).abs() < 0.01, "K {k}");
    let r = reached.unwrap() as f64 / 1e6;
    assert!((8.5..9.5).contains(&r), "reached W_max at {r} s");
    // Then convex growth: well past W_max by a minute.
    assert!(c.cwnd > 10 * 1000 * MDS);
}

#[test]
fn fast_convergence_and_persistent() {
    let mut c = Cubic::new(MDS);
    c.cwnd = 100 * MDS;
    c.on_congestion(0, 0);
    assert_eq!(c.w_max, 100 * MDS);
    // A second loss below W_max remembers 0.85 of the window.
    c.on_congestion(1, 1);
    assert_eq!(c.w_max, 70 * MDS * 17 / 20);
    assert_eq!(c.cwnd, 49 * MDS);
    c.on_persistent();
    assert_eq!(c.cwnd, 2 * MDS);
    c.raise_mds(1452);
    assert_eq!(c.cwnd, 2 * 1452);
}
