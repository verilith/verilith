//! `handle::ack_delay` scales without losing high bits.
use verilith_quic::handle::ack_delay;

#[test]
fn ack_delay_saturates() {
    assert_eq!(ack_delay(1000, 3), 8000);
    assert_eq!(ack_delay(5, 0), 5);
    // The largest field with the largest exponent: 2^62 - 1 times 2^20.
    assert_eq!(ack_delay((1 << 62) - 1, 20), u64::MAX);
    // `checked_shl` would have kept only the low bits here.
    assert_eq!((1u64 << 50).checked_shl(20), Some(0));
    assert_eq!(ack_delay(1 << 50, 20), u64::MAX);
    assert_eq!(ack_delay(1 << 40, 20), 1 << 60);
}
