//! `pktbuf::put_frame` never passes the end, and writes whole frames.
use verilith_quic::pktbuf::{pad, put_frame};

#[test]
fn frames_fit_or_are_not_written() {
    let mut x = 0x9e3779b97f4a7c15u64;
    for _ in 0..20000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let n = (x % 5) as usize;
        let f: Vec<u64> = (0..n).map(|i| ((x >> (i * 11)) >> (x % 60)) & ((1 << 62) - 1)).collect();
        let mut buf = vec![0u8; (x % 40) as usize];
        let before = buf.clone();
        let end = (x >> 20) as usize % 60;
        let extra = (x >> 30) as usize % 8;
        let mut want = before.clone();
        want.push(0x11);
        for &v in &f {
            verilith_quic::varint::write(&mut want, v);
        }
        let ok = put_frame(&mut buf, end, 0x11, &f, extra);
        assert_eq!(ok, want.len() + extra <= end);
        assert_eq!(buf, if ok { want } else { before });
    }
}

#[test]
fn padding() {
    assert_eq!(pad(300, 1452, true, None, 32), 900);
    assert_eq!(pad(300, 1000, true, None, 32), 700);
    assert_eq!(pad(1430, 1452, false, Some(1452), 32), 22);
    assert_eq!(pad(1400, 1452, false, Some(1452), 32), 0);
}
