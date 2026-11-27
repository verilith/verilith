//! `reasm::Reassembly` against a reference, and the memory bound under
//! overlapping frames.
use verilith_quic::reasm::{Reassembly, COMPACT};

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
fn random_fragments_read_back_in_order() {
    for seed in 1..200u64 {
        let mut r = Rng(seed);
        let len = 1 + (r.next() % 20_000) as usize;
        let stream: Vec<u8> = (0..len).map(|i| (i * 7 + seed as usize) as u8).collect();
        let window = 4096 + r.next() % 8192;
        let mut a = Reassembly::new(window);
        let mut out = Vec::new();
        let mut rounds = 0;
        while out.len() < len {
            rounds += 1;
            assert!(rounds < 1_000_000);
            // A fragment somewhere within the window, sometimes repeated or
            // overlapping what was read.
            let lo = a.read_offset().saturating_sub(r.next() % 100);
            let off = (lo + r.next() % window) as usize;
            if off >= len {
                continue;
            }
            let n = (1 + r.next() % 1500) as usize;
            let end = (off + n).min(len);
            let ok = a.insert(off as u64, &stream[off..end]);
            assert_eq!(ok, end as u64 <= a.read_offset() + window || end as u64 <= a.contiguous());
            assert!(a.buffered() < (2 * window + COMPACT) as usize);
            if r.next() % 3 == 0 {
                let m = (r.next() % 3000) as usize;
                a.read_into(&mut out, m);
            }
        }
        assert_eq!(out, stream, "seed {seed}");
    }
}

#[test]
fn overlapping_frames_stay_within_the_window() {
    // Frames that each start one byte later and run to the window's end:
    // stored by offset, these would need window^2 / 2 bytes.
    let window = 1 << 20;
    let mut a = Reassembly::new(window);
    let data = vec![7u8; window as usize];
    for off in 1..2000u64 {
        assert!(a.insert(off, &data[..(window - off) as usize]));
    }
    assert!(a.buffered() <= window as usize);
    assert_eq!(a.contiguous(), 0);
    assert!(a.insert(0, &[7]));
    assert_eq!(a.contiguous(), window);
    // Past the window: refused.
    assert!(!a.insert(window, &[1]));
}
