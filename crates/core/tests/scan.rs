//! `scan::any_upper` and `scan::any_nul_cr_lf` against the byte-by-byte
//! statement, on every length up to 40 with the one interesting byte at
//! every position, and on random strings.
use verilith_core::scan::{any_nul_cr_lf, any_upper};

fn naive_upper(b: &[u8]) -> bool {
    b.iter().any(|c| c.is_ascii_uppercase())
}

fn naive_ncl(b: &[u8]) -> bool {
    b.iter().any(|&c| c == 0 || c == b'\r' || c == b'\n')
}

#[test]
fn every_position() {
    let fill: &[u8] = &[b'a', b'z', b'@', b'[', 0x80, 0xc1, 0xda, 0xff, b'\t', 0x0b, 0x0c, 0x0e, b' ', b'0'];
    let probes: &[u8] = &[0, b'\r', b'\n', b'A', b'Z', b'M', b'@', b'[', 0xc1, 0x8d, 0x8a, 0x80];
    for n in 0..40 {
        for &f in fill {
            let base = vec![f; n];
            assert_eq!(any_upper(&base), naive_upper(&base));
            assert_eq!(any_nul_cr_lf(&base), naive_ncl(&base));
            for p in 0..n {
                for &x in probes {
                    let mut b = base.clone();
                    b[p] = x;
                    assert_eq!(any_upper(&b), naive_upper(&b), "{b:?}");
                    assert_eq!(any_nul_cr_lf(&b), naive_ncl(&b), "{b:?}");
                }
            }
        }
    }
}

#[test]
fn random() {
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for _ in 0..200_000 {
        let n = (next() % 70) as usize;
        let b: Vec<u8> = (0..n).map(|_| next() as u8).collect();
        assert_eq!(any_upper(&b), naive_upper(&b));
        assert_eq!(any_nul_cr_lf(&b), naive_ncl(&b));
        // Sub-slices at odd offsets.
        if n > 3 {
            let t = &b[1..n - 1];
            assert_eq!(any_upper(t), naive_upper(t));
            assert_eq!(any_nul_cr_lf(t), naive_ncl(t));
        }
    }
}
