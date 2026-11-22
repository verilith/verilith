//! The transcoders against the standard library, on random and mutated text.
use rand::{Rng, RngExt, SeedableRng};
use verilith_text::utf::conv::*;
use verilith_text::utf::valid8::utf8_valid;

fn sample_text(r: &mut impl Rng) -> String {
    const PIECES: &[&str] = &[
        "a", "hello world ", "\u{e9}", "\u{ff}", "\u{100}", "\u{7ff}", "\u{800}", "\u{20ac}", "\u{d7ff}", "\u{e000}",
        "\u{fffd}", "\u{ffff}", "\u{10000}", "\u{1f600}", "\u{10ffff}", "\u{4e2d}\u{6587}", "\u{3b1}\u{3b2}",
        "\u{5d0}", "\u{930}\u{94d}",
    ];
    let mut s = String::new();
    let n = r.random_range(0..200);
    let ascii_run = r.random_bool(0.5);
    for _ in 0..n {
        if ascii_run && r.random_bool(0.7) {
            s.push_str("the quick brown fox jumps over the lazy dog ");
        } else {
            s.push_str(PIECES[r.random_range(0..PIECES.len())]);
        }
    }
    s
}

fn mutate(r: &mut impl Rng, b: &mut Vec<u8>) {
    if b.is_empty() {
        return;
    }
    for _ in 0..r.random_range(1..4) {
        if b.is_empty() {
            return;
        }
        let i = r.random_range(0..b.len());
        match r.random_range(0..3) {
            0 => b[i] = r.random(),
            1 => {
                b.remove(i);
            }
            _ => b.insert(i, [0x80u8, 0xC0, 0xE0, 0xED, 0xF0, 0xF4, 0xF5, 0xFF][r.random_range(0..8)]),
        }
    }
}

fn cnt8(s: &[u8]) -> usize {
    s.iter().map(|&b| (!(0x80..=0xBF).contains(&b)) as usize + (b >= 0xF0) as usize).sum()
}

fn cnt16(s: &[u16]) -> usize {
    s.iter()
        .map(|&u| if u <= 0x7F { 1 } else if u <= 0x7FF || (0xD800..=0xDFFF).contains(&u) { 2 } else { 3 })
        .sum()
}

#[test]
fn utf8_side() {
    let mut r = rand::rngs::StdRng::seed_from_u64(1);
    for it in 0..60_000 {
        let mut b = sample_text(&mut r).into_bytes();
        if it % 2 == 1 {
            mutate(&mut r, &mut b);
        }
        let std_ok = std::str::from_utf8(&b).is_ok();
        assert_eq!(utf8_valid(&b), std_ok, "{:x?}", b);
        assert_eq!(count_utf8(&b, false), cnt8(&b));
        let mut out = vec![0u16; cnt8(&b)];
        let got = utf8_to_utf16(&b, &mut out);
        if std_ok {
            let want: Vec<u16> = std::str::from_utf8(&b).unwrap().encode_utf16().collect();
            assert_eq!(got, Some(want.len()));
            assert_eq!(&out[..], &want[..]);
            // Latin-1, when every character fits.
            let s = std::str::from_utf8(&b).unwrap();
            let mut l1 = vec![0u8; count_utf8(&b, true)];
            let got = utf8_to_latin1(&b, &mut l1);
            if s.chars().all(|c| (c as u32) < 0x100) {
                let want: Vec<u8> = s.chars().map(|c| c as u8).collect();
                assert_eq!(got, Some(want.len()));
                assert_eq!(l1, want);
            } else {
                assert_eq!(got, None);
            }
        } else {
            assert_eq!(got, None);
        }
        let ap = ascii_prefix(&b);
        assert_eq!(ap, b.iter().position(|&c| c >= 0x80).unwrap_or(b.len()));
    }
}

#[test]
fn utf16_side() {
    let mut r = rand::rngs::StdRng::seed_from_u64(2);
    for it in 0..60_000 {
        let mut u: Vec<u16> = sample_text(&mut r).encode_utf16().collect();
        if it % 2 == 1 && !u.is_empty() {
            for _ in 0..r.random_range(1..3) {
                let i = r.random_range(0..u.len());
                u[i] = [0xD800u16, 0xDBFF, 0xDC00, 0xDFFF, 0x41, 0xFFFF][r.random_range(0..6)];
            }
        }
        assert_eq!(count_utf16(&u), cnt16(&u));
        let mut out = vec![0u8; cnt16(&u)];
        let got = utf16_to_utf8(&u, &mut out);
        match String::from_utf16(&u) {
            Ok(s) => {
                assert_eq!(got, Some(s.len()));
                assert_eq!(out, s.as_bytes());
            }
            Err(_) => assert_eq!(got, None),
        }
        let mut l1 = vec![0u8; u.len()];
        let ok = utf16_to_latin1(&u, &mut l1);
        assert_eq!(ok, u.iter().all(|&x| x <= 0xFF));
        if ok {
            assert!(u.iter().zip(&l1).all(|(&a, &b)| a as u8 == b));
        }
    }
}

#[test]
fn latin1_side() {
    let mut r = rand::rngs::StdRng::seed_from_u64(3);
    for _ in 0..60_000 {
        let n = r.random_range(0..300);
        let hi = r.random_bool(0.3);
        let b: Vec<u8> = (0..n).map(|_| if hi && r.random_bool(0.2) { r.random() } else { r.random_range(0x20..0x7F) }).collect();
        let want: String = b.iter().map(|&c| c as char).collect();
        assert_eq!(count_latin1_utf8(&b), want.len());
        let mut out = vec![0u8; want.len()];
        assert_eq!(latin1_to_utf8(&b, &mut out), want.len());
        assert_eq!(out, want.as_bytes());
        // The bounded form, with every output size up to the full one.
        let cap = r.random_range(0..=want.len());
        let mut out = vec![0u8; cap];
        let (read, written) = latin1_to_utf8_safe(&b, &mut out);
        let pre: String = b[..read].iter().map(|&c| c as char).collect();
        assert_eq!(&out[..written], pre.as_bytes());
        if read < b.len() {
            assert!(written + (b[read] as char).len_utf8() > cap);
        }
        let mut w = vec![0u16; b.len()];
        latin1_to_utf16(&b, &mut w);
        assert!(b.iter().zip(&w).all(|(&a, &x)| a as u16 == x));
    }
}
