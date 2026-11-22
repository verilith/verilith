//! The trusted tables and the Huffman decoder's run-time layout check.
mod common;
use common::*;
use verilith_hpack::htables::{HUFF_CODE, HUFF_LEN};

#[test]
fn layout_check_passes() {
    assert!(verilith_hpack::huffman::check());
}

/// The code is prefix-free: no code is a prefix of another. With that,
/// the spec's "shortest matching code" is the RFC's "the code".
#[test]
fn prefix_free() {
    for a in 0..257 {
        for b in 0..257 {
            if a == b {
                continue;
            }
            let (la, lb) = (HUFF_LEN[a] as u32, HUFF_LEN[b] as u32);
            if la <= lb {
                assert_ne!(HUFF_CODE[b] >> (lb - la), HUFF_CODE[a], "{} is a prefix of {}", a, b);
            }
        }
    }
}

/// Kraft's sum is exactly 1: the code is complete.
#[test]
fn complete() {
    let s: u64 = (0..257).map(|i| 1u64 << (30 - HUFF_LEN[i] as u32)).sum();
    assert_eq!(s, 1 << 30);
}

#[test]
fn every_symbol_round_trips() {
    for c in 0..=255u8 {
        for n in [1, 2, 7] {
            let s = vec![c; n];
            let mut out = Vec::new();
            assert!(verilith_hpack::huffman::decode(&huff_encode(&s), &mut out, &start()));
            assert_eq!(out, s);
        }
    }
}

#[test]
fn padding_and_eos() {
    let mut out = Vec::new();
    // 'a' is 00011 (5 bits): padded with 111 is valid.
    assert!(verilith_hpack::huffman::decode(&[0b0001_1111], &mut out, &start()));
    assert_eq!(out, b"a");
    // Padding of 8 ones is too long.
    out.clear();
    assert!(!verilith_hpack::huffman::decode(&[0b0001_1111, 0xff], &mut out, &start()));
    // Padding that is not all ones.
    out.clear();
    assert!(!verilith_hpack::huffman::decode(&[0b0001_1110], &mut out, &start()));
    // EOS (30 ones) in the string.
    out.clear();
    assert!(!verilith_hpack::huffman::decode(&[0xff, 0xff, 0xff, 0xfc], &mut out, &start()));
    out.clear();
    assert!(!verilith_hpack::huffman::decode(&[0xff, 0xff, 0xff, 0xff], &mut out, &start()));
    // The empty string.
    out.clear();
    assert!(verilith_hpack::huffman::decode(&[], &mut out, &start()));
    assert!(out.is_empty());
}

#[test]
fn random_strings_round_trip() {
    let mut r = Rng(7);
    for _ in 0..20000 {
        let n = r.below(40) as usize;
        let s: Vec<u8> = (0..n).map(|_| if r.below(4) == 0 { r.below(256) as u8 } else { b"abcdefghij0123/:-"[r.below(17) as usize] }).collect();
        let mut out = Vec::new();
        assert!(verilith_hpack::huffman::decode(&huff_encode(&s), &mut out, &start()));
        assert_eq!(out, s);
    }
}

fn start() -> &'static [u32] {
    verilith_hpack::huffman::dtab().unwrap()
}

/// The shortest code at the start of the `w` bits `x`, by brute force.
fn first(x: u32, w: u32) -> Option<(u32, u32)> {
    for l in 1..=w {
        let v = x >> (w - l);
        for s in 0..257 {
            if verilith_hpack::htables::HUFF_LEN[s] as u32 == l && verilith_hpack::htables::HUFF_CODE[s] == v {
                return Some((s as u32, l));
            }
        }
    }
    None
}

/// The decoding table against a direct search.
#[test]
fn decoding_table() {
    let t = start();
    let (mut one, mut two) = (0, 0);
    for x in 0..4096u32 {
        let e = t[x as usize];
        let want = match first(x, 12) {
            None => 0,
            Some((s1, l1)) => match if l1 < 12 { first(x & ((1 << (12 - l1)) - 1), 12 - l1) } else { None } {
                Some((s2, l2)) => {
                    two += 1;
                    (l1 + l2) | 2 << 6 | l1 << 8 | s1 << 16 | s2 << 24
                }
                None => {
                    one += 1;
                    l1 | 1 << 6 | l1 << 8 | s1 << 16
                }
            },
        };
        assert_eq!(e, want, "x={x}");
    }
    assert!(one > 0 && two > 0);
}
