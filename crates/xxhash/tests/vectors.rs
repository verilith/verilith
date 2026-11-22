//! XXH32 and XXH64 against published values and against an independent
//! implementation (xxhash-rust), on every length around the stripe and
//! tail boundaries, and on streaming input split every way.
use verilith_xxhash::{Xxh64, xxh32_exec, xxh64_exec};
use vstd::prelude::Ghost;

/// Bytes that are not all alike, so a lane read from the wrong place shows.
fn data(n: usize) -> Vec<u8> {
    let mut x: u64 = 0x9E3779B97F4A7C15;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

#[test]
fn xxh32_published() {
    assert_eq!(xxh32_exec(b""), 0x02CC5D05);
    assert_eq!(xxh32_exec(b"a"), 0x550D7456);
    assert_eq!(xxh32_exec(b"abc"), 0x32D153FF);
    assert_eq!(xxh32_exec(b"Nobody inspects the spammish repetition"), 0xE2293B2F);
}

#[test]
fn xxh64_published() {
    assert_eq!(xxh64_exec(b""), 0xEF46DB3751D8E999);
    assert_eq!(xxh64_exec(b"a"), 0xD24EC4F1A98C6E5B);
    assert_eq!(xxh64_exec(b"abc"), 0x44BC2CF5AD770999);
    assert_eq!(xxh64_exec(b"Nobody inspects the spammish repetition"), 0xFBCEA83C8A378BF1);
}

#[test]
fn every_length_matches_xxhash_rust() {
    let d = data(1 << 12);
    for n in 0..=600 {
        assert_eq!(xxh32_exec(&d[..n]), xxhash_rust::xxh32::xxh32(&d[..n], 0), "xxh32, length {n}");
        assert_eq!(xxh64_exec(&d[..n]), xxhash_rust::xxh64::xxh64(&d[..n], 0), "xxh64, length {n}");
    }
    for n in [1000, 1023, 1024, 1025, 4095, 4096] {
        assert_eq!(xxh32_exec(&d[..n]), xxhash_rust::xxh32::xxh32(&d[..n], 0), "xxh32, length {n}");
        assert_eq!(xxh64_exec(&d[..n]), xxhash_rust::xxh64::xxh64(&d[..n], 0), "xxh64, length {n}");
    }
}

#[test]
fn unaligned_slices() {
    let d = data(300);
    for off in 0..16 {
        for n in [0, 3, 15, 16, 31, 32, 33, 100, 255] {
            let s = &d[off..off + n];
            assert_eq!(xxh32_exec(s), xxhash_rust::xxh32::xxh32(s, 0));
            assert_eq!(xxh64_exec(s), xxhash_rust::xxh64::xxh64(s, 0));
        }
    }
}

fn streamed(pieces: &[&[u8]]) -> u64 {
    let mut h = Xxh64::new();
    for p in pieces {
        h.update(p, Ghost::assume_new());
    }
    h.digest(Ghost::assume_new())
}

#[test]
fn streaming_split_anywhere() {
    let d = data(200);
    for n in [0, 1, 31, 32, 33, 64, 65, 100, 200] {
        let want = xxh64_exec(&d[..n]);
        assert_eq!(streamed(&[&d[..n]]), want);
        for a in 0..=n {
            assert_eq!(streamed(&[&d[..a], &d[a..n]]), want, "length {n}, split at {a}");
            for b in (a..=n).step_by(7) {
                assert_eq!(streamed(&[&d[..a], &d[a..b], &d[b..n]]), want, "length {n}, split at {a} and {b}");
            }
        }
    }
}

#[test]
fn streaming_byte_at_a_time() {
    let d = data(1000);
    let mut h = Xxh64::new();
    for i in 0..d.len() {
        h.update(&d[i..i + 1], Ghost::assume_new());
    }
    assert_eq!(h.digest(Ghost::assume_new()), xxhash_rust::xxh64::xxh64(&d, 0));
}
