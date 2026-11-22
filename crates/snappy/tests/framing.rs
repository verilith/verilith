//! The framing format against the `snap` crate, an independent
//! implementation (google/snappy's library does not have one).
mod common;
use common::{sample, sizes, Rng, KINDS};
use std::io::{Read, Write};
use verilith_snappy::frame::{frame_decode, frame_encode, FrameError};

fn snap_encode(input: &[u8]) -> Vec<u8> {
    let mut w = snap::write::FrameEncoder::new(Vec::new());
    w.write_all(input).unwrap();
    w.into_inner().unwrap()
}

fn snap_decode(c: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    snap::read::FrameDecoder::new(c).read_to_end(&mut out).ok()?;
    Some(out)
}

#[test]
fn round_trip_both_ways() {
    let mut rng = Rng(0x94d049bb133111eb);
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            let ours = frame_encode(&input);
            assert_eq!(snap_decode(&ours).as_deref(), Some(&input[..]), "size {size} kind {kind}");
            assert_eq!(frame_decode(&ours, usize::MAX).as_deref(), Ok(&input[..]));
            let theirs = snap_encode(&input);
            assert_eq!(frame_decode(&theirs, usize::MAX).as_deref(), Ok(&input[..]), "size {size} kind {kind}");
            if size > 0 {
                assert_eq!(frame_decode(&theirs, size - 1), Err(FrameError::TooLarge));
            }
            // Two streams one after the other are one stream.
            let mut two = ours.clone();
            two.extend_from_slice(&theirs);
            let mut twice = input.clone();
            twice.extend_from_slice(&input);
            assert_eq!(frame_decode(&two, usize::MAX).as_deref(), Ok(&twice[..]));
        }
    }
}

#[test]
fn other_chunks() {
    let mut s = frame_encode(b"hello");
    // Padding and a reserved skippable chunk are skipped.
    s.extend_from_slice(&[0xfe, 3, 0, 0, 1, 2, 3]);
    s.extend_from_slice(&[0x80, 1, 0, 0, 9]);
    s.extend_from_slice(&frame_encode(b" world")[10..]);
    assert_eq!(frame_decode(&s, 100).as_deref(), Ok(&b"hello world"[..]));
    // A reserved unskippable chunk is an error.
    let mut bad = s.clone();
    bad.extend_from_slice(&[0x02, 0, 0, 0]);
    assert_eq!(frame_decode(&bad, 100), Err(FrameError::Corrupt));
    // So are a missing identifier, a wrong one, and a wrong checksum.
    assert_eq!(frame_decode(&s[10..], 100), Err(FrameError::Corrupt));
    assert_eq!(frame_decode(b"", 100), Ok(Vec::new()));
    let mut wrong = s.clone();
    wrong[9] = b'y';
    assert_eq!(frame_decode(&wrong, 100), Err(FrameError::Corrupt));
    let mut sum = s.clone();
    sum[14] ^= 1;
    assert_eq!(frame_decode(&sum, 100), Err(FrameError::Corrupt));
}

#[test]
fn corrupted_agree() {
    let mut rng = Rng(0xd6e8feb86659fd93);
    let (mut both, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
    for round in 0..30000 {
        let size = [0usize, 3, 20, 300, 5000, 70000, 140_000][round % 7];
        let input = sample(&mut rng, size, round % KINDS);
        let mut c = if round % 2 == 0 { snap_encode(&input) } else { frame_encode(&input) };
        for _ in 0..1 + rng.below(2) {
            let at = rng.below(c.len().max(1)).min(c.len().saturating_sub(1));
            if c.is_empty() {
                break;
            }
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => c.truncate(at),
                _ => c.insert(at, rng.next() as u8),
            }
            if c.is_empty() {
                break;
            }
        }
        if c.is_empty() {
            continue;
        }
        let a = frame_decode(&c, usize::MAX).ok();
        let b = snap_decode(&c);
        match (&a, &b) {
            (Some(x), Some(y)) => {
                assert_eq!(x, y, "round {round}");
                both += 1;
            }
            (Some(_), None) => ours_only += 1,
            (None, Some(_)) => {
                theirs_only += 1;
                if theirs_only <= 5 {
                    eprintln!("round {round}: snap only, len {} head {:02x?}", c.len(), &c[..c.len().min(24)]);
                }
            }
            (None, None) => neither += 1,
        }
    }
    eprintln!("both accept {both}, vsnappy only {ours_only}, snap only {theirs_only}, neither {neither}");
}
