//! Differential tests against the system's libsnappy (google/snappy),
//! loaded at run time with `dlopen` (nothing is built or linked from C).
//! Skipped, with a message, when libsnappy.so.1 is not installed.
mod common;
use common::*;
use verilith_snappy::compress::{compress_into, max_compressed_length};
use verilith_snappy::decode::{decompress_into, decompress_vec, uncompressed_length, Error};

#[test]
fn round_trip_both_ways() {
    let Some(l) = Snappy::load() else {
        eprintln!("libsnappy not found: skipped");
        return;
    };
    let mut rng = Rng(0x243f_6a88_85a3_08d3);
    let (mut ours_total, mut theirs_total, mut count) = (0usize, 0usize, 0);
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            assert_eq!(max_compressed_length(size), l.max_len(size));
            // Ours, decompressed by libsnappy and by us.
            let mut c = vec![0u8; max_compressed_length(input.len())];
            let n = compress_into(&input, &mut c).expect("fits in the bound");
            c.truncate(n);
            assert!(l.validate(&c));
            assert_eq!(l.uncompress(&c).as_deref(), Some(&input[..]), "libsnappy on ours, size {size} kind {kind}");
            assert_eq!(decompress_vec(&c, usize::MAX).as_deref(), Ok(&input[..]));
            // Theirs, decompressed by us.
            let t = l.compress(&input);
            assert_eq!(uncompressed_length(&t), Some(input.len()));
            let mut o = vec![0xAAu8; input.len() + 37];
            assert_eq!(decompress_into(&t, &mut o), Ok(input.len()), "ours on libsnappy's, size {size} kind {kind}");
            assert_eq!(o[..input.len()], input[..]);
            assert_eq!(decompress_vec(&t, input.len()).as_deref(), Ok(&input[..]));
            if !input.is_empty() {
                let mut o = vec![0u8; input.len() - 1];
                assert_eq!(decompress_into(&t, &mut o), Err(Error::TooSmall));
                assert_eq!(decompress_vec(&t, input.len() - 1), Err(Error::TooSmall));
            }
            ours_total += n;
            theirs_total += t.len();
            count += 1;
        }
    }
    eprintln!("{count} inputs; compressed bytes: vsnappy {ours_total}, libsnappy {theirs_total}");
    assert!(ours_total as f64 <= theirs_total as f64 * 1.03, "{ours_total} vs {theirs_total}");
}

#[test]
fn corrupted_agree() {
    let Some(l) = Snappy::load() else {
        eprintln!("libsnappy not found: skipped");
        return;
    };
    let mut rng = Rng(0x1319_8a2e_0370_7344);
    let (mut both, mut neither) = (0, 0);
    for round in 0..60000 {
        let size = [0usize, 1, 5, 14, 15, 20, 64, 300, 5000, 70000][round % 10];
        let input = sample(&mut rng, size, round % KINDS);
        let mut c = l.compress(&input);
        for _ in 0..1 + rng.below(3) {
            if c.is_empty() {
                break;
            }
            let at = rng.below(c.len());
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => c.truncate(at),
                _ => c.insert(at, rng.next() as u8),
            }
        }
        let theirs = l.uncompress(&c);
        let ours = decompress_vec(&c, 1 << 28).ok();
        // The same verdict and the same output, with no exceptions.
        assert_eq!(l.validate(&c), theirs.is_some());
        assert!(ours == theirs, "round {round}: vsnappy {:?} libsnappy {:?} on {:?}", ours.as_ref().map(|v| v.len()), theirs.as_ref().map(|v| v.len()), &c[..c.len().min(60)]);
        assert_eq!(uncompressed_length(&c), l.uncompressed_length(&c));
        if ours.is_some() {
            both += 1;
        } else {
            neither += 1;
        }
    }
    eprintln!("both accept {both}, neither {neither}");
}

#[test]
fn every_element_kind() {
    // Literals with 1 to 4 length bytes, and copies with 1-, 2- and
    // 4-byte offsets, written by hand.
    let mut c = vec![0u8];
    let mut want = Vec::new();
    let lit = |c: &mut Vec<u8>, want: &mut Vec<u8>, n: usize, form: usize| {
        let data: Vec<u8> = (0..n).map(|i| (i * 7 + form) as u8).collect();
        match form {
            0 => c.push(((n - 1) << 2) as u8),
            k => {
                c.push(((59 + k) << 2) as u8);
                c.extend_from_slice(&((n - 1) as u32).to_le_bytes()[..k]);
            }
        }
        c.extend_from_slice(&data);
        want.extend_from_slice(&data);
    };
    lit(&mut c, &mut want, 60, 0);
    lit(&mut c, &mut want, 61, 1);
    lit(&mut c, &mut want, 5, 2);
    lit(&mut c, &mut want, 300, 3);
    lit(&mut c, &mut want, 70000, 4);
    let copy = |c: &mut Vec<u8>, want: &mut Vec<u8>, off: usize, n: usize, form: usize| {
        match form {
            1 => c.extend_from_slice(&[(1 | ((n - 4) << 2) | ((off >> 8) << 5)) as u8, off as u8]),
            2 => {
                c.push((2 | ((n - 1) << 2)) as u8);
                c.extend_from_slice(&(off as u16).to_le_bytes());
            }
            _ => {
                c.push((3 | ((n - 1) << 2)) as u8);
                c.extend_from_slice(&(off as u32).to_le_bytes());
            }
        }
        for _ in 0..n {
            want.push(want[want.len() - off]);
        }
    };
    copy(&mut c, &mut want, 1, 11, 1);
    copy(&mut c, &mut want, 2047, 4, 1);
    copy(&mut c, &mut want, 3, 64, 2);
    copy(&mut c, &mut want, 65535, 1, 2);
    copy(&mut c, &mut want, 70000, 64, 3);
    copy(&mut c, &mut want, 5, 2, 3);
    // The preamble, as a 5-byte varint with padding (allowed).
    let n = want.len() as u32;
    let pre = [(n & 127) as u8 | 128, ((n >> 7) & 127) as u8 | 128, ((n >> 14) & 127) as u8 | 128, ((n >> 21) & 127) as u8 | 128, (n >> 28) as u8];
    c.splice(0..1, pre);
    assert_eq!(decompress_vec(&c, usize::MAX).as_deref(), Ok(&want[..]));
    if let Some(l) = Snappy::load() {
        assert_eq!(l.uncompress(&c).as_deref(), Some(&want[..]));
    }
}
