//! Differential tests against the system's liblz4, loaded at run time
//! with `dlopen` (nothing is built or linked from C). Skipped, with a
//! message, when liblz4.so.1 is not installed.
mod common;
use common::*;

#[test]
fn blocks_round_trip_both_ways() {
    let Some(l) = Lz4::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x243f_6a88_85a3_08d3);
    let mut n_inputs = 0;
    let (mut ours_total, mut theirs_total) = (0usize, 0usize);
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            for accel in [1usize, 2, 8, 100] {
                // Ours, decoded by liblz4 and by us.
                let mut c = vec![0u8; verilith_lz4::compress::compress_bound(input.len())];
                let n = verilith_lz4::compress::compress_into(&input, &mut c, accel).expect("fits in the bound");
                c.truncate(n);
                // Exactly the decoded size: liblz4 then checks the end-of-block rules.
                assert_eq!(l.decompress(&c, input.len()).as_deref(), Some(&input[..]), "liblz4 on ours, size {size} kind {kind}");
                assert_eq!(l.decompress(&c, input.len() + 100).as_deref(), Some(&input[..]));
                let mut o = vec![0u8; input.len()];
                assert_eq!(verilith_lz4::block::decompress_into(&c, &mut o), Some(input.len()));
                assert_eq!(o, input);
                // One byte less of room must fail, as in liblz4.
                if !input.is_empty() {
                    let mut o = vec![0u8; input.len() - 1];
                    assert_eq!(verilith_lz4::block::decompress_into(&c, &mut o), None);
                }
                if accel == 1 {
                    ours_total += n;
                    // A destination with no room to spare gives the same
                    // block through the checked path; one byte less fails.
                    // Either way nothing is written outside it.
                    let mut tight = vec![0x5Au8; n + 9];
                    assert_eq!(verilith_lz4::compress::compress_at(&input, &mut tight[..n], 0), Some(n), "tight, size {size} kind {kind}");
                    assert_eq!(tight[..n], c[..]);
                    assert!(tight[n..].iter().all(|&b| b == 0x5A));
                    if n > 0 {
                        let mut short = vec![0x5Au8; n + 9];
                        assert_eq!(verilith_lz4::compress::compress_at(&input, &mut short[..n - 1], 0), None);
                        assert!(short[n - 1..].iter().all(|&b| b == 0x5A));
                    }
                    // Written after a prefix, which is left alone.
                    let base = 1 + size % 7;
                    let mut off = vec![0xC3u8; base + c.len() + 40];
                    assert_eq!(verilith_lz4::compress::compress_at(&input, &mut off, base), Some(base + n));
                    assert!(off[..base].iter().all(|&b| b == 0xC3));
                    assert_eq!(l.decompress(&off[base..base + n], input.len()).as_deref(), Some(&input[..]));
                }
            }
            // liblz4's, decoded by us.
            for accel in [1, 5] {
                let c = l.compress(&input, accel);
                let mut o = vec![0xAAu8; input.len() + 37];
                assert_eq!(verilith_lz4::block::decompress_into(&c, &mut o), Some(input.len()), "ours on liblz4's, size {size} kind {kind}");
                assert_eq!(o[..input.len()], input[..]);
                let mut o = vec![0u8; input.len()];
                assert_eq!(verilith_lz4::block::decompress_into(&c, &mut o), Some(input.len()));
                assert_eq!(o, input);
                if accel == 1 {
                    theirs_total += c.len();
                }
            }
            n_inputs += 1;
        }
    }
    eprintln!("{n_inputs} inputs; compressed bytes: vlz4 {ours_total}, liblz4 {theirs_total}");
    // Within 3% of liblz4's size overall.
    assert!(ours_total as f64 <= theirs_total as f64 * 1.03, "{ours_total} vs {theirs_total}");
}

#[test]
fn corrupted_blocks_agree() {
    let Some(l) = Lz4::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x1319_8a2e_0370_7344);
    let (mut both, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
    for round in 0..40000 {
        let size = [0usize, 1, 5, 12, 13, 20, 64, 300, 5000][round % 9];
        let input = sample(&mut rng, size, round % KINDS);
        let mut c = l.compress(&input, 1);
        let flips = 1 + rng.below(3);
        for _ in 0..flips {
            if c.is_empty() {
                break;
            }
            let at = rng.below(c.len());
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => {
                    c.truncate(at);
                }
                _ => c.insert(at, rng.next() as u8),
            }
        }
        let cap = input.len() * 2 + 600;
        let theirs = l.decompress(&c, cap);
        let mut o = vec![0u8; cap];
        let ours = verilith_lz4::block::decompress_into(&c, &mut o).map(|n| o[..n].to_vec());
        match (&ours, &theirs) {
            (Some(a), Some(b)) => {
                assert_eq!(a, b, "round {round}");
                both += 1;
            }
            // vlz4 accepts every block the format allows; liblz4 also
            // rejects blocks that break the end-of-block rules.
            (Some(a), None) => {
                assert!(breaks_end_rules(&c, a.len(), cap), "round {round}: liblz4 rejects, vlz4 accepts, and the end rules hold");
                ours_only += 1;
            }
            (None, Some(_)) => {
                // liblz4 does not reject an offset of 0, which the format
                // forbids: it copies whatever the output buffer held.
                assert!(has_zero_offset(&c), "round {round}: liblz4 accepts what vlz4 rejects: {c:?}");
                theirs_only += 1;
            }
            (None, None) => neither += 1,
        }
    }
    eprintln!("both accept {both}, vlz4 only {ours_only}, liblz4 only {theirs_only}, neither {neither}");
}
