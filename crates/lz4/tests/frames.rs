//! Frames against liblz4's LZ4F API (loaded with dlopen).
mod common;
use common::*;
use verilith_lz4::fcompress::Prefs;
use verilith_lz4::frame::{decompress, Error};

#[test]
fn xxh32_vectors() {
    use verilith_lz4::xxh::xxh32_exec;
    assert_eq!(xxh32_exec(b""), 0x02CC5D05);
    assert_eq!(xxh32_exec(b"a"), 0x550D7456);
    assert_eq!(xxh32_exec(b"abc"), 0x32D153FF);
    assert_eq!(xxh32_exec(b"Nobody inspects the spammish repetition"), 0xE2293B2F);
}

#[test]
fn frames_round_trip_both_ways() {
    let Some(l) = Lz4f::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0xa409_3822_299f_31d0);
    let mut count = 0;
    for size in [0usize, 1, 12, 13, 100, 4096, 65535, 65536, 65537, 200_000, 300_000, 1_500_000, 4_300_000] {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            for combo in 0..32u32 {
                // Not every combination for every input.
                if size > 100_000 && (combo + kind as u32) % 5 != 0 {
                    continue;
                }
                let id = 4 + (combo % 4) as u8;
                let indep = combo & 4 != 0;
                let bsum = combo & 8 != 0;
                let csum = combo & 16 != 0;
                let csize = (combo / 3) % 2 == 0;
                let ours = verilith_lz4::fcompress::compress(&input, &Prefs { block_id: id, indep, bsum, csum, csize, accel: 1 });
                // Written straight into a buffer: the same frame when it
                // fits, nothing past the end, and never a wrong frame
                // when it does not.
                let prefs = Prefs { block_id: id, indep, bsum, csum, csize, accel: 1 };
                let mut buf = vec![0x5Au8; ours.len() + 300];
                let m = verilith_lz4::fcompress::compress_into(&input, &mut buf[..ours.len() + 280], &prefs).expect("fits");
                assert!(buf[ours.len() + 280..].iter().all(|&b| b == 0x5A));
                assert!(decompress(&buf[..m], usize::MAX).unwrap() == input, "into: size {size} kind {kind} combo {combo}");
                assert!(l.decompress(&buf[..m], usize::MAX).expect("liblz4 on ours, into").0 == input);
                if size <= 70_000 {
                    for cut in [1usize, 2, 5, 9, 40] {
                        if cut <= m {
                            let mut small = vec![0x5Au8; m];
                            match verilith_lz4::fcompress::compress_into(&input, &mut small[..m - cut], &prefs) {
                                None => {},
                                Some(k) => assert!(decompress(&small[..k], usize::MAX).unwrap() == input),
                            }
                            assert!(small[m - cut..].iter().all(|&b| b == 0x5A));
                        }
                    }
                }
                let (back, used) = l.decompress(&ours, usize::MAX).expect("liblz4 on ours");
                assert_eq!(used, ours.len());
                assert!(back == input, "liblz4 on ours: size {size} kind {kind} combo {combo}");
                assert!(decompress(&ours, usize::MAX).unwrap() == input);
                // liblz4 fed 7 bytes at a time must agree too.
                if size <= 4096 {
                    assert!(l.decompress(&ours, 7).unwrap().0 == input);
                }

                let mut p = Preferences::default();
                p.frame_info.block_size_id = id as i32;
                p.frame_info.block_mode = indep as i32;
                p.frame_info.content_checksum = csum as i32;
                p.frame_info.block_checksum = bsum as i32;
                p.frame_info.content_size = if csize { input.len() as u64 } else { 0 };
                // Fast and high-compression blocks.
                p.compression_level = if combo % 3 == 0 { 9 } else { 0 };
                let theirs = l.compress(&input, &p);
                assert!(decompress(&theirs, usize::MAX).unwrap() == input, "ours on liblz4's: size {size} kind {kind} combo {combo}");
                // The limit: one byte short fails, exact passes.
                if !input.is_empty() {
                    assert_eq!(decompress(&theirs, input.len() - 1), Err(Error::TooLarge));
                }
                assert!(decompress(&theirs, input.len()).is_ok());
                count += 1;
            }
        }
    }
    eprintln!("{count} frames each way");
}

#[test]
fn several_frames_and_skippable() {
    let Some(l) = Lz4f::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x0822_3e11_4a5c_7711);
    let a = sample(&mut rng, 70000, 3);
    let b = sample(&mut rng, 500, 2);
    let mut s = Vec::new();
    s.extend(l.compress(&a, &Preferences::default()));
    s.extend([0x53, 0x2a, 0x4d, 0x18, 5, 0, 0, 0, 1, 2, 3, 4, 5]);
    s.extend(verilith_lz4::fcompress::compress(&b, &Prefs { block_id: 4, indep: false, bsum: true, csum: true, csize: true, accel: 1 }));
    s.extend([0x5f, 0x2a, 0x4d, 0x18, 0, 0, 0, 0]);
    let mut want = a.clone();
    want.extend(&b);
    assert!(decompress(&s, usize::MAX).unwrap() == want);
    assert!(decompress(&[], 0).unwrap().is_empty());
    // A skippable frame that runs past the end.
    assert_eq!(decompress(&[0x50, 0x2a, 0x4d, 0x18, 9, 0, 0, 0, 1], 100), Err(Error::Corrupt));
    // Truncations of a valid input are never accepted as the whole.
    for cut in 1..s.len().min(3000) {
        if let Ok(v) = decompress(&s[..cut], usize::MAX) {
            assert!(v.len() < want.len() || cut == s.len());
        }
    }
}

#[test]
fn corrupted_frames_agree() {
    let Some(l) = Lz4f::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x452821e638d01377);
    let (mut both, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
    for round in 0..30000 {
        let size = [0usize, 5, 20, 300, 5000, 70000][round % 6];
        let input = sample(&mut rng, size, round % KINDS);
        let mut p = Preferences::default();
        p.frame_info.block_size_id = 4 + (round % 4) as i32;
        p.frame_info.block_mode = (round / 4 % 2) as i32;
        p.frame_info.content_checksum = (round / 8 % 2) as i32;
        p.frame_info.block_checksum = (round / 16 % 2) as i32;
        p.frame_info.content_size = if round / 32 % 2 == 0 { input.len() as u64 } else { 0 };
        let mut c = l.compress(&input, &p);
        for _ in 0..1 + rng.below(2) {
            let at = rng.below(c.len());
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
        // One frame, which must be the whole input.
        let theirs = l.decompress(&c, usize::MAX).filter(|(_, used)| *used == c.len()).map(|(v, _)| v);
        let mut o = Vec::new();
        let ours = match verilith_lz4::frame::decode_frame(&c, 0, &mut o, 1 << 30) {
            Ok(j) if j == c.len() => Some(o),
            _ => None,
        };
        match (&ours, &theirs) {
            (Some(a), Some(b)) => {
                assert!(a == b, "round {round}");
                both += 1;
            }
            (Some(_), None) => ours_only += 1,
            (None, Some(_)) => {
                // Only the offset 0 that liblz4 lets through (DEPARTURES.md).
                assert!(frame_has_zero_offset(&c), "round {round}: liblz4 accepts what vlz4 rejects");
                theirs_only += 1;
            }
            (None, None) => neither += 1,
        }
    }
    eprintln!("both accept {both}, vlz4 only {ours_only}, liblz4 only {theirs_only}, neither {neither}");
}
