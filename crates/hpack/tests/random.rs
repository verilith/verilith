//! Generated header blocks, encoded by a small reference encoder with
//! every representation, both string codings, size updates and eviction,
//! decoded whole and in random pieces: the decoded lists must be what was
//! encoded, and the same for every split.
mod common;
use common::*;
use verilith_hpack::decoder::Decoder;

const NAMES: [&str; 8] = [":path", "content-type", "x-a", "cookie", "user-agent", "x-long-name-for-a-header", "", "accept"];

#[test]
fn round_trip() {
    let mut r = Rng(99);
    for _case in 0..300 {
        // Encoder-side model of the dynamic table, newest first.
        let mut table: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        let mut max: u64 = 4096;
        let mut blocks = Vec::new();
        for _b in 0..r.below(6) + 1 {
            let mut enc = Vec::new();
            let mut want = Vec::new();
            if r.below(4) == 0 {
                max = r.below(4097);
                enc_int(&mut enc, 0x20, 5, max);
                evict(&mut table, 0, max);
            }
            for _ in 0..r.below(12) {
                let kind = r.below(5);
                let dynlen = table.len() as u64;
                if kind == 0 {
                    // Indexed.
                    let i = 1 + r.below(61 + dynlen);
                    enc_int(&mut enc, 0x80, 7, i);
                    want.push((entry(&table, i), false));
                    continue;
                }
                let name: Vec<u8> = if r.below(2) == 0 {
                    NAMES[r.below(8) as usize].as_bytes().to_vec()
                } else {
                    (0..r.below(30)).map(|_| r.below(256) as u8).collect()
                };
                let vlen = if r.below(10) == 0 { r.below(5000) } else { r.below(40) };
                let value: Vec<u8> = (0..vlen).map(|_| b"abc012 ;=\xff"[r.below(10) as usize]).collect();
                let (first, n, never, incr) = match kind {
                    1 => (0x40u8, 6, false, true),
                    2 => (0x00, 4, false, false),
                    _ => (0x10, 4, true, false),
                };
                let by_index = r.below(2) == 0;
                let name = if by_index {
                    let i = 1 + r.below(61 + dynlen);
                    enc_int(&mut enc, first, n, i);
                    entry(&table, i).0
                } else {
                    enc.push(first);
                    enc_str(&mut enc, &name, r.below(2) == 0);
                    name
                };
                enc_str(&mut enc, &value, r.below(2) == 0);
                if incr {
                    let room = name.len() as u64 + value.len() as u64 + 32;
                    evict(&mut table, room, max);
                    if room <= max {
                        table.insert(0, (name.clone(), value.clone()));
                    }
                }
                want.push(((name, value), never));
            }
            blocks.push((enc, want));
        }
        let final_table = table.clone();
        let mut reference: Option<Vec<Vec<Hdr>>> = None;
        for split in 0..4 {
            let mut d = Decoder::new().unwrap();
            let mut got_all = Vec::new();
            for (enc, want) in &blocks {
                let pieces: Vec<usize> = match split {
                    0 => vec![],
                    1 => vec![1],
                    _ => (0..8).map(|_| 1 + r.below(20) as usize).collect(),
                };
                let got = decode_block(&mut d, enc, &pieces).expect("decodes");
                let w: Vec<Hdr> = want.iter().map(|((n, v), nv)| (n.clone(), v.clone(), *nv)).collect();
                assert_eq!(got, w);
                got_all.push(got);
            }
            assert_eq!(common::table(&d), final_table);
            match &reference {
                None => reference = Some(got_all),
                Some(r0) => assert_eq!(r0, &got_all),
            }
        }
    }
}

fn size(t: &[(Vec<u8>, Vec<u8>)]) -> u64 {
    t.iter().map(|(n, v)| n.len() as u64 + v.len() as u64 + 32).sum()
}

fn evict(t: &mut Vec<(Vec<u8>, Vec<u8>)>, room: u64, max: u64) {
    while !t.is_empty() && size(t) + room > max {
        t.pop();
    }
}

fn entry(t: &[(Vec<u8>, Vec<u8>)], i: u64) -> (Vec<u8>, Vec<u8>) {
    if i <= 61 {
        let (n, v) = verilith_hpack::table::static_entry(i as usize - 1);
        (n.to_vec(), v.to_vec())
    } else {
        t[(i - 62) as usize].clone()
    }
}

/// Malformed input never panics, and splitting never changes the verdict.
#[test]
fn garbage() {
    let mut r = Rng(5);
    for _ in 0..20000 {
        let n = r.below(40) as usize;
        let b: Vec<u8> = (0..n).map(|_| if r.below(3) == 0 { 0x80 | r.below(128) as u8 } else { r.below(256) as u8 }).collect();
        let mut d1 = Decoder::new().unwrap();
        let a = decode_block(&mut d1, &b, &[]);
        let mut d2 = Decoder::new().unwrap();
        let c = decode_block(&mut d2, &b, &[1]);
        assert_eq!(a, c, "{:02x?}", b);
    }
}
