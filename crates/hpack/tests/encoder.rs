//! The encoder against the verified decoder: generated header lists,
//! table size changes on both sides, decoded whole and in random pieces.
//! Every block must decode to exactly the fields given (with `never` for
//! the sensitive ones), and the two dynamic tables must stay equal. The
//! proofs say this already; the tests check the build, and the parts the
//! proofs trust (the tables, `bytes_eq`).
mod common;
use common::*;
use verilith_hpack::decoder::Decoder;
use verilith_hpack::encoder::{Encoder, Header};

const NAMES: [&str; 12] = [
    ":status", "content-type", "server", "cache-control", "date", "x-a", "set-cookie", ":path", "content-length",
    "x-long-name-for-a-header", "", "accept-ranges",
];
const VALUES: [&str; 8] = ["200", "text/html; charset=utf-8", "verilith", "max-age=3600", "", "gzip", "bytes", "404"];

fn enc_table(e: &Encoder) -> Vec<(Vec<u8>, Vec<u8>)> {
    e.table.ents.iter().map(|x| (x.name.clone(), x.value.clone())).collect()
}

fn random_bytes(r: &mut Rng, n: u64) -> Vec<u8> {
    let ascii = r.below(3) != 0;
    (0..r.below(n)).map(|_| if ascii { b' ' + r.below(95) as u8 } else { r.below(256) as u8 }).collect()
}

#[test]
fn round_trip() {
    let mut r = Rng(7);
    let mut fields_total = 0;
    for _case in 0..400 {
        let mut e = Encoder::new().unwrap();
        let mut d = Decoder::new().unwrap();
        for _b in 0..r.below(12) + 1 {
            match r.below(8) {
                0 => {
                    let n = [0, 1, 64, 100, 256, 4096, 8192, 65536, u32::MAX][r.below(9) as usize];
                    assert!(d.change_settings(n));
                    e.change_settings(n);
                }
                1 => e.set_table_size(r.below(8193) as u32),
                _ => {}
            }
            let mut owned: Vec<(Vec<u8>, Vec<u8>, bool)> = Vec::new();
            for _ in 0..r.below(16) {
                let name = if r.below(4) != 0 { NAMES[r.below(12) as usize].as_bytes().to_vec() } else { random_bytes(&mut r, 40) };
                let value = if r.below(3) != 0 { VALUES[r.below(8) as usize].as_bytes().to_vec() } else { random_bytes(&mut r, 300) };
                owned.push((name, value, r.below(10) == 0));
            }
            let hs: Vec<Header> = owned.iter().map(|(n, v, s)| Header { name: n, value: v, sensitive: *s }).collect();
            let mut out = Vec::new();
            assert!(e.encode(&hs, &mut out));
            let pieces: Vec<usize> = if r.below(2) == 0 { vec![] } else { (0..3).map(|_| 1 + r.below(7) as usize).collect() };
            let got = decode_block(&mut d, &out, &pieces).expect("decodes");
            assert_eq!(got, owned);
            assert_eq!(table(&d), enc_table(&e));
            assert_eq!(d.table.max, e.table.max);
            fields_total += owned.len();
        }
    }
    assert!(fields_total > 10000);
}

#[test]
fn representations() {
    let mut e = Encoder::new().unwrap();
    let mut out = Vec::new();
    let h = |n: &'static str, v: &'static str| Header { name: n.as_bytes(), value: v.as_bytes(), sensitive: false };
    // Static table matches are one byte each.
    assert!(e.encode(&[h(":method", "GET"), h(":scheme", "https"), h(":path", "/"), h(":status", "200")], &mut out));
    assert_eq!(out, [0x82, 0x87, 0x84, 0x88]);
    // A new field is added to the table, then sent as one byte.
    out.clear();
    assert!(e.encode(&[h("server", "verilith")], &mut out));
    assert_eq!(out[0], 0x40 | 54); // literal with incremental indexing, name index 54
    out.clear();
    assert!(e.encode(&[h("server", "verilith")], &mut out));
    assert_eq!(out, [0x80 | 62]);
    // Sensitive fields are never indexed, even when in the table.
    out.clear();
    assert!(e.encode(&[Header { name: b"server", value: b"verilith", sensitive: true }], &mut out));
    assert_eq!(out[0], 0x10 | 15);
    // Huffman only when shorter: "aaaa" (5 bits each) is, random bytes are not.
    out.clear();
    assert!(e.encode(&[h("x-b", "aaaaaaaa")], &mut out));
    assert!(out.len() < 1 + 1 + 3 + 1 + 8);
    assert!(out[5] & 0x80 != 0);
    // Too long for the decoder: refused, nothing written.
    let big = vec![b'a'; 65537];
    out.clear();
    let before = e.table.len();
    assert!(!e.encode(&[Header { name: b"x", value: &big, sensitive: false }], &mut out));
    assert!(out.is_empty());
    assert_eq!(e.table.len(), before);
}

#[test]
fn size_updates() {
    let mut e = Encoder::new().unwrap();
    let mut d = Decoder::new().unwrap();
    let hs = [Header { name: b"x-a", value: b"1", sensitive: false }];
    let mut out = Vec::new();
    assert!(e.encode(&hs, &mut out));
    assert_eq!(out[0], 0x40); // no update at first
    assert_eq!(decode_block(&mut d, &out, &[]).unwrap().len(), 1);
    // The peer lowers its limit to 100 then raises it to 8192: the next
    // block starts with an update to 100, then one to 4096 (the
    // encoder's size).
    assert!(d.change_settings(100));
    e.change_settings(100);
    assert!(d.change_settings(8192));
    e.change_settings(8192);
    out.clear();
    assert!(e.encode(&hs, &mut out));
    assert_eq!(&out[..5], &[0x3f, 0x45, 0x3f, 0xe1, 0x1f]);
    assert_eq!(decode_block(&mut d, &out, &[]).unwrap().len(), 1);
    // A smaller encoder size is announced once.
    e.set_table_size(256);
    out.clear();
    assert!(e.encode(&[], &mut out));
    assert_eq!(out, [0x3f, 0xe1, 0x01]);
    assert_eq!(decode_block(&mut d, &out, &[]).unwrap().len(), 0);
    assert_eq!(table(&d), enc_table(&e));
    out.clear();
    assert!(e.encode(&[], &mut out));
    assert!(out.is_empty());
}

#[test]
fn static_table_hits() {
    // Every static entry is found (the perfect hash in sindex.rs misses
    // none) and sent as one byte; every static name is used as a name index.
    let stable: Vec<(&[u8], &[u8])> = (0..61).map(|i| verilith_hpack::table::static_entry(i)).collect();
    for (i, (n, v)) in stable.iter().enumerate() {
        let mut e = Encoder::new().unwrap();
        let mut out = Vec::new();
        assert!(e.encode(&[Header { name: n, value: v, sensitive: false }], &mut out));
        let first = stable.iter().position(|(m, _)| m == n).unwrap();
        if stable[..i].iter().any(|(m, w)| m == n && w == v) {
            continue;
        }
        assert_eq!(out, [0x80 | (i as u8 + 1)], "entry {}", i + 1);
        out.clear();
        assert!(e.encode(&[Header { name: n, value: b"x-not-in-the-table", sensitive: true }], &mut out));
        if first + 1 < 15 {
            assert_eq!(out[0] as usize, 0x10 | (first + 1), "entry {}", i + 1);
        } else {
            assert_eq!(out[0], 0x10 | 0x0f, "entry {}", i + 1);
            assert_eq!(out[1] as usize, first + 1 - 15, "entry {}", i + 1);
        }
    }
}
