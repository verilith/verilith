//! Recent DNS parsing CVEs, each reproduced as a packet of the same shape
//! and checked against vdns. The proofs rule out each bug class for every
//! input; these tests show the concrete attack packets being handled.
//! See CVES.md for the mapping from each CVE to the proven property.

mod common;
use common::*;
use std::time::{Duration, Instant};
use verilith_dns::parse;

/// A response header with the given section counts.
fn header(qd: u16, an: u16, ns: u16, ar: u16) -> Vec<u8> {
    let mut b = vec![0x12, 0x34, 0x81, 0x80];
    for c in [qd, an, ns, ar] {
        b.extend_from_slice(&c.to_be_bytes());
    }
    b
}

fn ptr(target: usize) -> [u8; 2] {
    [0xC0 | (target >> 8) as u8, target as u8]
}

/// A chain of `hops` compression pointers, each pointing two bytes earlier,
/// ending at a one-label name. Returns the message and the offset of the
/// last pointer (the start of the longest chain).
fn pointer_chain(hops: usize) -> (Vec<u8>, usize) {
    let mut b = header(1, 0, 0, 0);
    b.extend_from_slice(&[1, b'a', 0, 0, 1, 0, 1]);
    let first = b.len();
    b.extend_from_slice(&ptr(12));
    for i in 1..hops {
        b.extend_from_slice(&ptr(first + 2 * (i - 1)));
    }
    let top = b.len() - 2;
    (b, top)
}

fn quick<T>(f: impl FnOnce() -> T) -> T {
    let t = Instant::now();
    let r = f();
    assert!(t.elapsed() < Duration::from_millis(50), "took {:?}", t.elapsed());
    r
}

/// CVE-2026-114605 (dnspython < 2.9.0, CVSS 7.5): name decompression follows
/// an attacker-controlled pointer chain with no hop limit, burning CPU.
/// CVE-2026-64194 (Net::DNS <= 1.55): the same chain makes the recursive
/// decoder overflow the stack (about 8k frames over UDP, 32k over TCP).
#[test]
fn cve_2026_114605_and_64194_pointer_chains() {
    // 14-bit pointers cap a chain of 2-byte hops at about 8k, whatever the
    // transport.
    for hops in [1_000, 8_000, 8_180] {
        let (b, top) = pointer_chain(hops);
        // Rejected at the first hop: a pointer must land on a label length
        // octet, never on another pointer (RFC 9267 §2), and decoding is a
        // loop proven to take at most 256 steps, so there is no recursion
        // to overflow and no chain to walk.
        quick(|| assert!(read_name(&b, top).is_none()));
    }
    // A chain whose links do land on labels is legal, but each link adds a
    // label, so it is cut off by the 255-octet limit within 127 hops.
    let mut b = header(0, 0, 0, 0);
    b.extend_from_slice(&[1, b'a', 0]);
    for _ in 0..3000 {
        let prev = b.len() - if b.len() == 15 { 3 } else { 4 };
        b.push(1);
        b.push(b'a');
        b.extend_from_slice(&ptr(prev));
    }
    let top = b.len() - 4;
    quick(|| assert!(read_name(&b, top).is_none()));
}

/// CVE-2025-2962 (Zephyr < 3.7.2 / 4.2.0, CVSS 7.5): infinite loop in
/// `dns_copy_qname` on crafted compression pointers.
#[test]
fn cve_2025_2962_pointer_loops() {
    // Pointer to itself, two pointers pointing at each other, and a label
    // followed by a pointer back to that label.
    let mut self_loop = header(1, 0, 0, 0);
    self_loop.extend_from_slice(&[0xC0, 12, 0, 1, 0, 1]);
    let mut mutual = header(1, 0, 0, 0);
    mutual.extend_from_slice(&[1, b'a', 0xC0, 16, 0xC0, 12, 0, 1, 0, 1]);
    let mut label_loop = header(1, 0, 0, 0);
    label_loop.extend_from_slice(&[1, b'a', 0xC0, 12, 0, 1, 0, 1]);
    for b in [self_loop, mutual, label_loop] {
        quick(|| {
            assert!(parse(&b).is_none());
            assert!(read_name(&b, 12).is_none());
        });
    }
}

/// CVE-2025-1675 (Zephyr < 3.7.2, CVSS 8.2 / NVD 9.1): `dns_copy_qname`
/// copies a label using its untrusted length without checking the source
/// buffer, reading out of bounds.
#[test]
fn cve_2025_1675_lengths_past_the_end() {
    // Label length 63 with 3 bytes present.
    let mut b = header(1, 0, 0, 0);
    b.extend_from_slice(&[63, b'a', b'b', b'c']);
    assert!(parse(&b).is_none());
    assert!(read_name(&b, 12).is_none());
    // Pointer to an offset past the end of the message.
    let mut b = header(1, 0, 0, 0);
    b.extend_from_slice(&[0xFF, 0xFF, 0, 1, 0, 1]);
    assert!(parse(&b).is_none());
    // Pointer cut off by the end of the message.
    let mut b = header(1, 0, 0, 0);
    b.push(0xC0);
    assert!(parse(&b).is_none());
    // RDLENGTH larger than the bytes left.
    let mut b = header(1, 1, 0, 0);
    b.extend_from_slice(&[1, b'a', 0, 0, 1, 0, 1]);
    b.extend_from_slice(&[0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 0, 0xFF, 0xFF, 1, 2, 3]);
    assert!(parse(&b).is_none());
    // Every truncation of a valid message is rejected without reading past
    // the end (the proofs cover every index; this just exercises it).
    let mut ok = header(1, 1, 0, 0);
    ok.extend_from_slice(&[1, b'a', 0, 0, 1, 0, 1]);
    ok.extend_from_slice(&[0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 1, 2, 3, 4]);
    assert!(parse(&ok).is_some());
    for n in 0..ok.len() {
        assert!(parse(&ok[..n]).is_none());
    }
}

/// CVE-2026-2291 (dnsmasq, 2026): heap buffer overflow in `extract_name`
/// on crafted name data. The classic shape is a name that grows past the
/// fixed-size output buffer once its pointers are expanded.
#[test]
fn cve_2026_2291_names_that_expand_past_255() {
    // A 249-octet name, then names with more labels in front of a pointer
    // to it: 6 + 249 = 255 is fine, 8 + 249 = 257 is not.
    let long: Vec<&[u8]> = vec![&[b'x'; 61][..], &[b'y'; 61], &[b'z'; 61], &[b'w'; 61]];
    let base = wire(&long);
    assert_eq!(base.len(), 249);
    let mut b = header(0, 0, 0, 0);
    b.extend_from_slice(&base);
    let fits = b.len();
    b.extend_from_slice(&[1, b'a', 1, b'b', 1, b'c']);
    b.extend_from_slice(&ptr(12));
    let over = b.len();
    b.extend_from_slice(&[1, b'a', 1, b'b', 1, b'c', 1, b'd']);
    b.extend_from_slice(&ptr(12));
    let (n, _) = read_name(&b, fits).expect("255 octets is fine");
    assert_eq!(n.len(), 7);
    assert!(read_name(&b, over).is_none());
    // Names live in a growable arena, never a fixed buffer, and the proof
    // bounds every decoded name at 255 octets however it is assembled.
}

/// CVE-2023-4408 (BIND 9, CVSS 7.5): parsing a large message with many
/// names had super-linear cost, so crafted messages pinned the CPU.
#[test]
fn cve_2023_4408_large_message_is_linear() {
    // A maximal TCP-sized message: one question with a 255-octet name, then
    // as many records as fit, each owner a pointer to a different label of
    // that name so the memos rarely apply and nearly every owner decodes and copies up to
    // 255 octets.
    let labels: Vec<Vec<u8>> = (0..127).map(|i| vec![b'a' + (i % 26) as u8]).collect();
    let refs: Vec<&[u8]> = labels.iter().map(|l| &l[..]).collect();
    let name = wire(&refs);
    assert_eq!(name.len(), 255);
    let records = (65_535 - 12 - name.len() - 4) / 12;
    let mut b = header(1, records as u16, 0, 0);
    b.extend_from_slice(&name);
    b.extend_from_slice(&[0, 1, 0, 1]);
    for i in 0..records {
        b.extend_from_slice(&ptr(12 + 2 * (i % 127)));
        b.extend_from_slice(&[0, 1, 0, 1, 0, 0, 0, 0, 0, 0]);
    }
    let t = Instant::now();
    let m = quick(|| parse(&b).expect("valid message"));
    println!("{} records, {} bytes: {:?}", records, b.len(), t.elapsed());
    assert_eq!(m.answers().len(), records);
    // Count limits: claiming 65535 of each section in a short message is
    // rejected before any decoding (RFC 9267 §6).
    let mut b = header(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF);
    b.extend_from_slice(&[0; 100]);
    quick(|| assert!(parse(&b).is_none()));
}
