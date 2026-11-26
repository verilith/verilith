//! Work bounds, shown on certificates built to hit the slow paths. The proof
//! (`parse_metered`) covers every input; these check that the bound is what
//! the code does, with timings far below what a quadratic check would take.
#![allow(dead_code)]
use std::time::Instant;

fn len(n: usize) -> Vec<u8> {
    match n {
        0..=0x7F => vec![n as u8],
        0x80..=0xFF => vec![0x81, n as u8],
        0x100..=0xFFFF => vec![0x82, (n >> 8) as u8, n as u8],
        _ => vec![0x83, (n >> 16) as u8, (n >> 8) as u8, n as u8],
    }
}

fn tlv(tag: u8, c: &[u8]) -> Vec<u8> {
    let mut v = vec![tag];
    v.extend(len(c.len()));
    v.extend_from_slice(c);
    v
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn seq(parts: &[&[u8]]) -> Vec<u8> {
    tlv(0x30, &cat(parts))
}

const CN: &[u8] = &[0x55, 0x04, 0x03];
const SHA256_RSA: &[u8] = &[0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x0B];
const EC_KEY: &[u8] = &[0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01];
const P256: &[u8] = &[0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07];

fn name_with(oid: &[u8], value: &[u8]) -> Vec<u8> {
    seq(&[&tlv(0x31, &seq(&[&tlv(0x06, oid), &tlv(0x0C, value)]))])
}

fn ext(id_ce: u8, critical: bool, value: &[u8]) -> Vec<u8> {
    let crit = if critical { tlv(0x01, &[0xFF]) } else { vec![] };
    seq(&[&tlv(0x06, &[0x55, 0x1D, id_ce]), &crit, &tlv(0x04, value)])
}

/// The parts of a v3 certificate, as DER, to modify one at a time.
#[derive(Clone)]
struct Parts {
    serial: Vec<u8>,
    alg: Vec<u8>,
    issuer: Vec<u8>,
    validity: Vec<u8>,
    subject: Vec<u8>,
    spki: Vec<u8>,
    exts: Vec<Vec<u8>>,
    outer_alg: Vec<u8>,
    sig: Vec<u8>,
}

impl Parts {
    fn new() -> Parts {
        let alg = seq(&[&tlv(0x06, SHA256_RSA), &tlv(0x05, &[])]);
        let mut point = vec![0x04];
        point.extend([7u8; 64]);
        let mut key = vec![0];
        key.extend(point);
        Parts {
            serial: tlv(0x02, &[0x01, 0x02, 0x03]),
            alg: alg.clone(),
            issuer: name_with(CN, b"Test CA"),
            validity: seq(&[&tlv(0x17, b"250101000000Z"), &tlv(0x18, b"20351231235959Z")]),
            subject: name_with(CN, b"www.example.com"),
            spki: seq(&[&seq(&[&tlv(0x06, EC_KEY), &tlv(0x06, P256)]), &tlv(0x03, &key)]),
            exts: vec![
                ext(19, true, &seq(&[])),
                ext(17, false, &seq(&[&tlv(0x82, b"www.example.com")])),
            ],
            outer_alg: alg,
            sig: tlv(0x03, &[0, 1, 2, 3, 4]),
        }
    }

    fn tbs(&self) -> Vec<u8> {
        let exts = tlv(0xA3, &seq(&self.exts.iter().map(|e| &e[..]).collect::<Vec<_>>()));
        seq(&[
            &tlv(0xA0, &tlv(0x02, &[2])),
            &self.serial,
            &self.alg,
            &self.issuer,
            &self.validity,
            &self.subject,
            &self.spki,
            if self.exts.is_empty() { &[] } else { &exts },
        ])
    }

    fn der(&self) -> Vec<u8> {
        seq(&[&self.tbs(), &self.outer_alg, &self.sig])
    }
}

/// An extension with the private OID 1.3.6.1.4.1.`i` and an empty value.
fn private_ext(i: u32) -> Vec<u8> {
    let mut oid = vec![0x2B, 0x06, 0x01, 0x04, 0x01];
    let mut arc = vec![(i & 0x7F) as u8];
    let mut x = i >> 7;
    while x > 0 {
        arc.push(0x80 | (x & 0x7F) as u8);
        x >>= 7;
    }
    arc.reverse();
    oid.extend(arc);
    seq(&[&tlv(0x06, &oid), &tlv(0x04, &[])])
}

fn with_private(n: u32, extra: Option<u32>) -> Vec<u8> {
    let mut p = Parts::new();
    for i in 0..n {
        p.exts.push(private_ext(i));
    }
    if let Some(i) = extra {
        p.exts.push(private_ext(i));
    }
    p.der()
}

const N: u32 = 50_000;

/// More than eight OIDs outside the low id-ce arcs take the second pass of
/// the duplicate check. 50,000 of them would be about 1.25e9 comparisons
/// for a check of each against every later one.
#[test]
fn many_distinct_extensions() {
    let b = with_private(N, None);
    let t = Instant::now();
    let c = verilith_x509::parse(&b).expect("distinct extensions");
    let e = t.elapsed();
    assert_eq!(c.extensions().count(), N as usize + 2);
    eprintln!("{N} distinct extensions: {e:?}");
    assert!(e.as_millis() < 1000, "{e:?}");
}

/// The same with one repeated OID at the end, and at the start.
#[test]
fn many_extensions_one_duplicate() {
    for (dup, at) in [(N - 1, N), (0, N), (7, 9)] {
        let mut p = Parts::new();
        for i in 0..N {
            p.exts.push(private_ext(i));
            if i == at {
                p.exts.push(private_ext(dup));
            }
        }
        if at == N {
            p.exts.push(private_ext(dup));
        }
        let b = p.der();
        let t = Instant::now();
        assert!(verilith_x509::parse(&b).is_none());
        let e = verilith_x509::try_parse(&b).err().unwrap();
        let el = t.elapsed();
        assert_eq!(e.kind, verilith_x509::ErrorKind::DuplicateExtension);
        let rest = &b[e.offset..];
        assert!(rest.starts_with(&private_ext(dup)), "offset {}", e.offset);
        assert!(el.as_millis() < 2000, "{el:?}");
    }
}

/// Exactly nine private OIDs, the first list that needs the second pass,
/// and a repeated id-ce OID among them.
#[test]
fn second_pass_edges() {
    assert!(verilith_x509::parse(&with_private(8, None)).is_some());
    assert!(verilith_x509::parse(&with_private(9, None)).is_some());
    assert!(verilith_x509::parse(&with_private(9, Some(8))).is_none());
    assert!(verilith_x509::parse(&with_private(9, Some(0))).is_none());
    let mut p = Parts::new();
    for i in 0..20 {
        p.exts.push(private_ext(i));
    }
    p.exts.push(ext(19, false, &seq(&[])));
    assert!(verilith_x509::parse(&p.der()).is_none());
}
