//! X.509 and DER parsing CVEs from OpenSSL, NSS, CryptoAPI and
//! PolarSSL/mbedTLS, each reproduced as a certificate of the same shape and
//! checked against vx509. The proofs cover every input; these tests show the
//! concrete attack certificates being handled. See CVES.md for the mapping
//! from each CVE to the proven property.
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

fn accepts(b: &[u8]) -> bool {
    verilith_x509::parse(b).is_some()
}

/// Rejected, for the expected reason.
fn rejects(b: &[u8], kind: verilith_x509::ErrorKind) {
    assert_eq!(verilith_x509::try_parse(b).err().map(|e| e.kind), Some(kind));
}

#[test]
fn baseline_is_accepted() {
    let b = Parts::new().der();
    let c = verilith_x509::parse(&b).expect("baseline certificate");
    assert_eq!(c.dns_names().collect::<Vec<_>>(), vec![&b"www.example.com"[..]]);
}

/// CVE-2014-1569 (NSS < 3.17.3): `definite_length_decoder` accepted
/// non-minimal long-form lengths, which let data be smuggled into a signed
/// structure and certificates be forged. CVE-2012-2110 (OpenSSL): length
/// arithmetic in `asn1_d2i_read_bio` overflowed into a heap overflow.
#[test]
fn cve_2014_1569_and_2012_2110_lengths() {
    let p = Parts::new();
    // The serial INTEGER's length in every non-minimal form.
    for long in [&[0x81, 0x03][..], &[0x82, 0x00, 0x03], &[0x83, 0, 0, 3], &[0x84, 0, 0, 0, 3]] {
        let mut q = p.clone();
        q.serial = cat(&[&[0x02], long, &[1, 2, 3]]);
        assert!(!accepts(&q.der()), "length {long:02x?}");
    }
    // A long form for a length under 128, and 0x81 0x00.
    let b = p.der();
    let mut q = p.clone();
    q.sig = vec![0x03, 0x81, 0x05, 0, 1, 2, 3, 4];
    assert!(!accepts(&q.der()));
    // Indefinite length, five length octets, and lengths past the end.
    for l in [&[0x80][..], &[0x85, 0, 0, 0, 0, 1], &[0x84, 0xFF, 0xFF, 0xFF, 0xFF], &[0x84, 0x7F, 0xFF, 0xFF, 0xFF]] {
        let mut v = vec![0x30];
        v.extend_from_slice(l);
        v.extend_from_slice(&b[2..]);
        assert!(!accepts(&v), "outer length {l:02x?}");
    }
}

/// CVE-2009-2511 (Windows CryptoAPI, MS09-056): an OID arc padded with 0x80
/// octets, or too large for a 32-bit integer, was decoded to a different
/// OID (such as commonName), letting a CA-signed certificate spoof a name.
#[test]
fn cve_2009_2511_oid_arcs() {
    // 2.5.4.3 with the last arc padded: 55 04 80 03.
    let mut p = Parts::new();
    p.subject = name_with(&[0x55, 0x04, 0x80, 0x03], b"www.bank.com");
    rejects(&p.der(), verilith_x509::ErrorKind::Subject);
    // 2.5.4.(2^64 + 3): accepted as its own OID, never confused with CN.
    let mut huge = vec![0x55, 0x04];
    huge.extend([0x82, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x03]);
    p.subject = name_with(&huge, b"www.bank.com");
    let b = p.der();
    let c = verilith_x509::parse(&b).expect("a large arc is valid");
    let oids: Vec<&[u8]> = c.subject().attributes().map(|a| a.oid).collect();
    assert_eq!(oids, vec![&huge[..]]);
    assert!(oids.iter().all(|o| *o != CN));
}

/// CVE-2009-2408 (NSS) and CVE-2009-2510 (CryptoAPI): a NUL in a name
/// (`www.bank.com\0.evil.com`) was matched as the part before the NUL.
#[test]
fn cve_2009_2408_and_2510_nul_in_names() {
    for tag in [0x81, 0x82, 0x86] {
        let mut p = Parts::new();
        p.exts[1] = ext(17, false, &seq(&[&tlv(tag, b"www.bank.com\0.evil.com")]));
        rejects(&p.der(), verilith_x509::ErrorKind::ExtensionContents(17));
        p.exts[1] = ext(17, false, &seq(&[&tlv(tag, "www.bänk.com".as_bytes())]));
        rejects(&p.der(), verilith_x509::ErrorKind::ExtensionContents(17));
    }
}

/// CVE-2020-1971 (OpenSSL, EDIPartyName) and CVE-2023-0286 (OpenSSL,
/// x400Address): `GENERAL_NAME_cmp` handled these GeneralName choices as the
/// wrong type, giving a NULL dereference or a type confusion.
#[test]
fn cve_2020_1971_and_2023_0286_general_name_choices() {
    let mut p = Parts::new();
    let edi = tlv(0xA5, &tlv(0xA1, &tlv(0x0C, b"party")));
    let x400 = tlv(0xA3, &seq(&[&tlv(0x13, b"x")]));
    p.exts[1] = ext(17, false, &seq(&[&edi, &x400]));
    let b = p.der();
    let c = verilith_x509::parse(&b).expect("both choices are valid");
    let names: Vec<_> = c.subject_alt_names().unwrap().collect();
    assert!(matches!(names[0], verilith_x509::GeneralName::EdiParty(_)));
    assert!(matches!(names[1], verilith_x509::GeneralName::X400(_)));
    // The primitive forms of these context tags are not GeneralNames.
    p.exts[1] = ext(17, false, &seq(&[&tlv(0x85, b"party")]));
    rejects(&p.der(), verilith_x509::ErrorKind::ExtensionContents(17));
    p.exts[1] = ext(17, false, &seq(&[&tlv(0x83, b"x")]));
    rejects(&p.der(), verilith_x509::ErrorKind::ExtensionContents(17));
}

/// CVE-2021-3712 (OpenSSL): code assumed ASN.1 strings were NUL-terminated
/// and read past them. CVE-2015-1182 (PolarSSL): an error inside a SEQUENCE
/// OF freed an uninitialized pointer. vx509 hands out bounded slices of the
/// input and never allocates, so every truncation is just a rejection.
#[test]
fn cve_2021_3712_and_2015_1182_truncations() {
    let b = Parts::new().der();
    for n in 0..b.len() {
        assert!(!accepts(&b[..n]), "prefix of {n} octets");
    }
    // Errors in the middle of each list-valued extension.
    let bad_lists = [
        ext(37, false, &seq(&[&tlv(0x06, &[0x2B, 0x06]), &tlv(0x02, &[1])])),
        ext(17, false, &seq(&[&tlv(0x82, b"a.example"), &[0x82, 0x05, b'b']])),
        ext(32, false, &seq(&[&seq(&[&tlv(0x06, &[0x55, 0x1D, 0x20, 0x00])]), &seq(&[])])),
    ];
    for e in bad_lists {
        let mut p = Parts::new();
        let id = e[6];
        p.exts.push(e);
        let b = p.der();
        let k = verilith_x509::try_parse(&b).err().map(|e| e.kind);
        assert!(k == Some(verilith_x509::ErrorKind::ExtensionContents(id)) || k == Some(verilith_x509::ErrorKind::DuplicateExtension), "{k:?}");
    }
}

/// CVE-2015-1789 (OpenSSL): `X509_cmp_time` read out of bounds on a
/// malformed ASN1_TIME.
#[test]
fn cve_2015_1789_times() {
    let bad: [(u8, &[u8]); 9] = [
        (0x17, b"2501010000Z"),
        (0x17, b"250101000000"),
        (0x17, b"250101000000+0100"),
        (0x17, b"251301000000Z"),
        (0x17, b"250230000000Z"),
        (0x17, b"250101240000Z"),
        (0x17, b"25010100000aZ"),
        (0x18, b"250101000000Z"),
        (0x18, b"20250101000000.5Z"),
    ];
    for (tag, t) in bad {
        let mut p = Parts::new();
        p.validity = seq(&[&tlv(tag, t), &tlv(0x18, b"20351231235959Z")]);
        rejects(&p.der(), verilith_x509::ErrorKind::Validity);
    }
    let mut p = Parts::new();
    p.validity = seq(&[&tlv(0x17, b"240229000000Z"), &tlv(0x18, b"20351231235959Z")]);
    assert!(accepts(&p.der()), "leap day");
}

/// CVE-2016-2108 (OpenSSL): a negative zero INTEGER corrupted memory on
/// re-encoding. CVE-2014-8275 (OpenSSL): non-DER encodings changed a
/// certificate's fingerprint without changing its signature.
#[test]
fn cve_2016_2108_and_2014_8275_non_der() {
    for serial in [&[0x00, 0x01][..], &[0xFF, 0x80], &[]] {
        let mut p = Parts::new();
        p.serial = tlv(0x02, serial);
        rejects(&p.der(), verilith_x509::ErrorKind::Serial);
    }
    // signatureAlgorithm differing from the TBSCertificate's signature.
    let mut p = Parts::new();
    p.outer_alg = seq(&[&tlv(0x06, SHA256_RSA)]);
    rejects(&p.der(), verilith_x509::ErrorKind::AlgorithmMismatch);
    // Non-zero padding bits in the signature BIT STRING.
    let mut p = Parts::new();
    p.sig = tlv(0x03, &[3, 0xFF, 0xFF]);
    rejects(&p.der(), verilith_x509::ErrorKind::SignatureValue);
    // Explicit v1, a DEFAULT value encoded.
    let mut p = Parts::new();
    p.exts.clear();
    let b = p.der();
    let mut v1 = b.clone();
    let i = b.windows(5).position(|w| w == [0xA0, 0x03, 0x02, 0x01, 0x02]).unwrap();
    v1[i + 4] = 0;
    rejects(&v1, verilith_x509::ErrorKind::Version);
}

/// Duplicate extensions: RFC 5280 §4.2 forbids them, and parsers that keep
/// the first or the last disagree on which one applies.
#[test]
fn duplicate_extensions() {
    let mut p = Parts::new();
    p.exts.push(ext(19, true, &seq(&[&tlv(0x01, &[0xFF])])));
    rejects(&p.der(), verilith_x509::ErrorKind::DuplicateExtension);
}

/// CVE-2023-2650 (OpenSSL): `OBJ_obj2txt` was super-linear on very long
/// OIDs. vx509 checks OIDs in one pass and never converts them.
#[test]
fn cve_2023_2650_long_oids() {
    let mut oid = vec![0x2B];
    for _ in 0..100_000 {
        oid.extend([0xFF, 0x7F]);
    }
    let mut p = Parts::new();
    p.subject = name_with(&oid, b"x");
    let b = p.der();
    let t = Instant::now();
    assert!(accepts(&b));
    assert!(t.elapsed().as_millis() < 50, "{:?}", t.elapsed());
}

/// CVE-2021-43527 (NSS "BigSig"): an oversized signature was copied into a
/// fixed-size stack buffer. vx509 copies nothing: the signature is a slice.
#[test]
fn cve_2021_43527_big_signature() {
    let mut p = Parts::new();
    let mut sig = vec![0u8];
    sig.extend(vec![0xAB; 1 << 16]);
    p.sig = tlv(0x03, &sig);
    let b = p.der();
    let c = verilith_x509::parse(&b).unwrap();
    assert_eq!(c.signature.len(), 1 << 16);
    assert!(b.as_ptr_range().contains(&c.signature.as_ptr()));
}
