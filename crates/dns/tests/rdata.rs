mod common;
use common::*;
use verilith_dns::rdata::Rdata;
use verilith_dns::{parse, Name};

/// A response to `example.com`: the question name at offset 12, then one
/// answer of type `rtype` with the given RDATA.
fn answer(rtype: u16, rdata: &[u8]) -> Vec<u8> {
    let mut b = vec![0x12, 0x34, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0];
    b.extend_from_slice(&wire(&[b"example", b"com"]));
    b.extend_from_slice(&[0, 1, 0, 1]);
    b.extend_from_slice(&[0xC0, 12]);
    b.extend_from_slice(&rtype.to_be_bytes());
    b.extend_from_slice(&[0, 1, 0, 0, 0x0E, 0x10]);
    b.extend_from_slice(&(rdata.len() as u16).to_be_bytes());
    b.extend_from_slice(rdata);
    b
}

fn decode(rtype: u16, rdata: &[u8]) -> Option<String> {
    let b = answer(rtype, rdata);
    // RDATA of a type with names in it is decoded while parsing, so a bad
    // one rejects the message; any other type is decoded on demand.
    let Some(m) = parse(&b) else {
        assert!(matches!(rtype, 2 | 5 | 6 | 12 | 15 | 24 | 33 | 35), "message parses");
        return None;
    };
    let rr = m.answers().next().unwrap();
    rr.data().map(|d| show(&d))
}

fn n(w: &[u8]) -> String {
    Name::from_wire(w).to_string()
}

fn show(d: &Rdata) -> String {
    let s = |x: &[u8]| String::from_utf8_lossy(x).into_owned();
    match d {
        Rdata::A(a) => format!("A {}.{}.{}.{}", a[0], a[1], a[2], a[3]),
        Rdata::Aaaa(a) => format!("AAAA {:02x?}", a),
        Rdata::Ns(x) => format!("NS {}", n(x)),
        Rdata::Cname(x) => format!("CNAME {}", n(x)),
        Rdata::Ptr(x) => format!("PTR {}", n(x)),
        Rdata::Mx { preference, exchange } => format!("MX {} {}", preference, n(exchange)),
        Rdata::Txt(v) => format!("TXT {:?}", v.iter().map(|x| s(x)).collect::<Vec<_>>()),
        Rdata::Hinfo { cpu, os } => format!("HINFO {} {}", s(cpu), s(os)),
        Rdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => format!(
            "SOA {} {} {} {} {} {} {}",
            n(mname),
            n(rname),
            serial,
            refresh,
            retry,
            expire,
            minimum
        ),
        Rdata::Sig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature } => format!(
            "SIG {} {} {} {} {} {} {} {} {:02x?}",
            type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, n(signer), signature
        ),
        Rdata::Rrsig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature } => format!(
            "RRSIG {} {} {} {} {} {} {} {} {:02x?}",
            type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, n(signer), signature
        ),
        Rdata::Ds { key_tag, algorithm, digest_type, digest } => {
            format!("DS {} {} {} {:02x?}", key_tag, algorithm, digest_type, digest)
        }
        Rdata::Sshfp { algorithm, fp_type, fingerprint } => format!("SSHFP {} {} {:02x?}", algorithm, fp_type, fingerprint),
        Rdata::Nsec { next, type_bitmaps } => format!("NSEC {} {:02x?}", n(next), type_bitmaps),
        Rdata::Dnskey { flags, protocol, algorithm, public_key } => {
            format!("DNSKEY {} {} {} {:02x?}", flags, protocol, algorithm, public_key)
        }
        Rdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } => format!(
            "NSEC3 {} {} {} {:02x?} {:02x?} {:02x?}",
            hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps
        ),
        Rdata::Nsec3param { hash_algorithm, flags, iterations, salt } => {
            format!("NSEC3PARAM {} {} {} {:02x?}", hash_algorithm, flags, iterations, salt)
        }
        Rdata::Srv { priority, weight, port, target } => {
            format!("SRV {} {} {} {}", priority, weight, port, n(target))
        }
        Rdata::Naptr { order, preference, flags, services, regexp, replacement } => format!(
            "NAPTR {} {} {} {} {} {}",
            order,
            preference,
            s(flags),
            s(services),
            s(regexp),
            n(replacement)
        ),
        Rdata::Opt(v) => format!("OPT {:?}", v),
        Rdata::Tlsa { usage, selector, matching, data } => {
            format!("TLSA {} {} {} {:02x?}", usage, selector, matching, data)
        }
        Rdata::Svcb { priority, target, params } => {
            format!("SVCB {} {} {:?}", priority, n(target), params)
        }
        Rdata::Https { priority, target, params } => {
            format!("HTTPS {} {} {:?}", priority, n(target), params)
        }
        Rdata::Uri { priority, weight, target } => format!("URI {} {} {}", priority, weight, s(target)),
        Rdata::Caa { flags, tag, value } => format!("CAA {} {} {}", flags, s(tag), s(value)),
        Rdata::Unknown(x) => format!("UNKNOWN {:02x?}", x),
    }
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

#[test]
fn decodes_every_type() {
    let www = wire(&[b"www"]);
    // "www" followed by a pointer to example.com: a compressed name in RDATA.
    let www_c = cat(&[&[3], b"www", &[0xC0, 12]]);
    let cases: Vec<(u16, Vec<u8>, &str)> = vec![
        (1, vec![93, 184, 216, 34], "A 93.184.216.34"),
        (28, (0..16).collect(), "AAAA [00, 01, 02, 03, 04, 05, 06, 07, 08, 09, 0a, 0b, 0c, 0d, 0e, 0f]"),
        (2, www_c.clone(), "NS www.example.com."),
        (5, vec![0xC0, 12], "CNAME example.com."),
        (12, www.clone(), "PTR www."),
        (15, cat(&[&[0, 10], &www_c]), "MX 10 www.example.com."),
        (16, cat(&[&[5], b"hello", &[0], &[3], b"abc"]), "TXT [\"hello\", \"\", \"abc\"]"),
        (13, cat(&[&[3], b"x86", &[5], b"linux"]), "HINFO x86 linux"),
        (
            6,
            cat(&[&www_c, &[0xC0, 12], &1u32.to_be_bytes(), &2u32.to_be_bytes(), &3u32.to_be_bytes(),
                &4u32.to_be_bytes(), &5u32.to_be_bytes()]),
            "SOA www.example.com. example.com. 1 2 3 4 5",
        ),
        (33, cat(&[&[0, 1, 0, 2, 0x01, 0xBB], &www_c]), "SRV 1 2 443 www.example.com."),
        (
            35,
            cat(&[&[0, 100, 0, 10], &[1], b"S", &[7], b"SIP+D2U", &[0], &[4], b"_sip", &[0xC0, 12]]),
            "NAPTR 100 10 S SIP+D2U  _sip.example.com.",
        ),
        (41, vec![0, 10, 0, 2, 0xAB, 0xCD, 0, 12, 0, 0], "OPT [(10, [171, 205]), (12, [])]"),
        (52, vec![3, 1, 1, 0xAA, 0xBB], "TLSA 3 1 1 [aa, bb]"),
        (64, cat(&[&[0, 1], &www, &[0, 1, 0, 2], b"h2", &[0, 3, 0, 2, 1, 187]]),
            "SVCB 1 www. [(1, [104, 50]), (3, [1, 187])]"),
        (65, vec![0, 0, 0], "HTTPS 0 . []"),
        (256, cat(&[&[0, 1, 0, 2], b"https://x"]), "URI 1 2 https://x"),
        (257, cat(&[&[0, 5], b"issue", b"ca.example"]), "CAA 0 issue ca.example"),
        (
            24,
            cat(&[&[0, 1, 8, 2], &60u32.to_be_bytes(), &9u32.to_be_bytes(), &7u32.to_be_bytes(), &[0x12, 0x34],
                &[0xC0, 12], &[0xEE]]),
            "SIG 1 8 2 60 9 7 4660 example.com. [ee]",
        ),
        (
            46,
            cat(&[&[0, 1, 8, 2], &60u32.to_be_bytes(), &9u32.to_be_bytes(), &7u32.to_be_bytes(), &[0x12, 0x34],
                &www, &[0xEE]]),
            "RRSIG 1 8 2 60 9 7 4660 www. [ee]",
        ),
        (43, vec![0x12, 0x34, 8, 2, 0xAA], "DS 4660 8 2 [aa]"),
        (44, vec![1, 2, 0xAA], "SSHFP 1 2 [aa]"),
        (47, cat(&[&www, &[0, 1, 0x40]]), "NSEC www. [00, 01, 40]"),
        (48, vec![1, 1, 3, 8, 0xAA], "DNSKEY 257 3 8 [aa]"),
        (50, vec![1, 0, 0, 10, 2, 0xAB, 0xCD, 1, 0xEF, 0, 1, 0x40], "NSEC3 1 0 10 [ab, cd] [ef] [00, 01, 40]"),
        (51, vec![1, 0, 0, 10, 0], "NSEC3PARAM 1 0 10 []"),
        (99, vec![1, 2, 3], "UNKNOWN [01, 02, 03]"),
    ];
    for (t, rdata, want) in cases {
        assert_eq!(decode(t, &rdata).as_deref(), Some(want), "type {t}");
    }
}

#[test]
fn rejects_rdata_that_does_not_match_its_type() {
    let www_c = cat(&[&[3], b"www", &[0xC0, 12]]);
    let bad: Vec<(u16, Vec<u8>)> = vec![
        (1, vec![1, 2, 3]),                                  // A must be 4 octets
        (28, vec![0; 15]),                                   // AAAA must be 16
        (2, cat(&[&www_c, &[0]])),                           // trailing byte after the name
        (5, vec![3, b'w', b'w']),                            // name runs past the RDATA
        (15, vec![0]),                                       // MX shorter than its preference
        (16, vec![]),                                        // TXT needs at least one string
        (16, vec![5, b'a']),                                 // string longer than the RDATA
        (13, cat(&[&[3], b"x86"])),                          // HINFO needs two strings
        (6, cat(&[&www_c, &[0xC0, 12], &[0; 19]])),          // SOA needs exactly 20 more octets
        (33, vec![0, 1, 0, 2, 0]),                           // SRV shorter than its fixed fields
        (41, vec![0, 10, 0, 5, 1]),                          // option longer than the RDATA
        (24, vec![0; 17]),                                   // SIG shorter than its fixed fields
        (46, cat(&[&[0; 18], &[0xC0, 12]])),                 // RRSIG signer must not be compressed
        (47, vec![0xC0, 12]),                                // nor the NSEC next name
        (43, vec![0, 1, 2]),                                 // DS shorter than its fixed fields
        (50, vec![1, 0, 0, 10, 3, 0xAB]),                    // NSEC3 salt longer than the RDATA
        (51, vec![1, 0, 0, 10, 0, 0]),                       // NSEC3PARAM trailing byte
        (52, vec![3, 1]),                                    // TLSA shorter than its fixed fields
        (64, cat(&[&[0, 1], &[0xC0, 12]])),                  // SVCB target must not be compressed
        (64, cat(&[&[0, 1, 0], &[0, 3, 0, 0, 0, 1, 0, 0]])), // SVCB keys must increase
        (256, vec![0, 1, 0, 2]),                             // URI target must not be empty
        (257, cat(&[&[0, 0]])),                              // CAA tag must not be empty
        (257, cat(&[&[0, 3], b"is-"])),                      // CAA tag must be alphanumeric
        (257, cat(&[&[0, 9], b"issue"])),                    // CAA tag longer than the RDATA
    ];
    for (t, rdata) in bad {
        assert_eq!(decode(t, &rdata), None, "type {t} rdata {rdata:?}");
    }
}

/// CVE-2017-1000381 (c-ares, CVSS 7.5): `ares_parse_naptr_reply` read past
/// the end of the input on crafted NAPTR RDATA.
#[test]
fn cve_2017_1000381_naptr_out_of_bounds() {
    let full = cat(&[&[0, 100, 0, 10], &[1], b"S", &[7], b"SIP+D2U", &[0], &[0]]);
    assert!(decode(35, &full).is_some());
    // Every truncation of the RDATA, with RDLENGTH matching what is there
    // (so the message itself is fine), and every way of overstating one of
    // the string lengths.
    for len in 0..full.len() {
        assert_eq!(decode(35, &full[..len]), None, "truncated to {len}");
    }
    for at in [4, 6, 14] {
        for v in [full[at] + 1, 0x7F, 0xFF] {
            let mut b = full.clone();
            b[at] = v;
            assert_eq!(decode(35, &b), None, "length at {at} = {v}");
        }
    }
    // A replacement name that runs into the next record or off the end.
    let mut b = answer(35, &cat(&[&[0, 1, 0, 1, 0, 0, 0], &[3], b"www"]));
    b.extend_from_slice(&[0]);
    assert!(parse(&b).is_none() || parse(&b).unwrap().answers().next().unwrap().data().is_none());
}

/// CVE-2021-3672 (c-ares, CVSS 5.6): host names from DNS were not
/// validated, so a label containing `.` or control characters printed as a
/// different name. Presentation format escapes them.
#[test]
fn cve_2021_3672_hostile_labels_are_escaped() {
    let cases: Vec<(Vec<u8>, &str)> = vec![
        (wire(&[b"evil.com", b"example"]), "evil\\.com.example."),
        (wire(&[b"a\0b"]), "a\\000b."),
        (wire(&[b"\\"]), "\\\\."),
        (wire(&[b"$(x)"]), "\\$\\(x\\)."),
    ];
    for (w, want) in cases {
        let b = answer(5, &w);
        let m = parse(&b).unwrap();
        let rr = m.answers().next().unwrap();
        match rr.data() {
            Some(Rdata::Cname(x)) => assert_eq!(n(&x), want),
            _ => panic!("expected a CNAME"),
        }
    }
}

/// Names inside RDATA are decompressed while parsing, so re-serializing a
/// parsed message keeps their meaning. (Copying the RDATA bytes as they
/// were would keep a pointer to offset 12, which in the uncompressed output
/// is a different name.)
#[test]
fn reserializing_keeps_names_in_rdata() {
    let www_c = cat(&[&[3], b"www", &[0xC0, 12]]);
    for (t, rdata) in [
        (5u16, www_c.clone()),
        (15, cat(&[&[0, 10], &www_c])),
        (6, cat(&[&www_c, &[0xC0, 12], &[0; 20]])),
        (33, cat(&[&[0, 1, 0, 2, 0, 3], &www_c])),
    ] {
        let mut b = answer(t, &rdata);
        // Move every later offset: a second question pushes the answer, and
        // so its RDATA, further from the name it points to.
        b[5] = 2;
        let q2 = cat(&[&[1, b'q', 0xC0, 12], &[0, 1, 0, 1]]);
        let at = 12 + 13 + 4;
        b.splice(at..at, q2);
        let m = parse(&b).unwrap();
        let before = show(&m.answers().next().unwrap().data().unwrap());
        assert!(before.contains("www.example.com."), "{before}");
        let again = parse(&m.to_bytes()).unwrap();
        let after = show(&again.answers().next().unwrap().data().unwrap());
        assert_eq!(before, after);
        assert!(same(&m, &again));
    }
}
