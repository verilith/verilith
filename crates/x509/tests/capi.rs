//! The native C API (`src/native.rs`) against the Rust API it wraps: both
//! must describe every certificate the same way, and reject the same ones.
#![cfg(feature = "capi")]
#![allow(unsafe_op_in_unsafe_fn)]
use std::fmt::Write;
use verilith_x509::native::*;
use verilith_x509::GeneralName;

fn gn_rust(g: GeneralName, o: &mut String) {
    match g {
        GeneralName::Other { type_id, value } => write!(o, "g0{:?}{:?}{:?}", value.content, type_id, value.tag),
        GeneralName::Rfc822(v) => write!(o, "g1{v:?}"),
        GeneralName::Dns(v) => write!(o, "g2{v:?}"),
        GeneralName::X400(v) => write!(o, "g3{v:?}"),
        GeneralName::Directory(n) => {
            write!(o, "g4{:?}", n.raw).unwrap();
            name_rust(n, o);
            Ok(())
        }
        GeneralName::EdiParty(v) => write!(o, "g5{v:?}"),
        GeneralName::Uri(v) => write!(o, "g6{v:?}"),
        GeneralName::Ip(v) => write!(o, "g7{v:?}"),
        GeneralName::Registered(v) => write!(o, "g8{v:?}"),
    }
    .unwrap()
}

fn name_rust(n: verilith_x509::Name, o: &mut String) {
    for r in n.rdns() {
        o.push('(');
        for a in r.attributes() {
            write!(o, "{:?}={:?}/{:?};", a.oid, a.value.tag, a.value.content).unwrap();
        }
        o.push(')');
    }
}

fn alg_rust(a: &verilith_x509::AlgId, o: &mut String) {
    write!(o, "alg{:?}{:?}", a.oid, a.params.map(|p| (p.tag, p.content))).unwrap();
}

fn dump_rust(c: &verilith_x509::Certificate) -> String {
    let mut o = String::new();
    let t = &c.tbs;
    write!(o, "v{} tbs{:?} ser{:?} ", t.version + 1, c.tbs_der, t.serial).unwrap();
    alg_rust(&t.signature, &mut o);
    name_rust(t.issuer, &mut o);
    name_rust(t.subject, &mut o);
    for x in [t.not_before, t.not_after] {
        write!(o, " {}-{}-{}T{}:{}:{}={}", x.year, x.month, x.day, x.hour, x.minute, x.second, x.unix_timestamp())
            .unwrap();
    }
    write!(o, " spki{:?}", t.spki_der).unwrap();
    alg_rust(&t.spki.alg, &mut o);
    write!(o, " key{:?} sig{:?}", t.spki.key, c.signature).unwrap();
    write!(o, " uid{:?}{:?}", t.issuer_uid.map(|u| (u.unused, u.bytes)), t.subject_uid.map(|u| (u.unused, u.bytes)))
        .unwrap();
    for e in c.extensions() {
        write!(o, " ext{:?}{}{:?}", e.oid, e.critical, e.value).unwrap();
        let f = c.extension(e.oid).unwrap();
        write!(o, "~{:?}{}{:?}:{}", f.oid, f.critical, f.value, verilith_x509::OidDisplay(e.oid)).unwrap();
    }
    write!(o, " bc{:?}", c.basic_constraints().map(|b| (b.ca, b.path_len))).unwrap();
    write!(o, " ku{:?}", c.key_usage()).unwrap();
    write!(o, " eku{:?}", c.ext_key_usage().map(|i| i.collect::<Vec<_>>())).unwrap();
    write!(o, " pol{:?}", c.certificate_policies().map(|i| i.collect::<Vec<_>>())).unwrap();
    for (tag, l) in [("san", c.subject_alt_names()), ("ian", c.issuer_alt_names())] {
        write!(o, " {tag}{}", l.is_some()).unwrap();
        l.into_iter().flatten().for_each(|g| gn_rust(g, &mut o));
    }
    write!(o, " ski{:?}", c.subject_key_id()).unwrap();
    match c.authority_key_id() {
        Some(a) => {
            write!(o, " aki{:?}{:?}{}", a.key_id, a.serial, a.issuer.is_some()).unwrap();
            a.issuer.into_iter().flat_map(verilith_x509::iter::GeneralNameIter::new).for_each(|g| gn_rust(g, &mut o));
        }
        None => o.push_str(" noaki"),
    }
    match c.name_constraints() {
        Some(n) => {
            for l in [n.permitted, n.excluded] {
                write!(o, " nc{}", l.is_some()).unwrap();
                l.into_iter().flat_map(verilith_x509::iter::SubtreeIter::new).for_each(|g| gn_rust(g, &mut o));
            }
        }
        None => o.push_str(" nonc"),
    }
    o
}

unsafe fn b<'a>(s: vx509_span) -> &'a [u8] {
    if s.p.is_null() {
        assert_eq!(s.len, 0);
        &[]
    } else {
        std::slice::from_raw_parts(s.p, s.len)
    }
}

unsafe fn ob<'a>(s: vx509_span) -> Option<&'a [u8]> {
    (!s.p.is_null()).then(|| b(s))
}

unsafe fn name_c(mut n: vx509_span, o: &mut String) {
    let mut rdn = std::mem::zeroed();
    let mut a = std::mem::zeroed::<vx509_atv>();
    while vx509_rdn_next(&mut n, &mut rdn) {
        o.push('(');
        while vx509_atv_next(&mut rdn, &mut a) {
            write!(o, "{:?}={:?}/{:?};", b(a.oid), b(a.value.tag), b(a.value.content)).unwrap();
        }
        o.push(')');
    }
    assert_eq!(n.len, 0);
}

unsafe fn gn_c(g: &vx509_general_name, o: &mut String) {
    write!(o, "g{}{:?}", g.kind, b(g.value)).unwrap();
    if g.kind == 0 {
        write!(o, "{:?}{:?}", b(g.other_type_id), b(g.other_value_tag)).unwrap();
    } else {
        assert!(g.other_type_id.p.is_null() && g.other_value_tag.p.is_null());
    }
    if g.kind == 4 {
        name_c(g.value, o);
    }
}

unsafe fn alg_c(a: &vx509_alg, o: &mut String) {
    let p = (!a.params.tag.p.is_null()).then(|| (b(a.params.tag), b(a.params.content)));
    write!(o, "alg{:?}{:?}", b(a.oid), p).unwrap();
}

unsafe fn oids_c(have: bool, mut l: vx509_span, next: unsafe extern "C" fn(*mut vx509_span, *mut vx509_span) -> bool) -> Option<Vec<&'static [u8]>> {
    have.then(|| {
        let mut v = Vec::new();
        let mut x = std::mem::zeroed();
        while next(&mut l, &mut x) {
            v.push(b(x));
        }
        v
    })
}

unsafe fn dump_c(c: &vx509_cert) -> String {
    let mut o = String::new();
    write!(o, "v{} tbs{:?} ser{:?} ", c.version, b(c.tbs), b(c.serial)).unwrap();
    alg_c(&c.signature_alg, &mut o);
    name_c(c.issuer, &mut o);
    name_c(c.subject, &mut o);
    for x in [&c.not_before, &c.not_after] {
        write!(o, " {}-{}-{}T{}:{}:{}={}", x.year, x.month, x.day, x.hour, x.minute, x.second, vx509_time_unix(x))
            .unwrap();
    }
    write!(o, " spki{:?}", b(c.spki)).unwrap();
    alg_c(&c.public_key_alg, &mut o);
    write!(o, " key{:?} sig{:?}", b(c.public_key), b(c.signature)).unwrap();
    write!(
        o,
        " uid{:?}{:?}",
        ob(c.issuer_uid).map(|u| (c.issuer_uid_unused_bits, u)),
        ob(c.subject_uid).map(|u| (c.subject_uid_unused_bits, u))
    )
    .unwrap();
    let mut exts = c.extensions;
    let mut e = std::mem::zeroed::<vx509_ext>();
    let mut f = std::mem::zeroed::<vx509_ext>();
    while vx509_ext_next(&mut exts, &mut e) {
        write!(o, " ext{:?}{}{:?}", b(e.oid), e.critical, b(e.value)).unwrap();
        assert!(vx509_ext_find(c, e.oid.p, e.oid.len, &mut f));
        // The text, through a buffer that is too small and then one that fits.
        let mut small = [0x55 as std::ffi::c_char; 4];
        let n = vx509_oid_text(e.oid.p, e.oid.len, small.as_mut_ptr(), 4);
        assert_eq!(small[3.min(n)], 0);
        let mut buf = vec![0 as std::ffi::c_char; n + 1];
        assert_eq!(vx509_oid_text(e.oid.p, e.oid.len, buf.as_mut_ptr(), n + 1), n);
        let text = std::ffi::CStr::from_ptr(buf.as_ptr()).to_str().unwrap();
        assert!(text.as_bytes().starts_with(std::slice::from_raw_parts(small.as_ptr() as *const u8, 3.min(n))));
        write!(o, "~{:?}{}{:?}:{}", b(f.oid), f.critical, b(f.value), text).unwrap();
    }
    assert!(!vx509_ext_find(c, [0x55, 0x1D, 0xFE].as_ptr(), 3, &mut f));
    let mut bc = std::mem::zeroed::<vx509_basic_constraints>();
    let have = vx509_get_basic_constraints(c, &mut bc);
    write!(o, " bc{:?}", have.then(|| (bc.ca, bc.has_path_len.then_some(bc.path_len)))).unwrap();
    let mut ku = 0u16;
    let have = vx509_get_key_usage(c, &mut ku);
    write!(o, " ku{:?}", have.then_some(ku)).unwrap();
    let mut l = std::mem::zeroed();
    let have = vx509_get_ext_key_usage(c, &mut l);
    write!(o, " eku{:?}", oids_c(have, l, vx509_oid_next)).unwrap();
    let have = vx509_get_certificate_policies(c, &mut l);
    write!(o, " pol{:?}", oids_c(have, l, vx509_policy_next)).unwrap();
    let mut g = std::mem::zeroed::<vx509_general_name>();
    for (tag, have) in [("san", vx509_get_subject_alt_names(c, &mut l)), ("ian", false)] {
        let have = if tag == "ian" { vx509_get_issuer_alt_names(c, &mut l) } else { have };
        write!(o, " {tag}{have}").unwrap();
        while have && vx509_general_name_next(&mut l, &mut g) {
            gn_c(&g, &mut o);
        }
    }
    let have = vx509_get_subject_key_id(c, &mut l);
    write!(o, " ski{:?}", have.then(|| b(l))).unwrap();
    let mut a = std::mem::zeroed::<vx509_authority_key_id>();
    if vx509_get_authority_key_id(c, &mut a) {
        write!(o, " aki{:?}{:?}{}", ob(a.key_id), ob(a.serial), !a.issuer.p.is_null()).unwrap();
        while !a.issuer.p.is_null() && vx509_general_name_next(&mut a.issuer, &mut g) {
            gn_c(&g, &mut o);
        }
    } else {
        o.push_str(" noaki");
    }
    let mut n = std::mem::zeroed::<vx509_name_constraints>();
    if vx509_get_name_constraints(c, &mut n) {
        for mut l in [n.permitted, n.excluded] {
            write!(o, " nc{}", !l.p.is_null()).unwrap();
            while !l.p.is_null() && vx509_subtree_next(&mut l, &mut g) {
                gn_c(&g, &mut o);
            }
        }
    } else {
        o.push_str(" nonc");
    }
    o
}

/// Parses `der` both ways; returns whether it was accepted.
fn check(der: &[u8]) -> bool {
    unsafe {
        let mut c = std::mem::zeroed::<vx509_cert>();
        let mut off = usize::MAX;
        let r = vx509_cert_parse(der.as_ptr(), der.len(), &mut c, &mut off);
        match verilith_x509::try_parse(der) {
            Ok(cert) => {
                assert_eq!(r, 0);
                assert_eq!(dump_rust(&cert), dump_c(&c));
                // Validation only.
                assert_eq!(vx509_cert_parse(der.as_ptr(), der.len(), std::ptr::null_mut(), std::ptr::null_mut()), 0);
                true
            }
            Err(e) => {
                assert!((1..=15).contains(&r), "{r}");
                assert_eq!(off, e.offset);
                false
            }
        }
    }
}

fn certs() -> Vec<Vec<u8>> {
    let mut v: Vec<Vec<u8>> = ["leaf", "root-ecdsa", "root-rsa"]
        .iter()
        .map(|n| std::fs::read(format!("{}/fuzz/seeds/{n}.der", env!("CARGO_MANIFEST_DIR"))).unwrap())
        .collect();
    // A certificate with every decoded extension, name constraints and
    // unusual GeneralNames included.
    let mut p = rcgen::CertificateParams::new(vec!["example.com".into(), "*.example.org".into()]).unwrap();
    p.subject_alt_names.push(rcgen::SanType::IpAddress("192.0.2.1".parse().unwrap()));
    p.subject_alt_names.push(rcgen::SanType::Rfc822Name("a@example.com".try_into().unwrap()));
    p.subject_alt_names.push(rcgen::SanType::URI("https://example.com/x".try_into().unwrap()));
    p.is_ca = rcgen::IsCa::Ca(rcgen::BasicConstraints::Constrained(3));
    p.key_usages = vec![rcgen::KeyUsagePurpose::KeyCertSign, rcgen::KeyUsagePurpose::CrlSign];
    p.extended_key_usages = vec![rcgen::ExtendedKeyUsagePurpose::ServerAuth, rcgen::ExtendedKeyUsagePurpose::ClientAuth];
    p.name_constraints = Some(rcgen::NameConstraints {
        permitted_subtrees: vec![rcgen::GeneralSubtree::DnsName("example.com".into())],
        excluded_subtrees: vec![rcgen::GeneralSubtree::IpAddress(rcgen::CidrSubnet::V4([10, 0, 0, 0], [255, 0, 0, 0]))],
    });
    p.distinguished_name.push(rcgen::DnType::OrganizationName, "Example Org");
    p.distinguished_name.push(rcgen::DnType::CountryName, "US");
    p.use_authority_key_identifier_extension = true;
    let key = rcgen::KeyPair::generate().unwrap();
    v.push(p.self_signed(&key).unwrap().der().to_vec());
    if let Some(dir) = std::env::var_os("VX509_CORPUS") {
        for f in std::fs::read_dir(dir).unwrap() {
            v.push(std::fs::read(f.unwrap().path()).unwrap());
        }
    }
    v
}

#[test]
fn agrees_with_the_rust_api() {
    let all = certs();
    for c in &all {
        assert!(check(c) || all.len() > 4);
    }
    let made = unsafe {
        let mut c = std::mem::zeroed::<vx509_cert>();
        assert_eq!(vx509_cert_parse(all[3].as_ptr(), all[3].len(), &mut c, std::ptr::null_mut()), 0);
        dump_c(&c)
    };
    // keyCertSign and cRLSign are bits 5 and 6.
    for part in [" bcSome((true, Some(3)))", " kuSome(96)", " santrue", "g2[", "g7[192, 0, 2, 1]", "g1[", "g6[", " nctrue", " aki"] {
        assert!(made.contains(part), "{part}: {made}");
    }
}

/// Truncations and single-byte changes of each certificate: the two APIs
/// agree on all of them, accepted or not.
#[test]
fn mutations_agree() {
    let mut accepted = 0;
    for c in certs().iter().take(4) {
        for i in (0..c.len()).step_by(7) {
            check(&c[..i]);
        }
        for i in 0..c.len() {
            for d in [1u8, 0x80, 0xFF] {
                let mut m = c.clone();
                m[i] ^= d;
                accepted += check(&m) as usize;
            }
        }
    }
    // Changes inside strings, keys and signatures leave a valid certificate.
    assert!(accepted > 1000, "{accepted}");
}

#[test]
fn arguments() {
    unsafe {
        let mut off = 7usize;
        assert_eq!(vx509_cert_parse(std::ptr::null(), 0, std::ptr::null_mut(), &mut off), 1);
        assert_eq!(vx509_cert_parse(std::ptr::null(), 5, std::ptr::null_mut(), &mut off), -1);
        let mut s = vx509_span { p: std::ptr::null(), len: 0 };
        let mut g = std::mem::zeroed::<vx509_general_name>();
        assert!(!vx509_general_name_next(&mut s, &mut g) && !vx509_rdn_next(&mut s, std::ptr::null_mut()));
        assert!(!vx509_rdn_next(std::ptr::null_mut(), &mut s) && !vx509_get_key_usage(std::ptr::null(), std::ptr::null_mut()));
        assert_eq!(vx509_oid_text([0x55, 4, 3].as_ptr(), 3, std::ptr::null_mut(), 0), 7);
        assert_eq!(vx509_time_unix(&vx509_time { year: 1970, month: 1, day: 2, hour: 0, minute: 0, second: 1 }), 86401);
    }
}
