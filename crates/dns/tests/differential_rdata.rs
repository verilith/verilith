//! Differential test of typed RDATA against c-ares's `ares_dns_parse`.
//!
//! Run with `CARES_LIB_DIR=/path/to/c-ares/build/lib cargo test --release
//! --test differential_rdata -- --nocapture`.
#![cfg(have_cares)]
mod common;
use common::packets::*;
use common::*;
use std::collections::BTreeMap;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int, c_uchar, c_uint, c_ushort, c_void};
use verilith_dns::rdata::Rdata;
use verilith_dns::{parse, Name, Section};

#[allow(non_camel_case_types)]
type rr_t = c_void;

#[link(name = "cares", kind = "static")]
extern "C" {
    fn ares_dns_parse(buf: *const c_uchar, len: usize, flags: c_uint, rec: *mut *mut c_void) -> c_int;
    fn ares_dns_record_destroy(rec: *mut c_void);
    fn ares_dns_record_rr_cnt(rec: *const c_void, sect: c_int) -> usize;
    fn ares_dns_record_rr_get_const(rec: *const c_void, sect: c_int, idx: usize) -> *const rr_t;
    fn ares_dns_rr_get_type(rr: *const rr_t) -> c_int;
    fn ares_dns_rr_get_str(rr: *const rr_t, key: c_int) -> *const c_char;
    fn ares_dns_rr_get_u8(rr: *const rr_t, key: c_int) -> c_uchar;
    fn ares_dns_rr_get_u16(rr: *const rr_t, key: c_int) -> c_ushort;
    fn ares_dns_rr_get_u32(rr: *const rr_t, key: c_int) -> c_uint;
    fn ares_dns_rr_get_addr(rr: *const rr_t, key: c_int) -> *const u8;
    fn ares_dns_rr_get_addr6(rr: *const rr_t, key: c_int) -> *const u8;
    fn ares_dns_rr_get_bin(rr: *const rr_t, key: c_int, len: *mut usize) -> *const u8;
    fn ares_dns_rr_get_abin_cnt(rr: *const rr_t, key: c_int) -> usize;
    fn ares_dns_rr_get_abin(rr: *const rr_t, key: c_int, idx: usize, len: *mut usize) -> *const u8;
    fn ares_dns_rr_get_opt_cnt(rr: *const rr_t, key: c_int) -> usize;
    fn ares_dns_rr_get_opt(
        rr: *const rr_t,
        key: c_int,
        idx: usize,
        val: *mut *const u8,
        len: *mut usize,
    ) -> c_ushort;
}

fn key(t: u16, n: i32) -> c_int {
    t as c_int * 100 + n
}

unsafe fn cstr(rr: *const rr_t, k: c_int) -> String {
    let p = ares_dns_rr_get_str(rr, k);
    if p.is_null() {
        "<null>".into()
    } else {
        String::from_utf8_lossy(CStr::from_ptr(p).to_bytes()).into_owned()
    }
}

unsafe fn bin(rr: *const rr_t, k: c_int) -> Vec<u8> {
    let mut len = 0;
    let p = ares_dns_rr_get_bin(rr, k, &mut len);
    if p.is_null() {
        vec![]
    } else {
        std::slice::from_raw_parts(p, len).to_vec()
    }
}

unsafe fn opts(rr: *const rr_t, k: c_int) -> Vec<(u16, Vec<u8>)> {
    (0..ares_dns_rr_get_opt_cnt(rr, k))
        .map(|i| {
            let (mut v, mut l) = (std::ptr::null(), 0);
            let code = ares_dns_rr_get_opt(rr, k, i, &mut v, &mut l);
            (code, if v.is_null() { vec![] } else { std::slice::from_raw_parts(v, l).to_vec() })
        })
        .collect()
}

/// A name in c-ares's form: presentation without the trailing dot.
fn name(w: &[u8]) -> String {
    let s = Name::from_wire(w).to_string();
    s.strip_suffix('.').unwrap_or(&s).to_string()
}

fn txt(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// One record's typed fields as c-ares reports them.
unsafe fn cares_fields(rr: *const rr_t) -> String {
    let t = ares_dns_rr_get_type(rr) as u16;
    let k = |n| key(t, n);
    match t {
        1 => format!("{:?}", std::slice::from_raw_parts(ares_dns_rr_get_addr(rr, k(1)), 4)),
        28 => format!("{:?}", std::slice::from_raw_parts(ares_dns_rr_get_addr6(rr, k(1)), 16)),
        2 | 5 | 12 => cstr(rr, k(1)),
        15 => format!("{} {}", ares_dns_rr_get_u16(rr, k(1)), cstr(rr, k(2))),
        16 => {
            let n = ares_dns_rr_get_abin_cnt(rr, k(1));
            let v: Vec<String> = (0..n)
                .map(|i| {
                    let mut l = 0;
                    let p = ares_dns_rr_get_abin(rr, k(1), i, &mut l);
                    txt(std::slice::from_raw_parts(p, l))
                })
                .collect();
            format!("{v:?}")
        }
        13 => format!("{} {}", cstr(rr, k(1)), cstr(rr, k(2))),
        6 => format!(
            "{} {} {} {} {} {} {}",
            cstr(rr, k(1)),
            cstr(rr, k(2)),
            ares_dns_rr_get_u32(rr, k(3)),
            ares_dns_rr_get_u32(rr, k(4)),
            ares_dns_rr_get_u32(rr, k(5)),
            ares_dns_rr_get_u32(rr, k(6)),
            ares_dns_rr_get_u32(rr, k(7))
        ),
        33 => format!(
            "{} {} {} {}",
            ares_dns_rr_get_u16(rr, k(2)),
            ares_dns_rr_get_u16(rr, k(3)),
            ares_dns_rr_get_u16(rr, k(4)),
            cstr(rr, k(5))
        ),
        35 => format!(
            "{} {} {} {} {} {}",
            ares_dns_rr_get_u16(rr, k(1)),
            ares_dns_rr_get_u16(rr, k(2)),
            cstr(rr, k(3)),
            cstr(rr, k(4)),
            cstr(rr, k(5)),
            cstr(rr, k(6))
        ),
        52 => format!(
            "{} {} {} {:?}",
            ares_dns_rr_get_u8(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u8(rr, k(3)),
            bin(rr, k(4))
        ),
        64 | 65 => format!("{} {} {:?}", ares_dns_rr_get_u16(rr, k(1)), cstr(rr, k(2)), opts(rr, k(3))),
        256 => format!("{} {} {}", ares_dns_rr_get_u16(rr, k(1)), ares_dns_rr_get_u16(rr, k(2)), cstr(rr, k(3))),
        257 => format!("{} {} {}", ares_dns_rr_get_u8(rr, k(1)), cstr(rr, k(2)), txt(&bin(rr, k(3)))),
        41 => format!("{:?}", opts(rr, k(5))),
        24 | 46 => format!(
            "{} {} {} {} {} {} {} {} {:?}",
            ares_dns_rr_get_u16(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u8(rr, k(3)),
            ares_dns_rr_get_u32(rr, k(4)),
            ares_dns_rr_get_u32(rr, k(5)),
            ares_dns_rr_get_u32(rr, k(6)),
            ares_dns_rr_get_u16(rr, k(7)),
            cstr(rr, k(8)),
            bin(rr, k(9))
        ),
        43 => format!(
            "{} {} {} {:?}",
            ares_dns_rr_get_u16(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u8(rr, k(3)),
            bin(rr, k(4))
        ),
        44 => format!("{} {} {:?}", ares_dns_rr_get_u8(rr, k(1)), ares_dns_rr_get_u8(rr, k(2)), bin(rr, k(3))),
        47 => format!("{} {:?}", cstr(rr, k(1)), bin(rr, k(2))),
        48 => format!(
            "{} {} {} {:?}",
            ares_dns_rr_get_u16(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u8(rr, k(3)),
            bin(rr, k(4))
        ),
        50 => format!(
            "{} {} {} {:?} {:?} {:?}",
            ares_dns_rr_get_u8(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u16(rr, k(3)),
            bin(rr, k(4)),
            bin(rr, k(5)),
            bin(rr, k(6))
        ),
        51 => format!(
            "{} {} {} {:?}",
            ares_dns_rr_get_u8(rr, k(1)),
            ares_dns_rr_get_u8(rr, k(2)),
            ares_dns_rr_get_u16(rr, k(3)),
            bin(rr, k(4))
        ),
        _ => "raw".into(),
    }
}

unsafe fn cares_type(rr: *const rr_t) -> u16 {
    let t = ares_dns_rr_get_type(rr);
    if t == 65536 {
        ares_dns_rr_get_u16(rr, 65536 * 100 + 1)
    } else {
        t as u16
    }
}

/// The same fields from vdns.
fn vdns_fields(d: &Rdata) -> String {
    match d {
        Rdata::A(a) => format!("{:?}", a),
        Rdata::Aaaa(a) => format!("{:?}", a),
        Rdata::Ns(x) | Rdata::Cname(x) | Rdata::Ptr(x) => name(x),
        Rdata::Mx { preference, exchange } => format!("{} {}", preference, name(exchange)),
        Rdata::Txt(v) => format!("{:?}", v.iter().map(|x| txt(x)).collect::<Vec<_>>()),
        Rdata::Hinfo { cpu, os } => format!("{} {}", txt(cpu), txt(os)),
        Rdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => format!(
            "{} {} {} {} {} {} {}",
            name(mname),
            name(rname),
            serial,
            refresh,
            retry,
            expire,
            minimum
        ),
        Rdata::Srv { priority, weight, port, target } => {
            format!("{} {} {} {}", priority, weight, port, name(target))
        }
        Rdata::Naptr { order, preference, flags, services, regexp, replacement } => format!(
            "{} {} {} {} {} {}",
            order,
            preference,
            txt(flags),
            txt(services),
            txt(regexp),
            name(replacement)
        ),
        Rdata::Tlsa { usage, selector, matching, data } => {
            format!("{} {} {} {:?}", usage, selector, matching, data)
        }
        Rdata::Svcb { priority, target, params } | Rdata::Https { priority, target, params } => format!(
            "{} {} {:?}",
            priority,
            name(target),
            params.iter().map(|(k, v)| (*k, v.to_vec())).collect::<Vec<_>>()
        ),
        Rdata::Uri { priority, weight, target } => format!("{} {} {}", priority, weight, txt(target)),
        Rdata::Caa { flags, tag, value } => format!("{} {} {}", flags, txt(tag), txt(value)),
        Rdata::Opt(v) => format!("{:?}", v.iter().map(|(k, v)| (*k, v.to_vec())).collect::<Vec<_>>()),
        Rdata::Sig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature }
        | Rdata::Rrsig {
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
            signer,
            signature,
        } => format!(
            "{} {} {} {} {} {} {} {} {:?}",
            type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, name(signer), signature
        ),
        Rdata::Ds { key_tag, algorithm, digest_type, digest } => {
            format!("{} {} {} {:?}", key_tag, algorithm, digest_type, digest)
        }
        Rdata::Sshfp { algorithm, fp_type, fingerprint } => format!("{} {} {:?}", algorithm, fp_type, fingerprint),
        Rdata::Nsec { next, type_bitmaps } => format!("{} {:?}", name(next), type_bitmaps),
        Rdata::Dnskey { flags, protocol, algorithm, public_key } => {
            format!("{} {} {} {:?}", flags, protocol, algorithm, public_key)
        }
        Rdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } => format!(
            "{} {} {} {:?} {:?} {:?}",
            hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps
        ),
        Rdata::Nsec3param { hash_algorithm, flags, iterations, salt } => {
            format!("{} {} {} {:?}", hash_algorithm, flags, iterations, salt)
        }
        Rdata::Unknown(_) => "raw".into(),
    }
}


/// Every record of a message, as (type, fields) per side; `None` if the
/// side rejects the message or any record's RDATA.
fn vdns_view(b: &[u8]) -> Option<Vec<(u16, String)>> {
    let m = parse(b)?;
    let mut v = vec![];
    for s in [Section::Answer, Section::Authority, Section::Additional] {
        for rr in m.records(s) {
            v.push((rr.rtype, vdns_fields(&rr.data()?)));
        }
    }
    Some(v)
}

fn cares_view(b: &[u8]) -> Option<Vec<(u16, String)>> {
    unsafe {
        let mut rec = std::ptr::null_mut();
        if ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec) != 0 {
            return None;
        }
        let mut v = vec![];
        for s in 1..=3 {
            for i in 0..ares_dns_record_rr_cnt(rec, s) {
                let rr = ares_dns_record_rr_get_const(rec, s, i);
                v.push((cares_type(rr), cares_fields(rr)));
            }
        }
        ares_dns_record_destroy(rec);
        Some(v)
    }
}


/// Whether the OPT record repeats an option code.
fn dup_opt(b: &[u8]) -> bool {
    let m = parse(b).unwrap();
    let rr = m.additionals().find(|r| r.rtype == 41);
    match rr.and_then(|r| r.data()) {
        Some(Rdata::Opt(v)) => (1..v.len()).any(|i| v[..i].iter().any(|o| o.0 == v[i].0)),
        _ => false,
    }
}

/// c-ares policies stricter than the RFCs, which vdns does not apply.
fn why_cares_rejects(b: &[u8]) -> String {
    let m = parse(b).unwrap();
    let known_class = |c: u16| matches!(c, 1 | 3 | 4 | 254);
    if m.questions().any(|q| !known_class(q.qclass) && q.qclass != 255)
        || [Section::Answer, Section::Authority, Section::Additional]
            .iter()
            .flat_map(|&s| m.records(s))
            .any(|rr| rr.rtype != 41 && !known_class(rr.rclass))
    {
        return "c-ares rejects classes other than IN, CH, HS, NONE (and ANY in questions)".into();
    }
    let printable = |x: &[u8]| x.iter().all(|&c| (0x20..0x7f).contains(&c));
    for s in [Section::Answer, Section::Authority, Section::Additional] {
        for rr in m.records(s) {
            match rr.data().unwrap() {
                Rdata::Hinfo { cpu, os } if !printable(cpu) || !printable(os) => {
                    return "c-ares requires printable HINFO strings".into()
                }
                Rdata::Naptr { flags, services, regexp, .. }
                    if !printable(flags) || !printable(services) || !printable(regexp) =>
                {
                    return "c-ares requires printable NAPTR strings".into()
                }
                Rdata::Uri { target, .. } if !printable(target) => {
                    return "c-ares requires a printable URI target".into()
                }
                Rdata::Caa { value, .. } if value.is_empty() => {
                    return "c-ares requires a non-empty CAA value".into()
                }
                Rdata::Tlsa { data, .. } if data.is_empty() => {
                    return "c-ares requires non-empty TLSA data".into()
                }
                Rdata::Sig { signature: x, .. }
                | Rdata::Rrsig { signature: x, .. }
                | Rdata::Ds { digest: x, .. }
                | Rdata::Sshfp { fingerprint: x, .. }
                | Rdata::Nsec { type_bitmaps: x, .. }
                | Rdata::Dnskey { public_key: x, .. }
                | Rdata::Nsec3 { next_hashed: x, .. }
                    if x.is_empty() =>
                {
                    return "c-ares requires the trailing DNSSEC field (signature, digest, key, bit map, hash) to be non-empty".into()
                }
                _ => {}
            }
        }
    }
    if m.answers().any(|r| r.rtype == 255) {
        return "c-ares rejects ANY records, which vdns keeps raw".into();
    }
    format!("other, types {:?}", m.answers().map(|r| r.rtype).collect::<Vec<_>>())
}

#[test]
fn typed_rdata_agrees_with_c_ares() {
    let mut r = Rng(0x5eed_d15c);
    let mut kinds: BTreeMap<String, (usize, Vec<u8>)> = BTreeMap::new();
    let mut both = 0;
    let total = 300_000;
    for i in 0..total {
        // Single-record packets, so a disagreement can be blamed on a type,
        // and some with several records.
        let single = i % 4 != 3;
        let n = if single { 1 } else { 2 + r.below(3) as u16 };
        let mut b = random_packet(&mut r, n);
        if i % 2 == 1 {
            mutate(&mut r, &mut b);
        }
        let ty = if single && b.len() > 33 { u16::from_be_bytes([b[31], b[32]]) } else { 0 };
        let (ours, theirs) = (vdns_view(&b), cares_view(&b));
        let kind = match (&ours, &theirs) {
            (Some(a), Some(c)) if a == c => {
                both += 1;
                continue;
            }
            (Some(a), Some(c)) => {
                match a.iter().zip(c).find(|(x, y)| x != y) {
                    Some((x, y)) if x.0 == 41 && dup_opt(&b) => {
                        "both accept: c-ares keeps one EDNS option per code".into()
                    }
                    Some((x, y)) => {
                        println!("DIFF type {}: vdns {:?} c-ares {:?}", x.0, x.1, y.1);
                        format!("both accept, fields differ: type {}", x.0)
                    }
                    None => format!("both accept, record counts differ"),
                }
            }
            (Some(_), None) => why_cares_rejects(&b),
            (None, Some(_)) => why_vdns_rejects(&b),
            (None, None) => continue,
        };
        let e = kinds.entry(kind).or_insert((0, b.clone()));
        e.0 += 1;
    }
    println!("{total} packets, {both} accepted by both with identical typed fields");
    for (k, (n, b)) in &kinds {
        println!("{n:7}  {k}\n         e.g. {:02x?}", &b[12..]);
    }
    // Every disagreement must have a known cause; in particular, whenever
    // both accept a message, every typed field must match.
    let unexplained: Vec<_> =
        kinds.keys().filter(|k| k.starts_with("other") || k.contains(": other") || k.contains("fields differ")).collect();
    assert!(unexplained.is_empty(), "unexplained differences: {unexplained:?}");
}
