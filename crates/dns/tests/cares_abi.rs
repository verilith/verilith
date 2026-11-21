//! The vdns-backed `ares_dns_parse` against c-ares's own, on the same
//! packets: both must agree on success, and on success build the same
//! record (compared through `ares_dns_write`), except where vdns follows the
//! RFCs more strictly than c-ares.
//!
//! Run with `CARES_LIB_DIR=/path/to/c-ares/build/lib cargo test --release
//! --features cares --test cares_abi -- --nocapture`.
#![cfg(all(have_cares, feature = "cares"))]
mod common;
use common::packets::*;
use common::*;
use std::collections::BTreeMap;
use std::os::raw::{c_int, c_uchar, c_uint, c_void};
use verilith_dns::cares::vdns_ares_dns_parse;
use verilith_dns::Section;

#[link(name = "cares", kind = "static")]
extern "C" {
    fn ares_dns_parse(buf: *const c_uchar, len: usize, flags: c_uint, rec: *mut *mut c_void) -> c_int;
    fn ares_dns_write(rec: *const c_void, buf: *mut *mut c_uchar, len: *mut usize) -> c_int;
    fn ares_dns_record_destroy(rec: *mut c_void);
    fn ares_free_string(s: *mut c_void);
}

type Parser = unsafe extern "C" fn(*const c_uchar, usize, c_uint, *mut *mut c_void) -> c_int;

/// The parse status, and on success the record written back to wire form.
fn run(f: Parser, b: &[u8], flags: u32) -> (c_int, Vec<u8>) {
    unsafe {
        let mut rec = std::ptr::null_mut();
        let st = f(b.as_ptr(), b.len(), flags, &mut rec);
        if st != 0 {
            assert!(rec.is_null());
            return (st, vec![]);
        }
        let (mut p, mut l) = (std::ptr::null_mut(), 0);
        let w = ares_dns_write(rec, &mut p, &mut l);
        let out = if w == 0 { std::slice::from_raw_parts(p, l).to_vec() } else { vec![0xEE; w as usize] };
        ares_free_string(p as *mut c_void);
        ares_dns_record_destroy(rec);
        (0, out)
    }
}

/// Whether the adapter keeps a record raw under `flags`, as c-ares does.
fn raw(s: Section, t: u16, flags: u32) -> bool {
    let sect = match s {
        Section::Answer => 0,
        Section::Authority => 1,
        Section::Additional => 2,
    };
    let base = matches!(t, 1 | 2 | 5 | 6 | 12 | 13 | 15 | 16);
    let known = TYPES.contains(&t) || t == 255;
    !known || flags & (1 << (sect + if base { 0 } else { 3 })) != 0
}

fn corpus() -> Vec<Vec<u8>> {
    let mut v = vec![];
    for name in std::fs::read_dir("tests/corpus").into_iter().flatten().flatten() {
        v.push(std::fs::read(name.path()).unwrap());
    }
    v
}

#[test]
fn agrees_with_c_ares() {
    let mut r = Rng(0xa5e5_0001);
    let mut kinds: BTreeMap<String, (usize, Vec<u8>)> = BTreeMap::new();
    let (mut same, mut total) = (0, 0);
    let mut packets = corpus();
    for _ in 0..200_000 {
        let n = 1 + r.below(4) as u16;
        let mut b = random_packet(&mut r, n);
        if r.below(2) == 0 {
            mutate(&mut r, &mut b);
        }
        packets.push(b);
    }
    for b in &packets {
        for flags in [0u32, 0b000111, 0b111000, 0b111111] {
            total += 1;
            let ours = run(vdns_ares_dns_parse, b, flags);
            let theirs = run(ares_dns_parse, b, flags);
            if ours == theirs || (ours.0 != 0 && theirs.0 != 0) {
                same += 1;
                continue;
            }
            if ours.0 == 0 && theirs.0 == 0 && std::env::var("SHOW").is_ok() {
                println!("flags {flags:06b}\n ours   {:02x?}\n theirs {:02x?}", ours.1, theirs.1);
            }
            let k = if ours.0 == 0 && theirs.0 == 0 {
                "other: both accept, records differ".to_string()
            } else if ours.0 == 0 {
                format!("other: only vdns accepts (c-ares status {})", theirs.0)
            } else {
                why_vdns_rejects_typed(b, &|s, t| !raw(s, t, flags))
            };
            let e = kinds.entry(k).or_insert((0, b.clone()));
            e.0 += 1;
        }
    }
    println!("{total} parses, {same} with the same outcome and record");
    for (k, (n, ex)) in &kinds {
        println!("{n:7}  {k}\n         e.g. {ex:02x?}");
    }
    assert!(!kinds.keys().any(|k| k.starts_with("other")), "unexplained differences");
}

/// Time per `ares_dns_parse` call (building the full c-ares record, then
/// freeing it), vdns-backed versus c-ares's own, on a typical response.
#[test]
fn speed() {
    let mut r = Rng(7);
    let packets: Vec<Vec<u8>> = (0..64).map(|_| random_packet(&mut r, 6)).collect();
    let packets: Vec<&Vec<u8>> = packets.iter().filter(|b| run(ares_dns_parse, b, 0).0 == 0 && run(vdns_ares_dns_parse, b, 0).0 == 0).collect();
    for (label, f) in [("vdns", vdns_ares_dns_parse as Parser), ("c-ares", ares_dns_parse as Parser)] {
        let t = std::time::Instant::now();
        let n = 20_000;
        for _ in 0..n {
            for b in &packets {
                unsafe {
                    let mut rec = std::ptr::null_mut();
                    f(b.as_ptr(), b.len(), 0, &mut rec);
                    ares_dns_record_destroy(rec);
                }
            }
        }
        let per = t.elapsed().as_nanos() as f64 / (n * packets.len()) as f64;
        println!("{label:7} {per:7.0} ns per message ({} messages)", packets.len());
    }
    // Writing the same records back (c-ares's ares_dns_write against the
    // vdns-backed one).
    let recs: Vec<*mut c_void> = packets
        .iter()
        .map(|b| unsafe {
            let mut rec = std::ptr::null_mut();
            ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec);
            rec
        })
        .collect();
    for label in ["vdns", "c-ares"] {
        let t = std::time::Instant::now();
        let n = 20_000;
        for _ in 0..n {
            for &rec in &recs {
                unsafe {
                    if label == "vdns" {
                        std::hint::black_box(verilith_dns::cares::dns_write(rec, 0).unwrap());
                    } else {
                        let (mut p, mut l) = (std::ptr::null_mut(), 0);
                        assert_eq!(ares_dns_write(rec, &mut p, &mut l), 0);
                        ares_free_string(p as *mut c_void);
                    }
                }
            }
        }
        let per = t.elapsed().as_nanos() as f64 / (n * recs.len()) as f64;
        println!("{label:7} {per:7.0} ns per ares_dns_write");
    }
    for rec in recs {
        unsafe { ares_dns_record_destroy(rec) };
    }
}

/// A message as c-ares sees it: parsed by c-ares and written back by c-ares,
/// so two messages with the same meaning compare equal.
fn cares_view(b: &[u8]) -> (c_int, Vec<u8>) {
    run(ares_dns_parse, b, 0)
}

/// Why a record c-ares writes is written differently, or refused, by the
/// vdns-backed writer, where that is deliberate. `theirs` is c-ares's
/// output for a record c-ares parsed with `flags`.
fn why_writes_differ(flags: u32, theirs: &[u8], ours: &Result<Vec<u8>, c_int>) -> String {
    // Raw RDATA of a type with names in it, as c-ares's parser keeps it.
    let raw_names = |pointers: bool| {
        flags != 0
            && record_spans(theirs).into_iter().flatten().any(|(s, t, p, e)| {
                let mut c = Vec::new();
                raw(s, t, flags)
                    && verilith_dns::parse::is_compressible(t)
                    && match verilith_dns::rdata::canon_into(theirs, t, p, e, &mut c) {
                        true => pointers && c[..] != theirs[p..e],
                        false => !pointers,
                    }
            })
    };
    match ours {
        Err(2) if raw_names(true) => "raw RDATA with compression pointers into the message it came from".into(),
        Err(2) if raw_names(false) => "raw RDATA that does not decode as its type (RFC 9267 §5)".into(),
        Err(8) if verilith_dns::try_parse(theirs).is_err_and(|e| e.kind == verilith_dns::ErrorKind::NameTooLong) => {
            "a name over 255 wire octets (RFC 1035 §2.3.4)".into()
        }
        Err(2) if undecodable_typed(theirs) => {
            "a field that does not fit its type's format, which c-ares writes anyway (a CAA tag that is not 1 to 15 letters and digits, RFC 8659 §4.1)".into()
        }
        Ok(_) if svcb_unsorted(theirs) => "SVCB/HTTPS keys written in increasing order (RFC 9460 §2.2)".into(),
        Ok(_) => "other: both write, meanings differ".into(),
        Err(e) => format!("other: only c-ares writes (vdns status {e})"),
    }
}

/// Whether c-ares's output holds a typed record whose RDATA does not decode
/// as its type.
fn undecodable_typed(b: &[u8]) -> bool {
    let Some(m) = verilith_dns::parse(b) else { return false };
    let all = [Section::Answer, Section::Authority, Section::Additional];
    all.iter().flat_map(|&s| m.records(s).collect::<Vec<_>>()).any(|r| r.data().is_none())
}

/// Whether c-ares's output holds SVCB or HTTPS parameters out of order.
fn svcb_unsorted(b: &[u8]) -> bool {
    let Some(m) = verilith_dns::parse(b) else { return false };
    let all = [Section::Answer, Section::Authority, Section::Additional];
    all.iter().flat_map(|&s| m.records(s).collect::<Vec<_>>()).any(|r| {
        if r.rtype != 64 && r.rtype != 65 {
            return false;
        }
        let d = r.rdata;
        let Some((_, mut p)) = read_name(d, 2) else { return false };
        let mut last = None;
        while p + 4 <= d.len() {
            let k = u16::from_be_bytes([d[p], d[p + 1]]);
            if last.is_some_and(|l| k <= l) {
                return true;
            }
            last = Some(k);
            p += 4 + u16::from_be_bytes([d[p + 2], d[p + 3]]) as usize;
        }
        false
    })
}

/// The longest presentation form of a name in message `b`, as c-ares
/// prints it.
fn longest_text(b: &[u8]) -> usize {
    use verilith_dns::rdata::Rdata;
    let m = verilith_dns::parse(b).unwrap();
    let mut names: Vec<Vec<u8>> = m.questions().map(|q| q.name.to_vec()).collect();
    for s in [Section::Answer, Section::Authority, Section::Additional] {
        for r in m.records(s) {
            names.push(r.name.to_vec());
            match r.data() {
                Some(Rdata::Ns(n) | Rdata::Cname(n) | Rdata::Ptr(n)) => names.push(n.to_vec()),
                Some(Rdata::Mx { exchange: n, .. } | Rdata::Srv { target: n, .. } | Rdata::Nsec { next: n, .. }) => {
                    names.push(n.to_vec())
                }
                Some(Rdata::Naptr { replacement: n, .. } | Rdata::Svcb { target: n, .. } | Rdata::Https { target: n, .. }) => {
                    names.push(n.to_vec())
                }
                Some(Rdata::Sig { signer: n, .. } | Rdata::Rrsig { signer: n, .. }) => names.push(n.to_vec()),
                Some(Rdata::Soa { mname, rname, .. }) => {
                    names.push(mname.to_vec());
                    names.push(rname.to_vec());
                }
                _ => {}
            }
        }
    }
    names
        .iter()
        .map(|n| {
            let mut v = Vec::new();
            verilith_dns::Name::from_wire(n).write_presentation(&mut v);
            v.len()
        })
        .max()
        .unwrap_or(0)
}

#[test]
fn writes_like_c_ares() {
    let mut r = Rng(0xa5e5_0002);
    let mut kinds: BTreeMap<String, (usize, Vec<u8>)> = BTreeMap::new();
    let (mut same, mut total, mut bytes_ours, mut bytes_theirs) = (0, 0, 0usize, 0usize);
    let mut packets = corpus();
    for _ in 0..100_000 {
        let n = 1 + r.below(4) as u16;
        let mut b = random_packet(&mut r, n);
        if r.below(2) == 0 {
            mutate(&mut r, &mut b);
        }
        packets.push(b);
    }
    for b in &packets {
        for flags in [0u32, 0b111111] {
            unsafe {
                let mut rec = std::ptr::null_mut();
                if ares_dns_parse(b.as_ptr(), b.len(), flags, &mut rec) != 0 {
                    continue;
                }
                total += 1;
                let (mut p, mut l) = (std::ptr::null_mut(), 0);
                let st = ares_dns_write(rec, &mut p, &mut l);
                let theirs = if st == 0 { Ok(std::slice::from_raw_parts(p, l).to_vec()) } else { Err(st) };
                ares_free_string(p as *mut c_void);
                let ours = verilith_dns::cares::dns_write(rec, 0);
                ares_dns_record_destroy(rec);
                // What vdns writes always parses (that is proven); check it
                // anyway, and that c-ares reads it as c-ares's own output.
                if let Ok(o) = &ours {
                    assert!(verilith_dns::parse(o).is_some());
                }
                let k = match (&ours, &theirs) {
                    (Err(a), Err(b)) if a == b => None,
                    (Ok(o), Ok(t)) if cares_view(o) == cares_view(t) => {
                        bytes_ours += o.len();
                        bytes_theirs += t.len();
                        None
                    }
                    (_, Ok(t)) => Some(why_writes_differ(flags, t, &ours)),
                    (Ok(o), Err(2)) if longest_text(o) > 255 => {
                        Some("a name whose escaped text is over 255 characters, which c-ares parses but will not write".into())
                    }
                    (Ok(_), Err(e)) => Some(format!("other: only vdns writes (c-ares status {e})")),
                    // Under the raw flags, vdns refuses raw RDATA it cannot
                    // write faithfully before c-ares reaches its own error.
                    (Err(2), Err(_)) if flags != 0 => Some("both refuse, vdns at an earlier record".into()),
                    (Err(a), Err(e)) => Some(format!("other: both refuse, statuses {a} and {e}")),
                };
                match k {
                    None => same += 1,
                    Some(k) => {
                        if k.starts_with("other") && std::env::var("SHOW").is_ok() {
                            println!("{k}\n packet {b:02x?}\n ours   {:02x?}\n theirs {:02x?}", ours, theirs);
                        }
                        let e = kinds.entry(k).or_insert((0, b.clone()));
                        e.0 += 1;
                    }
                }
            }
        }
    }
    println!("{total} records written, {same} the same; {bytes_ours} bytes from vdns, {bytes_theirs} from c-ares");
    for (k, (n, ex)) in &kinds {
        println!("{n:7}  {k}\n         e.g. {ex:02x?}");
    }
    assert!(!kinds.keys().any(|k| k.starts_with("other")), "unexplained differences");
}
