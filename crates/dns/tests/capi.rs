//! The native C API (`src/native.rs`) against the Rust API it wraps: the
//! same verdict and the same questions and records for every packet.
#![cfg(feature = "capi")]
#![allow(dead_code)]
mod common;
use common::packets::*;
use common::*;
use std::ffi::{c_char, CStr};
use verilith_dns::native::*;
use verilith_dns::{try_parse, ErrorKind, Name, Part};

unsafe fn b<'a>(p: *const u8, n: usize) -> &'a [u8] {
    std::slice::from_raw_parts(p, n)
}

unsafe fn text(name: &[u8]) -> String {
    let n = vdns_name_text(name.as_ptr(), name.len(), std::ptr::null_mut(), 0);
    let mut buf = vec![0 as c_char; n + 1];
    assert_eq!(vdns_name_text(name.as_ptr(), name.len(), buf.as_mut_ptr(), n + 1), n);
    // A buffer one byte short holds all but the last character.
    let mut short = vec![1 as c_char; n.max(1)];
    assert_eq!(vdns_name_text(name.as_ptr(), name.len(), short.as_mut_ptr(), n), n);
    if n > 0 {
        assert_eq!(CStr::from_ptr(short.as_ptr()).to_bytes(), &CStr::from_ptr(buf.as_ptr()).to_bytes()[..n - 1]);
    }
    String::from_utf8_lossy(CStr::from_ptr(buf.as_ptr()).to_bytes()).into_owned()
}

/// Parses `pkt` both ways into the reused `m`; returns whether it was
/// accepted.
fn check(m: *mut vdns_message, pkt: &[u8]) -> bool {
    unsafe {
        let mut e = std::mem::zeroed::<vdns_error>();
        let rc = vdns_parse(m, pkt.as_ptr(), pkt.len(), &mut e);
        let want = match try_parse(pkt) {
            Ok(w) => w,
            Err(x) => {
                let code = match x.kind {
                    ErrorKind::ShortHeader => 1,
                    ErrorKind::Truncated => 2,
                    ErrorKind::ReservedLabelType => 3,
                    ErrorKind::PointerNotPrior => 4,
                    ErrorKind::PointerToPointer => 5,
                    ErrorKind::NameTooLong => 6,
                    ErrorKind::BadRdata => 7,
                    ErrorKind::TrailingBytes => 8,
                    k => panic!("{k:?}"),
                };
                let part = match x.part {
                    Part::Header => (0, 0),
                    Part::Question(i) => (1, i),
                    Part::Answer(i) => (2, i),
                    Part::Authority(i) => (3, i),
                    Part::Additional(i) => (4, i),
                    Part::End => (5, 0),
                    p => panic!("{p:?}"),
                };
                assert_eq!((rc, e.code, (e.part, e.index), e.offset), (code, code, part, x.offset));
                assert_eq!(vdns_question_count(m), 0);
                assert!((0..3).all(|s| vdns_record_count(m, s) == 0));
                return false;
            }
        };
        assert_eq!((rc, e.code), (0, 0));
        assert_eq!((vdns_id(m), vdns_flags(m)), (want.id(), want.flags()));
        assert_eq!(vdns_question_count(m), want.question_count());
        let mut q = std::mem::zeroed::<vdns_question>();
        for (i, w) in want.questions().enumerate() {
            assert!(vdns_get_question(m, i, &mut q));
            assert_eq!((b(q.name, q.name_len), q.qtype, q.qclass), (w.name, w.qtype, w.qclass));
            let mut t = Vec::new();
            Name::from_wire(w.name).write_presentation(&mut t);
            assert_eq!(text(w.name).as_bytes(), String::from_utf8_lossy(&t).as_bytes());
        }
        assert!(!vdns_get_question(m, want.question_count(), &mut q));
        let mut r = std::mem::zeroed::<vdns_record>();
        for (s, sec) in SECTIONS.into_iter().enumerate() {
            let s = s as i32;
            assert_eq!(vdns_record_count(m, s), want.record_count(sec));
            for (i, w) in want.records(sec).enumerate() {
                assert!(vdns_get_record(m, s, i, &mut r));
                assert_eq!(
                    (b(r.name, r.name_len), r.rtype, r.rclass, r.ttl, b(r.rdata, r.rdata_len)),
                    (w.name, w.rtype, w.rclass, w.ttl, w.rdata)
                );
            }
            assert!(!vdns_get_record(m, s, want.record_count(sec), &mut r));
        }
        true
    }
}

#[test]
fn agrees_with_the_rust_api() {
    let mut r = Rng(0x5EED);
    let m = vdns_message_new();
    let (mut ok, mut bad) = (0, 0);
    for n in 0..3000u16 {
        let mut p = random_packet(&mut r, n % 8);
        if check(m, &p) {
            ok += 1;
        } else {
            bad += 1;
        }
        // Truncated and corrupted, into the same message.
        check(m, &p[..r.below(p.len() as u64 + 1) as usize]);
        for _ in 0..4 {
            mutate(&mut r, &mut p);
            if check(m, &p) {
                ok += 1;
            } else {
                bad += 1;
            }
        }
    }
    assert!(ok > 1000 && bad > 1000, "{ok} {bad}");
    unsafe { vdns_message_free(m) };
}

/// Queries written through the C API parse back to what was asked.
#[test]
fn queries_round_trip() {
    let mut r = Rng(7);
    let m = vdns_message_new();
    for i in 0..500u16 {
        let wire = random_name(&mut r);
        let mut t = Vec::new();
        Name::from_wire(&wire).write_presentation(&mut t);
        unsafe {
            let mut out = vec![0u8; 12 + wire.len() + 4];
            let mut len = 0usize;
            let rc = vdns_write_query(i, 0x0100, t.as_ptr() as *const c_char, t.len(), 28, 1, out.as_mut_ptr(), out.len(), &mut len);
            assert_eq!((rc, len), (0, out.len()));
            // One byte less is not enough, and writes nothing.
            let mut short = vec![0xAAu8; out.len() - 1];
            assert_eq!(vdns_write_query(i, 0, t.as_ptr() as *const c_char, t.len(), 28, 1, short.as_mut_ptr(), short.len(), &mut len), VDNS_E_SPACE);
            assert!(len == out.len() && short.iter().all(|&c| c == 0xAA));
            assert_eq!(vdns_parse(m, out.as_ptr(), out.len(), std::ptr::null_mut()), 0);
            let mut q = std::mem::zeroed::<vdns_question>();
            assert!(vdns_get_question(m, 0, &mut q));
            assert_eq!((vdns_id(m), vdns_flags(m), b(q.name, q.name_len), q.qtype, q.qclass), (i, 0x0100, &wire[..], 28, 1));
        }
    }
    unsafe { vdns_message_free(m) };
}
