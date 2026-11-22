//! The vdns-backed `ares_dns_write` (`cares::dns_write`) on records built by
//! c-ares's own parser, with every `ARES_DNS_PARSE_*_RAW` flag combination
//! and a TTL decrement: what vdns writes always parses, and whenever c-ares's
//! writer succeeds too, c-ares reads the two messages as the same record
//! (SVCB and HTTPS aside, whose keys vdns sorts as RFC 9460 §2.2 requires).
#![no_main]
#![allow(unsafe_op_in_unsafe_fn)]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_int, c_uchar, c_uint, c_void};

unsafe extern "C" {
    fn ares_dns_parse(buf: *const c_uchar, len: usize, flags: c_uint, rec: *mut *mut c_void) -> c_int;
    fn ares_dns_write(rec: *const c_void, buf: *mut *mut c_uchar, len: *mut usize) -> c_int;
    fn ares_dns_record_destroy(rec: *mut c_void);
    fn ares_dns_record_ttl_decrement(rec: *mut c_void, ttl_decrement: c_uint);
    fn ares_free_string(s: *mut c_void);
}

unsafe fn write(rec: *const c_void) -> Option<Vec<u8>> {
    let (mut p, mut l) = (std::ptr::null_mut(), 0);
    let st = ares_dns_write(rec, &mut p, &mut l);
    let out = (st == 0).then(|| std::slice::from_raw_parts(p, l).to_vec());
    ares_free_string(p as *mut c_void);
    out
}

/// The message as c-ares reads it, written back by c-ares.
fn view(b: &[u8]) -> Option<Vec<u8>> {
    unsafe {
        let mut rec = std::ptr::null_mut();
        if ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec) != 0 {
            return None;
        }
        let out = write(rec);
        ares_dns_record_destroy(rec);
        out
    }
}

fuzz_target!(|data: &[u8]| {
    let Some((&[f, d], b)) = data.split_first_chunk() else { return };
    let flags = (f & 0x3f) as u32;
    let td = if f & 0x40 != 0 { d as u32 * 1000 } else { 0 };
    unsafe {
        let mut rec = std::ptr::null_mut();
        if ares_dns_parse(b.as_ptr(), b.len(), flags, &mut rec) != 0 {
            return;
        }
        ares_dns_record_ttl_decrement(rec, td);
        let ours = verilith_dns::cares::dns_write(rec, td);
        let theirs = write(rec);
        ares_dns_record_destroy(rec);
        let Ok(o) = ours else { return };
        let m = verilith_dns::parse(&o).expect("vdns writes only what it parses");
        let svcb = |m: &verilith_dns::Message| m.answers().chain(m.authorities()).chain(m.additionals()).any(|r| r.rtype == 64 || r.rtype == 65);
        if let Some(t) = theirs {
            if !svcb(&m) {
                assert_eq!(view(&o), view(&t), "flags {flags:06b}");
            }
        }
    }
});
