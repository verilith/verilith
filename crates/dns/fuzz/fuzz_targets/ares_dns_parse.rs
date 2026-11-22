//! The vdns-backed `ares_dns_parse` (the c-ares adapter), with every
//! `ARES_DNS_PARSE_*_RAW` flag combination, checked against c-ares's own
//! parser: same status class, and byte-identical records written back with
//! `ares_dns_write` whenever both accept, unless vdns is stricter.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_int, c_uchar, c_uint, c_void};
use verilith_dns::cares::vdns_ares_dns_parse;

unsafe extern "C" {
    fn ares_dns_parse(buf: *const c_uchar, len: usize, flags: c_uint, rec: *mut *mut c_void) -> c_int;
    fn ares_dns_write(rec: *const c_void, buf: *mut *mut c_uchar, len: *mut usize) -> c_int;
    fn ares_dns_record_destroy(rec: *mut c_void);
    fn ares_free_string(s: *mut c_void);
}

type Parser = unsafe extern "C" fn(*const c_uchar, usize, c_uint, *mut *mut c_void) -> c_int;

fn run(f: Parser, b: &[u8], flags: u32) -> Option<Vec<u8>> {
    unsafe {
        let mut rec = std::ptr::null_mut();
        if f(b.as_ptr(), b.len(), flags, &mut rec) != 0 {
            assert!(rec.is_null());
            return None;
        }
        let (mut p, mut l) = (std::ptr::null_mut(), 0);
        let w = ares_dns_write(rec, &mut p, &mut l);
        let out = if w == 0 { std::slice::from_raw_parts(p, l).to_vec() } else { vec![] };
        ares_free_string(p as *mut c_void);
        ares_dns_record_destroy(rec);
        Some(out)
    }
}

fuzz_target!(|data: &[u8]| {
    let Some((&f, b)) = data.split_first() else { return };
    let flags = (f & 0x3f) as u32;
    let ours = run(vdns_ares_dns_parse, b, flags);
    let theirs = run(ares_dns_parse, b, flags);
    if let Some(o) = &ours {
        // vdns never accepts what c-ares rejects, and when both accept they
        // build the same record.
        assert_eq!(Some(o), theirs.as_ref(), "flags {flags:06b}");
    }
});
