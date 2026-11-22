//! The C API under ASan: arbitrary input, header array sizes and
//! `last_len`, with output arrays exactly as large as promised.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_char, c_int};
use verilith_http::capi::*;

fn empty() -> phr_header {
    phr_header { name: std::ptr::null(), name_len: 0, value: std::ptr::null(), value_len: 0 }
}

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    let (n, ctl, buf) = (data[0] as usize % 12, data[1], &data[2..]);
    // An exact copy, so that ASan sees reads past the end.
    let b: Vec<u8> = buf.to_vec();
    let p = b.as_ptr() as *const c_char;
    let mut hs: Vec<phr_header> = (0..n).map(|_| empty()).collect();
    unsafe {
        let (mut m, mut ml, mut path, mut pl, mut minor) = (std::ptr::null(), 0, std::ptr::null(), 0, 0 as c_int);
        let mut num = n;
        let last_len = (ctl as usize * b.len()) / 255;
        let r = vhttp_phr_parse_request(p, b.len(), &mut m, &mut ml, &mut path, &mut pl, &mut minor, hs.as_mut_ptr(), &mut num, last_len);
        assert!(r >= -2 && r as isize <= b.len() as isize);
        if r > 0 {
            assert!(num <= n);
            let _ = std::slice::from_raw_parts(m as *const u8, ml).iter().fold(0u8, |a, &x| a ^ x);
            let _ = std::slice::from_raw_parts(path as *const u8, pl).iter().fold(0u8, |a, &x| a ^ x);
            for h in &hs[..num] {
                let _ = std::slice::from_raw_parts(h.name as *const u8, h.name_len).iter().fold(0u8, |a, &x| a ^ x);
                let _ = std::slice::from_raw_parts(h.value as *const u8, h.value_len).iter().fold(0u8, |a, &x| a ^ x);
            }
        }
        let mut num = n;
        let (mut status, mut msg, mut msgl) = (0 as c_int, std::ptr::null(), 0);
        let r = vhttp_phr_parse_response(p, b.len(), &mut minor, &mut status, &mut msg, &mut msgl, hs.as_mut_ptr(), &mut num, 0);
        if r > 0 {
            let _ = std::slice::from_raw_parts(msg as *const u8, msgl).iter().fold(0u8, |a, &x| a ^ x);
        }
        let mut num = n;
        let r = vhttp_phr_parse_headers(p, b.len(), hs.as_mut_ptr(), &mut num, 0);
        assert!(r >= -2 && r as isize <= b.len() as isize);
        // The chunked decoder, in place, in two calls.
        let mut body = b.clone();
        let mut dec: phr_chunked_decoder = std::mem::zeroed();
        dec.consume_trailer = (ctl & 1) as c_char;
        let cut = (ctl as usize * body.len()) / 255;
        let mut len1 = cut;
        let r1 = vhttp_phr_decode_chunked(&mut dec, body.as_mut_ptr() as *mut c_char, &mut len1);
        if r1 == -2 {
            assert!(len1 <= cut);
            let mut rest = body[cut..].to_vec();
            let mut len2 = rest.len();
            let r2 = vhttp_phr_decode_chunked(&mut dec, rest.as_mut_ptr() as *mut c_char, &mut len2);
            assert!(r2 >= -2 && r2 as isize <= rest.len() as isize);
            assert!(len2 <= rest.len());
        }
        let _ = vhttp_phr_decode_chunked_is_in_data(&mut dec);
    }
});
