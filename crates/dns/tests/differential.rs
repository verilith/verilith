//! Differential test against c-ares's own `ares_expand_name`.
//!
//! Run with `CARES_LIB_DIR=/path/to/c-ares/build/lib cargo test --release`.
#![cfg(have_cares)]
mod common;
use common::*;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int, c_long, c_uchar};
use verilith_dns::capi::vdns_expand_name;

#[link(name = "cares", kind = "static")]
extern "C" {
    fn ares_expand_name(
        encoded: *const c_uchar,
        abuf: *const c_uchar,
        alen: c_int,
        s: *mut *mut c_char,
        enclen: *mut c_long,
    ) -> c_int;
    fn ares_free_string(s: *mut std::ffi::c_void);
}

fn call(
    f: unsafe extern "C" fn(*const c_uchar, *const c_uchar, c_int, *mut *mut c_char, *mut c_long) -> c_int,
    b: &[u8],
    p: usize,
) -> (c_int, Option<Vec<u8>>, c_long) {
    let mut s: *mut c_char = std::ptr::null_mut();
    let mut enclen: c_long = -1;
    let st = unsafe { f(b.as_ptr().add(p), b.as_ptr(), b.len() as c_int, &mut s, &mut enclen) };
    let text = if s.is_null() {
        None
    } else {
        let t = unsafe { CStr::from_ptr(s) }.to_bytes().to_vec();
        unsafe { ares_free_string(s as *mut _) };
        Some(t)
    };
    (st, text, if st == 0 { enclen } else { 0 })
}

/// Unescaped presentation length (label bytes plus dots) of c-ares output.
fn presentation_len(s: &[u8]) -> usize {
    let (mut n, mut i) = (0, 0);
    while i < s.len() {
        if s[i] == b'\\' {
            i += if s.get(i + 1).is_some_and(|c| c.is_ascii_digit()) { 4 } else { 2 };
        } else {
            i += 1;
        }
        n += 1;
    }
    n
}

/// Whether decoding the name at `p` with c-ares's rules follows a pointer
/// that lands on another pointer, which RFC 9267 §2 forbids.
fn follows_non_label_pointer(b: &[u8], mut p: usize) -> bool {
    let mut seg = p;
    while p < b.len() {
        seg = seg.min(p);
        match b[p] {
            0 => return false,
            c if c >= 0xC0 => {
                let Some(&lo) = b.get(p + 1) else { return false };
                let t = ((c as usize & 0x3F) << 8) | lo as usize;
                if t >= seg {
                    return false;
                }
                if b[t] >= 64 {
                    return true;
                }
                p = t;
            }
            c if c >= 64 => return false,
            c => p += 1 + c as usize,
        }
    }
    false
}

#[test]
fn agrees_with_c_ares() {
    let mut r = Rng(0xc0ffee);
    let (mut compared, mut ok, mut length_policy, mut rfc9267) = (0u64, 0u64, 0u64, 0u64);
    for i in 0..60_000 {
        let mut b = match i % 3 {
            0 => encode_compressed(&random_message(&mut r)),
            1 => (0..1 + r.below(80)).map(|_| r.byte()).collect(),
            _ => {
                // Dense label/pointer soup to exercise compression paths.
                let mut v = vec![0u8; 12];
                for _ in 0..r.below(40) {
                    match r.below(4) {
                        0 => v.extend_from_slice(&[0xC0 | r.below(2) as u8, r.byte()]),
                        1 => v.push(0),
                        _ => {
                            let len = 1 + r.below(63) as u8;
                            v.push(len);
                            v.extend((0..len).map(|_| r.byte()));
                        }
                    }
                }
                v
            }
        };
        for _ in 0..r.below(3) {
            let j = r.below(b.len() as u64) as usize;
            b[j] = r.byte();
        }
        for p in 0..b.len() {
            let theirs = call(ares_expand_name, &b, p);
            let ours = call(vdns_expand_name, &b, p);
            compared += 1;
            if theirs == ours {
                ok += (theirs.0 == 0) as u64;
                continue;
            }
            // Known policy difference: c-ares caps the presentation length
            // at 255 (wire length 257); we enforce RFC 1035's 255-octet wire
            // limit, i.e. presentation length 253.
            if let (0, Some(t), _) = &theirs {
                if ours.0 == 8 && matches!(presentation_len(t), 254 | 255) {
                    length_policy += 1;
                    continue;
                }
            }
            if theirs.0 == 0 && ours.0 == 8 && follows_non_label_pointer(&b, p) {
                rfc9267 += 1;
                continue;
            }
            panic!("mismatch at offset {p} of {b:02x?}: c-ares {theirs:?}, ours {ours:?}");
        }
    }
    eprintln!(
        "compared {compared} name decodes, {ok} accepted by both, {length_policy} over-long names, \
         {rfc9267} pointers to non-labels (RFC 9267), 0 other differences"
    );
    assert!(ok > 10_000);
}
