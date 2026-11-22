//! Compresses the fuzz input with zlib (options from its first bytes),
//! optionally corrupts the stream, then decompresses it with vzlib's
//! zlib-compatible `inflate()` in pieces of fuzzer-chosen sizes and with
//! zlib in one go. Under ASan this checks the C ABI and streaming layer for
//! memory errors; it also checks vzlib accepts exactly what zlib accepts,
//! with the same output.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_int, c_uint};
use verilith_zlib::capi::*;

#[path = "../../tests/common/mod.rs"]
mod common;

fuzz_target!(|data: &[u8]| {
    if data.len() < 6 {
        return;
    }
    let (opt, body) = data.split_at(6);
    let wbits = match opt[0] % 3 {
        0 => 15,
        1 => -15,
        _ => 31,
    };
    let level = (opt[1] % 10) as i32;
    let chunk_in = 1 + opt[2] as usize;
    let chunk_out = 1 + opt[3] as usize * 4;
    let mut z = common::compress(body, level, wbits, 0, 0);
    if opt[4] & 1 == 1 && !z.is_empty() {
        let i = (opt[5] as usize * 31) % z.len();
        z[i] ^= 1 << (opt[4] >> 5);
    }
    let reference = common::zinflate(&z, wbits);
    unsafe {
        let mut s: ZStream = std::mem::zeroed();
        assert_eq!(vz_inflateInit2_(&mut s, wbits, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
        let mut out = Vec::new();
        let mut buf = vec![0u8; chunk_out];
        let mut ip = 0;
        let mut r;
        loop {
            let n = chunk_in.min(z.len() - ip);
            s.next_in = z.as_ptr().add(ip);
            s.avail_in = n as c_uint;
            s.next_out = buf.as_mut_ptr();
            s.avail_out = buf.len() as c_uint;
            r = vz_inflate(&mut s, 0);
            ip += n - s.avail_in as usize;
            out.extend_from_slice(&buf[..buf.len() - s.avail_out as usize]);
            if r != Z_OK {
                break;
            }
        }
        vz_inflateEnd(&mut s);
        match reference {
            Some((want, used)) => {
                assert_eq!(r, Z_STREAM_END);
                assert_eq!(out, want);
                assert_eq!(ip, used);
            }
            None => assert_ne!(r, Z_STREAM_END),
        }
    }
});
