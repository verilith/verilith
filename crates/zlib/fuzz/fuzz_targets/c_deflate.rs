//! Drives the compression C API (`deflate()`, `deflateParams`,
//! `deflateCopy`) with fuzzer-chosen input pieces, output buffer sizes and
//! flushes under AddressSanitizer, and checks zlib decompresses the result
//! to the input.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_int, c_uint};
use verilith_zlib::capi::*;

#[path = "../../tests/common/mod.rs"]
mod common;

fuzz_target!(|data: &[u8]| {
    if data.len() < 4 {
        return;
    }
    let (opt, body) = data.split_at(4);
    let wbits = [15, -15, 31, 9, -12, 25][opt[0] as usize % 6];
    let level = (opt[1] % 11) as c_int - 1;
    let mut seed = (opt[2] as u64) << 8 | opt[3] as u64 | 1;
    let mut next = move |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    let mut out = Vec::new();
    unsafe {
        let mut s: ZStream = std::mem::zeroed();
        assert_eq!(
            vz_deflateInit2_(&mut s, level, Z_DEFLATED, wbits, 8, 0, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int),
            Z_OK
        );
        let mut ip = 0;
        loop {
            let n = (next(2000) as usize).min(body.len() - ip);
            let last = ip + n == body.len();
            let flush = if last { Z_FINISH } else { next(6) as c_int };
            if next(16) == 0 {
                // No output room: the block's output waits for deflate().
                s.avail_out = 0;
                assert_eq!(vz_deflateParams(&mut s, next(10) as c_int, 0), Z_OK);
            }
            if next(16) == 0 {
                // Continue on a copy.
                let mut c: ZStream = std::mem::zeroed();
                assert_eq!(vz_deflateCopy(&mut c, &mut s), Z_OK);
                vz_deflateEnd(&mut s);
                s = c;
            }
            s.next_in = body.as_ptr().add(ip);
            s.avail_in = n as c_uint;
            loop {
                let mut buf = vec![0u8; 1 + next(3000) as usize];
                s.next_out = buf.as_mut_ptr();
                s.avail_out = buf.len() as c_uint;
                let r = vz_deflate(&mut s, if flush == 4 && !last { 0 } else { flush });
                out.extend_from_slice(&buf[..buf.len() - s.avail_out as usize]);
                if r == Z_STREAM_END {
                    break;
                }
                assert!(r == Z_OK || r == Z_BUF_ERROR);
                if s.avail_in == 0 && s.avail_out > 0 && !last {
                    break;
                }
            }
            ip += n;
            if last {
                break;
            }
        }
        assert_eq!(vz_deflateEnd(&mut s), Z_OK);
    }
    let (got, used) = common::zinflate(&out, wbits).expect("zlib rejected vzlib's stream");
    assert_eq!(got, body);
    assert_eq!(used, out.len());
});
