//! Feeds arbitrary bytes, with arbitrary buffer sizes, to every
//! decompression entry point of the C ABI. Under ASan this checks the
//! adapters for memory errors on hostile input.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_int, c_uint, c_ulong};
use verilith_zlib::capi::*;

fuzz_target!(|data: &[u8]| {
    if data.len() < 3 {
        return;
    }
    let (opt, input) = data.split_at(3);
    let avail = opt[0] as usize * 64;
    let mut out = vec![0u8; avail];
    unsafe {
        let mut dl = avail as c_ulong;
        let mut sl = input.len() as c_ulong;
        vz_uncompress2(out.as_mut_ptr(), &mut dl, input.as_ptr(), &mut sl);
        assert!(dl as usize <= avail && sl as usize <= input.len());
        let d = vzlib_alloc_decompressor();
        let (mut ai, mut ao) = (0usize, 0usize);
        for f in [vzlib_deflate_decompress_ex, vzlib_zlib_decompress_ex, vzlib_gzip_decompress_ex] {
            if f(d, input.as_ptr(), input.len(), out.as_mut_ptr(), avail, &mut ai, &mut ao) == LIBDEFLATE_SUCCESS {
                assert!(ai <= input.len() && ao <= avail);
            }
        }
        vzlib_free_decompressor(d);
        for wbits in [15, -15, 31, 47] {
            let mut s: ZStream = std::mem::zeroed();
            assert_eq!(vz_inflateInit2_(&mut s, wbits, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
            let step = 1 + opt[1] as usize;
            let ostep = 1 + opt[2] as usize;
            let mut ip = 0;
            let mut buf = vec![0u8; ostep];
            for _ in 0..10_000 {
                let n = step.min(input.len() - ip);
                s.next_in = input.as_ptr().add(ip);
                s.avail_in = n as c_uint;
                s.next_out = buf.as_mut_ptr();
                s.avail_out = ostep as c_uint;
                let r = vz_inflate(&mut s, 0);
                ip += n - s.avail_in as usize;
                if r != Z_OK {
                    break;
                }
            }
            vz_inflateEnd(&mut s);
        }
    }
});
