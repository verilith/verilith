//! Drives the stateful parts of the zlib C ABI on arbitrary bytes:
//! gzip header capture into small buffers, preset dictionaries,
//! inflateSync after errors, inflateCopy midway and inflateGetDictionary
//! after every call. Under ASan this checks them for memory errors.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_zlib::capi::*;
use std::os::raw::{c_int, c_uint};

fuzz_target!(|data: &[u8]| {
    if data.len() < 4 { return; }
    let wb: c_int = [15, -15, 31, 47][data[0] as usize % 4];
    let ichunk = 1 + data[1] as usize % 64;
    let ochunk = 1 + data[2] as usize % 300;
    let max = data[3] as c_uint % 20;
    let input = &data[4..];
    unsafe {
        let mut s: ZStream = std::mem::zeroed();
        assert_eq!(vz_inflateInit2_(&mut s, wb, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
        let mut ex = vec![0u8; 20];
        let mut nm = vec![0u8; 20];
        let mut cm = vec![0u8; 20];
        let mut g = GzHeader { text: 0, time: 0, xflags: 0, os: 0, extra: ex.as_mut_ptr(), extra_len: 0, extra_max: max,
            name: nm.as_mut_ptr(), name_max: max, comment: cm.as_mut_ptr(), comm_max: max, hcrc: 0, done: 0 };
        if wb > 16 { assert_eq!(vz_inflateGetHeader(&mut s, &mut g), Z_OK); }
        if wb < 0 && data[3] & 1 == 1 { vz_inflateSetDictionary(&mut s, input.as_ptr(), (input.len() / 3) as c_uint); }
        let mut obuf = vec![0u8; ochunk];
        let mut pos = 0;
        let mut copied = false;
        for _ in 0..1_000_000 {
            let end = (pos + ichunk).min(input.len());
            s.next_in = input.as_ptr().add(pos);
            s.avail_in = (end - pos) as c_uint;
            s.next_out = obuf.as_mut_ptr();
            s.avail_out = ochunk as c_uint;
            let r = vz_inflate(&mut s, 0);
            pos = end - s.avail_in as usize;
            let mut h = vec![0u8; 32768];
            let mut hn: c_uint = 0;
            assert_eq!(vz_inflateGetDictionary(&mut s, h.as_mut_ptr(), &mut hn), Z_OK);
            assert!(hn <= 32768);
            if !copied && pos > input.len() / 2 {
                copied = true;
                let mut t: ZStream = std::mem::zeroed();
                assert_eq!(vz_inflateCopy(&mut t, &mut s), Z_OK);
                vz_inflateEnd(&mut s);
                s = t;
            }
            match r {
                Z_OK => {}
                Z_NEED_DICT => {
                    if vz_inflateSetDictionary(&mut s, input.as_ptr(), (input.len() / 2) as c_uint) != Z_OK { break; }
                }
                Z_BUF_ERROR if pos == input.len() => break,
                Z_DATA_ERROR => {
                    if pos == input.len() || vz_inflateSync(&mut s) != Z_OK { break; }
                }
                _ => break,
            }
        }
        assert!(g.done >= -1 && g.done <= 1);
        vz_inflateEnd(&mut s);
    }
});
