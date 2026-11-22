//! The C ABI, called the way C programs call zlib and libdeflate.
#![allow(unsafe_op_in_unsafe_fn)]
mod common;
use common::{compress, text, Rng};
use std::os::raw::{c_int, c_uint, c_ulong};
use verilith_zlib::capi::*;

fn new_stream() -> ZStream {
    unsafe { std::mem::zeroed() }
}

#[test]
fn inflate_api_streaming() {
    let data = text(&mut Rng(1), 200_000);
    for (wb, cwb) in [(15, 15), (-15, -15), (31, 31), (16, 31), (32, 31), (32, 15), (47, 31), (47, 15), (0, 15)] {
        let c = compress(&data, 6, cwb, 0, 0);
        unsafe {
            let mut s = new_stream();
            assert_eq!(vz_inflateInit2_(&mut s, wb, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
            let mut out = vec![0u8; data.len() + 10];
            let mut ip = 0;
            let mut op = 0;
            let mut ret;
            loop {
                let n = (c.len() - ip).min(1000);
                s.next_in = c.as_ptr().add(ip);
                s.avail_in = n as c_uint;
                s.next_out = out.as_mut_ptr().add(op);
                s.avail_out = (out.len() - op).min(777) as c_uint;
                let before_out = s.avail_out;
                ret = vz_inflate(&mut s, 0);
                ip += n - s.avail_in as usize;
                op += (before_out - s.avail_out) as usize;
                if ret != Z_OK {
                    break;
                }
            }
            assert_eq!(ret, Z_STREAM_END, "wb {wb}");
            assert_eq!(&out[..op], &data[..]);
            assert_eq!(ip, c.len());
            assert_eq!(s.total_in as usize, c.len());
            assert_eq!(s.total_out as usize, data.len());
            assert_eq!(vz_inflateEnd(&mut s), Z_OK);
        }
    }
}

#[test]
fn inflate_api_finish_and_errors() {
    let data = text(&mut Rng(2), 50_000);
    let c = compress(&data, 9, 15, 0, 0);
    unsafe {
        let mut s = new_stream();
        assert_eq!(vz_inflateInit_(&mut s, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
        let mut out = vec![0u8; data.len()];
        s.next_in = c.as_ptr();
        s.avail_in = c.len() as c_uint;
        s.next_out = out.as_mut_ptr();
        s.avail_out = 1000;
        assert_eq!(vz_inflate(&mut s, Z_FINISH), Z_BUF_ERROR);
        s.avail_out = (data.len() - 1000) as c_uint;
        assert_eq!(vz_inflate(&mut s, Z_FINISH), Z_STREAM_END);
        assert_eq!(out, data);
        assert_eq!(s.adler as u32, verilith_zlib::checksum::adler32(&data));
        // Reset and feed garbage.
        assert_eq!(vz_inflateReset(&mut s), Z_OK);
        let bad = [0x78u8, 0x9c, 0xff, 0xff, 0xff, 0xff];
        s.next_in = bad.as_ptr();
        s.avail_in = bad.len() as c_uint;
        s.next_out = out.as_mut_ptr();
        s.avail_out = out.len() as c_uint;
        assert_eq!(vz_inflate(&mut s, 0), Z_DATA_ERROR);
        assert!(!s.msg.is_null());
        assert_eq!(vz_inflateEnd(&mut s), Z_OK);
        assert_eq!(vz_inflate(&mut s, 0), Z_STREAM_ERROR);
        assert_eq!(vz_inflateInit2_(&mut s, 15, b"2.0\0".as_ptr() as *const _, std::mem::size_of::<ZStream>() as c_int), Z_VERSION_ERROR);
    }
}

#[test]
fn uncompress_api() {
    let data = text(&mut Rng(3), 30_000);
    let c = compress(&data, 6, 15, 0, 0);
    unsafe {
        let mut out = vec![0u8; data.len() + 5];
        let mut n = out.len() as c_ulong;
        assert_eq!(vz_uncompress(out.as_mut_ptr(), &mut n, c.as_ptr(), c.len() as c_ulong), Z_OK);
        assert_eq!(n as usize, data.len());
        assert_eq!(&out[..data.len()], &data[..]);
        let mut n = 100 as c_ulong;
        assert_eq!(vz_uncompress(out.as_mut_ptr(), &mut n, c.as_ptr(), c.len() as c_ulong), Z_BUF_ERROR);
        let mut n = out.len() as c_ulong;
        assert_eq!(vz_uncompress(out.as_mut_ptr(), &mut n, c.as_ptr(), (c.len() - 3) as c_ulong), Z_DATA_ERROR);
        let mut t = c.clone();
        t.extend_from_slice(b"xyz");
        let mut n = out.len() as c_ulong;
        let mut sl = t.len() as c_ulong;
        assert_eq!(vz_uncompress2(out.as_mut_ptr(), &mut n, t.as_ptr(), &mut sl), Z_OK);
        assert_eq!(sl as usize, c.len());
        assert_eq!(vz_adler32(vz_adler32(0, std::ptr::null(), 0), data.as_ptr(), data.len() as c_uint) as u32, verilith_zlib::checksum::adler32(&data));
        assert_eq!(vz_crc32(vz_crc32(0, std::ptr::null(), 0), data.as_ptr(), data.len() as c_uint) as u32, verilith_zlib::checksum::crc32(&data));
        // Incremental checksums.
        let a = vz_adler32(vz_adler32(1, data.as_ptr(), 1000), data.as_ptr().add(1000), (data.len() - 1000) as c_uint);
        assert_eq!(a as u32, verilith_zlib::checksum::adler32(&data));
        let k = vz_crc32(vz_crc32(0, data.as_ptr(), 1000), data.as_ptr().add(1000), (data.len() - 1000) as c_uint);
        assert_eq!(k as u32, verilith_zlib::checksum::crc32(&data));
    }
}

#[test]
fn libdeflate_api() {
    let data = text(&mut Rng(4), 40_000);
    unsafe {
        let d = vzlib_alloc_decompressor();
        for (wb, f, fex) in [
            (-15, vzlib_deflate_decompress as unsafe extern "C" fn(_, _, _, _, _, _) -> c_int, vzlib_deflate_decompress_ex as unsafe extern "C" fn(_, _, _, _, _, _, _) -> c_int),
            (15, vzlib_zlib_decompress, vzlib_zlib_decompress_ex),
            (31, vzlib_gzip_decompress, vzlib_gzip_decompress_ex),
        ] {
            let c = compress(&data, 6, wb, 0, 0);
            let mut out = vec![0u8; data.len()];
            assert_eq!(f(d, c.as_ptr(), c.len(), out.as_mut_ptr(), out.len(), std::ptr::null_mut()), LIBDEFLATE_SUCCESS);
            assert_eq!(out, data);
            let mut big = vec![0u8; data.len() + 1];
            assert_eq!(f(d, c.as_ptr(), c.len(), big.as_mut_ptr(), big.len(), std::ptr::null_mut()), LIBDEFLATE_SHORT_OUTPUT);
            let (mut ai, mut ao) = (0usize, 0usize);
            assert_eq!(fex(d, c.as_ptr(), c.len(), big.as_mut_ptr(), big.len(), &mut ai, &mut ao), LIBDEFLATE_SUCCESS);
            assert_eq!((ai, ao), (c.len(), data.len()));
            assert_eq!(f(d, c.as_ptr(), c.len(), out.as_mut_ptr(), 10, std::ptr::null_mut()), LIBDEFLATE_INSUFFICIENT_SPACE);
            assert_eq!(f(d, c.as_ptr(), c.len() - 1, out.as_mut_ptr(), out.len(), std::ptr::null_mut()), LIBDEFLATE_BAD_DATA);
        }
        vzlib_free_decompressor(d);
    }
}

/// Runs `vz_inflate` over `input` in pieces of at most `step` bytes (in
/// and out) until it stops returning `Z_OK`; returns the last result, the
/// input used and the output.
unsafe fn run(s: &mut ZStream, input: &[u8], step: usize) -> (c_int, usize, Vec<u8>) {
    let mut out = Vec::new();
    let mut buf = vec![0u8; step];
    let mut ip = 0;
    loop {
        let n = (input.len() - ip).min(step);
        s.next_in = input.as_ptr().add(ip);
        s.avail_in = n as c_uint;
        s.next_out = buf.as_mut_ptr();
        s.avail_out = step as c_uint;
        let r = vz_inflate(s, 0);
        ip += n - s.avail_in as usize;
        out.extend_from_slice(&buf[..step - s.avail_out as usize]);
        if r != Z_OK {
            return (r, ip, out);
        }
    }
}

unsafe fn init(s: &mut ZStream, wb: c_int) {
    assert_eq!(vz_inflateInit2_(s, wb, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
}

#[test]
fn dictionaries() {
    let mut rng = Rng(5);
    let dict = text(&mut rng, 40_000);
    let data = text(&mut rng, 100_000);
    let ad = verilith_zlib::checksum::adler32(&dict) as c_ulong;
    for step in [1usize, 77, 5000] {
        // zlib: Z_NEED_DICT, a wrong dictionary, then the right one.
        let c = common::compress_ex(&data, 6, 15, 0, 0, Some(&dict), std::ptr::null_mut());
        unsafe {
            let mut s = new_stream();
            init(&mut s, 15);
            let (r, ip, out) = run(&mut s, &c, step);
            assert_eq!((r, out.len()), (Z_NEED_DICT, 0));
            assert_eq!(s.adler, ad);
            assert_eq!(vz_inflateSetDictionary(&mut s, dict.as_ptr(), 100), Z_DATA_ERROR);
            assert_eq!(vz_inflateSetDictionary(&mut s, dict.as_ptr(), dict.len() as c_uint), Z_OK);
            let (r, ip2, out) = run(&mut s, &c[ip..], step);
            assert_eq!(r, Z_STREAM_END);
            assert_eq!(ip + ip2, c.len());
            assert_eq!(out, data);
            // The history matches zlib's, partway through.
            let mut z: common::ZStream = std::mem::zeroed();
            common::zinflate_init(&mut z, 15);
            let mut zo = vec![0u8; 60_000];
            let (r, zi, _) = common::zinflate_step(&mut z, &c, &mut zo);
            assert_eq!(r, Z_NEED_DICT);
            assert_eq!(common::inflateSetDictionary(&mut z, dict.as_ptr(), dict.len() as c_uint), 0);
            assert_eq!(common::zinflate_step(&mut z, &c[zi..], &mut zo).0, Z_OK);
            let mut zh = vec![0u8; 32768];
            let mut zn: c_uint = 0;
            assert_eq!(common::inflateGetDictionary(&mut z, zh.as_mut_ptr(), &mut zn), 0);
            common::zinflate_end(&mut z);
            let mut t = new_stream();
            init(&mut t, 15);
            let (_, ip, _) = run(&mut t, &c, 1 << 20);
            assert_eq!(vz_inflateSetDictionary(&mut t, dict.as_ptr(), dict.len() as c_uint), Z_OK);
            let mut part = vec![0u8; 60_000];
            t.next_in = c.as_ptr().add(ip);
            t.avail_in = (c.len() - ip) as c_uint;
            t.next_out = part.as_mut_ptr();
            t.avail_out = 60_000;
            while t.avail_out > 0 {
                assert_eq!(vz_inflate(&mut t, 0), Z_OK);
            }
            let mut h = vec![0u8; 32768];
            let mut hn: c_uint = 0;
            assert_eq!(vz_inflateGetDictionary(&mut t, h.as_mut_ptr(), &mut hn), Z_OK);
            assert_eq!(&h[..hn as usize], &zh[..zn as usize]);
            vz_inflateEnd(&mut t);
            // At the end, it is the end of the output.
            assert_eq!(vz_inflateGetDictionary(&mut s, h.as_mut_ptr(), &mut hn), Z_OK);
            assert_eq!(&h[..hn as usize], &data[data.len() - 32768..]);
            // Setting a dictionary now is a usage error.
            assert_eq!(vz_inflateSetDictionary(&mut s, dict.as_ptr(), dict.len() as c_uint), Z_STREAM_ERROR);
            assert_eq!(vz_inflateEnd(&mut s), Z_OK);
        }
        // Raw: the dictionary goes in before any input.
        let c = common::compress_ex(&data, 6, -15, 0, 0, Some(&dict), std::ptr::null_mut());
        unsafe {
            let mut s = new_stream();
            init(&mut s, -15);
            assert_eq!(vz_inflateSetDictionary(&mut s, dict.as_ptr(), dict.len() as c_uint), Z_OK);
            let (r, ip, out) = run(&mut s, &c, step);
            assert_eq!((r, ip), (Z_STREAM_END, c.len()));
            assert_eq!(out, data);
            // Without it, the stream refers back past its start.
            assert_eq!(vz_inflateReset(&mut s), Z_OK);
            assert_eq!(run(&mut s, &c, step).0, Z_DATA_ERROR);
            assert_eq!(vz_inflateEnd(&mut s), Z_OK);
        }
    }
    // Small dictionaries, and one longer than the window.
    for n in [0usize, 1, 100, 32768, 40_000] {
        let d = &dict[..n];
        for wb in [15, -15] {
            let c = common::compress_ex(&data[..5000], 9, wb, 0, 0, Some(d), std::ptr::null_mut());
            unsafe {
                let mut s = new_stream();
                init(&mut s, wb);
                if wb < 0 {
                    assert_eq!(vz_inflateSetDictionary(&mut s, d.as_ptr(), n as c_uint), Z_OK);
                }
                let (mut r, ip, mut out) = run(&mut s, &c, 1 << 20);
                if r == Z_NEED_DICT {
                    assert_eq!(vz_inflateSetDictionary(&mut s, d.as_ptr(), n as c_uint), Z_OK);
                    let (r2, _, o2) = run(&mut s, &c[ip..], 1 << 20);
                    r = r2;
                    out = o2;
                }
                assert_eq!(r, Z_STREAM_END, "n {n} wb {wb}");
                assert_eq!(out, &data[..5000]);
                vz_inflateEnd(&mut s);
            }
        }
    }
}

#[test]
fn gzip_header() {
    let data = text(&mut Rng(6), 20_000);
    let mut extra = b"AB\x04\x00wxyz".to_vec();
    let mut name = b"file.txt\0".to_vec();
    let mut comment = b"a comment\0".to_vec();
    let mut h = GzHeader {
        text: 1,
        time: 0x1234_5678,
        xflags: 0,
        os: 3,
        extra: extra.as_mut_ptr(),
        extra_len: extra.len() as c_uint,
        extra_max: 0,
        name: name.as_mut_ptr(),
        name_max: 0,
        comment: comment.as_mut_ptr(),
        comm_max: 0,
        hcrc: 1,
        done: 0,
    };
    let c = common::compress_ex(&data, 6, 31, 0, 0, None, &mut h);
    for (wb, step) in [(31, 1usize), (47, 3), (31, 100_000)] {
        for small in [false, true] {
            unsafe {
                let mut s = new_stream();
                init(&mut s, wb);
                let mut ex = vec![0u8; 64];
                let mut nm = vec![0u8; 64];
                let mut cm = vec![0u8; 64];
                let max = if small { 3 } else { 64 };
                let mut g = GzHeader {
                    text: 0,
                    time: 0,
                    xflags: 0,
                    os: 0,
                    extra: ex.as_mut_ptr(),
                    extra_len: 0,
                    extra_max: max,
                    name: nm.as_mut_ptr(),
                    name_max: max,
                    comment: cm.as_mut_ptr(),
                    comm_max: max,
                    hcrc: 0,
                    done: 7,
                };
                assert_eq!(vz_inflateGetHeader(&mut s, &mut g), Z_OK);
                assert_eq!(g.done, 0);
                let (r, _, out) = run(&mut s, &c, step);
                assert_eq!(r, Z_STREAM_END);
                assert_eq!(out, data);
                assert_eq!((g.text, g.time, g.os, g.hcrc, g.done, g.extra_len), (1, 0x1234_5678, 3, 1, 1, 8));
                let m = max as usize;
                assert_eq!(&ex[..m.min(8)], &extra[..m.min(8)]);
                assert_eq!(&nm[..m.min(9)], &name[..m.min(9)]);
                assert_eq!(&cm[..m.min(10)], &comment[..m.min(10)]);
                vz_inflateEnd(&mut s);
            }
        }
    }
    // A zlib stream under auto-detection reports done = -1; a zlib-only
    // stream has no header to get.
    let c = compress(&data, 6, 15, 0, 0);
    unsafe {
        let mut s = new_stream();
        init(&mut s, 47);
        let mut g: GzHeader = std::mem::zeroed();
        assert_eq!(vz_inflateGetHeader(&mut s, &mut g), Z_OK);
        assert_eq!(run(&mut s, &c, 1).0, Z_STREAM_END);
        assert_eq!(g.done, -1);
        vz_inflateEnd(&mut s);
        init(&mut s, 15);
        assert_eq!(vz_inflateGetHeader(&mut s, &mut g), Z_STREAM_ERROR);
        vz_inflateEnd(&mut s);
    }
    // No optional fields: the pointers are cleared, as zlib does.
    let c = compress(&data, 6, 31, 0, 0);
    unsafe {
        let mut s = new_stream();
        init(&mut s, 31);
        let mut buf = [0u8; 4];
        let mut g: GzHeader = std::mem::zeroed();
        g.name = buf.as_mut_ptr();
        g.extra = buf.as_mut_ptr();
        assert_eq!(vz_inflateGetHeader(&mut s, &mut g), Z_OK);
        assert_eq!(run(&mut s, &c, 7).0, Z_STREAM_END);
        assert!(g.name.is_null() && g.extra.is_null() && g.done == 1);
        vz_inflateEnd(&mut s);
    }
}

#[test]
fn sync_and_copy() {
    let data = text(&mut Rng(7), 200_000);
    let c = compress(&data, 6, 15, 0, 10_000);
    for skip in [1usize, 5000, c.len() / 3, c.len() * 3 / 4] {
        unsafe {
            // Ours and zlib's resynchronize at the same place and agree.
            let mut s = new_stream();
            init(&mut s, 15);
            s.next_in = c.as_ptr().add(skip);
            s.avail_in = (c.len() - skip) as c_uint;
            assert_eq!(vz_inflateSync(&mut s), Z_OK);
            let at = c.len() - s.avail_in as usize;
            let (r, _, out) = run(&mut s, &c[at..], 4096);
            assert_eq!(r, Z_STREAM_END);
            assert!(data.ends_with(&out) && !out.is_empty());
            vz_inflateEnd(&mut s);

            let mut z: common::ZStream = std::mem::zeroed();
            common::zinflate_init(&mut z, 15);
            z.next_in = c.as_ptr().add(skip);
            z.avail_in = (c.len() - skip) as c_uint;
            assert_eq!(common::inflateSync(&mut z), 0);
            assert_eq!(c.len() - z.avail_in as usize, at);
            common::zinflate_end(&mut z);
        }
    }
    unsafe {
        let mut s = new_stream();
        init(&mut s, 15);
        let junk = [1u8, 2, 3];
        s.next_in = junk.as_ptr();
        s.avail_in = 3;
        assert_eq!(vz_inflateSync(&mut s), Z_DATA_ERROR);
        assert_eq!(s.avail_in, 0);
        assert_eq!(vz_inflateSync(&mut s), Z_BUF_ERROR);
        vz_inflateEnd(&mut s);
    }
    // Copy halfway, then finish both.
    unsafe {
        let mut s = new_stream();
        init(&mut s, 15);
        let half = c.len() / 2;
        let (r, ip, mut a) = run(&mut s, &c[..half], 1000);
        assert_eq!((r, ip), (Z_BUF_ERROR, half));
        let mut t = new_stream();
        assert_eq!(vz_inflateCopy(&mut t, &mut s), Z_OK);
        let (r, _, a2) = run(&mut s, &c[half..], 1000);
        assert_eq!(r, Z_STREAM_END);
        vz_inflateEnd(&mut s);
        a.extend_from_slice(&a2);
        assert_eq!(a, data);
        let (r, _, b2) = run(&mut t, &c[half..], 333);
        assert_eq!(r, Z_STREAM_END);
        assert!(data.ends_with(&b2) && b2.len() == a2.len());
        assert_eq!(t.total_out as usize, data.len());
        vz_inflateEnd(&mut t);
    }
}

unsafe extern "C" fn back_in(desc: *mut std::os::raw::c_void, buf: *mut *const u8) -> c_uint {
    // `desc` is (data, position, piece size).
    let d = &mut *(desc as *mut (Vec<u8>, usize, usize));
    let n = (d.0.len() - d.1).min(d.2);
    *buf = d.0.as_ptr().add(d.1);
    d.1 += n;
    n as c_uint
}

unsafe extern "C" fn back_out(desc: *mut std::os::raw::c_void, buf: *mut u8, len: c_uint) -> c_int {
    let v = &mut *(desc as *mut Vec<u8>);
    v.extend_from_slice(std::slice::from_raw_parts(buf, len as usize));
    0
}

#[test]
fn inflate_back() {
    let data = text(&mut Rng(8), 150_000);
    let c = compress(&data, 6, -15, 0, 0);
    let mut window = vec![0u8; 32768];
    for piece in [1usize, 1000, 1 << 20] {
        unsafe {
            let mut s = new_stream();
            assert_eq!(vz_inflateBackInit_(&mut s, 15, window.as_mut_ptr(), vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
            let mut src = (c.clone(), 0usize, piece);
            src.0.extend_from_slice(b"tail");
            let mut out: Vec<u8> = Vec::new();
            let r = vz_inflateBack(&mut s, Some(back_in), &mut src as *mut _ as *mut _, Some(back_out), &mut out as *mut _ as *mut _);
            assert_eq!(r, Z_STREAM_END);
            assert_eq!(out, data);
            // What was read past the end is handed back.
            let rest = std::slice::from_raw_parts(s.next_in, s.avail_in as usize);
            assert!(b"tail".starts_with(rest) && src.1 - rest.len() == c.len() + (src.1 - c.len()).min(4) - rest.len());
            // Truncated input: in() runs dry.
            let mut src = (c[..c.len() / 2].to_vec(), 0usize, piece);
            let mut out: Vec<u8> = Vec::new();
            s.next_in = std::ptr::null();
            let r = vz_inflateBack(&mut s, Some(back_in), &mut src as *mut _ as *mut _, Some(back_out), &mut out as *mut _ as *mut _);
            assert_eq!(r, Z_BUF_ERROR);
            assert!(s.next_in.is_null());
            assert_eq!(vz_inflateBackEnd(&mut s), Z_OK);
        }
    }
}

#[test]
fn checksum_helpers() {
    let mut rng = Rng(9);
    unsafe {
        let ours = std::slice::from_raw_parts(vz_get_crc_table(), 256);
        // Compared as values: the system zlib's entries may be wider (see
        // `common::ZCrc`).
        let theirs: Vec<u32> =
            std::slice::from_raw_parts(common::get_crc_table(), 256).iter().map(|&e| e as u32).collect();
        assert_eq!(ours, &theirs[..]);
    }
    for _ in 0..2000 {
        let a = rng.next() as u32 as c_ulong;
        let b = rng.next() as u32 as c_ulong;
        let n = match rng.below(3) {
            0 => rng.below(100),
            1 => rng.below(1 << 20),
            _ => rng.next() >> 2,
        } as std::os::raw::c_long;
        // Adler-32 values have each half below 65521.
        let (aa, ab) = ((a & 0xffff) % 65521 | ((a >> 16) % 65521) << 16, (b & 0xffff) % 65521 | ((b >> 16) % 65521) << 16);
        unsafe {
            assert_eq!(vz_adler32_combine(aa, ab, n), common::adler32_combine(aa, ab, n), "{aa} {ab} {n}");
            assert_eq!(vz_crc32_combine(a, b, n), common::crc32_combine(a, b, n));
            let op = vz_crc32_combine_gen(n);
            assert_eq!(op, common::crc32_combine_gen(n));
            assert_eq!(vz_crc32_combine_op(a, b, op), common::crc32_combine_op(a, b, op));
        }
    }
    // And on real data.
    let d = text(&mut rng, 10_000);
    let (x, y) = d.split_at(3777);
    let cx = verilith_zlib::checksum::crc32(x) as c_ulong;
    let cy = verilith_zlib::checksum::crc32(y) as c_ulong;
    assert_eq!(vz_crc32_combine(cx, cy, y.len() as _) as u32, verilith_zlib::checksum::crc32(&d));
    let ax = verilith_zlib::checksum::adler32(x) as c_ulong;
    let ay = verilith_zlib::checksum::adler32(y) as c_ulong;
    assert_eq!(vz_adler32_combine(ax, ay, y.len() as _) as u32, verilith_zlib::checksum::adler32(&d));
    unsafe {
        assert_eq!(vz_adler32_z(1, d.as_ptr(), d.len()) as u32, verilith_zlib::checksum::adler32(&d));
        assert_eq!(vz_crc32_z(0, d.as_ptr(), d.len()) as u32, verilith_zlib::checksum::crc32(&d));
        assert_eq!(std::ffi::CStr::from_ptr(vz_zError(Z_DATA_ERROR)).to_str().unwrap(), "data error");
    }
    assert_eq!(vz_zlibCompileFlags() & 0xff, if cfg!(target_pointer_width = "64") { 0xa9 } else { 0x55 });
}
