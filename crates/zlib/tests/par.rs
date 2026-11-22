//! Parallel compression against both decompressors.
mod common;
use common::{text, zinflate, Rng};
use std::os::raw::{c_int, c_uint, c_ulong};
use verilith_zlib::capi::*;
use verilith_zlib::Format;

fn inputs() -> Vec<Vec<u8>> {
    let mut rng = Rng(11);
    let mut v = vec![Vec::new(), vec![7u8; 1], text(&mut rng, 32768), text(&mut rng, 32769), text(&mut rng, 100_000), text(&mut rng, 1_500_000)];
    // Incompressible, then long runs (matches that cross chunk borders).
    let mut r = Rng(5);
    v.push((0..700_000).map(|_| (r.next() >> 24) as u8).collect());
    v.push(vec![0u8; 400_000]);
    v
}

#[test]
fn round_trip() {
    for (k, d) in inputs().iter().enumerate() {
        for level in [0u32, 1, 6, 9] {
            for (chunk, threads) in [(32768usize, 1usize), (32768, 4), (50_000, 3), (262144, 8)] {
                let what = format!("input {k} level {level} chunk {chunk} threads {threads}");
                let c = verilith_zlib::par::compress(Format::Raw, d, level, 15, chunk, threads);
                assert_eq!(verilith_zlib::inflate(&c).unwrap(), *d, "raw, vzlib, {what}");
                assert_eq!(zinflate(&c, -15).expect("zlib rejected"), (d.clone(), c.len()), "raw, zlib, {what}");
                let c = verilith_zlib::par::compress(Format::Zlib, d, level, 15, chunk, threads);
                assert_eq!(verilith_zlib::zlib_decompress(&c).unwrap(), *d, "zlib, vzlib, {what}");
                assert_eq!(zinflate(&c, 15).expect("zlib rejected"), (d.clone(), c.len()), "zlib, zlib, {what}");
                let c = verilith_zlib::par::compress(Format::Gzip, d, level, 15, chunk, threads);
                assert_eq!(verilith_zlib::gzip_decompress(&c).unwrap(), *d, "gzip, vzlib, {what}");
                assert_eq!(zinflate(&c, 31).expect("zlib rejected"), (d.clone(), c.len()), "gzip, zlib, {what}");
            }
        }
    }
}

/// The output does not depend on how many threads made it.
#[test]
fn same_bytes_for_any_thread_count() {
    let mut rng = Rng(3);
    let d = text(&mut rng, 2_000_000);
    let one = verilith_zlib::par::compress(Format::Gzip, &d, 6, 15, 65536, 1);
    for threads in [2usize, 5, 16] {
        assert_eq!(verilith_zlib::par::compress(Format::Gzip, &d, 6, 15, 65536, threads), one);
    }
}

/// Small windows: zlib, told the same `windowBits`, must still decode it.
#[test]
fn small_windows() {
    let mut rng = Rng(9);
    let d = text(&mut rng, 300_000);
    for wbits in 9u32..=15 {
        let c = verilith_zlib::par::compress(Format::Zlib, &d, 6, wbits, 40_000, 4);
        assert_eq!(zinflate(&c, wbits as i32).expect("zlib rejected").0, d, "wbits {wbits}");
    }
}

/// The C API with threads on: `compress2` and one-call `deflate()` stay
/// within `compressBound`, give streams zlib reads, and report the same
/// totals and check value as with threads off.
#[test]
fn c_api() {
    let mut rng = Rng(21);
    let mut r = Rng(22);
    let noise: Vec<u8> = (0..3_000_000).map(|_| (r.next() >> 24) as u8).collect();
    for d in [text(&mut rng, 3_000_000), noise] {
        unsafe {
            let size = std::mem::size_of::<ZStream>() as c_int;
            let mut serial: Vec<(c_ulong, c_ulong)> = Vec::new();
            for threads in [1, 4] {
                assert_eq!(vzlib_set_threads(threads), threads);
                let mut out = vec![0u8; vz_compressBound(d.len() as c_ulong) as usize];
                let mut n = out.len() as c_ulong;
                assert_eq!(vz_compress2(out.as_mut_ptr(), &mut n, d.as_ptr(), d.len() as c_ulong, 6), 0);
                assert_eq!(zinflate(&out[..n as usize], 15).unwrap(), (d.clone(), n as usize));
                for (w, wbits) in [15, 31, -15].into_iter().enumerate() {
                    // Output in two buffers, so the second call only drains.
                    let mut s: ZStream = std::mem::zeroed();
                    assert_eq!(vz_deflateInit2_(&mut s, 6, 8, wbits, 8, 0, vz_zlibVersion(), size), 0);
                    let bound = vz_deflateBound(&mut s, d.len() as c_ulong) as usize;
                    let mut out = vec![0u8; bound];
                    s.next_in = d.as_ptr();
                    s.avail_in = d.len() as c_uint;
                    s.next_out = out.as_mut_ptr();
                    s.avail_out = 1000;
                    assert_eq!(vz_deflate(&mut s, 4), 0);
                    assert_eq!(s.avail_out, 0);
                    s.avail_out = (bound - 1000) as c_uint;
                    assert_eq!(vz_deflate(&mut s, 4), 1);
                    assert_eq!(s.avail_in, 0);
                    assert_eq!(s.total_in as usize, d.len());
                    let n = s.total_out as usize;
                    assert_eq!(zinflate(&out[..n], wbits).unwrap(), (d.clone(), n));
                    if threads == 1 {
                        serial.push((s.total_in, s.adler));
                    } else if wbits > 0 {
                        assert_eq!((s.total_in, s.adler), serial[w]);
                    }
                    assert_eq!(vz_deflateEnd(&mut s), 0);
                }
            }
            vzlib_set_threads(1);
        }
    }
}
