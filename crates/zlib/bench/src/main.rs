//! Throughput of vzlib against zlib, zlib-ng and libdeflate, on the same
//! machine in the same process, interleaved, best of N rounds.
//!
//! `vzlib-bench inflate DIR [rounds]`: one-shot decompression of each file
//! (compressed by zlib at level 6) into a buffer of the known size, MB/s of
//! output, for raw, zlib and gzip.
//!
//! `vzlib-bench deflate DIR [rounds]`: one-shot raw compression at levels
//! 1, 6 and 9, MB/s of input and compressed size over input size.
extern crate libz_ng_sys;
use std::os::raw::{c_char, c_int, c_uint, c_ulong, c_void};
use std::time::Instant;

#[repr(C)]
struct ZStream {
    next_in: *const u8,
    avail_in: c_uint,
    total_in: c_ulong,
    next_out: *mut u8,
    avail_out: c_uint,
    total_out: c_ulong,
    msg: *const c_char,
    state: *mut c_void,
    zalloc: *const c_void,
    zfree: *const c_void,
    opaque: *mut c_void,
    data_type: c_int,
    adler: c_ulong,
    reserved: c_ulong,
}

#[repr(C)]
struct ZngStream {
    next_in: *const u8,
    avail_in: u32,
    total_in: usize,
    next_out: *mut u8,
    avail_out: u32,
    total_out: usize,
    msg: *const c_char,
    state: *mut c_void,
    zalloc: *const c_void,
    zfree: *const c_void,
    opaque: *mut c_void,
    data_type: c_int,
    adler: u32,
    reserved: c_ulong,
}

extern "C" {
    fn zlibVersion() -> *const c_char;
    fn inflateInit2_(s: *mut ZStream, wbits: c_int, ver: *const c_char, size: c_int) -> c_int;
    fn inflateReset2(s: *mut ZStream, wbits: c_int) -> c_int;
    fn inflate(s: *mut ZStream, flush: c_int) -> c_int;
    fn deflateInit2_(s: *mut ZStream, level: c_int, method: c_int, wbits: c_int, mem: c_int, strategy: c_int, ver: *const c_char, size: c_int) -> c_int;
    fn deflate(s: *mut ZStream, flush: c_int) -> c_int;
    fn deflateEnd(s: *mut ZStream) -> c_int;
    fn deflateBound(s: *mut ZStream, n: c_ulong) -> c_ulong;

    fn zlibng_version() -> *const c_char;
    fn zng_inflateInit2(s: *mut ZngStream, wbits: i32) -> i32;
    fn zng_inflateReset2(s: *mut ZngStream, wbits: i32) -> i32;
    fn zng_inflate(s: *mut ZngStream, flush: i32) -> i32;
    fn zng_deflateInit2(s: *mut ZngStream, level: i32, method: i32, wbits: i32, mem: i32, strategy: i32) -> i32;
    fn zng_deflate(s: *mut ZngStream, flush: i32) -> i32;
    fn zng_deflateEnd(s: *mut ZngStream) -> i32;

    fn libdeflate_alloc_decompressor() -> *mut c_void;
    fn libdeflate_deflate_decompress(d: *mut c_void, i: *const u8, n: usize, o: *mut u8, on: usize, actual: *mut usize) -> c_int;
    fn libdeflate_gzip_decompress(d: *mut c_void, i: *const u8, n: usize, o: *mut u8, on: usize, actual: *mut usize) -> c_int;
    fn libdeflate_zlib_decompress(d: *mut c_void, i: *const u8, n: usize, o: *mut u8, on: usize, actual: *mut usize) -> c_int;
    fn libdeflate_alloc_compressor(level: c_int) -> *mut c_void;
    fn libdeflate_free_compressor(c: *mut c_void);
    fn libdeflate_deflate_compress(c: *mut c_void, i: *const u8, n: usize, o: *mut u8, on: usize) -> usize;
    fn libdeflate_deflate_compress_bound(c: *mut c_void, n: usize) -> usize;
}

/// Times each closure for `rounds` rounds and returns each one's best time
/// in seconds. By default the closures take turns each round; with
/// `VZLIB_BENCH_SEQ` set, each one runs all its rounds alone (after a
/// warm-up round), which suits machines whose clock speed drifts with
/// load. Each closure returns a size that must not change.
fn race(rounds: usize, bytes: usize, fs: &mut [&mut dyn FnMut() -> usize]) -> Vec<f64> {
    let mut best = vec![f64::MAX; fs.len()];
    let reps = (20_000_000 / bytes.max(1)).max(1);
    let mut sizes = vec![None; fs.len()];
    let mut time = |k: usize, f: &mut dyn FnMut() -> usize| {
        let t = Instant::now();
        for _ in 0..reps {
            let n = f();
            assert_eq!(*sizes[k].get_or_insert(n), n);
        }
        t.elapsed().as_secs_f64() / reps as f64
    };
    // `VZLIB_BENCH_ONLY=k` times only library `k` (0 vzlib, 1 zlib, 2
    // zlib-ng, 3 libdeflate), so each can run in its own process.
    let only: Option<usize> = std::env::var("VZLIB_BENCH_ONLY").ok().map(|s| s.parse().unwrap());
    if let Some(k) = only {
        time(k, fs[k]);
        for _ in 0..rounds {
            best[k] = best[k].min(time(k, fs[k]));
        }
    } else if std::env::var_os("VZLIB_BENCH_SEQ").is_some() {
        for (k, f) in fs.iter_mut().enumerate() {
            time(k, *f);
            for _ in 0..rounds {
                best[k] = best[k].min(time(k, *f));
            }
        }
    } else {
        for _ in 0..rounds {
            for (k, f) in fs.iter_mut().enumerate() {
                best[k] = best[k].min(time(k, *f));
            }
        }
    }
    best
}

fn zlib_compress(data: &[u8], level: c_int, wbits: c_int) -> Vec<u8> {
    unsafe {
        let mut s: ZStream = std::mem::zeroed();
        assert_eq!(deflateInit2_(&mut s, level, 8, wbits, 8, 0, zlibVersion(), std::mem::size_of::<ZStream>() as c_int), 0);
        let mut out = vec![0u8; deflateBound(&mut s, data.len() as c_ulong) as usize];
        s.next_in = data.as_ptr();
        s.avail_in = data.len() as c_uint;
        s.next_out = out.as_mut_ptr();
        s.avail_out = out.len() as c_uint;
        assert_eq!(deflate(&mut s, 4), 1);
        out.truncate(s.total_out as usize);
        deflateEnd(&mut s);
        out
    }
}

fn files(dir: &str) -> Vec<(String, Vec<u8>)> {
    let mut names: Vec<String> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
    names.sort();
    names.into_iter().map(|n| (n.clone(), std::fs::read(format!("{dir}/{n}")).unwrap())).collect()
}

fn bench_inflate(dir: &str, rounds: usize) {
    println!("file\tformat\tsize\tvzlib\tzlib\tzlib-ng\tlibdeflate\t(MB/s of output)");
    let mut d = verilith_zlib::Decompressor::new();
    let ld = unsafe { libdeflate_alloc_decompressor() };
    let mut zs: ZStream = unsafe { std::mem::zeroed() };
    let mut ns: ZngStream = unsafe { std::mem::zeroed() };
    unsafe {
        assert_eq!(inflateInit2_(&mut zs, -15, zlibVersion(), std::mem::size_of::<ZStream>() as c_int), 0);
        assert_eq!(zng_inflateInit2(&mut ns, -15), 0);
    }
    for (name, orig) in files(dir) {
        for (ext, fmt, wb) in [("raw", verilith_zlib::Format::Raw, -15), ("zlib", verilith_zlib::Format::Zlib, 15), ("gzip", verilith_zlib::Format::Gzip, 31)] {
            let c = zlib_compress(&orig, 6, wb);
            let n = orig.len();
            let mut o1 = vec![0u8; n];
            let mut o2 = vec![0u8; n];
            let mut o3 = vec![0u8; n];
            let mut o4 = vec![0u8; n];
            let t = {
                let mut fv = || d.decompress_into(fmt, &c, &mut o1).unwrap().1;
                let zsp = &mut zs;
                let mut fz = || unsafe {
                    inflateReset2(zsp, wb);
                    zsp.next_in = c.as_ptr();
                    zsp.avail_in = c.len() as c_uint;
                    zsp.next_out = o2.as_mut_ptr();
                    zsp.avail_out = n as c_uint;
                    assert_eq!(inflate(zsp, 4), 1);
                    n - zsp.avail_out as usize
                };
                let nsp = &mut ns;
                let mut fn_ = || unsafe {
                    zng_inflateReset2(nsp, wb);
                    nsp.next_in = c.as_ptr();
                    nsp.avail_in = c.len() as u32;
                    nsp.next_out = o3.as_mut_ptr();
                    nsp.avail_out = n as u32;
                    assert_eq!(zng_inflate(nsp, 4), 1);
                    n - nsp.avail_out as usize
                };
                let mut fl = || unsafe {
                    let mut m = 0usize;
                    let f = match fmt {
                        verilith_zlib::Format::Raw => libdeflate_deflate_decompress,
                        verilith_zlib::Format::Gzip => libdeflate_gzip_decompress,
                        _ => libdeflate_zlib_decompress,
                    };
                    assert_eq!(f(ld, c.as_ptr(), c.len(), o4.as_mut_ptr(), n, &mut m), 0);
                    m
                };
                // Once each, so every output is checked below.
                let fs: &mut [&mut dyn FnMut() -> usize] = &mut [&mut fv, &mut fz, &mut fn_, &mut fl];
                for f in fs.iter_mut() {
                    f();
                }
                race(rounds, n, fs)
            };
            assert!(o1 == orig && o2 == orig && o3 == orig && o4 == orig);
            let mbs: Vec<String> = t.iter().map(|s| format!("{:.0}", n as f64 / s / 1e6)).collect();
            println!("{name}\t{ext}\t{n}\t{}", mbs.join("\t"));
        }
    }
}

fn bench_deflate(dir: &str, rounds: usize) {
    println!("file\tlevel\tsize\tvzlib\tzlib\tzlib-ng\tlibdeflate\t(MB/s of input; then compressed/input)");
    for (name, orig) in files(dir) {
        let n = orig.len();
        let levels: Vec<c_int> = std::env::var("VZLIB_LEVELS").map(|v| v.split(',').map(|x| x.parse().unwrap()).collect()).unwrap_or(vec![1, 6, 9]);
        for &level in &levels {
            let ldc = unsafe { libdeflate_alloc_compressor(level) };
            let mut outz = vec![0u8; n + n / 100 + 1024];
            let mut outn = vec![0u8; n + n / 100 + 1024];
            let mut outl = vec![0u8; unsafe { libdeflate_deflate_compress_bound(ldc, n) }];
            let mut sizes = [0usize; 4];
            let t = {
                let mut fv = || verilith_zlib::deflate::compress_raw(&orig, level as u32).len();
                let mut fz = || unsafe {
                    let mut s: ZStream = std::mem::zeroed();
                    deflateInit2_(&mut s, level, 8, -15, 8, 0, zlibVersion(), std::mem::size_of::<ZStream>() as c_int);
                    s.next_in = orig.as_ptr();
                    s.avail_in = n as c_uint;
                    s.next_out = outz.as_mut_ptr();
                    s.avail_out = outz.len() as c_uint;
                    assert_eq!(deflate(&mut s, 4), 1);
                    let m = s.total_out as usize;
                    deflateEnd(&mut s);
                    m
                };
                let mut fn_ = || unsafe {
                    let mut s: ZngStream = std::mem::zeroed();
                    zng_deflateInit2(&mut s, level, 8, -15, 8, 0);
                    s.next_in = orig.as_ptr();
                    s.avail_in = n as u32;
                    s.next_out = outn.as_mut_ptr();
                    s.avail_out = outn.len() as u32;
                    assert_eq!(zng_deflate(&mut s, 4), 1);
                    let m = s.total_out;
                    zng_deflateEnd(&mut s);
                    m
                };
                let mut fl = || unsafe { libdeflate_deflate_compress(ldc, orig.as_ptr(), n, outl.as_mut_ptr(), outl.len()) };
                let fs: &mut [&mut dyn FnMut() -> usize] = &mut [&mut fv, &mut fz, &mut fn_, &mut fl];
                for (k, f) in fs.iter_mut().enumerate() {
                    sizes[k] = f();
                }
                race(rounds, n, fs)
            };
            unsafe { libdeflate_free_compressor(ldc) };
            // Every output must round-trip.
            let v = verilith_zlib::deflate::compress_raw(&orig, level as u32);
            assert_eq!(verilith_zlib::inflate(&v).unwrap(), orig);
            let mbs: Vec<String> = t.iter().map(|s| format!("{:.0}", n as f64 / s / 1e6)).collect();
            let ratios: Vec<String> = sizes.iter().map(|&m| format!("{:.4}", m as f64 / n as f64)).collect();
            println!("{name}\t{level}\t{n}\t{}\t{}", mbs.join("\t"), ratios.join("\t"));
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let rounds: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(9);
    unsafe {
        eprintln!(
            "zlib {}, zlib-ng {}",
            std::ffi::CStr::from_ptr(zlibVersion()).to_string_lossy(),
            std::ffi::CStr::from_ptr(zlibng_version()).to_string_lossy()
        );
    }
    match args.get(1).map(|s| s.as_str()) {
        Some("inflate") => bench_inflate(&args[2], rounds),
        Some("deflate") => bench_deflate(&args[2], rounds),
        _ => eprintln!("usage: vzlib-bench inflate|deflate DIR [rounds]"),
    }
}
