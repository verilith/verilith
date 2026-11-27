//! Compression ratio and speed of vzstd against libzstd (dlopen), with
//! every vzstd frame checked by libzstd's decoder.
//! Usage: cbench [--rounds N] [--levels 1,3,19] FILE...
use std::ffi::{c_char, c_int, c_void, CString};
use std::time::Instant;
use verilith_zstd::compress;

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}
type Compress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize, c_int) -> usize;
type Decompress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize) -> usize;
type Bound = unsafe extern "C" fn(usize) -> usize;
type IsError = unsafe extern "C" fn(usize) -> u32;

fn main() {
    let mut rounds = 3;
    let mut levels = vec![1, 3, 19];
    let mut files = vec![];
    let mut a = std::env::args().skip(1);
    while let Some(x) = a.next() {
        match x.as_str() {
            "--rounds" => rounds = a.next().unwrap().parse().unwrap(),
            "--levels" => levels = a.next().unwrap().split(',').map(|s| s.parse().unwrap()).collect(),
            _ => files.push(x),
        }
    }
    let name = std::env::var("VZSTD_LIBZSTD").unwrap_or("libzstd.so.1".into());
    let h = unsafe { dlopen(CString::new(name).unwrap().as_ptr(), 2) };
    assert!(!h.is_null());
    let sym = |s: &str| unsafe { dlsym(h, CString::new(s).unwrap().as_ptr()) };
    let comp: Compress = unsafe { std::mem::transmute(sym("ZSTD_compress")) };
    let dec: Decompress = unsafe { std::mem::transmute(sym("ZSTD_decompress")) };
    let bound: Bound = unsafe { std::mem::transmute(sym("ZSTD_compressBound")) };
    let iserr: IsError = unsafe { std::mem::transmute(sym("ZSTD_isError")) };
    println!("file\tlevel\tsize\tv_ratio\tz_ratio\tv_MB/s\tz_MB/s\tratio_rel\tspeed_rel");
    let (mut gr, mut gs, mut k) = (0f64, 0f64, 0);
    for lv in &levels {
        for f in &files {
            let src = std::fs::read(f).unwrap();
            let mut zb = vec![0u8; unsafe { bound(src.len()) }];
            let (mut vt, mut zt) = (f64::MAX, f64::MAX);
            let mut vout = vec![];
            let mut zn = 0;
            for _ in 0..rounds {
                let t = Instant::now();
                vout = compress(&src, *lv, false);
                vt = vt.min(t.elapsed().as_secs_f64());
                let t = Instant::now();
                zn = unsafe { comp(zb.as_mut_ptr(), zb.len(), src.as_ptr(), src.len(), *lv) };
                zt = zt.min(t.elapsed().as_secs_f64());
            }
            let mut back = vec![0u8; src.len()];
            let r = unsafe { dec(back.as_mut_ptr(), back.len(), vout.as_ptr(), vout.len()) };
            assert!(unsafe { iserr(r) } == 0 && r == src.len() && back == src, "libzstd rejects vzstd output for {f} level {lv}");
            let mb = src.len() as f64 / 1e6;
            let vr = src.len() as f64 / vout.len() as f64;
            let zr = src.len() as f64 / zn as f64;
            println!("{}\t{}\t{}\t{:.3}\t{:.3}\t{:.1}\t{:.1}\t{:.3}\t{:.3}", f.rsplit('/').next().unwrap(), lv, src.len(), vr, zr, mb / vt, mb / zt, vr / zr, zt / vt);
            gr += (vr / zr).ln();
            gs += (zt / vt).ln();
            k += 1;
        }
    }
    println!("geomean ratio_rel {:.3} speed_rel {:.3}", (gr / k as f64).exp(), (gs / k as f64).exp());
}
