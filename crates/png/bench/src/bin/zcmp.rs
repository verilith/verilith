//! Times inflating one PNG's image data with vzlib, fdeflate and zlib.
use std::time::Instant;
extern "C" {
    fn uncompress(dst: *mut u8, dlen: *mut u64, src: *const u8, slen: u64) -> i32;
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let d = std::fs::read(&a[1]).unwrap();
    let n: usize = a.get(2).map_or(10, |s| s.parse().unwrap());
    let (h, w) = verilith_png::decode::container_exec(&d).unwrap();
    let idat = verilith_png::decode::gather(&d, &w.idat).unwrap();
    let rs = verilith_png::geom::raw_size_exec(&h) as usize;
    let mut out = vec![0u8; rs + 1];
    let mut t = [f64::MAX; 3];
    for _ in 0..n {
        let s = Instant::now();
        let mut z = verilith_zlib::wrap::Decompressor::new();
        z.decompress_into(verilith_zlib::wrap::Format::Zlib, &idat, &mut out).unwrap();
        t[0] = t[0].min(s.elapsed().as_secs_f64());
        let chk = out.clone();
        let s = Instant::now();
        let mut f = fdeflate::Decompressor::new();
        let (_, m) = f.read(&idat, &mut out, 0, true).unwrap();
        assert_eq!(m, rs);
        assert!(out[..rs] == chk[..rs], "vzlib output differs");
        t[1] = t[1].min(s.elapsed().as_secs_f64());
        let s = Instant::now();
        let mut l = out.len() as u64;
        unsafe { assert_eq!(uncompress(out.as_mut_ptr(), &mut l, idat.as_ptr(), idat.len() as u64), 0) };
        t[2] = t[2].min(s.elapsed().as_secs_f64());
    }
    println!("{} in, {} out: vzlib {:.2} ms, fdeflate {:.2} ms, zlib {:.2} ms", idat.len(), rs, t[0] * 1e3, t[1] * 1e3, t[2] * 1e3);
}
