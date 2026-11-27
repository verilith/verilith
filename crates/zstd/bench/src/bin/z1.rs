//! One libzstd (dlopen) compression of FILE at LEVEL, for profilers: Z1 LEVEL FILE [ROUNDS]
use std::ffi::{c_char, c_int, c_void, CString};
unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}
type Compress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize, c_int) -> usize;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let lv: i32 = a[1].parse().unwrap();
    let src = std::fs::read(&a[2]).unwrap();
    let r: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1);
    let h = unsafe { dlopen(CString::new("libzstd.so.1").unwrap().as_ptr(), 2) };
    let comp: Compress = unsafe { std::mem::transmute(dlsym(h, CString::new("ZSTD_compress").unwrap().as_ptr())) };
    let mut out = vec![0u8; src.len() + src.len() / 64 + 1024];
    let mut best = f64::MAX;
    let mut n = 0;
    for _ in 0..r {
        let t = std::time::Instant::now();
        n = unsafe { comp(out.as_mut_ptr(), out.len(), src.as_ptr(), src.len(), lv) };
        best = best.min(t.elapsed().as_secs_f64());
    }
    println!("{} -> {} in {:.1} ms, {:.1} MB/s", src.len(), n, best * 1e3, src.len() as f64 / 1e6 / best);
}
