// Compresses FILE at LEVEL once with libdeflate (for profiling).
use std::ffi::c_void;
unsafe extern "C" {
    fn libdeflate_alloc_compressor(level: i32) -> *mut c_void;
    fn libdeflate_deflate_compress(c: *mut c_void, i: *const u8, n: usize, o: *mut u8, on: usize) -> usize;
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let level: i32 = a[2].parse().unwrap();
    let mut out = vec![0u8; data.len() + 100000];
    let n = unsafe { libdeflate_deflate_compress(libdeflate_alloc_compressor(level), data.as_ptr(), data.len(), out.as_mut_ptr(), out.len()) };
    println!("{n}");
}
