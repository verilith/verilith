//! gzip of a 16 KiB HTML page, as the proxy compresses one: microseconds
//! per call and output size, verilith-zlib against the system zlib, by
//! level. `cargo run --release --example page_bench [ITERS] [LEVELS...]`;
//! `PAGE=file` times that file instead, `ONLY=1` skips zlib.
#[path = "../tests/common/mod.rs"]
#[allow(dead_code)]
mod common;

/// The fastest of 25 rounds of `n / 25` calls: the VM is noisy.
fn per_call<F: FnMut() -> usize>(n: usize, mut f: F) -> (f64, usize) {
    let mut len = 0;
    let k = (n / 25).max(1);
    let mut best = f64::MAX;
    for _ in 0..25 {
        let s = std::time::Instant::now();
        for _ in 0..k {
            len = f();
        }
        best = best.min(s.elapsed().as_secs_f64() * 1e6 / k as f64);
    }
    (best, len)
}

fn main() {
    let n: usize = std::env::args().nth(1).map_or(5000, |a| a.parse().unwrap());
    let page: String = (0..320).map(|i| format!("<p>paragraph {i} of a page that proxies compress</p>\n")).collect();
    let file = std::env::var("PAGE").ok().filter(|f| !f.is_empty()).map(|f| std::fs::read(f).unwrap());
    let b = file.as_deref().unwrap_or(page.as_bytes());
    println!("level\tvzlib us\tzlib us\tvzlib bytes\tzlib bytes");
    let levels: Vec<u32> = std::env::args().skip(2).map(|a| a.parse().unwrap()).collect();
    let levels = if levels.is_empty() { vec![1, 2, 3, 4, 5, 6] } else { levels };
    for level in levels {
        let (tv, nv) = per_call(n, || verilith_zlib::gzip_compress(b, level).len());
        let only = std::env::var("ONLY").is_ok();
        let (tz, nz) = if only { (0.0, 0) } else { per_call(n, || common::compress(b, level as i32, 31, 0, 0).len()) };
        println!("{level}\t{tv:.1}\t{tz:.1}\t{nv}\t{nz}");
    }
}
