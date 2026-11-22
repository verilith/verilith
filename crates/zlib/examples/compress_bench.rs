//! Compression speed and ratio against the system zlib: best of 5 runs per
//! file and level. `cargo run --release --example compress_bench FILES`.
#[path = "../tests/common/mod.rs"]
#[allow(dead_code)]
mod common;

fn best<F: FnMut() -> usize>(mut f: F) -> (f64, usize) {
    let mut t = f64::MAX;
    let mut n = 0;
    for _ in 0..5 {
        let s = std::time::Instant::now();
        n = f();
        t = t.min(s.elapsed().as_secs_f64());
    }
    (t, n)
}

fn main() {
    println!("file\tlevel\tsize\tvzlib MB/s\tzlib MB/s\tvzlib ratio\tzlib ratio");
    for p in std::env::args().skip(1) {
        let d = std::fs::read(&p).unwrap();
        for level in [1u32, 6, 9] {
            let (tv, nv) = best(|| verilith_zlib::deflate::compress_raw(&d, level).len());
            let (tz, nz) = best(|| common::compress(&d, level as i32, -15, 0, 0).len());
            let mb = d.len() as f64 / 1e6;
            println!(
                "{p}\t{level}\t{}\t{:.0}\t{:.0}\t{:.4}\t{:.4}",
                d.len(),
                mb / tv,
                mb / tz,
                nv as f64 / d.len() as f64,
                nz as f64 / d.len() as f64
            );
        }
    }
}
