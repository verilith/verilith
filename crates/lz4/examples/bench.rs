//! Speed against the system's liblz4 (loaded with dlopen), best of N:
//! `cargo run --release --example bench -- FILE...`
#[path = "../tests/common/mod.rs"]
mod common;
use common::Lz4;
use std::time::Instant;

fn best<F: FnMut() -> usize>(mut f: F, bytes: usize) -> f64 {
    let mut best = f64::MAX;
    let t0 = Instant::now();
    let mut runs = 0;
    while runs < 5 || (t0.elapsed().as_secs_f64() < 1.0 && runs < 200) {
        let t = Instant::now();
        std::hint::black_box(f());
        best = best.min(t.elapsed().as_secs_f64());
        runs += 1;
    }
    bytes as f64 / best / 1e6
}

fn main() {
    let l = Lz4::load().expect("liblz4");
    println!("{:<12} {:>9} {:>7} {:>7} | {:>8} {:>8} {:>6} | {:>8} {:>8} {:>6}", "file", "size", "ratio", "ref", "c MB/s", "ref", "x", "d MB/s", "ref", "x");
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        let name = std::path::Path::new(&path).file_name().unwrap().to_string_lossy().to_string();
        let mut ours = vec![0u8; verilith_lz4::compress::compress_bound(data.len())];
        let n = verilith_lz4::compress::compress_into(&data, &mut ours, 1).unwrap();
        ours.truncate(n);
        let theirs = l.compress(&data, 1);
        let mut buf = vec![0u8; ours.len().max(theirs.len()) + 64];
        let c_ours = best(|| verilith_lz4::compress::compress_into(&data, &mut buf, 1).unwrap(), data.len());
        let c_ref = best(|| l.compress_into(&data, &mut buf), data.len());
        let mut out = vec![0u8; data.len()];
        // Both decode liblz4's block.
        let d_ours = best(|| verilith_lz4::block::decompress_into(&theirs, &mut out).unwrap(), data.len());
        assert_eq!(out, data);
        let d_ref = best(|| l.decompress_into(&theirs, &mut out), data.len());
        println!(
            "{:<12} {:>9} {:>7.3} {:>7.3} | {:>8.0} {:>8.0} {:>6.2} | {:>8.0} {:>8.0} {:>6.2}",
            name,
            data.len(),
            data.len() as f64 / ours.len() as f64,
            data.len() as f64 / theirs.len() as f64,
            c_ours,
            c_ref,
            c_ours / c_ref,
            d_ours,
            d_ref,
            d_ours / d_ref
        );
    }
}
