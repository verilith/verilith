//! Throughput of the verified core: `cargo run --release --example bench_core FILE...`
//! Prints the best of 31 samples of MB/s for a reused `verilith_json::Parser`
//! and for one-shot `verilith_json::parse`.
use std::time::Instant;
fn main() {
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        let iters = (20_000_000 / data.len()).max(1);
        let mut parser = verilith_json::Parser::new();
        let reused = median(&data, iters, || parser.parse(std::hint::black_box(&data)).is_ok());
        let fresh = median(&data, iters, || verilith_json::parse(std::hint::black_box(&data)).is_ok());
        println!("{path}: {reused:.0} MB/s (Parser), {fresh:.0} MB/s (parse)");
    }
}

fn median(data: &[u8], iters: usize, mut f: impl FnMut() -> bool) -> f64 {
    let mut samples = Vec::new();
    for _ in 0..31 {
        let t = Instant::now();
        for _ in 0..iters {
            assert!(f());
        }
        samples.push(data.len() as f64 * iters as f64 / t.elapsed().as_secs_f64() / 1e6);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples[30]
}
