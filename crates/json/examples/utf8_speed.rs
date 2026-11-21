//! Speed of the UTF-8 check alone: `cargo run --release --example utf8_speed FILE...`
use std::time::Instant;
fn main() {
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        let iters = (50_000_000 / data.len()).max(1);
        let mut best = f64::MAX;
        for _ in 0..21 {
            let t = Instant::now();
            for _ in 0..iters {
                assert!(verilith_json::utf8::utf8_valid(std::hint::black_box(&data), 0));
            }
            best = best.min(t.elapsed().as_secs_f64() / iters as f64);
        }
        let mut stdbest = f64::MAX;
        for _ in 0..21 {
            let t = Instant::now();
            for _ in 0..iters {
                assert!(std::str::from_utf8(std::hint::black_box(&data)).is_ok());
            }
            stdbest = stdbest.min(t.elapsed().as_secs_f64() / iters as f64);
        }
        println!("{path}: {:.2}us ({:.1} GB/s), std {:.2}us", best * 1e6, data.len() as f64 / best / 1e9, stdbest * 1e6);
    }
}
