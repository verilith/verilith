//! Stage timing: `cargo run --release --example split FILE...` prints, for
//! stage 1 alone and for a whole parse with a reused `Parser`, the best of
//! 400 samples, each the mean of enough runs to cover 100 KB.
//! With `S1` set in the environment, only stage 1 is timed.
use std::time::Instant;
fn best(reps: usize, mut f: impl FnMut()) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..400 {
        let t = Instant::now();
        for _ in 0..reps {
            f();
        }
        b = b.min(t.elapsed().as_secs_f64() / reps as f64);
    }
    b
}
fn main() {
    for path in std::env::args().skip(1) {
        let d = std::fs::read(&path).unwrap();
        let mut idx = Vec::new();
        let mut p = verilith_json::Parser::new();
        let reps = (100_000 / d.len()).max(1);
        let t1 = best(reps, || { std::hint::black_box(verilith_json::index::index(std::hint::black_box(&d), 0, &mut idx)); });
        let n = verilith_json::index::index(&d, 0, &mut idx).0;
        if std::env::var("S1").is_ok() { println!("{path}: stage1 {:.0} MB/s ({:.2}us)", d.len() as f64/1e6/t1, t1*1e6); continue; }
        let t2 = best(reps, || { assert!(p.parse(std::hint::black_box(&d)).is_ok()); });
        let mb = d.len() as f64 / 1e6;
        println!("{path}: stage1 {:.0} MB/s ({:.2}us), total {:.0} MB/s ({:.2}us), stage2 {:.2}us, idx {} ({:.2}/byte)", mb/t1, t1*1e6, mb/t2, t2*1e6, (t2-t1)*1e6, n, n as f64/d.len() as f64);
    }
}
