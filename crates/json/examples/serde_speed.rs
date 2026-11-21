//! serde speed against serde_json: `cargo run --release --features serde --example serde_speed FILE...`
use std::time::Instant;
fn best(mut f: impl FnMut()) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..30 {
        let t = Instant::now();
        f();
        b = b.min(t.elapsed().as_secs_f64());
    }
    b * 1e6
}
fn main() {
    for path in std::env::args().skip(1) {
        let d = std::fs::read(&path).unwrap();
        let v: serde_json::Value = serde_json::from_slice(&d).unwrap();
        let a = best(|| { std::hint::black_box(verilith_json::from_slice::<serde_json::Value>(&d).unwrap()); });
        let b = best(|| { std::hint::black_box(serde_json::from_slice::<serde_json::Value>(&d).unwrap()); });
        let c = best(|| { std::hint::black_box(verilith_json::to_vec(&v).unwrap()); });
        let e = best(|| { std::hint::black_box(serde_json::to_vec(&v).unwrap()); });
        println!("{path}: read {a:.0}us vs serde_json {b:.0}us; write {c:.0}us vs {e:.0}us");
    }
}
