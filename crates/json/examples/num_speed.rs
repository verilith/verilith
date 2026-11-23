//! Number conversion speed against `f64::from_str`:
//! `cargo run --release --example num_speed FILE`
use std::time::Instant;
fn main() {
    let d = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let doc = verilith_json::parse(&d).unwrap();
    let nums: Vec<(usize, usize)> =
        doc.tape().iter().filter(|t| t.kind == verilith_json::parser::Kind::Num).map(|t| (t.start(), t.end())).collect();
    for _ in 0..15 {
        let t = Instant::now();
        let mut s = 0.0;
        for &(a, b) in &nums {
            s += verilith_json::number::parse_f64_at(&d, a, b);
        }
        let ours = t.elapsed();
        let t = Instant::now();
        for &(a, b) in &nums {
            s += std::str::from_utf8(&d[a..b]).unwrap().parse::<f64>().unwrap();
        }
        println!("{} nums: parse_f64_at {:?} std {:?} {s}", nums.len(), ours, t.elapsed());
    }
}
