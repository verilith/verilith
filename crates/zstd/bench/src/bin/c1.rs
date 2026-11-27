//! One level-N compression of FILE, for profilers: C1 LEVEL FILE [ROUNDS]
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let lv: i32 = a[1].parse().unwrap();
    let src = std::fs::read(&a[2]).unwrap();
    let r: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1);
    let mut best = f64::MAX;
    let mut n = 0;
    for _ in 0..r {
        let t = std::time::Instant::now();
        n = verilith_zstd::compress(&src, lv, false).len();
        best = best.min(t.elapsed().as_secs_f64());
    }
    println!("{} -> {} in {:.1} ms, {:.1} MB/s", src.len(), n, best * 1e3, src.len() as f64 / 1e6 / best);
}
