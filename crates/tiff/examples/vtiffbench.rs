//! Times verilith-tiff on a file already in memory:
//!   vtiffbench FILE ROUNDS   prints the best time per decode in milliseconds.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let b = std::fs::read(&a[1]).expect("read");
    let rounds: usize = a[2].parse().unwrap();
    let mut best = f64::MAX;
    let mut check = 0;
    for _ in 0..rounds {
        let t = std::time::Instant::now();
        let img = verilith_tiff::decode::decode(&b, usize::MAX).expect("decodes");
        check += img.pixels.len();
        drop(img);
        best = best.min(t.elapsed().as_secs_f64() * 1e3);
    }
    assert!(check > 0);
    println!("{best:.3}");
}
