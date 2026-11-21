// Compresses FILE at LEVEL ROUNDS times with vzlib (for profiling).
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let level: u32 = a[2].parse().unwrap();
    let rounds: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1);
    let mut total = 0;
    for _ in 0..rounds {
        total += verilith_zlib::deflate::compress_raw(&data, level).len();
    }
    println!("{}", total / rounds);
}
