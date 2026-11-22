//! Decompresses each file given `VZSTD_ROUNDS` times (default 1) with the
//! one-shot decoder; for profilers.
fn main() {
    let rounds: usize = std::env::var("VZSTD_ROUNDS").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
    for f in std::env::args().skip(1) {
        let c = std::fs::read(&f).unwrap();
        let mut n = 0;
        for _ in 0..rounds {
            n = verilith_zstd::frame::decompress_exec(&c, 1 << 40).expect("invalid").len();
        }
        println!("{f}: {n} bytes");
    }
}
