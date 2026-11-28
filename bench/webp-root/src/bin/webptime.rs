//! Decode time of WebP files: `webptime ROUNDS FILE...` prints the fastest
//! round over all the files, in ms, and a checksum of the decoded pixels
//! (so builds with different table sizes can be checked to agree).
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let rounds: usize = a[1].parse().unwrap();
    let files: Vec<Vec<u8>> = a[2..].iter().map(|f| std::fs::read(f).unwrap()).collect();
    let mut best = f64::MAX;
    let mut sum = 0u64;
    for _ in 0..rounds {
        sum = 0;
        let t = std::time::Instant::now();
        for d in &files {
            let im = verilith_webp::capi::decode(std::hint::black_box(d)).unwrap();
            sum = sum.wrapping_mul(31).wrapping_add(im.argb.iter().fold(0u64, |s, &p| s.wrapping_mul(1_000_003).wrapping_add(p as u64)));
        }
        best = best.min(t.elapsed().as_secs_f64());
    }
    println!("{:.3}\t{sum:016x}", best * 1e3);
}
