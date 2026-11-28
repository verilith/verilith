//! Decode time of verilith-lz4 blocks: `lz4dec ROUNDS FILE...`. Each file
//! is compressed in 4 MiB blocks once, then all of them are decoded ROUNDS
//! times; prints, per file, the fastest round in ns per input byte. The
//! fastest of many rounds is the least disturbed by other work on the
//! machine. `wild-sweep.sh` runs it for several values of WILD_MAX.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let rounds: usize = a[1].parse().unwrap();
    for f in &a[2..] {
        let d = std::fs::read(f).unwrap();
        let blocks: Vec<(Vec<u8>, usize)> = d
            .chunks(4 << 20)
            .map(|p| {
                let mut c = vec![0u8; verilith_lz4::compress::compress_bound(p.len())];
                let n = verilith_lz4::compress::compress_into(p, &mut c, 1).unwrap();
                c.truncate(n);
                (c, p.len())
            })
            .collect();
        let mut out = vec![0u8; 4 << 20];
        let mut best = f64::MAX;
        for _ in 0..rounds {
            let t = std::time::Instant::now();
            for (c, n) in &blocks {
                let r = verilith_lz4::block::decompress_into(std::hint::black_box(c), &mut out[..*n]);
                assert_eq!(r, Some(*n));
            }
            best = best.min(t.elapsed().as_secs_f64());
        }
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy();
        println!("{name}\t{:.4}", best * 1e9 / d.len() as f64);
    }
}
