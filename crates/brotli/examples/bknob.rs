// Compresses files with planner settings from the environment (for tuning):
//   QUALITY, MODES, MAXT, MAXB, MAXCH, MINCH.
fn env(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}
fn main() {
    let q = env("QUALITY", 6) as u32;
    let mut p = verilith_brotli::compress::params(q);
    p.k.modes = env("MODES", p.k.modes as usize) as u32;
    p.k.maxt = env("MAXT", p.k.maxt);
    p.k.maxb = env("MAXB", p.k.maxb);
    p.k.maxch = env("MAXCH", p.k.maxch);
    p.k.minch = env("MINCH", p.k.minch);
    p.block = env("BLOCK", p.block);
    p.k.fastmode = env("FASTMODE", p.k.fastmode as usize) != 0;
    let mut tot = 0;
    for f in std::env::args().skip(1) {
        let d = std::fs::read(&f).unwrap();
        let t = std::time::Instant::now();
        let c = verilith_brotli::compress::compress_with(&d, p.clone(), 22);
        let el = t.elapsed().as_secs_f64();
        assert!(verilith_brotli::decompress(&c, 1 << 31).unwrap() == d);
        tot += c.len();
        println!("{f}\tq{q}\t{}\t{}\t{:.3}s", d.len(), c.len(), el);
    }
    println!("total\t{tot}");
}
