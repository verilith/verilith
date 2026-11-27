// Compresses files at a quality and reports sizes and times, checking each
// round trip with the verified decoder.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let q: u32 = args[1].parse().unwrap();
    for f in &args[2..] {
        let d = std::fs::read(f).unwrap();
        let t = std::time::Instant::now();
        let c = verilith_brotli::compress::compress(&d, q, 22);
        let el = t.elapsed().as_secs_f64();
        let back = verilith_brotli::decompress(&c, 1 << 31).unwrap();
        assert!(back == d);
        println!("{f}\tq{q}\t{}\t{}\t{:.3}s\t{:.1} MB/s", d.len(), c.len(), el, d.len() as f64 / el / 1e6);
    }
}
