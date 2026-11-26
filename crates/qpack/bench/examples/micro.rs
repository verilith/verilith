use std::time::Instant;
fn main() {
    let vals: Vec<Vec<u8>> = (0..200).map(|i| format!("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36 {i}").into_bytes()).collect();
    let total: usize = vals.iter().map(|v| v.len()).sum();
    let mut out = Vec::with_capacity(1 << 16);
    for _ in 0..3 {
        let t = Instant::now();
        for _ in 0..100 {
            out.clear();
            for v in &vals {
                verilith_qpack::encoder::write_str(&mut out, 0, 8, v);
            }
        }
        let ns = t.elapsed().as_nanos() as f64 / (100 * total) as f64;
        let t = Instant::now();
        let mut s = 0u64;
        for _ in 0..100 {
            for v in &vals {
                s += verilith_qpack::henc::bits_of(v);
            }
        }
        let ns2 = t.elapsed().as_nanos() as f64 / (100 * total) as f64;
        println!("write_str {ns:.3} ns/byte, bits_of {ns2:.3} ns/byte ({s})");
    }
}
