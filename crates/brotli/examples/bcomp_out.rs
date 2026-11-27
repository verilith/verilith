// Writes `file` compressed at a quality to `out`.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let d = std::fs::read(&a[2]).unwrap();
    let c = verilith_brotli::compress::compress(&d, a[1].parse().unwrap(), 22);
    std::fs::write(&a[3], c).unwrap();
}
