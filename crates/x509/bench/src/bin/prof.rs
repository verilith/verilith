// Runs one parser many times on one certificate, for callgrind.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let b = std::fs::read(&a[1]).unwrap();
    let mut n = 0;
    for _ in 0..2000 {
        n += std::hint::black_box(verilith_x509::parse(std::hint::black_box(&b)).unwrap().tbs.serial.len());
    }
    println!("{n}");
}
