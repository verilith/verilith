fn main() {
    let b = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let mut c = 0; for _ in 0..20000 { c += verilith_dns::parse::parse(&b).unwrap().answer_count(); } println!("{c}");
}
