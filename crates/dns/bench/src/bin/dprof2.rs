fn main() {
    let b = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let k: usize = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(0);
    let mut c = 0; for _ in 0..20000 { c += verilith_dns::parse::parse(&b).unwrap().answer_count(); }
    for _ in 0..k { let m = verilith_dns::parse(&b).unwrap(); for rr in m.answers() { c += rr.data().is_some() as usize; } }
    println!("{c}");
}
