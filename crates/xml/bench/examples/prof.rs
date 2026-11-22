//! Parses one file N times, for profilers: prof FILE [N]
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let n: usize = a.get(2).map(|x| x.parse().unwrap()).unwrap_or(10);
    let mut tape = verilith_xml::tape::Tape::new();
    let mut ok = 0;
    for _ in 0..n {
        ok += verilith_xml::check(std::hint::black_box(&data), &mut tape) as usize;
    }
    println!("{ok} {}", tape.len());
}
