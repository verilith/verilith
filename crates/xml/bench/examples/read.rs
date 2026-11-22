//! Parses one file and walks it N times, for profilers: read FILE [N]
use verilith_xml::{Child, Element};
fn walk(e: Element, n: &mut u64) {
    *n += 1;
    for a in e.attrs() {
        *n += a.value.len() as u64;
    }
    for c in e.children() {
        match c {
            Child::Element(c) => walk(c, n),
            Child::Text(t) | Child::CData(t) => *n += t.len() as u64,
            _ => {}
        }
    }
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let k: usize = a.get(2).map(|x| x.parse().unwrap()).unwrap_or(10);
    let mut n = 0;
    for _ in 0..k {
        let doc = verilith_xml::parse(std::hint::black_box(&data)).unwrap();
        walk(doc.root(), &mut n);
    }
    println!("{n}");
}
