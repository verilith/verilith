//! For profiling: parses FILE and reads every value, N times.
fn walk(v: verilith_json::Value, a: &mut (f64, usize)) {
    use verilith_json::Type::*;
    match v.kind() {
        Array => v.elements().unwrap().for_each(|e| walk(e, a)),
        Object => {
            for (k, e) in v.members().unwrap() {
                a.1 += k.as_bytes().len();
                walk(e, a);
            }
        }
        Number => a.0 += v.as_f64().unwrap(),
        String => a.1 += v.as_bytes().unwrap().len(),
        _ => {}
    }
}
fn main() {
    let d = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let n: usize = std::env::args().nth(2).map_or(10, |s| s.parse().unwrap());
    let read = std::env::args().nth(3).is_none();
    let mut p = if std::env::var_os("LAZY").is_some() { verilith_json::Parser::lazy() } else { verilith_json::Parser::new() };
    let mut a = (0.0, 0);
    for _ in 0..n {
        let doc = p.parse(&d).unwrap();
        if read {
            walk(doc.root(), &mut a);
        }
    }
    println!("{a:?}");
}
