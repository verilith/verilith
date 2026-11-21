//! vjson side of the like-for-like benchmark (bench/run.sh). For each file
//! prints MB/s for: parse only (lazy), and parse then read every value
//! (eager; every number as an f64, every string and key decoded). Like the
//! simdjson side, both use one reused parser.
use std::time::Instant;

#[derive(Default)]
struct Acc {
    sum: f64,
    bytes: usize,
}

fn walk(v: verilith_json::Value, a: &mut Acc) {
    use verilith_json::Type::*;
    match v.kind() {
        Array => v.elements().unwrap().for_each(|e| walk(e, a)),
        Object => {
            for (k, e) in v.members().unwrap() {
                a.bytes += k.as_bytes().len();
                walk(e, a);
            }
        }
        Number => a.sum += v.as_f64().unwrap(),
        String => a.bytes += v.as_bytes().unwrap().len(),
        _ => {}
    }
}

fn main() {
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        let reps = (2_000_000 / data.len()).max(1);
        let mut p = verilith_json::Parser::new();
        let eager = std::env::var_os("LAZY").is_none();
        let (mut parse, mut read) = (f64::MAX, f64::MAX);
        let mut keep = 0usize;
        for _ in 0..200 {
            p.set_lazy(true);
            let t = Instant::now();
            for _ in 0..reps {
                assert!(p.parse(std::hint::black_box(&data)).is_ok());
            }
            p.set_lazy(!eager);
            let t2 = Instant::now();
            for _ in 0..reps {
                let d = p.parse(std::hint::black_box(&data)).unwrap();
                let mut a = Acc::default();
                walk(d.root(), &mut a);
                keep = keep.wrapping_add(a.bytes).wrapping_add(a.sum as usize);
            }
            let t3 = Instant::now();
            parse = parse.min((t2 - t).as_secs_f64() / reps as f64);
            read = read.min((t3 - t2).as_secs_f64() / reps as f64);
        }
        let n = data.len() as f64 / 1e6;
        println!("{path} {:.0} {:.0} {}", n / parse, n / read, keep % 7);
    }
}
