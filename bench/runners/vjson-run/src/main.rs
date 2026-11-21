//! JSON through vjson's own API: parse with a reused verilith_json::Parser, then
//! read every value (every number as an f64, every string and key decoded),
//! as vjson's like-for-like benchmark (vjson/examples/like_for_like.rs).
//!
//!   vjson-run               cases read/FILE, against simdjson's DOM parser
//!                           (suites/json/simdjson.cpp)
//!   vjson-run cjson-parse   the same work as cases cjson-parse/FILE, against
//!                           cJSON doing that job through its own API
//!                           (suites/json/cjson.c parse)
//!
//! The check is the same in all three drivers.
use verilith_json::Type;

#[derive(Default)]
struct Acc {
    sum: f64,
    bytes: u64,
    nums: u64,
}

fn walk(v: verilith_json::Value, a: &mut Acc) {
    match v.kind() {
        Type::Array => v.elements().unwrap().for_each(|e| walk(e, a)),
        Type::Object => {
            for (k, e) in v.members().unwrap() {
                a.bytes += k.as_bytes().len() as u64;
                walk(e, a);
            }
        }
        Type::Number => {
            a.sum += v.as_f64().unwrap();
            a.nums += 1;
        }
        Type::String => a.bytes += v.as_bytes().unwrap().len() as u64,
        _ => {}
    }
}

fn main() {
    let prefix = std::env::args().nth(1).unwrap_or_else(|| "read".into());
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".json") else { continue };
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let mut p = verilith_json::Parser::new();
        p.set_lazy(false);
        let len = data.len() as u64;
        r.case(format!("{prefix}/{stem}"), len, move || {
            let d = p.parse(std::hint::black_box(&data)).unwrap();
            let mut a = Acc::default();
            walk(d.root(), &mut a);
            std::hint::black_box(a.sum);
            a.bytes * 1000003 + a.nums
        });
    }
    r.main();
}
