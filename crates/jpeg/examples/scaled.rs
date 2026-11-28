//! Decodes a file at m/8 of its size and writes a PNM: `scaled M IN OUT [ROUNDS]`.
use std::io::Write;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let m: u32 = a[1].parse().unwrap();
    let data = std::fs::read(&a[2]).unwrap();
    let rounds: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
    let mut times = Vec::new();
    let mut pic = None;
    for _ in 0..rounds {
        let t = std::time::Instant::now();
        let p = if m == 8 { verilith_jpeg::decode(&data) } else { verilith_jpeg::decode_scaled(&data, m) };
        times.push(t.elapsed().as_secs_f64() * 1e3);
        pic = Some(p.expect("decode"));
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let p = pic.unwrap();
    if rounds > 1 {
        eprintln!("{} m={m} {}x{} median {:.2} ms", a[2], p.w, p.h, times[times.len() / 2]);
    }
    let mut f = std::fs::File::create(&a[3]).unwrap();
    write!(f, "P{}\n{} {}\n255\n", if p.nc == 1 { 5 } else { 6 }, p.w, p.h).unwrap();
    f.write_all(&p.px).unwrap();
}
