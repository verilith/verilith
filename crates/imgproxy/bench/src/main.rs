//! Times verilith-imgproxy's pipeline (decode, resize, PNG encode) on
//! files, one thread, and prints one TSV line per file:
//!   file  width  height  median_ms  min_ms  out_bytes
//!   imgproxy-bench WIDTH HEIGHT ROUNDS FILE...
use std::time::Instant;
use verilith_imgproxy::fit::Mode;
use verilith_imgproxy::proxy::{process, Limits, Options};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (w, h, rounds): (u32, u32, usize) = (a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap());
    let o = Options { mode: Mode::Fit, w, h, ..Default::default() };
    let lim = Limits::default();
    for f in &a[4..] {
        let data = std::fs::read(f).unwrap();
        let mut out = process(&data, &o, &lim).unwrap();
        let mut ts = Vec::new();
        for _ in 0..rounds {
            let t = Instant::now();
            out = process(&data, &o, &lim).unwrap();
            ts.push(t.elapsed().as_secs_f64() * 1e3);
        }
        ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("{}\tverilith\t{:.2}\t{:.2}\t{}", f.rsplit('/').next().unwrap(), ts[ts.len() / 2], ts[0], out.len());
    }
}
