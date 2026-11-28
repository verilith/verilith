//! Decodes each WebP file given and prints the counters `instrument.py`
//! added: per code length, how many prefix codes had it as their longest,
//! and how many symbols of that length the slow path decoded.
use std::sync::atomic::Ordering::Relaxed;
use verilith_webp::stats::{BUILT, SLOW};

fn main() {
    for f in std::env::args().skip(1) {
        let d = std::fs::read(&f).unwrap();
        verilith_webp::capi::decode(&d).unwrap_or_else(|e| panic!("{f}: {e:?}"));
    }
    println!("len\tcodes_longest\tslow_symbols");
    for l in 0..16 {
        println!("{l}\t{}\t{}", BUILT[l].load(Relaxed), SLOW[l].load(Relaxed));
    }
}
