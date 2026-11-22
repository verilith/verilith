//! The compressor against both decompressors.
mod common;
use common::*;

#[test]
fn raw_round_trip() {
    for (k, d) in corpus().iter().enumerate() {
        for level in [0u32, 1, 6, 9] {
            let c = verilith_zlib::deflate::compress_raw(d, level);
            assert_eq!(verilith_zlib::inflate(&c).unwrap(), *d, "vzlib, input {k} level {level}");
            let (z, used) = zinflate(&c, -15).expect("zlib rejected");
            assert_eq!(z, *d, "zlib, input {k} level {level}");
            assert_eq!(used, c.len());
        }
    }
}

#[test]
fn ratio_report() {
    let mut tv = 0usize;
    let mut tz = 0usize;
    for d in corpus() {
        let v = verilith_zlib::deflate::compress_raw(&d, 6).len();
        let z = compress(&d, 6, -15, 0, 0).len();
        eprintln!("{:>8} bytes: vzlib {:>8} zlib {:>8}", d.len(), v, z);
        tv += v;
        tz += z;
    }
    eprintln!("total: vzlib {tv} zlib {tz} ({:.3}x)", tv as f64 / tz as f64);
}

#[test]
fn wrappers_round_trip() {
    for (k, d) in corpus().iter().enumerate() {
        for level in [0u32, 1, 6, 9] {
            let z = verilith_zlib::deflate::zlib_compress(d, level);
            assert_eq!(verilith_zlib::zlib_decompress(&z).unwrap(), *d, "zlib input {k} level {level}");
            assert_eq!(zinflate(&z, 15).unwrap(), (d.clone(), z.len()));
            let g = verilith_zlib::deflate::gzip_compress(d, level);
            assert_eq!(verilith_zlib::gzip_decompress(&g).unwrap(), *d, "gzip input {k} level {level}");
            assert_eq!(zinflate(&g, 31).unwrap(), (d.clone(), g.len()));
        }
    }
}

#[test]
#[ignore]
fn speed_report() {
    let mut rng = Rng(7);
    let d = text(&mut rng, 20_000_000);
    for level in [1u32, 6, 9] {
        let t = std::time::Instant::now();
        let v = verilith_zlib::deflate::compress_raw(&d, level);
        let tv = t.elapsed().as_secs_f64();
        let t = std::time::Instant::now();
        let z = compress(&d, level as i32, -15, 0, 0);
        let tz = t.elapsed().as_secs_f64();
        eprintln!(
            "level {level}: vzlib {:.0} MB/s ratio {:.4}, zlib {:.0} MB/s ratio {:.4}",
            d.len() as f64 / tv / 1e6,
            v.len() as f64 / d.len() as f64,
            d.len() as f64 / tz / 1e6,
            z.len() as f64 / d.len() as f64
        );
    }
}
