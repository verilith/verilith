//! Parallel against serial compression of one file, as gzip:
//! `cargo run --release --example par_bench FILE LEVEL THREADS[,THREADS...] [CHUNK_KIB]`.
//! Prints MB/s (best of the runs that fit in 3 seconds, at least 3), the
//! ratio to the serial `gzip_compress`, and the size against it.
use std::time::Instant;
use verilith_zlib::Format;

fn best(mut f: impl FnMut() -> usize) -> f64 {
    let start = Instant::now();
    let mut best = f64::MAX;
    let mut runs = 0;
    while runs < 3 || start.elapsed().as_secs_f64() < 3.0 {
        let t = Instant::now();
        std::hint::black_box(f());
        best = best.min(t.elapsed().as_secs_f64());
        runs += 1;
    }
    best
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let level: u32 = a[2].parse().unwrap();
    let threads: Vec<usize> = a[3].split(',').map(|x| x.parse().unwrap()).collect();
    let chunk = a.get(4).map_or(verilith_zlib::par::CHUNK, |x| x.parse::<usize>().unwrap() * 1024);
    let mb = data.len() as f64 / 1e6;
    let name = a[1].rsplit('/').next().unwrap();
    let base = verilith_zlib::deflate::gzip_compress(&data, level);
    let t1 = best(|| verilith_zlib::deflate::gzip_compress(&data, level).len());
    println!("{name}\t{level}\tserial\t{:.1}\t1.00\t{}\t0.00", mb / t1, base.len());
    for &t in &threads {
        let o = verilith_zlib::par::compress(Format::Gzip, &data, level, 15, chunk, t);
        assert!(verilith_zlib::gzip_decompress(&o).unwrap() == data, "round trip");
        let tt = best(|| verilith_zlib::par::compress(Format::Gzip, &data, level, 15, chunk, t).len());
        println!("{name}\t{level}\t{t}\t{:.1}\t{:.2}\t{}\t{:+.2}", mb / tt, t1 / tt, o.len(), (o.len() as f64 / base.len() as f64 - 1.0) * 100.0);
    }
}
