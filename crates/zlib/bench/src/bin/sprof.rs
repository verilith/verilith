// Times N one-shot streams of FILE at LEVEL; SIZED=1 uses new_sized.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let level: u32 = a[2].parse().unwrap();
    let n: usize = a[3].parse().unwrap();
    let sized = std::env::var("SIZED").is_ok();
    let t = std::time::Instant::now();
    let mut total = 0;
    let mut fx = None;
    for _ in 0..n {
        let mut d = if sized {
            verilith_zlib::dstream::Deflater::new_sized(verilith_zlib::wrap::Format::Zlib, level, 15, data.len())
        } else {
            verilith_zlib::dstream::Deflater::new(verilith_zlib::wrap::Format::Zlib, level, 15)
        };
        // Reuses the fixed codes from stream to stream, as the C API does.
        d.give_fx(fx.take());
        d.write(&data, verilith_zlib::dstream::Flush::None);
        let (out, f) = d.finish_keep();
        fx = f;
        total += out.len();
    }
    let e = t.elapsed();
    println!("{} bytes, {:.2} us/stream", total / n, e.as_secs_f64() * 1e6 / n as f64);
}
