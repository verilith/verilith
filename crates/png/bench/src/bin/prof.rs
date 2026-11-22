//! Times vpng's phases on one file: container + CRC, parse + inflate,
//! unfilter, output conversion (generic and direct paths).
use std::time::Instant;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let d = std::fs::read(&a[1]).unwrap();
    let n: usize = a.get(2).map_or(10, |s| s.parse().unwrap());
    let mut t = [f64::MAX; 6];
    let mut tick = |i: usize, s: Instant| t[i] = t[i].min(s.elapsed().as_secs_f64());
    for _ in 0..n {
        let s = Instant::now();
        std::hint::black_box(verilith_png::decode::container_exec(&d).unwrap());
        tick(0, s);
        let s = Instant::now();
        let (png, mut buf) = verilith_png::decode::parse_exec(&d, 1 << 34).unwrap();
        tick(1, s);
        let s = Instant::now();
        let off = verilith_png::passes::reconstruct(&png.hdr, &mut buf).unwrap();
        tick(2, s);
        let s = Instant::now();
        std::hint::black_box(verilith_png::output::to_native(&png.hdr, &buf, &off, 1 << 34).unwrap());
        tick(3, s);
        let s = Instant::now();
        std::hint::black_box(verilith_png::output::to_rgba8(&png, &buf, &off, 1 << 34).unwrap());
        tick(4, s);
        if png.hdr.interlace == 1 {
            let s = Instant::now();
            std::hint::black_box(verilith_png::deint::deinterlace(&png.hdr, &buf, &off, 1 << 34).unwrap());
            tick(5, s);
        }
        if png.hdr.interlace == 0 && png.hdr.bit_depth == 8 {
            let s = Instant::now();
            std::hint::black_box(verilith_png::fast::rgba8_flat(&png, buf, &off, 1 << 34).unwrap());
            tick(5, s);
        }
    }
    println!(
        "container+crc {:.2} ms, parse+inflate {:.2} ms, unfilter {:.2} ms, native (generic) {:.2} ms, rgba8 (generic) {:.2} ms, rgba8 direct / deinterlace {:.2} ms",
        t[0] * 1e3, t[1] * 1e3, t[2] * 1e3, t[3] * 1e3, t[4] * 1e3, t[5] * 1e3
    );
}
