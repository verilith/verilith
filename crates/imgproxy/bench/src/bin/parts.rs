use std::time::Instant;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&a[1]).unwrap();
    let t = Instant::now();
    let img = verilith_imgproxy::proxy::decode(&data, 1 << 40).unwrap_or_else(|_| panic!());
    let d = t.elapsed();
    let p = verilith_imgproxy::fit::plan_x(img.w, img.h, 300, 300, verilith_imgproxy::fit::Mode::Fit, false, 1 << 40).unwrap();
    let t = Instant::now();
    let r = verilith_imgproxy::resize::resize_rgba(&img.px, img.w as usize, img.h as usize, p.rw as usize, p.rh as usize);
    let rs = t.elapsed();
    let t = Instant::now();
    let rows = verilith_imgproxy::resize::rows(&img.px, img.w as usize, img.h as usize, p.rw as usize);
    let ro = t.elapsed();
    let t = Instant::now();
    let png = verilith_imgproxy::pngenc::encode_rgba(&r, p.rw, p.rh, 6).unwrap();
    let e = t.elapsed();
    println!("{}x{} decode {:?} resize {:?} (rows {:?}) encode {:?} ({} bytes)", img.w, img.h, d, rs, ro, e, png.len());
}
