//! Decodes a PNG file and writes `width height` and the pixels to stdout,
//! or `ERR kind`. Usage: vpngcat FILE [rgba8|native]
use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let data = std::fs::read(&args[1]).expect("read");
    let fmt = match args.get(2).map(|s| s.as_str()) {
        Some("native") => verilith_png::top::PixelFormat::Native,
        _ => verilith_png::top::PixelFormat::Rgba8,
    };
    let mut out = std::io::stdout().lock();
    match verilith_png::top::decode(&data, fmt, 1 << 32) {
        Ok((h, px)) => {
            writeln!(out, "{} {} {} {} {}", h.width, h.height, h.bit_depth, h.color_type, h.interlace).unwrap();
            out.write_all(&px).unwrap();
        }
        Err(e) => {
            writeln!(out, "ERR {:?}", e).unwrap();
        }
    }
}
