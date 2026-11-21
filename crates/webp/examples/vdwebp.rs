//! Decodes a lossless WebP file to PAM (like `dwebp -pam`).
//!
//! Usage: vdwebp input.webp output.pam
use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: vdwebp input.webp output.pam");
        std::process::exit(2);
    }
    let data = std::fs::read(&args[1]).expect("read input");
    let (rgba, w, h) = match verilith_webp::decode_to(&data, verilith_webp::Mode::RGBA) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{}: {:?}", args[1], e);
            std::process::exit(1);
        }
    };
    let mut f = std::fs::File::create(&args[2]).expect("create output");
    write!(f, "P7\nWIDTH {}\nHEIGHT {}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n", w, h).unwrap();
    f.write_all(&rgba).unwrap();
}
