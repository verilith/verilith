//! Decodes a JPEG to a PPM/PGM on stdout.
use std::io::Write;
fn main() {
    let path = std::env::args().nth(1).expect("usage: djpeg FILE");
    let data = std::fs::read(path).unwrap();
    match verilith_jpeg::decode(&data) {
        Ok(p) => {
            let mut o = std::io::stdout().lock();
            write!(o, "P{}\n{} {}\n255\n", if p.nc == 1 { 5 } else { 6 }, p.w, p.h).unwrap();
            o.write_all(&p.px).unwrap();
        }
        Err(e) => {
            eprintln!("error: {:?}", e);
            std::process::exit(1);
        }
    }
}
