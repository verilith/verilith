//! Decodes a GIF file and prints a summary of it, in the format
//! `difftest/refgif.c` prints for giflib, so the two can be compared:
//!   vgifcat FILE
use verilith_gif::decode::{decode, Error};

fn fnv(h: &mut u64, b: &[u8]) {
    for &x in b {
        *h ^= x as u64;
        *h = h.wrapping_mul(0x100000001b3);
    }
}

fn table(t: &Option<Vec<u8>>) -> String {
    match t {
        None => "-".into(),
        Some(v) => {
            let mut h = 0xcbf29ce484222325;
            fnv(&mut h, v);
            format!("{}:{:016x}", v.len() / 3, h)
        }
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: vgifcat FILE");
    let b = std::fs::read(&path).expect("read");
    match decode(&b, 1 << 32) {
        Err(Error::Invalid) => println!("invalid"),
        Err(e) => println!("error {:?}", e),
        Ok(g) => {
            println!("screen {} {} bg {} gct {}", g.width, g.height, g.bg, table(&g.gct));
            for f in &g.frames {
                let mut h = 0xcbf29ce484222325;
                fnv(&mut h, &f.pixels);
                let gce = match f.gce {
                    None => "-".to_string(),
                    Some(c) => format!(
                        "{} {} {} {}",
                        c.disposal,
                        c.user_input as u8,
                        c.delay,
                        c.transparent.map(|t| t as i32).unwrap_or(-1)
                    ),
                };
                println!(
                    "image {} {} {} {} il {} lct {} gce {} px {:016x}",
                    f.left,
                    f.top,
                    f.width,
                    f.height,
                    (f.flags >> 6) & 1,
                    table(&f.lct),
                    gce,
                    h
                );
            }
        }
    }
}
