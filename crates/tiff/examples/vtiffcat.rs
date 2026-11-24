//! Decodes a TIFF file and prints a summary of it, in the format
//! `difftest/reftiff.c` prints for libtiff, so the two can be compared:
//!   vtiffcat FILE [OUT]   (OUT: also write the decoded samples there)
use verilith_tiff::decode::decode;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let b = std::fs::read(&a[1]).expect("read");
    match decode(&b, 1 << 32) {
        Err(e) => println!("invalid {:?}", e),
        Ok(t) => {
            let mut h: u64 = 0xcbf29ce484222325;
            for &x in &t.pixels {
                h ^= x as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
            println!(
                "image {} {}x{} bps {} spp {} comp {} planar {} bytes {} px {:016x}",
                if t.le { "II" } else { "MM" },
                t.width,
                t.height,
                t.bits_per_sample,
                t.samples_per_pixel,
                t.compression,
                t.planar,
                t.pixels.len(),
                h
            );
            if let Some(out) = a.get(2) {
                std::fs::write(out, &t.pixels).expect("write");
            }
        }
    }
}
