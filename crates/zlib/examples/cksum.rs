use std::time::Instant;
fn main() {
    let d: Vec<u8> = (0..8_000_000u32).map(|i| (i.wrapping_mul(2654435761) >> 13) as u8).collect();
    for _ in 0..3 {
        let t = Instant::now();
        let mut x = 0u32;
        for _ in 0..10 { x ^= verilith_zlib::checksum::crc32(&d); }
        println!("crc32 {:.0} MB/s {x}", 80e6 / t.elapsed().as_secs_f64() / 1e6);
        let t = Instant::now();
        for _ in 0..10 { x ^= verilith_zlib::checksum::adler32(&d); }
        println!("adler32 {:.0} MB/s {x}", 80e6 / t.elapsed().as_secs_f64() / 1e6);
    }
}
