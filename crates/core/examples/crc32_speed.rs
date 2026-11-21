//! Times `checksum::crc32` (the kernel `cpu` picks) against the portable
//! table kernel: `cargo run --release --example crc32_speed`.
use std::time::Instant;
use verilith_core::checksum::{crc32, crc32_update};

fn best(mut f: impl FnMut() -> u32, bytes: usize) -> (f64, u32) {
    let mut best = f64::MAX;
    let mut r = 0;
    for _ in 0..15 {
        let t = Instant::now();
        let reps = (64usize << 20) / bytes.max(1) + 1;
        for _ in 0..reps {
            r = std::hint::black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / reps as f64);
    }
    (bytes as f64 / best / 1e9, r)
}

fn main() {
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let data: Vec<u8> = (0..16usize << 20)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 32) as u8
        })
        .collect();
    println!("{:>10}  {:>12}  {:>12}", "bytes", "crc32 GB/s", "table GB/s");
    for n in [64usize, 96, 192, 384, 512, 1024, 1536, 2048, 4096, 8192, 12288, 65536, 1 << 20, 16 << 20] {
        let d = &data[..n];
        let (fast, a) = best(|| crc32(std::hint::black_box(d)), n);
        let (table, b) = best(|| !crc32_update(0xffff_ffff, std::hint::black_box(d)), n);
        assert_eq!(a, b);
        println!("{n:>10}  {fast:>12.2}  {table:>12.2}");
    }
}
