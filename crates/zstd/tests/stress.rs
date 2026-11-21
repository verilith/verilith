//! The fuzz target's checks on random and mutated inputs, without
//! libFuzzer. `VZSTD_STRESS=n cargo test --release --test stress -- --ignored`
//! runs `n` rounds (default 2000).
#[path = "libzstd.rs"]
#[allow(dead_code)]
mod lz;
use lz::{sample, Rng, Zstd};

#[test]
#[ignore]
fn stress() {
    let rounds: u64 = std::env::var("VZSTD_STRESS").ok().and_then(|s| s.parse().ok()).unwrap_or(2000);
    let z = Zstd::load();
    let mut r = Rng(0x5eed_1234_abcd);
    for round in 0..rounds {
        let mut data: Vec<u8> = (0..3).map(|_| r.next() as u8).collect();
        match (r.below(4), &z) {
            (0, _) | (_, None) => data.extend((0..r.below(2000)).map(|_| r.next() as u8)),
            (_, Some(z)) => {
                let n = r.below(if round % 20 == 0 { 400_000 } else { 5000 }) as usize;
                let src = sample(&mut r, n);
                let mut c = z.compress(&src, [1, 3, 19][r.below(3) as usize], r.below(2) == 0, if r.below(2) == 0 { 10 + r.below(8) as i32 } else { 0 }, r.below(2) == 0, 0);
                for _ in 0..r.below(4) {
                    if c.is_empty() {
                        break;
                    }
                    let i = r.below(c.len() as u64) as usize;
                    match r.below(3) {
                        0 => c[i] ^= 1 << r.below(8),
                        1 => c[i] = r.next() as u8,
                        _ => c.truncate(i),
                    }
                }
                data.extend_from_slice(&c);
            },
        }
        verilith_zstd::capi::exercise(&data);
    }
}
