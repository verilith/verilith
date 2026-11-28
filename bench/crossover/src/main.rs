//! Runs one call of a kernel on an input of a given length, so that
//! `trace.py` can record exactly the instructions that call executes.
//!
//!     crossover <kernel> <n>
//!
//! The call is made twice: the first one resolves lazy bindings (the
//! platform's `memcpy`) and warms nothing that matters to the model; the
//! second one, through `probe`, is the one traced.
use std::hint::black_box;

#[target_feature(enable = "avx512f,vpclmulqdq,pclmulqdq")]
unsafe fn crc_512(reg: u32, d: &[u8]) -> u32 {
    verilith_checksum::fold::crc32_vpclmul(reg, d)
}

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn crc_256(reg: u32, d: &[u8]) -> u32 {
    verilith_checksum::fold::crc32_vpclmul256(reg, d)
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn crc_128(reg: u32, d: &[u8]) -> u32 {
    verilith_checksum::fold::crc32_pclmul(reg, d)
}

/// `copy_lits`' 32-byte loop. Both copies sit behind a call of their own,
/// so that each trace holds one call's overhead; `trace.py` leaves out
/// `probe`.
#[inline(never)]
fn wild(out: &mut [u8], src: &[u8], n: usize) -> u32 {
    verilith_core::lz::copy_lits_wild(out, 0, src, 0, n);
    out[0] as u32
}

/// `copy_lits`' other branch: one call of the platform's copy.
#[inline(never)]
fn platform(out: &mut [u8], src: &[u8], n: usize) -> u32 {
    verilith_core::prims::copy_in(out, 0, src, 0, n);
    out[0] as u32
}

/// The kernel to trace, by name, on `n` bytes. Inputs have 64 bytes of
/// slack on both sides, which the wild copy needs.
#[inline(never)]
#[unsafe(no_mangle)]
pub fn probe(k: u32, src: &[u8], out: &mut [u8], n: usize) -> u32 {
    match k {
        // SAFETY: main checks the CPU features before choosing these.
        0 => unsafe { crc_512(0, &src[..n]) },
        1 => unsafe { crc_256(0, &src[..n]) },
        2 => unsafe { crc_128(0, &src[..n]) },
        3 => wild(out, src, n),
        _ => platform(out, src, n),
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let k = match a[1].as_str() {
        "crc512" => 0,
        "crc256" => 1,
        "crc128" => 2,
        "wild" => 3,
        "memcpy" => 4,
        s => panic!("unknown kernel {s}"),
    };
    if k <= 2 {
        assert!(is_x86_feature_detected!("avx512f") && is_x86_feature_detected!("vpclmulqdq"));
    }
    let n: usize = a[2].parse().unwrap();
    if a.len() > 3 && a[3] == "time" {
        return time(k, n);
    }
    let src: Vec<u8> = (0..n + 64).map(|i| (i * 131 + 7) as u8).collect();
    let mut out = vec![0u8; n + 64];
    let mut r = probe(k, black_box(&src), black_box(&mut out), n);
    r ^= probe(k, black_box(&src), black_box(&mut out), n);
    black_box(r);
}

/// Wall-clock check of the model (`crossover <kernel> <n> time`): the
/// median over 31 runs of the time per call, calls back to back.
fn time(k: u32, n: usize) {
    let src: Vec<u8> = (0..n + 64).map(|i| (i * 131 + 7) as u8).collect();
    let mut out = vec![0u8; n + 64];
    let reps = 200_000;
    let mut v = Vec::new();
    for _ in 0..31 {
        let t = std::time::Instant::now();
        let mut r = 0;
        for _ in 0..reps {
            r ^= probe(k, black_box(&src), black_box(&mut out), black_box(n));
        }
        black_box(r);
        v.push(t.elapsed().as_secs_f64() * 1e9 / reps as f64);
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.2}", v[15]);
}
