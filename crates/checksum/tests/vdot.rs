//! The trusted dot-product contracts (`vdot`) against a plain
//! reference, and the Adler-32 kernels against the portable code, on
//! random inputs. The AVX-512 checks need AVX-512 VNNI and are skipped,
//! with a message, on a CPU without it.
#![cfg(target_arch = "x86_64")]
#![allow(unsafe_op_in_unsafe_fn)]
use verilith_checksum::adlerv::*;
use verilith_simd::vdot::*;
use verilith_checksum::{adler32_update, cpu};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn byte(&mut self) -> u8 {
        match self.next() % 4 {
            0 => 0,
            1 => 255,
            _ => self.next() as u8,
        }
    }
}

fn iters() -> usize {
    std::env::var("VDOT_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(100_000)
}

fn dot_ref(acc: &[u32], x: &[u8], w: &[u8]) -> Vec<u32> {
    acc.iter()
        .enumerate()
        .map(|(j, &a)| a.wrapping_add((0..4).map(|k| x[4 * j + k] as u32 * w[4 * j + k] as u32).sum::<u32>()))
        .collect()
}

#[target_feature(enable = "avx512f,avx512bw,avx512vnni")]
unsafe fn check_z(n: usize) {
    let mut r = Rng(0x2545F4914F6CDD1D);
    let mut buf = [0u8; 256];
    for _ in 0..n {
        for b in buf.iter_mut() {
            *b = r.byte();
        }
        // Weights below 128 (`vpdpbusd` reads them as signed).
        let mut wv = [0u8; 64];
        for b in wv.iter_mut() {
            *b = (r.next() % 128) as u8;
        }
        let i = (r.next() % 129) as usize;
        let x = zb_load(&buf, i);
        let w = zb_load(&wv, 0);
        // An accumulator with known lanes: zero plus a dot by ones of random bytes.
        let mut a = zd_zero();
        assert_eq!(zd_store(&a), [0u32; 16]);
        let seed: Vec<u8> = (0..64).map(|_| r.byte()).collect();
        a = zd_dot(&a, &zb_load(&seed, 0), &zb_load(&ONES64, 0));
        let a0 = dot_ref(&[0; 16], &seed, &ONES64);
        assert_eq!(zd_store(&a).to_vec(), a0);
        let got = zd_store(&zd_dot(&a, &x, &w)).to_vec();
        assert_eq!(got, dot_ref(&a0, &buf[i..i + 64], &wv));
        let s = zd_store(&zd_add(&a, &a)).to_vec();
        assert_eq!(s, a0.iter().map(|v| v.wrapping_add(*v)).collect::<Vec<_>>());
    }
}

#[target_feature(enable = "avx2")]
unsafe fn check_y(n: usize) {
    let mut r = Rng(0x9E3779B97F4A7C15);
    let mut buf = [0u8; 128];
    for _ in 0..n {
        for b in buf.iter_mut() {
            *b = r.byte();
        }
        let mut wv = [0u8; 32];
        for b in wv.iter_mut() {
            *b = (r.next() % 65) as u8;
        }
        let i = (r.next() % 97) as usize;
        let seed: Vec<u8> = (0..32).map(|_| r.byte()).collect();
        let mut a = yd_zero();
        assert_eq!(yd_store(&a), [0u32; 8]);
        a = yd_dot(&a, &yb_load(&seed, 0), &yb_load(&ONES32, 0));
        let a0 = dot_ref(&[0; 8], &seed, &ONES32);
        assert_eq!(yd_store(&a).to_vec(), a0);
        let got = yd_store(&yd_dot(&a, &yb_load(&buf, i), &yb_load(&wv, 0))).to_vec();
        assert_eq!(got, dot_ref(&a0, &buf[i..i + 32], &wv));
        let s = yd_store(&yd_add(&a, &a)).to_vec();
        assert_eq!(s, a0.iter().map(|v| v.wrapping_add(*v)).collect::<Vec<_>>());
    }
}

fn has_vnni() -> bool {
    std::is_x86_feature_detected!("avx512f")
        && std::is_x86_feature_detected!("avx512bw")
        && std::is_x86_feature_detected!("avx512vnni")
}

#[test]
fn z_contracts() {
    if !has_vnni() {
        eprintln!("skipped: no AVX-512 VNNI");
        return;
    }
    unsafe { check_z(iters()) }
}

#[test]
fn y_contracts() {
    if !std::is_x86_feature_detected!("avx2") {
        eprintln!("skipped: no AVX2");
        return;
    }
    unsafe { check_y(iters()) }
}

/// The maddubs path at its saturation edge: all bytes 255, weights 64.
#[test]
fn y_no_saturation() {
    if !std::is_x86_feature_detected!("avx2") {
        return;
    }
    #[target_feature(enable = "avx2")]
    unsafe fn go() {
        let x = [255u8; 32];
        let w = [64u8; 32];
        let got = yd_store(&yd_dot(&yd_zero(), &yb_load(&x, 0), &yb_load(&w, 0)));
        assert_eq!(got, [4 * 255 * 64; 8]);
    }
    unsafe { go() }
}

#[target_feature(enable = "avx512f,avx512bw,avx512vnni")]
unsafe fn vnni(a: u32, b: u32, d: &[u8]) -> (u32, u32) {
    adler32_vnni(a, b, d)
}

#[target_feature(enable = "avx2")]
unsafe fn avx2k(a: u32, b: u32, d: &[u8]) -> (u32, u32) {
    adler32_avx2(a, b, d)
}

/// Every length to 1100, random lengths to 200 KiB (several blocks), all
/// 0xFF (the overflow edge), at random alignments and starting sums.
#[test]
fn kernels_agree() {
    let mut r = Rng(0xA0761D6478BD642F);
    let rand: Vec<u8> = (0..210_000).map(|_| r.next() as u8).collect();
    let ff = vec![0xffu8; 210_000];
    let z = has_vnni();
    if !z {
        eprintln!("VNNI kernel skipped: no AVX-512 VNNI");
    }
    let mut lens: Vec<usize> = (0..1100).collect();
    lens.extend((0..200).map(|_| (r.next() % 200_000) as usize));
    lens.extend([65536, 65536 + 63, 131072, 32768, 32768 + 31]);
    for &n in &lens {
        for data in [&rand, &ff] {
            let o = (r.next() % 64) as usize;
            let d = &data[o..o + n];
            let (a, b) = ((r.next() % 65521) as u32, (r.next() % 65521) as u32);
            let want = adler32_update(a, b, d);
            if z {
                assert_eq!(unsafe { vnni(a, b, d) }, want, "vnni n={n}");
            }
            if std::is_x86_feature_detected!("avx2") {
                assert_eq!(unsafe { avx2k(a, b, d) }, want, "avx2 n={n}");
            }
            assert_eq!(cpu::adler32_update(a, b, d), want, "dispatch n={n}");
        }
    }
}
