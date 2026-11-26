//! The trusted carry-less-multiply contracts (`vclmul`) against
//! the verified reference (`fold::clmul_ref`), and the CRC-32 kernels
//! against the table code, on random inputs. The 512-bit checks need a
//! CPU with AVX-512F and VPCLMULQDQ and are skipped, with a message, on
//! one without.
#![cfg(target_arch = "x86_64")]
#![allow(unsafe_op_in_unsafe_fn)]
use verilith_checksum::fold::*;
use verilith_simd::clmul::*;
use verilith_checksum::{cpu, crc32_update};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    /// Sparse and dense bit patterns, and the edges.
    fn word(&mut self) -> u64 {
        match self.next() % 6 {
            0 => 0,
            1 => !0,
            2 => 1 << (self.next() % 64),
            3 => self.next() & self.next(),
            _ => self.next(),
        }
    }
    fn block(&mut self) -> u128 {
        ((self.word() as u128) << 64) | self.word() as u128
    }
}

fn iters() -> usize {
    std::env::var("VCLMUL_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000)
}

fn fold_ref(a: u128, k: u128) -> u128 {
    clmul_ref(a as u64, k as u64) ^ clmul_ref((a >> 64) as u64, (k >> 64) as u64)
}

/// A slow, independent carry-less product, to check the reference itself.
fn clmul_naive(a: u64, b: u64) -> u128 {
    let mut r = 0u128;
    for i in 0..64 {
        for j in 0..64 {
            if (a >> i) & 1 == 1 && (b >> j) & 1 == 1 {
                r ^= 1u128 << (i + j);
            }
        }
    }
    r
}

#[test]
fn reference_is_the_carry_less_product() {
    let mut r = Rng(0x2545F4914F6CDD1D);
    for _ in 0..2000 {
        let (a, b) = (r.word(), r.word());
        assert_eq!(clmul_ref(a, b), clmul_naive(a, b), "{a:#x} {b:#x}");
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn check_x128(n: usize) {
    let mut r = Rng(0x9E3779B97F4A7C15);
    let mut buf = [0u8; 48];
    for _ in 0..n {
        let (a, b, k) = (r.block(), r.block(), r.block());
        assert_eq!(x_get(&x_set(a)), a);
        assert_eq!(x_get(&x_xor(&x_set(a), &x_set(b))), a ^ b);
        assert_eq!(x_get(&x_fold(&x_set(a), &x_set(k))), fold_ref(a, k), "{a:#x} {k:#x}");
        for b in buf.iter_mut() {
            *b = r.next() as u8;
        }
        let i = (r.next() % 33) as usize;
        let want = u128::from_le_bytes(buf[i..i + 16].try_into().unwrap());
        assert_eq!(x_get(&x_load(&buf, i)), want);
    }
}

#[test]
fn x128_contracts() {
    if !std::is_x86_feature_detected!("pclmulqdq") {
        eprintln!("skipped: no PCLMULQDQ");
        return;
    }
    unsafe { check_x128(iters()) }
}

#[target_feature(enable = "avx512f,vpclmulqdq,pclmulqdq")]
unsafe fn blocks(z: &Z512) -> [u128; 4] {
    [
        x_get(&z_block::<0>(z)),
        x_get(&z_block::<1>(z)),
        x_get(&z_block::<2>(z)),
        x_get(&z_block::<3>(z)),
    ]
}

#[target_feature(enable = "avx512f,vpclmulqdq,pclmulqdq")]
unsafe fn check_z512(n: usize) {
    let mut r = Rng(0xD1B54A32D192ED03);
    let mut buf = [0u8; 128];
    for _ in 0..n {
        for b in buf.iter_mut() {
            *b = r.next() as u8;
        }
        let i = (r.next() % 65) as usize;
        let lanes = |o: usize| -> [u128; 4] {
            core::array::from_fn(|j| u128::from_le_bytes(buf[o + 16 * j..o + 16 * j + 16].try_into().unwrap()))
        };
        let za = z_load(&buf, i);
        let a = lanes(i);
        assert_eq!(blocks(&za), a);
        let c = r.next() as u32;
        assert_eq!(blocks(&z_reg(c)), [c as u128, 0, 0, 0]);
        let v = r.block();
        let zk = z_splat(v);
        assert_eq!(blocks(&zk), [v; 4]);
        let j = (r.next() % 65) as usize;
        let zb = z_load(&buf, j);
        let b = lanes(j);
        let x = blocks(&z_xor(&za, &zb));
        let f = blocks(&z_fold(&za, &zb));
        let fk = blocks(&z_fold(&za, &zk));
        for l in 0..4 {
            assert_eq!(x[l], a[l] ^ b[l]);
            assert_eq!(f[l], fold_ref(a[l], b[l]));
            assert_eq!(fk[l], fold_ref(a[l], v));
        }
    }
}

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn yblocks(y: &Y256) -> [u128; 2] {
    [x_get(&y_block::<0>(y)), x_get(&y_block::<1>(y))]
}

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn check_y256(n: usize) {
    let mut r = Rng(0x8CB92BA72F3D8DD7);
    let mut buf = [0u8; 96];
    for _ in 0..n {
        for b in buf.iter_mut() {
            *b = r.next() as u8;
        }
        let lanes = |o: usize| -> [u128; 2] {
            core::array::from_fn(|j| u128::from_le_bytes(buf[o + 16 * j..o + 16 * j + 16].try_into().unwrap()))
        };
        let i = (r.next() % 65) as usize;
        let ya = y_load(&buf, i);
        let a = lanes(i);
        assert_eq!(yblocks(&ya), a);
        let c = r.next() as u32;
        assert_eq!(yblocks(&y_reg(c)), [c as u128, 0]);
        let v = r.block();
        let yk = y_splat(v);
        assert_eq!(yblocks(&yk), [v; 2]);
        let j = (r.next() % 65) as usize;
        let yb = y_load(&buf, j);
        let b = lanes(j);
        let x = yblocks(&y_xor(&ya, &yb));
        let f = yblocks(&y_fold(&ya, &yb));
        let fk = yblocks(&y_fold(&ya, &yk));
        for l in 0..2 {
            assert_eq!(x[l], a[l] ^ b[l]);
            assert_eq!(f[l], fold_ref(a[l], b[l]));
            assert_eq!(fk[l], fold_ref(a[l], v));
        }
    }
}

fn has_vpclmul256() -> bool {
    std::is_x86_feature_detected!("avx2")
        && std::is_x86_feature_detected!("vpclmulqdq")
        && std::is_x86_feature_detected!("pclmulqdq")
}

#[test]
fn y256_contracts() {
    if !has_vpclmul256() {
        eprintln!("skipped: no AVX2 and VPCLMULQDQ");
        return;
    }
    unsafe { check_y256(iters() / 2) }
}

fn has_vpclmul() -> bool {
    std::is_x86_feature_detected!("avx512f")
        && std::is_x86_feature_detected!("vpclmulqdq")
        && std::is_x86_feature_detected!("pclmulqdq")
}

#[test]
fn z512_contracts() {
    if !has_vpclmul() {
        eprintln!("skipped: no AVX-512F and VPCLMULQDQ");
        return;
    }
    unsafe { check_z512(iters() / 4) }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn pclmul_kernel(reg: u32, d: &[u8]) -> u32 {
    crc32_pclmul(reg, d)
}

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn vpclmul256_kernel(reg: u32, d: &[u8]) -> u32 {
    crc32_vpclmul256(reg, d)
}

#[target_feature(enable = "avx512f,vpclmulqdq,pclmulqdq")]
unsafe fn vpclmul_kernel(reg: u32, d: &[u8]) -> u32 {
    crc32_vpclmul(reg, d)
}

/// The kernels, every length to 1100 and random ones to 64 KiB, at every
/// alignment of the start, against the table code.
#[test]
fn kernels_agree() {
    let mut r = Rng(0xA0761D6478BD642F);
    let data: Vec<u8> = (0..70_000).map(|_| r.next() as u8).collect();
    let z = has_vpclmul();
    if !z {
        eprintln!("512-bit kernel skipped: no AVX-512F and VPCLMULQDQ");
    }
    let mut lens: Vec<usize> = (0..1100).collect();
    lens.extend((0..300).map(|_| (r.next() % 65_536) as usize));
    for &n in &lens {
        let o = (r.next() % 64) as usize;
        let d = &data[o..o + n];
        let reg = r.next() as u32;
        let want = crc32_update(reg, d);
        if n >= 64 && std::is_x86_feature_detected!("pclmulqdq") {
            assert_eq!(unsafe { pclmul_kernel(reg, d) }, want, "pclmul n={n}");
        }
        if n >= 128 && has_vpclmul256() {
            assert_eq!(unsafe { vpclmul256_kernel(reg, d) }, want, "vpclmul256 n={n}");
        }
        if n >= 256 && z {
            assert_eq!(unsafe { vpclmul_kernel(reg, d) }, want, "vpclmul n={n}");
        }
        assert_eq!(cpu::crc32_update(reg, d), want, "dispatch n={n}");
    }
}

/// The check value from the CRC catalogue, and gzip's register convention.
#[test]
fn check_value() {
    let d: Vec<u8> = b"123456789".iter().cycle().take(9 * 1000).copied().collect();
    assert_eq!(!cpu::crc32_update(!0, b"123456789"), 0xCBF4_3926);
    assert_eq!(cpu::crc32_update(!0, &d), crc32_update(!0, &d));
}
