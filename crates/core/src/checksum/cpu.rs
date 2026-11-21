//! CPU-specific checksum kernels (part of the trusted base).
//!
//! - `adler32_update` runs the verified `checksum::adler32_update`, compiled
//!   a second time with AVX2 enabled when the CPU has it. The code is the
//!   same; only instruction selection differs.
//! - `crc32_update` uses carry-less multiplication (PCLMULQDQ) when the CPU
//!   has it. This one is *not* verified: it folds 64 bytes at a time with
//!   constants for the CRC-32 polynomial, the method of Intel's "Fast CRC
//!   Computation for Generic Polynomials Using PCLMULQDQ". Its spec is the
//!   verified table-driven `checksum::crc32_update`, which it is tested
//!   against, and which it falls back to for short inputs and other CPUs.
//!   On AArch64 with the CRC extension (every Apple Silicon CPU) it runs
//!   `checksum::lanes::crc32_update`, which *is* verified, down to one
//!   assumption: that the `crc32x` instruction computes this CRC-32 over
//!   its eight bytes (`lanes::crc_word`).
//! - On AArch64, `adler32_update` is the portable code, which the compiler
//!   vectorizes with NEON (part of the AArch64 baseline).
#[cfg(verus_only)]
use crate::checksum::{adler_from, crc_from};
use vstd::prelude::*;

// Runtime CPU feature detection needs `std`; a `no_std` build uses only
// the features the target is compiled for.
#[cfg(all(feature = "std", target_arch = "x86_64"))]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(all(not(feature = "std"), target_arch = "x86_64"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }
#[cfg(all(feature = "std", target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { std::arch::is_aarch64_feature_detected!($f) }; }
#[cfg(all(not(feature = "std"), target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

#[verifier::external_body]
pub fn adler32_update(a: u32, b: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@),
{
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") {
            // SAFETY: the CPU supports AVX2.
            return unsafe { adler32_avx2(a, b, d) };
        }
    }
    super::adler32_update(a, b, d)
}

#[verifier::external_body]
pub fn crc32_update(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc_from(reg, d@),
{
    #[cfg(target_arch = "x86_64")]
    {
        if d.len() >= 128 && x86_has!("pclmulqdq") && x86_has!("sse4.1") {
            // SAFETY: the CPU supports PCLMULQDQ and SSE4.1.
            return unsafe { pclmul::crc32_update(reg, d) };
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if d.len() >= 16 && arm_has!("crc") {
            // SAFETY: the CPU has the CRC32 instructions.
            return unsafe { arm_crc::crc32_update(reg, d) };
        }
    }
    super::crc32_update(reg, d)
}

} // verus!

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn adler32_avx2(a: u32, b: u32, d: &[u8]) -> (u32, u32) {
    super::adler32_update(a, b, d)
}

#[cfg(target_arch = "x86_64")]
mod pclmul {
    use core::arch::x86_64::*;

    // x^(4*128+64) mod P, x^(4*128) mod P, x^(128+64), x^128, x^96 (bit
    // reflected, shifted left by one), P and floor(x^64 / P).
    const K1: i64 = 0x1_5444_2bd4;
    const K2: i64 = 0x1_c6e4_1596;
    const K3: i64 = 0x1_7519_97d0;
    const K4: i64 = 0x0_ccaa_009e;
    const K5: i64 = 0x1_63cd_6124;
    const P_X: i64 = 0x1_db71_0641;
    const U_PRIME: i64 = 0x1_f701_1641;

    #[inline(always)]
    unsafe fn fold(a: __m128i, b: __m128i, k: __m128i) -> __m128i {
        let t1 = _mm_clmulepi64_si128(a, k, 0x00);
        let t2 = _mm_clmulepi64_si128(a, k, 0x11);
        _mm_xor_si128(_mm_xor_si128(b, t1), t2)
    }

    #[inline(always)]
    unsafe fn load(d: &[u8], i: usize) -> __m128i {
        debug_assert!(i + 16 <= d.len());
        _mm_loadu_si128(d.as_ptr().add(i) as *const __m128i)
    }

    /// Requires `d.len() >= 64`.
    #[target_feature(enable = "pclmulqdq", enable = "sse4.1")]
    pub unsafe fn crc32_update(reg: u32, d: &[u8]) -> u32 {
        let n = d.len();
        let mut x3 = load(d, 0);
        let mut x2 = load(d, 16);
        let mut x1 = load(d, 32);
        let mut x0 = load(d, 48);
        x3 = _mm_xor_si128(x3, _mm_cvtsi32_si128(reg as i32));
        let mut i = 64;
        let k1k2 = _mm_set_epi64x(K2, K1);
        while n - i >= 64 {
            x3 = fold(x3, load(d, i), k1k2);
            x2 = fold(x2, load(d, i + 16), k1k2);
            x1 = fold(x1, load(d, i + 32), k1k2);
            x0 = fold(x0, load(d, i + 48), k1k2);
            i += 64;
        }
        let k3k4 = _mm_set_epi64x(K4, K3);
        let mut x = fold(x3, x2, k3k4);
        x = fold(x, x1, k3k4);
        x = fold(x, x0, k3k4);
        while n - i >= 16 {
            x = fold(x, load(d, i), k3k4);
            i += 16;
        }
        // 128 bits to 64.
        let x = _mm_xor_si128(_mm_clmulepi64_si128(x, k3k4, 0x10), _mm_srli_si128(x, 8));
        let lo = _mm_set_epi32(0, 0, 0, !0);
        let x = _mm_xor_si128(
            _mm_clmulepi64_si128(_mm_and_si128(x, lo), _mm_set_epi64x(0, K5), 0x00),
            _mm_srli_si128(x, 4),
        );
        // Barrett reduction to 32.
        let pu = _mm_set_epi64x(U_PRIME, P_X);
        let t1 = _mm_clmulepi64_si128(_mm_and_si128(x, lo), pu, 0x10);
        let t2 = _mm_clmulepi64_si128(_mm_and_si128(t1, lo), pu, 0x00);
        let c = _mm_extract_epi32(_mm_xor_si128(x, t2), 1) as u32;
        crate::checksum::crc32_update(c, &d[i..])
    }
}

#[cfg(target_arch = "aarch64")]
mod arm_crc {
    /// `lanes::crc32_update`, compiled with the CRC extension enabled so
    /// that `lanes::crc_word` becomes one `crc32x` instruction.
    #[target_feature(enable = "crc")]
    pub unsafe fn crc32_update(reg: u32, d: &[u8]) -> u32 {
        crate::checksum::lanes::crc32_update(reg, d)
    }
}
