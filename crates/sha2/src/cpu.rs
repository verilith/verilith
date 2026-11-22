//! CPU-specific SHA-256 kernels (part of the trusted base).
//!
//! [`compress_blocks`] states the same contract as the verified
//! [`crate::compress::compress_blocks`] and meets it in one of three ways:
//!
//! - on x86-64 with the SHA extensions (SHA-NI: Intel since Goldmont and
//!   Ice Lake, AMD since Zen), with `sha256rnds2`, `sha256msg1` and
//!   `sha256msg2`, the method of Intel's "New Instructions Supporting the
//!   Secure Hash Algorithm on Intel Architecture Processors" (2013);
//! - on AArch64 with the SHA2 extension (every Apple Silicon CPU, and most
//!   ARMv8 server and phone cores), with `sha256h`, `sha256h2`,
//!   `sha256su0` and `sha256su1`;
//! - otherwise with the verified portable kernel, compiled with BMI2 where
//!   the CPU has it (as verilith-core does for Adler-32 with AVX2: the same
//!   verified code, other instruction selection).
//!
//! [`compress512_blocks`] does the same for the SHA-512 family: with the
//! ARMv8.2 SHA-512 instructions (`sha512h`, `sha512h2`, `sha512su0`,
//! `sha512su1`; Apple M1 and later, Neoverse V1 and later) where the CPU
//! has them. On x86-64 with AVX2 the message schedule is computed for two
//! blocks at once with AVX2 (`crate::avx2`, trusted) and the rounds are
//! the verified ones; elsewhere the verified portable kernel runs (with
//! BMI2 where there is BMI2). x86-64
//! has SHA-512 instructions only on its newest CPUs (Arrow Lake, Lunar
//! Lake), and no kernel for them is written yet.
//!
//! The two instruction kernels are *not* verified. Their spec is the
//! verified portable kernel, which `tests/kernels.rs` runs them against
//! (every block count up to 40, from random states, and random messages
//! through the streaming API).
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::spec;

// Run-time CPU feature detection needs `std`, as in verilith-core.
#[cfg(target_arch = "x86_64")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(target_arch = "aarch64")]
macro_rules! arm_has { ($f:tt) => { std::arch::is_aarch64_feature_detected!($f) }; }

verus! {

/// H(n) from H(0) = `st` over the `n = p.len() / 64` whole blocks of `p`,
/// with the fastest kernel this CPU has.
#[verifier::external_body]
#[inline]
pub fn compress_blocks(st: &mut [u32; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("sha") && x86_has!("sse4.1") {
            // SAFETY: the CPU has SHA-NI and SSE4.1 (and so SSSE3).
            unsafe { shani::compress_blocks(st, p) };
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if arm_has!("sha2") {
            // SAFETY: the CPU has the SHA2 extension.
            unsafe { armv8::compress_blocks(st, p) };
            return;
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("bmi2") {
            // SAFETY: the CPU has BMI2.
            unsafe { bmi2::compress_blocks(st, p) };
            return;
        }
    }
    crate::compress::compress_blocks(st, p)
}

/// SHA-512's H(n) from H(0) = `st` over the `n = p.len() / 128` whole
/// blocks of `p`, with the fastest kernel this CPU has.
#[verifier::external_body]
#[inline]
pub fn compress512_blocks(st: &mut [u64; 8], p: &[u8])
    ensures
        final(st)@ == crate::spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    #[cfg(target_arch = "aarch64")]
    {
        if arm_has!("sha3") {
            // SAFETY: the CPU has the SHA-512 instructions (FEAT_SHA512,
            // which Rust names with the SHA-3 ones).
            unsafe { armv8_512::compress_blocks(st, p) };
            return;
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") && x86_has!("bmi2") {
            // SAFETY: the CPU has AVX2 and BMI2.
            unsafe { bmi2::compress512_blocks_avx2(st, p) };
            return;
        }
        if x86_has!("bmi2") {
            // SAFETY: the CPU has BMI2.
            unsafe { bmi2::compress512_blocks(st, p) };
            return;
        }
    }
    crate::compress512::compress_blocks(st, p)
}

} // verus!

/// Which kernel [`compress512_blocks`] runs on this CPU: `"armv8-sha512"`
/// or `"portable"`.
pub fn kernel512() -> &'static str {
    #[cfg(target_arch = "aarch64")]
    {
        if arm_has!("sha3") {
            return "armv8-sha512";
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") && x86_has!("bmi2") {
            return "avx2 schedule";
        }
        if x86_has!("bmi2") {
            return "portable (bmi2)";
        }
    }
    "portable"
}

/// Which kernel [`compress_blocks`] runs on this CPU: `"sha-ni"`,
/// `"armv8-sha2"` or `"portable"`.
pub fn kernel() -> &'static str {
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("sha") && x86_has!("sse4.1") {
            return "sha-ni";
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if arm_has!("sha2") {
            return "armv8-sha2";
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("bmi2") {
            return "portable (bmi2)";
        }
    }
    "portable"
}

/// The verified portable kernels, compiled a second time with BMI2, whose
/// three-operand rotate (`rorx`) saves the moves around each rotation.
/// The code is the same; only instruction selection differs.
#[cfg(target_arch = "x86_64")]
pub(crate) mod bmi2 {
    #[target_feature(enable = "bmi2")]
    pub unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        crate::compress::compress_blocks(st, p)
    }

    #[target_feature(enable = "bmi2")]
    pub unsafe fn compress512_blocks(st: &mut [u64; 8], p: &[u8]) {
        crate::compress512::compress_blocks(st, p)
    }

    /// The verified rounds over the AVX2 schedule (`crate::avx2`), which
    /// needs AVX2 enabled for its intrinsics to be inlined.
    #[target_feature(enable = "avx2,bmi2")]
    pub unsafe fn compress512_blocks_avx2(st: &mut [u64; 8], p: &[u8]) {
        crate::compress512::compress_blocks_x2(st, p)
    }
}

#[cfg(target_arch = "x86_64")]
pub(crate) mod shani {
    use crate::spec::K;
    use core::arch::x86_64::*;

    /// W_{t..t+3} from the four vectors before them.
    #[inline(always)]
    unsafe fn schedule(w0: __m128i, w1: __m128i, w2: __m128i, w3: __m128i) -> __m128i {
        let t = _mm_add_epi32(_mm_sha256msg1_epu32(w0, w1), _mm_alignr_epi8(w3, w2, 4));
        _mm_sha256msg2_epu32(t, w3)
    }

    /// Rounds 4i..4i+3 with W_{4i..4i+3} in `w`.
    #[inline(always)]
    unsafe fn rounds4(abef: &mut __m128i, cdgh: &mut __m128i, w: __m128i, i: usize) {
        let k = _mm_loadu_si128(K.as_ptr().add(4 * i) as *const __m128i);
        let t = _mm_add_epi32(w, k);
        *cdgh = _mm_sha256rnds2_epu32(*cdgh, *abef, t);
        *abef = _mm_sha256rnds2_epu32(*abef, *cdgh, _mm_shuffle_epi32(t, 0x0e));
    }

    /// The whole blocks of `p`.
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    pub unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        // Big-endian words from little-endian lanes.
        let bswap = _mm_set_epi64x(0x0c0d_0e0f_0809_0a0b, 0x0405_0607_0001_0203);
        let sp = st.as_mut_ptr() as *mut __m128i;
        // sha256rnds2 keeps the state as (a, b, e, f) and (c, d, g, h),
        // most significant lane first.
        let dcba = _mm_loadu_si128(sp);
        let hgfe = _mm_loadu_si128(sp.add(1));
        let cdab = _mm_shuffle_epi32(dcba, 0xb1);
        let efgh = _mm_shuffle_epi32(hgfe, 0x1b);
        let mut abef = _mm_alignr_epi8(cdab, efgh, 8);
        let mut cdgh = _mm_blend_epi16(efgh, cdab, 0xf0);

        for blk in p.chunks_exact(64) {
            let (abef0, cdgh0) = (abef, cdgh);
            let bp = blk.as_ptr() as *const __m128i;
            let mut w0 = _mm_shuffle_epi8(_mm_loadu_si128(bp), bswap);
            let mut w1 = _mm_shuffle_epi8(_mm_loadu_si128(bp.add(1)), bswap);
            let mut w2 = _mm_shuffle_epi8(_mm_loadu_si128(bp.add(2)), bswap);
            let mut w3 = _mm_shuffle_epi8(_mm_loadu_si128(bp.add(3)), bswap);
            rounds4(&mut abef, &mut cdgh, w0, 0);
            rounds4(&mut abef, &mut cdgh, w1, 1);
            rounds4(&mut abef, &mut cdgh, w2, 2);
            rounds4(&mut abef, &mut cdgh, w3, 3);
            let mut i = 4;
            while i < 16 {
                let w4 = schedule(w0, w1, w2, w3);
                rounds4(&mut abef, &mut cdgh, w4, i);
                (w0, w1, w2, w3) = (w1, w2, w3, w4);
                i += 1;
            }
            abef = _mm_add_epi32(abef, abef0);
            cdgh = _mm_add_epi32(cdgh, cdgh0);
        }

        let feba = _mm_shuffle_epi32(abef, 0x1b);
        let dchg = _mm_shuffle_epi32(cdgh, 0xb1);
        _mm_storeu_si128(sp, _mm_blend_epi16(feba, dchg, 0xf0));
        _mm_storeu_si128(sp.add(1), _mm_alignr_epi8(dchg, feba, 8));
    }
}

#[cfg(target_arch = "aarch64")]
pub(crate) mod armv8 {
    use crate::spec::K;
    use core::arch::aarch64::*;

    /// Rounds 4i..4i+3 with W_{4i..4i+3} in `w`.
    #[inline(always)]
    unsafe fn rounds4(abcd: &mut uint32x4_t, efgh: &mut uint32x4_t, w: uint32x4_t, i: usize) {
        let t = vaddq_u32(w, vld1q_u32(K.as_ptr().add(4 * i)));
        let abcd0 = *abcd;
        *abcd = vsha256hq_u32(abcd0, *efgh, t);
        *efgh = vsha256h2q_u32(*efgh, abcd0, t);
    }

    /// The whole blocks of `p`.
    #[target_feature(enable = "sha2")]
    pub unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        let mut abcd = vld1q_u32(st.as_ptr());
        let mut efgh = vld1q_u32(st.as_ptr().add(4));
        for blk in p.chunks_exact(64) {
            let (abcd0, efgh0) = (abcd, efgh);
            let bp = blk.as_ptr();
            let mut w0 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp)));
            let mut w1 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(16))));
            let mut w2 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(32))));
            let mut w3 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(48))));
            rounds4(&mut abcd, &mut efgh, w0, 0);
            rounds4(&mut abcd, &mut efgh, w1, 1);
            rounds4(&mut abcd, &mut efgh, w2, 2);
            rounds4(&mut abcd, &mut efgh, w3, 3);
            let mut i = 4;
            while i < 16 {
                let w4 = vsha256su1q_u32(vsha256su0q_u32(w0, w1), w2, w3);
                rounds4(&mut abcd, &mut efgh, w4, i);
                (w0, w1, w2, w3) = (w1, w2, w3, w4);
                i += 1;
            }
            abcd = vaddq_u32(abcd, abcd0);
            efgh = vaddq_u32(efgh, efgh0);
        }
        vst1q_u32(st.as_mut_ptr(), abcd);
        vst1q_u32(st.as_mut_ptr().add(4), efgh);
    }
}

#[cfg(target_arch = "aarch64")]
pub(crate) mod armv8_512 {
    use crate::spec512::K;
    use core::arch::aarch64::*;

    /// The whole blocks of `p`. Each step is two rounds; the four state
    /// vectors (a, b), (c, d), (e, f), (g, h) trade roles from step to
    /// step, so the steps are unrolled with constant indices.
    #[target_feature(enable = "sha3")]
    pub unsafe fn compress_blocks(st: &mut [u64; 8], p: &[u8]) {
        let sp = st.as_mut_ptr();
        let mut v = [vld1q_u64(sp), vld1q_u64(sp.add(2)), vld1q_u64(sp.add(4)), vld1q_u64(sp.add(6))];
        for blk in p.chunks_exact(128) {
            let v0 = v;
            let bp = blk.as_ptr();
            let mut s = [vdupq_n_u64(0); 8];
            for (j, w) in s.iter_mut().enumerate() {
                *w = vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(bp.add(16 * j))));
            }
            // Step i: rounds 2i and 2i + 1, with W in s[i % 8].
            macro_rules! step {
                ($i:literal) => {{
                    const I: usize = $i;
                    if I >= 8 {
                        s[I % 8] = vsha512su1q_u64(
                            vsha512su0q_u64(s[I % 8], s[(I + 1) % 8]),
                            s[(I + 7) % 8],
                            vextq_u64(s[(I + 4) % 8], s[(I + 5) % 8], 1),
                        );
                    }
                    // The vectors playing (a, b), (c, d), (e, f), (g, h).
                    const AB: usize = (4 - I % 4) % 4;
                    const CD: usize = (5 - I % 4) % 4;
                    const EF: usize = (6 - I % 4) % 4;
                    const GH: usize = (7 - I % 4) % 4;
                    let kw = vaddq_u64(s[I % 8], vld1q_u64(K.as_ptr().add(2 * I)));
                    let sum = vaddq_u64(vextq_u64(kw, kw, 1), v[GH]);
                    let t = vsha512hq_u64(sum, vextq_u64(v[EF], v[GH], 1), vextq_u64(v[CD], v[EF], 1));
                    v[GH] = vsha512h2q_u64(t, v[CD], v[AB]);
                    v[CD] = vaddq_u64(v[CD], t);
                }};
            }
            macro_rules! steps {
                ($($i:literal)*) => { $( step!($i); )* };
            }
            steps!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
                   20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39);
            for j in 0..4 {
                v[j] = vaddq_u64(v[j], v0[j]);
            }
        }
        vst1q_u64(sp, v[0]);
        vst1q_u64(sp.add(2), v[1]);
        vst1q_u64(sp.add(4), v[2]);
        vst1q_u64(sp.add(6), v[3]);
    }
}

/// For the tests: the verified portable kernels as compiled with BMI2, if
/// the CPU has it (on a CPU with SHA-NI, `compress_blocks` never runs it).
#[doc(hidden)]
pub type Kernel256 = fn(&mut [u32; 8], &[u8]);
#[doc(hidden)]
pub type Kernel512 = fn(&mut [u64; 8], &[u8]);

#[doc(hidden)]
pub fn bmi2_kernels() -> Option<(Kernel256, Kernel512)> {
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("bmi2") {
            // SAFETY: only returned when the CPU has BMI2.
            return Some((
                |st, p| unsafe { bmi2::compress_blocks(st, p) },
                |st, p| unsafe { bmi2::compress512_blocks(st, p) },
            ));
        }
    }
    None
}
