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
//! - otherwise with the verified portable kernel.
//!
//! The two instruction kernels are *not* verified. Their spec is the
//! verified portable kernel, which `tests/kernels.rs` runs them against
//! (every block count up to 40, from every state the earlier blocks
//! produce, and random messages through the streaming API).
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
    crate::compress::compress_blocks(st, p)
}

} // verus!

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
    "portable"
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
