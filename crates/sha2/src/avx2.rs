//! The SHA-512 message schedule with AVX2, two blocks at once (part of the
//! trusted base).
//!
//! [`schedule512x2`] computes K_t + W_t for t = 0..80 for two blocks, as
//! OpenSSL's `sha512_block_data_order_avx2` does: a 256-bit vector holds
//! W_t and W_{t+1} of the first block in its low half and of the second
//! block in its high half, and each step computes the next two words of
//! both blocks. The rounds that consume it are verified
//! (`compress512::compress_block_kw`); this function is not. Its contract
//! is its `ensures`, stated with `spec512::schedule` itself, and
//! `tests/kernels512.rs` checks it against the verified scalar kernel. The
//! caller must run it only where the CPU has AVX2 (`cpu.rs` checks).
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::spec512 as spec;

verus! {

#[cfg(verus_only)]
use crate::spec512::K;

/// K_t + W_t for the 128-byte blocks at `o0` and `o1` of `p`.
#[verifier::external_body]
#[inline(always)]
pub fn schedule512x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80])
    requires
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        crate::compress512::kw_schedule(final(w0)@, spec::words(p@.subrange(o0 as int, o0 + 128))),
        crate::compress512::kw_schedule(final(w1)@, spec::words(p@.subrange(o1 as int, o1 + 128))),
{
    assert!(o0 + 128 <= p.len() && o1 + 128 <= p.len());
    // SAFETY: both blocks are inside `p` (checked above); the caller has
    // checked that the CPU has AVX2.
    unsafe { imp::schedule512x2(p.as_ptr().add(o0), p.as_ptr().add(o1), w0, w1) }
}

} // verus!

mod imp {
    use crate::spec512::K;
    use core::arch::x86_64::*;

    /// K_{2s}, K_{2s+1}, K_{2s}, K_{2s+1} at 4s: K in pairs, once for each
    /// half of a vector.
    static KK: [u64; 160] = {
        let mut kk = [0u64; 160];
        let mut s = 0;
        while s < 40 {
            kk[4 * s] = K[2 * s];
            kk[4 * s + 1] = K[2 * s + 1];
            kk[4 * s + 2] = K[2 * s];
            kk[4 * s + 3] = K[2 * s + 1];
            s += 1;
        }
        kk
    };

    macro_rules! rotr {
        ($x:expr, $n:literal) => {
            _mm256_or_si256(_mm256_srli_epi64::<$n>($x), _mm256_slli_epi64::<{ 64 - $n }>($x))
        };
    }

    #[inline(always)]
    unsafe fn sigma0(x: __m256i) -> __m256i {
        _mm256_xor_si256(_mm256_xor_si256(rotr!(x, 1), rotr!(x, 8)), _mm256_srli_epi64::<7>(x))
    }

    #[inline(always)]
    unsafe fn sigma1(x: __m256i) -> __m256i {
        _mm256_xor_si256(_mm256_xor_si256(rotr!(x, 19), rotr!(x, 61)), _mm256_srli_epi64::<6>(x))
    }

    /// Stores K + W for words 2s and 2s + 1 of both blocks.
    #[inline(always)]
    unsafe fn store(x: __m256i, s: usize, w0: &mut [u64; 80], w1: &mut [u64; 80]) {
        let kw = _mm256_add_epi64(x, _mm256_loadu_si256(KK.as_ptr().add(4 * s) as *const __m256i));
        _mm_storeu_si128(w0.as_mut_ptr().add(2 * s) as *mut __m128i, _mm256_castsi256_si128(kw));
        _mm_storeu_si128(w1.as_mut_ptr().add(2 * s) as *mut __m128i, _mm256_extracti128_si256::<1>(kw));
    }

    /// `b0` and `b1` each point at 128 readable bytes; the CPU has AVX2.
    ///
    /// Not inlined, on purpose: inlined, LLVM forwards the stores to the
    /// rounds as lane extractions, which take the ALU ports the rounds
    /// need; through memory they cost store and load ports instead, and the
    /// rounds fold the loads into their additions.
    #[target_feature(enable = "avx2")]
    #[inline(never)]
    #[allow(unused_assignments)] // the last step's window entry is not read
    pub unsafe fn schedule512x2(b0: *const u8, b1: *const u8, w0: &mut [u64; 80], w1: &mut [u64; 80]) {
        // Big-endian 64-bit words from little-endian lanes.
        let bswap = _mm256_setr_epi8(
            7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, //
            7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
        );
        // x[s % 8] holds W_{2s} and W_{2s+1} of both blocks.
        let mut x = [_mm256_setzero_si256(); 8];
        for (s, v) in x.iter_mut().enumerate() {
            let lo = _mm_loadu_si128(b0.add(16 * s) as *const __m128i);
            let hi = _mm_loadu_si128(b1.add(16 * s) as *const __m128i);
            *v = _mm256_shuffle_epi8(_mm256_set_m128i(hi, lo), bswap);
            store(*v, s, w0, w1);
        }
        // W_t = σ1(W_{t-2}) + W_{t-7} + σ0(W_{t-15}) + W_{t-16}, for t = 2s
        // and 2s + 1: W_{t-15..t-13} and W_{t-7..t-5} straddle two vectors.
        macro_rules! step {
            ($s:literal) => {{
                const S: usize = $s;
                let w15 = _mm256_alignr_epi8::<8>(x[(S + 1) % 8], x[S % 8]);
                let w7 = _mm256_alignr_epi8::<8>(x[(S + 5) % 8], x[(S + 4) % 8]);
                let v = _mm256_add_epi64(
                    _mm256_add_epi64(sigma1(x[(S + 7) % 8]), w7),
                    _mm256_add_epi64(sigma0(w15), x[S % 8]),
                );
                x[S % 8] = v;
                store(v, S, w0, w1);
            }};
        }
        macro_rules! steps {
            ($($s:literal)*) => { $( step!($s); )* };
        }
        steps!(8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
               32 33 34 35 36 37 38 39);
    }
}
