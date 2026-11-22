//! The SHA-512 message schedule with AVX2, two blocks at once (part of the
//! trusted base).
//!
//! Two forms. [`schedule512x2`] computes a pair's whole schedule. The
//! pipelined form, [`sched_start`] and [`sched_steps2`], computes it a few
//! words at a time, so that the verified rounds of one pair can run with
//! the next pair's schedule interleaved: the vector work then fills the
//! ports the rounds' dependency chains leave idle, as in OpenSSL. Its
//! state, [`Sched512`], is opaque to the proofs; what they rely on is each
//! function's `ensures` about the words written.
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

/// A pair's schedule part way: the last 16 words of each block, in
/// vectors. Opaque to the proofs.
#[verifier::external_body]
pub struct Sched512 {
    x: [core::arch::x86_64::__m256i; 8],
}

/// `st` holds the schedule of block words `m0` and `m1` up to step `s`
/// (words `2s - 16` to `2s`).
pub uninterp spec fn sched_at(st: Sched512, m0: Seq<u64>, m1: Seq<u64>, s: int) -> bool;

/// Starts the schedule of the blocks at `o0` and `o1`: their first 16 words.
#[verifier::external_body]
#[inline(always)]
pub fn sched_start(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80]) -> (r: Sched512)
    requires
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        sched_at(
            r,
            spec::words(p@.subrange(o0 as int, o0 + 128)),
            spec::words(p@.subrange(o1 as int, o1 + 128)),
            8,
        ),
        crate::compress512::kw_upto(final(w0)@, spec::words(p@.subrange(o0 as int, o0 + 128)), 16),
        crate::compress512::kw_upto(final(w1)@, spec::words(p@.subrange(o1 as int, o1 + 128)), 16),
{
    assert!(o0 + 128 <= p.len() && o1 + 128 <= p.len());
    // SAFETY: both blocks are inside `p`; the caller has checked AVX2.
    unsafe { Sched512 { x: imp::start(p.as_ptr().add(o0), p.as_ptr().add(o1), w0, w1) } }
}

/// Steps `s` and `s + 1`: words `2s` to `2s + 4` of both blocks.
#[verifier::external_body]
#[inline(always)]
pub fn sched_steps2(
    st: &mut Sched512,
    s: usize,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        8 <= s,
        s + 2 <= 40,
        sched_at(*old(st), m0, m1, s as int),
        crate::compress512::kw_upto(old(w0)@, m0, 2 * s),
        crate::compress512::kw_upto(old(w1)@, m1, 2 * s),
    ensures
        sched_at(*final(st), m0, m1, s + 2),
        crate::compress512::kw_upto(final(w0)@, m0, 2 * s + 4),
        crate::compress512::kw_upto(final(w1)@, m1, 2 * s + 4),
{
    assert!((8..=38).contains(&s));
    // SAFETY: the caller has checked AVX2.
    unsafe {
        imp::step(&mut st.x, s, w0, w1);
        imp::step(&mut st.x, s + 1, w0, w1);
    }
}

// ---------------------------------------------------------------------------
// SHA-256: the same, with four 32-bit words of each block per step
// ---------------------------------------------------------------------------

/// A SHA-256 pair's schedule part way: its last 16 words, in vectors.
#[verifier::external_body]
pub struct Sched256 {
    x: [core::arch::x86_64::__m256i; 4],
}

/// `st` holds the schedule of SHA-256 block words `m0` and `m1` up to step
/// `s` (words `4s - 16` to `4s`).
pub uninterp spec fn sched256_at(st: Sched256, m0: Seq<u32>, m1: Seq<u32>, s: int) -> bool;

/// The whole SHA-256 schedule of the 64-byte blocks at `o0` and `o1`.
#[verifier::external_body]
#[inline(always)]
pub fn schedule256x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64])
    requires
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        crate::compress::kw256_upto(final(w0)@, crate::spec::words(p@.subrange(o0 as int, o0 + 64)), 64),
        crate::compress::kw256_upto(final(w1)@, crate::spec::words(p@.subrange(o1 as int, o1 + 64)), 64),
{
    assert!(o0 + 64 <= p.len() && o1 + 64 <= p.len());
    // SAFETY: both blocks are inside `p`; the caller has checked AVX2.
    unsafe { imp::schedule256x2(p.as_ptr().add(o0), p.as_ptr().add(o1), w0, w1) }
}

/// Starts the SHA-256 schedule of the blocks at `o0` and `o1`.
#[verifier::external_body]
#[inline(always)]
pub fn sched256_start(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64]) -> (r: Sched256)
    requires
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        sched256_at(
            r,
            crate::spec::words(p@.subrange(o0 as int, o0 + 64)),
            crate::spec::words(p@.subrange(o1 as int, o1 + 64)),
            4,
        ),
        crate::compress::kw256_upto(final(w0)@, crate::spec::words(p@.subrange(o0 as int, o0 + 64)), 16),
        crate::compress::kw256_upto(final(w1)@, crate::spec::words(p@.subrange(o1 as int, o1 + 64)), 16),
{
    assert!(o0 + 64 <= p.len() && o1 + 64 <= p.len());
    // SAFETY: both blocks are inside `p`; the caller has checked AVX2.
    unsafe { Sched256 { x: imp::start256(p.as_ptr().add(o0), p.as_ptr().add(o1), w0, w1) } }
}

/// Step `s`: words `4s` to `4s + 4` of both blocks.
#[verifier::external_body]
#[inline(always)]
pub fn sched256_step(
    st: &mut Sched256,
    s: usize,
    w0: &mut [u32; 64],
    w1: &mut [u32; 64],
    Ghost(m0): Ghost<Seq<u32>>,
    Ghost(m1): Ghost<Seq<u32>>,
)
    requires
        4 <= s < 16,
        sched256_at(*old(st), m0, m1, s as int),
        crate::compress::kw256_upto(old(w0)@, m0, 4 * s),
        crate::compress::kw256_upto(old(w1)@, m1, 4 * s),
    ensures
        sched256_at(*final(st), m0, m1, s + 1),
        crate::compress::kw256_upto(final(w0)@, m0, 4 * s + 4),
        crate::compress::kw256_upto(final(w1)@, m1, 4 * s + 4),
{
    assert!((4..16).contains(&s));
    // SAFETY: the caller has checked AVX2.
    unsafe { imp::step256(&mut st.x, s, w0, w1) }
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

    #[inline(always)]
    unsafe fn bswap() -> __m256i {
        _mm256_setr_epi8(
            7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, //
            7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
        )
    }

    /// The first 16 words of both blocks, stored and returned as vectors.
    #[inline(always)]
    pub unsafe fn start(b0: *const u8, b1: *const u8, w0: &mut [u64; 80], w1: &mut [u64; 80]) -> [__m256i; 8] {
        let mut x = [_mm256_setzero_si256(); 8];
        for (s, v) in x.iter_mut().enumerate() {
            let lo = _mm_loadu_si128(b0.add(16 * s) as *const __m128i);
            let hi = _mm_loadu_si128(b1.add(16 * s) as *const __m128i);
            *v = _mm256_shuffle_epi8(_mm256_set_m128i(hi, lo), bswap());
            store(*v, s, w0, w1);
        }
        x
    }

    /// Step `s` (8 <= s < 40): W_{2s} and W_{2s+1} of both blocks, over
    /// the window `x`, in which `x[s % 8]` is W_{2s-16}, W_{2s-15}.
    #[target_feature(enable = "avx2")]
    #[inline]
    pub unsafe fn step(x: &mut [__m256i; 8], s: usize, w0: &mut [u64; 80], w1: &mut [u64; 80]) {
        let w15 = _mm256_alignr_epi8::<8>(x[(s + 1) % 8], x[s % 8]);
        let w7 = _mm256_alignr_epi8::<8>(x[(s + 5) % 8], x[(s + 4) % 8]);
        let mut v = _mm256_add_epi64(
            _mm256_add_epi64(sigma1(x[(s + 7) % 8]), w7),
            _mm256_add_epi64(sigma0(w15), x[s % 8]),
        );
        // An empty asm that the step's result passes through, and that is
        // ordered with memory: it keeps each step between the round groups
        // it was placed between. Without it LLVM hoists every step to the
        // top of the pair, and the interleaving is lost.
        core::arch::asm!("/* {0} */", inout(ymm_reg) v, options(nostack, preserves_flags));
        x[s % 8] = v;
        store(v, s, w0, w1);
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

    /// SHA-256's K_{4s..4s+4} at 8s, once for each half of a vector.
    static KK256: [u32; 128] = {
        let k = crate::spec::K;
        let mut kk = [0u32; 128];
        let mut s = 0;
        while s < 16 {
            let mut j = 0;
            while j < 4 {
                kk[8 * s + j] = k[4 * s + j];
                kk[8 * s + 4 + j] = k[4 * s + j];
                j += 1;
            }
            s += 1;
        }
        kk
    };

    macro_rules! rotr32 {
        ($x:expr, $n:literal) => {
            _mm256_or_si256(_mm256_srli_epi32::<$n>($x), _mm256_slli_epi32::<{ 32 - $n }>($x))
        };
    }

    #[inline(always)]
    unsafe fn sigma0_256(x: __m256i) -> __m256i {
        _mm256_xor_si256(_mm256_xor_si256(rotr32!(x, 7), rotr32!(x, 18)), _mm256_srli_epi32::<3>(x))
    }

    #[inline(always)]
    unsafe fn sigma1_256(x: __m256i) -> __m256i {
        _mm256_xor_si256(_mm256_xor_si256(rotr32!(x, 17), rotr32!(x, 19)), _mm256_srli_epi32::<10>(x))
    }

    /// Stores K + W for words 4s to 4s + 4 of both blocks.
    #[inline(always)]
    unsafe fn store256(x: __m256i, s: usize, w0: &mut [u32; 64], w1: &mut [u32; 64]) {
        let kw = _mm256_add_epi32(x, _mm256_loadu_si256(KK256.as_ptr().add(8 * s) as *const __m256i));
        _mm_storeu_si128(w0.as_mut_ptr().add(4 * s) as *mut __m128i, _mm256_castsi256_si128(kw));
        _mm_storeu_si128(w1.as_mut_ptr().add(4 * s) as *mut __m128i, _mm256_extracti128_si256::<1>(kw));
    }

    /// The first 16 words of both SHA-256 blocks.
    #[inline(always)]
    pub unsafe fn start256(b0: *const u8, b1: *const u8, w0: &mut [u32; 64], w1: &mut [u32; 64]) -> [__m256i; 4] {
        // Big-endian 32-bit words from little-endian lanes.
        let bswap = _mm256_setr_epi8(
            3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, //
            3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
        );
        let mut x = [_mm256_setzero_si256(); 4];
        for (s, v) in x.iter_mut().enumerate() {
            let lo = _mm_loadu_si128(b0.add(16 * s) as *const __m128i);
            let hi = _mm_loadu_si128(b1.add(16 * s) as *const __m128i);
            *v = _mm256_shuffle_epi8(_mm256_set_m128i(hi, lo), bswap);
            store256(*v, s, w0, w1);
        }
        x
    }

    /// Step `s` (4 <= s < 16): W_{4s..4s+4} of both blocks over the window
    /// `x`, in which `x[s % 4]` is W_{4s-16..4s-12}. W_{4s+2} and W_{4s+3}
    /// need σ1 of W_{4s} and W_{4s+1}, so the low two words come first.
    #[target_feature(enable = "avx2")]
    #[inline]
    pub unsafe fn step256(x: &mut [__m256i; 4], s: usize, w0: &mut [u32; 64], w1: &mut [u32; 64]) {
        let x0 = x[s % 4];
        let x2 = x[(s + 2) % 4];
        let x3 = x[(s + 3) % 4];
        let w15 = _mm256_alignr_epi8::<4>(x[(s + 1) % 4], x0);
        let w7 = _mm256_alignr_epi8::<4>(x3, x2);
        let t = _mm256_add_epi32(_mm256_add_epi32(x0, sigma0_256(w15)), w7);
        let lo = _mm256_setr_epi32(-1, -1, 0, 0, -1, -1, 0, 0);
        // σ1(W_{4s-2}), σ1(W_{4s-1}) into lanes 0 and 1.
        let s1 = sigma1_256(_mm256_shuffle_epi32::<0b11_10_11_10>(x3));
        let v = _mm256_add_epi32(t, _mm256_and_si256(s1, lo));
        // σ1(W_{4s}), σ1(W_{4s+1}) into lanes 2 and 3.
        let s1 = sigma1_256(_mm256_shuffle_epi32::<0b01_00_01_00>(v));
        let mut v = _mm256_add_epi32(v, _mm256_andnot_si256(lo, s1));
        // Keeps each step where it is placed (see `step`).
        core::arch::asm!("/* {0} */", inout(ymm_reg) v, options(nostack, preserves_flags));
        x[s % 4] = v;
        store256(v, s, w0, w1);
    }

    /// The whole SHA-256 schedule of two blocks. Not inlined (see
    /// `schedule512x2`).
    #[target_feature(enable = "avx2")]
    #[inline(never)]
    pub unsafe fn schedule256x2(b0: *const u8, b1: *const u8, w0: &mut [u32; 64], w1: &mut [u32; 64]) {
        let mut x = start256(b0, b1, w0, w1);
        for s in 4..16 {
            step256(&mut x, s, w0, w1);
        }
    }
}
