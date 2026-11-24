//! The SHA-512 and SHA-256 message schedules with AVX2, two blocks at once,
//! proven against `spec512::schedule` and `spec::schedule`.
//!
//! A 256-bit vector holds W_t and W_{t+1} of the first block in its low
//! half and of the second block in its high half (for SHA-256, W_t to
//! W_{t+3}), and each step computes the next two (four) words of both
//! blocks, as OpenSSL's `sha512_block_data_order_avx2` does. The
//! intrinsics are verilith-simd's, whose specifications are checked against
//! the CPU there (`tests/difftest.rs`); the lane reasoning is in
//! `crate::lanes`.
//!
//! Two forms. [`schedule512x2`] computes a pair's whole schedule. The
//! pipelined form, [`sched_start`] and [`sched_steps2`], computes it a few
//! words at a time, so that the verified rounds of one pair can run with
//! the next pair's schedule interleaved: the vector work then fills the
//! ports the rounds' dependency chains leave idle, as in OpenSSL. Its state
//! is the last 16 words of each block, [`Sched512`], and `sched_at` says
//! which words they are.
//!
//! Trusted here: `barrier`, an empty `asm!` each pipelined step's result
//! passes through (it only keeps LLVM from moving the step), and the two
//! whole-schedule functions' trampolines, which compile the verified body
//! with AVX2 enabled.
use crate::lanes::*;
use crate::spec512 as spec;
use verilith_simd::arch::*;
#[cfg(verus_only)]
use verilith_simd::cpu::avx2;
use verilith_simd::lanes::*;
use verilith_simd::mem::{load128_u32, load128_u64, load128_u8, store128_u32, store128_u64};
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::lanes::group_lanes;

/// Passes `v` through an empty `asm!` that is ordered with memory, which
/// keeps a pipelined step between the round groups it was placed between.
/// Without it LLVM hoists every step to the top of the pair, and the
/// interleaving is lost.
#[verifier::external_body]
#[inline(always)]
fn barrier(v: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        r == v,
{
    // SAFETY: the CPU has AVX2: the verified callers all require `avx2()`.
    unsafe { tf::barrier(v) }
}

proof fn lemma_add4(a: u64, b: u64, c: u64, d: u64)
    ensures
        spec::add(spec::add(a, b), spec::add(c, d)) == spec::add(spec::add(spec::add(a, b), c), d),
{
    let m = 0x1_0000_0000_0000_0000int;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int + b as int, c as int + d as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int + b as int + c as int, d as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int + b as int, c as int, m);
    vstd::arithmetic::div_mod::lemma_mod_twice(d as int, m);
    vstd::arithmetic::div_mod::lemma_small_mod(d as nat, m as nat);
    vstd::arithmetic::div_mod::lemma_small_mod(c as nat, m as nat);
}

// ---------------------------------------------------------------------------
// SHA-512
// ---------------------------------------------------------------------------

/// `v` holds W_t and W_{t+1} of block words `m0` and of `m1`.
pub open spec fn holds512(v: __m256i, m0: Seq<u64>, m1: Seq<u64>, t: int) -> bool {
    u64x4(v) == seq![spec::schedule(m0, t), spec::schedule(m0, t + 1), spec::schedule(m1, t), spec::schedule(m1, t + 1)]
}

/// σ0 on each 64-bit lane (FIPS 180-4 (4.12)).
#[inline(always)]
fn sigma0(x: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] u64x4(r)[i] == spec::small_sigma0(u64x4(x)[i]),
{
    let a = _mm256_srli_epi64::<1>(x);
    let b = _mm256_slli_epi64::<63>(x);
    let c = _mm256_srli_epi64::<8>(x);
    let d = _mm256_slli_epi64::<56>(x);
    let ab = _mm256_or_si256(a, b);
    let cd = _mm256_or_si256(c, d);
    let abcd = _mm256_xor_si256(ab, cd);
    let e = _mm256_srli_epi64::<7>(x);
    let r = _mm256_xor_si256(abcd, e);
    proof {
        lemma_bitw_u64s(b256(a), b256(b));
        lemma_bitw_u64s(b256(c), b256(d));
        lemma_bitw_u64s(b256(ab), b256(cd));
        lemma_bitw_u64s(b256(abcd), b256(e));
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u64x4(r)[i] == spec::small_sigma0(u64x4(x)[i]) by {
            let xi = u64x4(x)[i];
            lemma_shr64_1(xi);
            lemma_shl64_63(xi);
            lemma_shr64_8(xi);
            lemma_shl64_56(xi);
            lemma_shr64_7(xi);
        }
    }
    r
}

/// σ1 on each 64-bit lane (FIPS 180-4 (4.13)).
#[inline(always)]
fn sigma1(x: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] u64x4(r)[i] == spec::small_sigma1(u64x4(x)[i]),
{
    let a = _mm256_srli_epi64::<19>(x);
    let b = _mm256_slli_epi64::<45>(x);
    let c = _mm256_srli_epi64::<61>(x);
    let d = _mm256_slli_epi64::<3>(x);
    let ab = _mm256_or_si256(a, b);
    let cd = _mm256_or_si256(c, d);
    let abcd = _mm256_xor_si256(ab, cd);
    let e = _mm256_srli_epi64::<6>(x);
    let r = _mm256_xor_si256(abcd, e);
    proof {
        lemma_bitw_u64s(b256(a), b256(b));
        lemma_bitw_u64s(b256(c), b256(d));
        lemma_bitw_u64s(b256(ab), b256(cd));
        lemma_bitw_u64s(b256(abcd), b256(e));
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u64x4(r)[i] == spec::small_sigma1(u64x4(x)[i]) by {
            let xi = u64x4(x)[i];
            lemma_shr64_19(xi);
            lemma_shl64_45(xi);
            lemma_shr64_61(xi);
            lemma_shl64_3(xi);
            lemma_shr64_6(xi);
        }
    }
    r
}

/// Stores K + W for words 2s and 2s + 1 of both blocks, from `v`, which
/// holds W_{2s} and W_{2s+1}.
#[verifier::spinoff_prover]
#[inline(always)]
fn store512(v: __m256i, s: usize, w0: &mut [u64; 80], w1: &mut [u64; 80], Ghost(m0): Ghost<Seq<u64>>, Ghost(m1): Ghost<Seq<u64>>)
    requires
        avx2(),
        s < 40,
        holds512(v, m0, m1, 2 * s),
        crate::compress512::kw_upto(old(w0)@, m0, 2 * s),
        crate::compress512::kw_upto(old(w1)@, m1, 2 * s),
    ensures
        crate::compress512::kw_upto(final(w0)@, m0, 2 * s + 2),
        crate::compress512::kw_upto(final(w1)@, m1, 2 * s + 2),
{
    let kq = load128_u64(spec::K.as_slice(), 2 * s);
    let k = _mm256_broadcastsi128_si256(kq);
    let kw = _mm256_add_epi64(v, k);
    let lo = _mm256_castsi256_si128(kw);
    let hi = _mm256_extracti128_si256::<1>(kw);
    proof {
        lemma_u64s_concat(b128(kq), b128(kq));
        lemma_u64s_sub(b256(kw), 0, 2);
        lemma_u64s_sub(b256(kw), 2, 4);
        assert(u64x2(lo) == u64x4(kw).subrange(0, 2));
        assert(u64x2(hi) == u64x4(kw).subrange(2, 4));
    }
    store128_u64(w0, 2 * s, lo);
    store128_u64(w1, 2 * s, hi);
    proof {
        let t = 2 * s as int;
        assert(w0@[t] == spec::add(spec::K[t], spec::schedule(m0, t)));
        assert(w0@[t + 1] == spec::add(spec::K[t + 1], spec::schedule(m0, t + 1)));
        assert(w1@[t] == spec::add(spec::K[t], spec::schedule(m1, t)));
        assert(w1@[t + 1] == spec::add(spec::K[t + 1], spec::schedule(m1, t + 1)));
        assert forall|i: int| 0 <= i < t + 2 implies #[trigger] w0@[i] == spec::add(spec::K[i], spec::schedule(m0, i)) by {
            if i < t {
                assert(w0@[i] == old(w0)@[i]);
            }
        }
        assert forall|i: int| 0 <= i < t + 2 implies #[trigger] w1@[i] == spec::add(spec::K[i], spec::schedule(m1, i)) by {
            if i < t {
                assert(w1@[i] == old(w1)@[i]);
            }
        }
    }
}

/// Words 2s and 2s + 1 of the blocks at `o0` and `o1` of `p` (s < 8).
#[inline(always)]
fn load512(p: &[u8], o0: usize, o1: usize, s: usize) -> (r: __m256i)
    requires
        avx2(),
        s < 8,
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        holds512(r, spec::words(p@.subrange(o0 as int, o0 + 128)), spec::words(p@.subrange(o1 as int, o1 + 128)), 2 * s),
{
    // Big-endian 64-bit words from little-endian lanes.
    let bswap = _mm256_setr_epi8(
        7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, //
        7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
    );
    assert(16 * s < 128) by (nonlinear_arith)
        requires
            s < 8,
    ;
    let _n = p.len();
    let lo = load128_u8(p, o0 + 16 * s);
    let hi = load128_u8(p, o1 + 16 * s);
    let both = _mm256_set_m128i(hi, lo);
    let r = _mm256_shuffle_epi8(both, bswap);
    proof {
        assert(b256(bswap) =~= bswap64_mask());
        lemma_bswap64(b256(both), b256(bswap));
        let b0 = p@.subrange(o0 as int, o0 + 128);
        let b1 = p@.subrange(o1 as int, o1 + 128);
        let src = b256(both);
        let m0 = spec::words(b0);
        let m1 = spec::words(b1);
        assert forall|j: int| 0 <= j < 16 implies #[trigger] src[j] == b0[16 * s + j] && src[16 + j] == b1[16 * s + j] by {}
        assert(spec::schedule(m0, 2 * s as int) == spec::be64_at(src, 0));
        assert(spec::schedule(m0, 2 * s + 1) == spec::be64_at(src, 8));
        assert(spec::schedule(m1, 2 * s as int) == spec::be64_at(src, 16));
        assert(spec::schedule(m1, 2 * s + 1) == spec::be64_at(src, 24));
        assert(u64x4(r) =~= seq![
            spec::schedule(m0, 2 * s as int),
            spec::schedule(m0, 2 * s + 1),
            spec::schedule(m1, 2 * s as int),
            spec::schedule(m1, 2 * s + 1),
        ]);
    }
    r
}

/// A pair's schedule part way: the last 16 words of each block, in
/// vectors.
pub struct Sched512 {
    x: [__m256i; 8],
}

/// The words slot `k` of the window holds at step `s`: W_{2s'} and
/// W_{2s'+1} for the step s' (s - 8 <= s' < s) with s' = k mod 8.
pub open spec fn slot512(s: int, k: int) -> int {
    2 * (s - 8 + (k - s) % 8)
}

/// `st` holds the schedule of block words `m0` and `m1` up to step `s`
/// (words `2s - 16` to `2s`), and the CPU has AVX2.
pub closed spec fn sched_at(st: Sched512, m0: Seq<u64>, m1: Seq<u64>, s: int) -> bool {
    &&& avx2()
    &&& 8 <= s <= 40
    &&& forall|k: int| 0 <= k < 8 ==> #[trigger] holds512(st.x@[k], m0, m1, slot512(s, k))
}

/// Where step `s - 8 + j`'s words are in the window at step `s`.
proof fn lemma_slot512(s: int, j: int)
    requires
        8 <= s,
        0 <= j < 8,
    ensures
        0 <= (s + j) % 8 < 8,
        slot512(s, (s + j) % 8) == 2 * (s - 8 + j),
{
    let k = (s + j) % 8;
    assert((k - s) % 8 == j);
}

/// The window after step `s`: slot `s % 8` now has the words of step `s`,
/// and the others are where they were.
proof fn lemma_slot512_next(s: int, k: int)
    requires
        8 <= s,
        0 <= k < 8,
    ensures
        k == s % 8 ==> slot512(s + 1, k) == 2 * s,
        k != s % 8 ==> slot512(s + 1, k) == slot512(s, k),
{
    if k == s % 8 {
        assert((k - (s + 1)) % 8 == 7);
    } else {
        assert((k - (s + 1)) % 8 == (k - s) % 8 - 1);
    }
}

/// The four lanes of a step, on sequences.
proof fn lemma_next512_lanes(
    a0: Seq<u64>,
    a1: Seq<u64>,
    a4: Seq<u64>,
    a5: Seq<u64>,
    a7: Seq<u64>,
    w15: Seq<u64>,
    w7: Seq<u64>,
    s0: Seq<u64>,
    s1: Seq<u64>,
    r: Seq<u64>,
    m0: Seq<u64>,
    m1: Seq<u64>,
    t: int,
)
    requires
        16 <= t,
        a0 == seq![spec::schedule(m0, t - 16), spec::schedule(m0, t - 15), spec::schedule(m1, t - 16), spec::schedule(m1, t - 15)],
        a1 == seq![spec::schedule(m0, t - 14), spec::schedule(m0, t - 13), spec::schedule(m1, t - 14), spec::schedule(m1, t - 13)],
        a4 == seq![spec::schedule(m0, t - 8), spec::schedule(m0, t - 7), spec::schedule(m1, t - 8), spec::schedule(m1, t - 7)],
        a5 == seq![spec::schedule(m0, t - 6), spec::schedule(m0, t - 5), spec::schedule(m1, t - 6), spec::schedule(m1, t - 5)],
        a7 == seq![spec::schedule(m0, t - 2), spec::schedule(m0, t - 1), spec::schedule(m1, t - 2), spec::schedule(m1, t - 1)],
        w15 == seq![a0[1], a1[0], a0[3], a1[2]],
        w7 == seq![a4[1], a5[0], a4[3], a5[2]],
        s0.len() == 4,
        s1.len() == 4,
        forall|i: int| 0 <= i < 4 ==> #[trigger] s0[i] == spec::small_sigma0(w15[i]),
        forall|i: int| 0 <= i < 4 ==> #[trigger] s1[i] == spec::small_sigma1(a7[i]),
        r == add64(add64(s1, w7), add64(s0, a0)),
    ensures
        r == seq![spec::schedule(m0, t), spec::schedule(m0, t + 1), spec::schedule(m1, t), spec::schedule(m1, t + 1)],
{
    hide(spec::schedule);
    let a = add64(s1, w7);
    let b = add64(s0, a0);
    assert(s0[0] == spec::small_sigma0(w15[0]) && s1[0] == spec::small_sigma1(a7[0]));
    assert(s0[1] == spec::small_sigma0(w15[1]) && s1[1] == spec::small_sigma1(a7[1]));
    assert(s0[2] == spec::small_sigma0(w15[2]) && s1[2] == spec::small_sigma1(a7[2]));
    assert(s0[3] == spec::small_sigma0(w15[3]) && s1[3] == spec::small_sigma1(a7[3]));
    lemma_lane512(m0, t, a0[0], a0[1], a4[1], a7[0], r[0]);
    lemma_lane512(m0, t + 1, a0[1], a1[0], a5[0], a7[1], r[1]);
    lemma_lane512(m1, t, a0[2], a0[3], a4[3], a7[2], r[2]);
    lemma_lane512(m1, t + 1, a0[3], a1[2], a5[2], a7[3], r[3]);
    assert(r =~= seq![spec::schedule(m0, t), spec::schedule(m0, t + 1), spec::schedule(m1, t), spec::schedule(m1, t + 1)]);
}

/// One word of a step: W_t from W_{t-16}, W_{t-15}, W_{t-7} and W_{t-2}.
proof fn lemma_lane512(m: Seq<u64>, t: int, x16: u64, x15: u64, x7: u64, x2: u64, r: u64)
    requires
        16 <= t,
        x16 == spec::schedule(m, t - 16),
        x15 == spec::schedule(m, t - 15),
        x7 == spec::schedule(m, t - 7),
        x2 == spec::schedule(m, t - 2),
        r == spec::add(spec::add(spec::small_sigma1(x2), x7), spec::add(spec::small_sigma0(x15), x16)),
    ensures
        r == spec::schedule(m, t),
{
    lemma_add4(spec::small_sigma1(x2), x7, spec::small_sigma0(x15), x16);
}

/// Step `s`: words 2s and 2s + 1 of both blocks, from the window.
#[inline(always)]
fn next512(st: &Sched512, s: usize, Ghost(m0): Ghost<Seq<u64>>, Ghost(m1): Ghost<Seq<u64>>) -> (r: __m256i)
    requires
        sched_at(*st, m0, m1, s as int),
        s < 40,
    ensures
        avx2(),
        holds512(r, m0, m1, 2 * s),
{
    let ghost si = s as int;
    proof {
        lemma_slot512(si, 0);
        lemma_slot512(si, 1);
        lemma_slot512(si, 4);
        lemma_slot512(si, 5);
        lemma_slot512(si, 7);
        assert(holds512(st.x@[(si + 0) % 8], m0, m1, slot512(si, (si + 0) % 8)));
        assert(holds512(st.x@[(si + 1) % 8], m0, m1, slot512(si, (si + 1) % 8)));
        assert(holds512(st.x@[(si + 4) % 8], m0, m1, slot512(si, (si + 4) % 8)));
        assert(holds512(st.x@[(si + 5) % 8], m0, m1, slot512(si, (si + 5) % 8)));
        assert(holds512(st.x@[(si + 7) % 8], m0, m1, slot512(si, (si + 7) % 8)));
    }
    let x0 = st.x[s % 8];
    let x1 = st.x[(s + 1) % 8];
    let x4 = st.x[(s + 4) % 8];
    let x5 = st.x[(s + 5) % 8];
    let x7 = st.x[(s + 7) % 8];
    // W_t = σ1(W_{t-2}) + W_{t-7} + σ0(W_{t-15}) + W_{t-16}, for t = 2s
    // and 2s + 1: W_{t-15..t-13} and W_{t-7..t-5} straddle two vectors.
    let w15 = _mm256_alignr_epi8::<8>(x1, x0);
    let w7 = _mm256_alignr_epi8::<8>(x5, x4);
    let s1 = sigma1(x7);
    let s0 = sigma0(w15);
    let a = _mm256_add_epi64(s1, w7);
    let b = _mm256_add_epi64(s0, x0);
    let r = _mm256_add_epi64(a, b);
    proof {
        lemma_alignr8_u64s(b256(x1), b256(x0));
        lemma_alignr8_u64s(b256(x5), b256(x4));
        lemma_next512_lanes(
            u64x4(x0), u64x4(x1), u64x4(x4), u64x4(x5), u64x4(x7),
            u64x4(w15), u64x4(w7), u64x4(s0), u64x4(s1), u64x4(r),
            m0, m1, 2 * si,
        );
    }
    r
}

/// The window after step `s`, whose words `v` replace those of step `s - 8`.
proof fn lemma_window512(st: Sched512, st2: Sched512, m0: Seq<u64>, m1: Seq<u64>, s: int, v: __m256i)
    requires
        sched_at(st, m0, m1, s),
        s < 40,
        holds512(v, m0, m1, 2 * s),
        st2.x@ == st.x@.update(s % 8, v),
    ensures
        sched_at(st2, m0, m1, s + 1),
{
    assert forall|k: int| 0 <= k < 8 implies #[trigger] holds512(st2.x@[k], m0, m1, slot512(s + 1, k)) by {
        lemma_slot512_next(s, k);
        if k != s % 8 {
            assert(holds512(st.x@[k], m0, m1, slot512(s, k)));
        }
    }
}

/// Starts the schedule of the blocks at `o0` and `o1`: their first 16 words.
#[inline(always)]
pub fn sched_start(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80]) -> (r: Sched512)
    requires
        avx2(),
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
    let ghost m0 = spec::words(p@.subrange(o0 as int, o0 + 128));
    let ghost m1 = spec::words(p@.subrange(o1 as int, o1 + 128));
    let mut x = [_mm256_setzero_si256(); 8];
    let mut s: usize = 0;
    while s < 8
        invariant
            avx2(),
            s <= 8,
            o0 + 128 <= p@.len(),
            o1 + 128 <= p@.len(),
            m0 == spec::words(p@.subrange(o0 as int, o0 + 128)),
            m1 == spec::words(p@.subrange(o1 as int, o1 + 128)),
            forall|k: int| 0 <= k < s ==> #[trigger] holds512(x@[k], m0, m1, 2 * k),
            crate::compress512::kw_upto(w0@, m0, 2 * s),
            crate::compress512::kw_upto(w1@, m1, 2 * s),
        decreases 8 - s,
    {
        let v = load512(p, o0, o1, s);
        x[s] = v;
        store512(v, s, w0, w1, Ghost(m0), Ghost(m1));
        s = s + 1;
    }
    let r = Sched512 { x };
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] holds512(r.x@[k], m0, m1, slot512(8, k)) by {
            assert((k - 8) % 8 == k);
        }
    }
    r
}

/// Steps `s` and `s + 1`: words `2s` to `2s + 4` of both blocks.
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
    step512_pipe(st, s, w0, w1, Ghost(m0), Ghost(m1));
    step512_pipe(st, s + 1, w0, w1, Ghost(m0), Ghost(m1));
}

/// One step of the pipelined schedule, through `barrier`.
#[inline(always)]
fn step512_pipe(
    st: &mut Sched512,
    s: usize,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        s < 40,
        sched_at(*old(st), m0, m1, s as int),
        crate::compress512::kw_upto(old(w0)@, m0, 2 * s),
        crate::compress512::kw_upto(old(w1)@, m1, 2 * s),
    ensures
        sched_at(*final(st), m0, m1, s + 1),
        crate::compress512::kw_upto(final(w0)@, m0, 2 * s + 2),
        crate::compress512::kw_upto(final(w1)@, m1, 2 * s + 2),
{
    let v = next512(st, s, Ghost(m0), Ghost(m1));
    let v = barrier(v);

    let ghost st0 = *st;
    st.x[s % 8] = v;
    proof {
        lemma_window512(st0, *st, m0, m1, s as int, v);
    }
    store512(v, s, w0, w1, Ghost(m0), Ghost(m1));
}

/// One step of the whole schedule.
#[inline(always)]
fn step512(
    st: &mut Sched512,
    s: usize,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        s < 40,
        sched_at(*old(st), m0, m1, s as int),
        crate::compress512::kw_upto(old(w0)@, m0, 2 * s),
        crate::compress512::kw_upto(old(w1)@, m1, 2 * s),
    ensures
        sched_at(*final(st), m0, m1, s + 1),
        crate::compress512::kw_upto(final(w0)@, m0, 2 * s + 2),
        crate::compress512::kw_upto(final(w1)@, m1, 2 * s + 2),
{
    let v = next512(st, s, Ghost(m0), Ghost(m1));
    let ghost st0 = *st;
    st.x[s % 8] = v;
    proof {
        lemma_window512(st0, *st, m0, m1, s as int, v);
    }
    store512(v, s, w0, w1, Ghost(m0), Ghost(m1));
}

/// K_t + W_t for t = 0..80 of the 128-byte blocks at `o0` and `o1` of `p`.
#[inline(always)]
fn schedule512x2_body(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80])
    requires
        avx2(),
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        crate::compress512::kw_schedule(final(w0)@, spec::words(p@.subrange(o0 as int, o0 + 128))),
        crate::compress512::kw_schedule(final(w1)@, spec::words(p@.subrange(o1 as int, o1 + 128))),
{
    let ghost m0 = spec::words(p@.subrange(o0 as int, o0 + 128));
    let ghost m1 = spec::words(p@.subrange(o1 as int, o1 + 128));
    let mut st = sched_start(p, o0, o1, w0, w1);
    // Each step written out, so that every window index is a constant.
    step512(&mut st, 8, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 9, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 10, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 11, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 12, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 13, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 14, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 15, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 16, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 17, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 18, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 19, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 20, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 21, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 22, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 23, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 24, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 25, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 26, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 27, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 28, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 29, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 30, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 31, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 32, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 33, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 34, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 35, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 36, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 37, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 38, w0, w1, Ghost(m0), Ghost(m1));
    step512(&mut st, 39, w0, w1, Ghost(m0), Ghost(m1));
}

/// K_t + W_t for t = 0..80 of the 128-byte blocks at `o0` and `o1` of `p`:
/// `schedule512x2_body` compiled with AVX2 and out of line (trusted to be
/// that function).
///
/// Not inlined, on purpose: inlined, LLVM forwards the stores to the
/// rounds as lane extractions, which take the ALU ports the rounds need;
/// through memory they cost store and load ports instead, and the rounds
/// fold the loads into their additions.
#[verifier::external_body]
#[inline(always)]
pub fn schedule512x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80])
    requires
        avx2(),
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        crate::compress512::kw_schedule(final(w0)@, spec::words(p@.subrange(o0 as int, o0 + 128))),
        crate::compress512::kw_schedule(final(w1)@, spec::words(p@.subrange(o1 as int, o1 + 128))),
{
    // SAFETY: the CPU has AVX2 (`avx2()`).
    unsafe { tf::schedule512x2(p, o0, o1, w0, w1) }
}


// ---------------------------------------------------------------------------
// SHA-256: the same, with four 32-bit words of each block per step
// ---------------------------------------------------------------------------

/// `v` holds W_t to W_{t+3} of SHA-256 block words `m0` and of `m1`.
pub open spec fn holds256(v: __m256i, m0: Seq<u32>, m1: Seq<u32>, t: int) -> bool {
    u32x8(v) == seq![
        crate::spec::schedule(m0, t), crate::spec::schedule(m0, t + 1),
        crate::spec::schedule(m0, t + 2), crate::spec::schedule(m0, t + 3),
        crate::spec::schedule(m1, t), crate::spec::schedule(m1, t + 1),
        crate::spec::schedule(m1, t + 2), crate::spec::schedule(m1, t + 3),
    ]
}

/// σ0 on each 32-bit lane (FIPS 180-4 (4.6)).
#[inline(always)]
fn sigma0_256(x: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u32x8(r)[i] == crate::spec::small_sigma0(u32x8(x)[i]),
{
    let a = _mm256_srli_epi32::<7>(x);
    let b = _mm256_slli_epi32::<25>(x);
    let c = _mm256_srli_epi32::<18>(x);
    let d = _mm256_slli_epi32::<14>(x);
    let ab = _mm256_or_si256(a, b);
    let cd = _mm256_or_si256(c, d);
    let abcd = _mm256_xor_si256(ab, cd);
    let e = _mm256_srli_epi32::<3>(x);
    let r = _mm256_xor_si256(abcd, e);
    proof {
        lemma_bitw_u32s(b256(a), b256(b));
        lemma_bitw_u32s(b256(c), b256(d));
        lemma_bitw_u32s(b256(ab), b256(cd));
        lemma_bitw_u32s(b256(abcd), b256(e));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u32x8(r)[i] == crate::spec::small_sigma0(u32x8(x)[i]) by {
            let xi = u32x8(x)[i];
            lemma_shr32_7(xi);
            lemma_shl32_25(xi);
            lemma_shr32_18(xi);
            lemma_shl32_14(xi);
            lemma_shr32_3(xi);
        }
    }
    r
}

/// σ1 on each 32-bit lane (FIPS 180-4 (4.7)).
#[inline(always)]
fn sigma1_256(x: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u32x8(r)[i] == crate::spec::small_sigma1(u32x8(x)[i]),
{
    let a = _mm256_srli_epi32::<17>(x);
    let b = _mm256_slli_epi32::<15>(x);
    let c = _mm256_srli_epi32::<19>(x);
    let d = _mm256_slli_epi32::<13>(x);
    let ab = _mm256_or_si256(a, b);
    let cd = _mm256_or_si256(c, d);
    let abcd = _mm256_xor_si256(ab, cd);
    let e = _mm256_srli_epi32::<10>(x);
    let r = _mm256_xor_si256(abcd, e);
    proof {
        lemma_bitw_u32s(b256(a), b256(b));
        lemma_bitw_u32s(b256(c), b256(d));
        lemma_bitw_u32s(b256(ab), b256(cd));
        lemma_bitw_u32s(b256(abcd), b256(e));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u32x8(r)[i] == crate::spec::small_sigma1(u32x8(x)[i]) by {
            let xi = u32x8(x)[i];
            lemma_shr32_17(xi);
            lemma_shl32_15(xi);
            lemma_shr32_19(xi);
            lemma_shl32_13(xi);
            lemma_shr32_10(xi);
        }
    }
    r
}

/// Stores K + W for words 4s to 4s + 4 of both blocks, from `v`, which
/// holds W_{4s} to W_{4s+3}.
#[verifier::spinoff_prover]
#[inline(always)]
fn store256(v: __m256i, s: usize, w0: &mut [u32; 64], w1: &mut [u32; 64], Ghost(m0): Ghost<Seq<u32>>, Ghost(m1): Ghost<Seq<u32>>)
    requires
        avx2(),
        s < 16,
        holds256(v, m0, m1, 4 * s),
        crate::compress::kw256_upto(old(w0)@, m0, 4 * s),
        crate::compress::kw256_upto(old(w1)@, m1, 4 * s),
    ensures
        crate::compress::kw256_upto(final(w0)@, m0, 4 * s + 4),
        crate::compress::kw256_upto(final(w1)@, m1, 4 * s + 4),
{
    let kq = load128_u32(crate::spec::K.as_slice(), 4 * s);
    let k = _mm256_broadcastsi128_si256(kq);
    let kw = _mm256_add_epi32(v, k);
    let lo = _mm256_castsi256_si128(kw);
    let hi = _mm256_extracti128_si256::<1>(kw);
    proof {
        lemma_u32s_concat(b128(kq), b128(kq));
        lemma_u32s_sub(b256(kw), 0, 4);
        lemma_u32s_sub(b256(kw), 4, 8);
        assert(u32x4(lo) == u32x8(kw).subrange(0, 4));
        assert(u32x4(hi) == u32x8(kw).subrange(4, 8));
    }
    store128_u32(w0, 4 * s, lo);
    store128_u32(w1, 4 * s, hi);
    proof {
        let t = 4 * s as int;
        assert(w0@[t + 0] == crate::spec::add(crate::spec::K[t + 0], crate::spec::schedule(m0, t + 0)));
        assert(w1@[t + 0] == crate::spec::add(crate::spec::K[t + 0], crate::spec::schedule(m1, t + 0)));
        assert(w0@[t + 1] == crate::spec::add(crate::spec::K[t + 1], crate::spec::schedule(m0, t + 1)));
        assert(w1@[t + 1] == crate::spec::add(crate::spec::K[t + 1], crate::spec::schedule(m1, t + 1)));
        assert(w0@[t + 2] == crate::spec::add(crate::spec::K[t + 2], crate::spec::schedule(m0, t + 2)));
        assert(w1@[t + 2] == crate::spec::add(crate::spec::K[t + 2], crate::spec::schedule(m1, t + 2)));
        assert(w0@[t + 3] == crate::spec::add(crate::spec::K[t + 3], crate::spec::schedule(m0, t + 3)));
        assert(w1@[t + 3] == crate::spec::add(crate::spec::K[t + 3], crate::spec::schedule(m1, t + 3)));
        assert forall|i: int| 0 <= i < t + 4 implies #[trigger] w0@[i] == crate::spec::add(crate::spec::K[i], crate::spec::schedule(m0, i)) by {
            if i < t {
                assert(w0@[i] == old(w0)@[i]);
            }
        }
        assert forall|i: int| 0 <= i < t + 4 implies #[trigger] w1@[i] == crate::spec::add(crate::spec::K[i], crate::spec::schedule(m1, i)) by {
            if i < t {
                assert(w1@[i] == old(w1)@[i]);
            }
        }
    }
}

/// Words 4s to 4s + 4 of the SHA-256 blocks at `o0` and `o1` of `p` (s < 4).
#[inline(always)]
fn load256(p: &[u8], o0: usize, o1: usize, s: usize) -> (r: __m256i)
    requires
        avx2(),
        s < 4,
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        holds256(r, crate::spec::words(p@.subrange(o0 as int, o0 + 64)), crate::spec::words(p@.subrange(o1 as int, o1 + 64)), 4 * s),
{
    // Big-endian 32-bit words from little-endian lanes.
    let bswap = _mm256_setr_epi8(
        3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, //
        3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
    );
    let _n = p.len();
    let lo = load128_u8(p, o0 + 16 * s);
    let hi = load128_u8(p, o1 + 16 * s);
    let both = _mm256_set_m128i(hi, lo);
    let r = _mm256_shuffle_epi8(both, bswap);
    proof {
        assert(b256(bswap) =~= bswap32_mask());
        lemma_bswap32(b256(both), b256(bswap));
        let b0 = p@.subrange(o0 as int, o0 + 64);
        let b1 = p@.subrange(o1 as int, o1 + 64);
        let src = b256(both);
        let m0 = crate::spec::words(b0);
        let m1 = crate::spec::words(b1);
        let t = 4 * s as int;
        assert forall|j: int| 0 <= j < 16 implies #[trigger] src[j] == b0[16 * s + j] && src[16 + j] == b1[16 * s + j] by {}
        assert forall|j: int| 0 <= j < 4 implies #[trigger] crate::spec::schedule(m0, t + j) == crate::spec::be32(src, 4 * j)
            && crate::spec::schedule(m1, t + j) == crate::spec::be32(src, 16 + 4 * j) by {
            assert(4 * (t + j) == 16 * s + 4 * j);
        }
        assert(crate::spec::be32(src, 16int + 4 * 0) == u32x8(r)[4]);
        assert(crate::spec::be32(src, 16int + 4 * 1) == u32x8(r)[5]);
        assert(crate::spec::be32(src, 16int + 4 * 2) == u32x8(r)[6]);
        assert(crate::spec::be32(src, 16int + 4 * 3) == u32x8(r)[7]);
        assert(crate::spec::schedule(m0, t + 0) == u32x8(r)[0]);
        assert(crate::spec::schedule(m0, t + 1) == u32x8(r)[1]);
        assert(crate::spec::schedule(m0, t + 2) == u32x8(r)[2]);
        assert(crate::spec::schedule(m0, t + 3) == u32x8(r)[3]);
        assert(crate::spec::schedule(m1, t + 0) == u32x8(r)[4]);
        assert(crate::spec::schedule(m1, t + 1) == u32x8(r)[5]);
        assert(crate::spec::schedule(m1, t + 2) == u32x8(r)[6]);
        assert(crate::spec::schedule(m1, t + 3) == u32x8(r)[7]);
        assert(u32x8(r) =~= seq![
            crate::spec::schedule(m0, t), crate::spec::schedule(m0, t + 1),
            crate::spec::schedule(m0, t + 2), crate::spec::schedule(m0, t + 3),
            crate::spec::schedule(m1, t), crate::spec::schedule(m1, t + 1),
            crate::spec::schedule(m1, t + 2), crate::spec::schedule(m1, t + 3),
        ]);
    }
    r
}

/// A SHA-256 pair's schedule part way: its last 16 words, in vectors.
pub struct Sched256 {
    x: [__m256i; 4],
}

/// The words slot `k` of the window holds at step `s`: W_{4s'} to
/// W_{4s'+3} for the step s' (s - 4 <= s' < s) with s' = k mod 4.
pub open spec fn slot256(s: int, k: int) -> int {
    4 * (s - 4 + (k - s) % 4)
}

/// `st` holds the schedule of SHA-256 block words `m0` and `m1` up to step
/// `s` (words `4s - 16` to `4s`), and the CPU has AVX2.
pub closed spec fn sched256_at(st: Sched256, m0: Seq<u32>, m1: Seq<u32>, s: int) -> bool {
    &&& avx2()
    &&& 4 <= s <= 16
    &&& forall|k: int| 0 <= k < 4 ==> #[trigger] holds256(st.x@[k], m0, m1, slot256(s, k))
}

proof fn lemma_slot256(s: int, j: int)
    requires
        4 <= s,
        0 <= j < 4,
    ensures
        0 <= (s + j) % 4 < 4,
        slot256(s, (s + j) % 4) == 4 * (s - 4 + j),
{
    let k = (s + j) % 4;
    assert((k - s) % 4 == j);
}

proof fn lemma_slot256_next(s: int, k: int)
    requires
        4 <= s,
        0 <= k < 4,
    ensures
        k == s % 4 ==> slot256(s + 1, k) == 4 * s,
        k != s % 4 ==> slot256(s + 1, k) == slot256(s, k),
{
    if k == s % 4 {
        assert((k - (s + 1)) % 4 == 3);
    } else {
        assert((k - (s + 1)) % 4 == (k - s) % 4 - 1);
    }
}

proof fn lemma_add4_256(a: u32, b: u32, c: u32, d: u32)
    ensures
        crate::spec::add(crate::spec::add(crate::spec::add(a, b), c), d)
            == crate::spec::add(crate::spec::add(crate::spec::add(d, c), b), a),
        crate::spec::add(a, 0) == a,
{
    let m = 0x1_0000_0000int;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int + b as int, c as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int + b as int + c as int, d as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((a as int + b as int) % m, c as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(d as int + c as int, b as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(d as int + c as int + b as int, a as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((d as int + c as int) % m, b as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(((a as int + b as int) % m + c as int) % m, d as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(((d as int + c as int) % m + b as int) % m, a as int, m);
    vstd::arithmetic::div_mod::lemma_small_mod(a as nat, m as nat);
    vstd::arithmetic::div_mod::lemma_small_mod(d as nat, m as nat);
    vstd::arithmetic::div_mod::lemma_mod_twice(a as int + b as int + c as int + d as int, m);
}

/// One word of a step: W_t from W_{t-16}, W_{t-15}, W_{t-7} and W_{t-2}.
proof fn lemma_lane256(m: Seq<u32>, t: int, x16: u32, x15: u32, x7: u32, x2: u32, r: u32)
    requires
        16 <= t,
        x16 == crate::spec::schedule(m, t - 16),
        x15 == crate::spec::schedule(m, t - 15),
        x7 == crate::spec::schedule(m, t - 7),
        x2 == crate::spec::schedule(m, t - 2),
        r == crate::spec::add(
            crate::spec::add(crate::spec::add(x16, crate::spec::small_sigma0(x15)), x7),
            crate::spec::small_sigma1(x2),
        ),
    ensures
        r == crate::spec::schedule(m, t),
{
    lemma_add4_256(x16, crate::spec::small_sigma0(x15), x7, crate::spec::small_sigma1(x2));
}

proof fn lemma_mask32(x: u32)
    ensures
        x & 0xffff_ffff == x,
        x & 0 == 0,
        !0xffff_ffffu32 & x == 0,
        !0u32 & x == x,
{
    assert(x & 0xffff_ffff == x) by (bit_vector);
    assert(x & 0 == 0) by (bit_vector);
    assert(!0xffff_ffffu32 & x == 0) by (bit_vector);
    assert(!0u32 & x == x) by (bit_vector);
}

/// The lanes `shuffle_epi32` picks for the two controls of a step.
proof fn lemma_shuffle32_step(a: Seq<u32>)
    requires
        a.len() == 8,
    ensures
        shuffle32_lanes(a, 0b11_10_11_10) == seq![a[2], a[3], a[2], a[3], a[6], a[7], a[6], a[7]],
        shuffle32_lanes(a, 0b01_00_01_00) == seq![a[0], a[1], a[0], a[1], a[4], a[5], a[4], a[5]],
{
    assert((0int / 4) * 4 + (238int / pow2_spec((2 * (0int % 4)) as nat) as int) % 4 == 2) by (compute_only);
    assert((1int / 4) * 4 + (238int / pow2_spec((2 * (1int % 4)) as nat) as int) % 4 == 3) by (compute_only);
    assert((2int / 4) * 4 + (238int / pow2_spec((2 * (2int % 4)) as nat) as int) % 4 == 2) by (compute_only);
    assert((3int / 4) * 4 + (238int / pow2_spec((2 * (3int % 4)) as nat) as int) % 4 == 3) by (compute_only);
    assert((4int / 4) * 4 + (238int / pow2_spec((2 * (4int % 4)) as nat) as int) % 4 == 6) by (compute_only);
    assert((5int / 4) * 4 + (238int / pow2_spec((2 * (5int % 4)) as nat) as int) % 4 == 7) by (compute_only);
    assert((6int / 4) * 4 + (238int / pow2_spec((2 * (6int % 4)) as nat) as int) % 4 == 6) by (compute_only);
    assert((7int / 4) * 4 + (238int / pow2_spec((2 * (7int % 4)) as nat) as int) % 4 == 7) by (compute_only);
    assert((0int / 4) * 4 + (68int / pow2_spec((2 * (0int % 4)) as nat) as int) % 4 == 0) by (compute_only);
    assert((1int / 4) * 4 + (68int / pow2_spec((2 * (1int % 4)) as nat) as int) % 4 == 1) by (compute_only);
    assert((2int / 4) * 4 + (68int / pow2_spec((2 * (2int % 4)) as nat) as int) % 4 == 0) by (compute_only);
    assert((3int / 4) * 4 + (68int / pow2_spec((2 * (3int % 4)) as nat) as int) % 4 == 1) by (compute_only);
    assert((4int / 4) * 4 + (68int / pow2_spec((2 * (4int % 4)) as nat) as int) % 4 == 4) by (compute_only);
    assert((5int / 4) * 4 + (68int / pow2_spec((2 * (5int % 4)) as nat) as int) % 4 == 5) by (compute_only);
    assert((6int / 4) * 4 + (68int / pow2_spec((2 * (6int % 4)) as nat) as int) % 4 == 4) by (compute_only);
    assert((7int / 4) * 4 + (68int / pow2_spec((2 * (7int % 4)) as nat) as int) % 4 == 5) by (compute_only);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[0] == a[2]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[1] == a[3]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[2] == a[2]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[3] == a[3]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[4] == a[6]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[5] == a[7]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[6] == a[6]);
    assert(shuffle32_lanes(a, 0b11_10_11_10)[7] == a[7]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[0] == a[0]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[1] == a[1]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[2] == a[0]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[3] == a[1]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[4] == a[4]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[5] == a[5]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[6] == a[4]);
    assert(shuffle32_lanes(a, 0b01_00_01_00)[7] == a[5]);
    assert(shuffle32_lanes(a, 0b11_10_11_10) =~= seq![a[2], a[3], a[2], a[3], a[6], a[7], a[6], a[7]]);
    assert(shuffle32_lanes(a, 0b01_00_01_00) =~= seq![a[0], a[1], a[0], a[1], a[4], a[5], a[4], a[5]]);
}

/// Step `s`: words 4s to 4s + 4 of both blocks, from the window. W_{4s+2}
/// and W_{4s+3} need σ1 of W_{4s} and W_{4s+1}, so the low two words come
/// first.
#[verifier::spinoff_prover]
#[inline(always)]
fn next256(st: &Sched256, s: usize, Ghost(m0): Ghost<Seq<u32>>, Ghost(m1): Ghost<Seq<u32>>) -> (r: __m256i)
    requires
        sched256_at(*st, m0, m1, s as int),
        s < 16,
    ensures
        avx2(),
        holds256(r, m0, m1, 4 * s),
{
    let ghost si = s as int;
    proof {
        lemma_slot256(si, 0);
        lemma_slot256(si, 1);
        lemma_slot256(si, 2);
        lemma_slot256(si, 3);
        assert(holds256(st.x@[(si + 0) % 4], m0, m1, slot256(si, (si + 0) % 4)));
        assert(holds256(st.x@[(si + 1) % 4], m0, m1, slot256(si, (si + 1) % 4)));
        assert(holds256(st.x@[(si + 2) % 4], m0, m1, slot256(si, (si + 2) % 4)));
        assert(holds256(st.x@[(si + 3) % 4], m0, m1, slot256(si, (si + 3) % 4)));
    }
    let x0 = st.x[s % 4];
    let x1 = st.x[(s + 1) % 4];
    let x2 = st.x[(s + 2) % 4];
    let x3 = st.x[(s + 3) % 4];
    let w15 = _mm256_alignr_epi8::<4>(x1, x0);
    let w7 = _mm256_alignr_epi8::<4>(x3, x2);
    let s0 = sigma0_256(w15);
    let t0 = _mm256_add_epi32(x0, s0);
    let t = _mm256_add_epi32(t0, w7);
    let lo = _mm256_setr_epi32(-1, -1, 0, 0, -1, -1, 0, 0);
    // σ1(W_{4s-2}), σ1(W_{4s-1}) into lanes 0 and 1.
    let y = _mm256_shuffle_epi32::<0b11_10_11_10>(x3);
    let s1 = sigma1_256(y);
    let s1lo = _mm256_and_si256(s1, lo);
    let v = _mm256_add_epi32(t, s1lo);
    // σ1(W_{4s}), σ1(W_{4s+1}) into lanes 2 and 3.
    let y2 = _mm256_shuffle_epi32::<0b01_00_01_00>(v);
    let s1b = sigma1_256(y2);
    let s1hi = _mm256_andnot_si256(lo, s1b);
    let r = _mm256_add_epi32(v, s1hi);
    proof {
        let tt = 4 * si;
        lemma_alignr4_u32s(b256(x1), b256(x0));
        lemma_alignr4_u32s(b256(x3), b256(x2));
        lemma_shuffle32_step(u32x8(x3));
        lemma_shuffle32_step(u32x8(v));
        lemma_bitw_u32s(b256(s1), b256(lo));
        lemma_bitw_u32s(b256(lo), b256(s1b));
        lemma_next256_lanes(
            u32x8(x0), u32x8(x1), u32x8(x2), u32x8(x3), u32x8(w15), u32x8(w7),
            u32x8(s0), u32x8(t), u32x8(lo), u32x8(y), u32x8(s1), u32x8(s1lo), u32x8(v),
            u32x8(y2), u32x8(s1b), u32x8(s1hi), u32x8(r), m0, m1, tt,
        );
    }
    r
}

/// The lanes of a SHA-256 step, on sequences.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_next256_lanes(
    x0: Seq<u32>,
    x1: Seq<u32>,
    x2: Seq<u32>,
    x3: Seq<u32>,
    w15: Seq<u32>,
    w7: Seq<u32>,
    s0: Seq<u32>,
    t: Seq<u32>,
    lo: Seq<u32>,
    y: Seq<u32>,
    s1: Seq<u32>,
    s1lo: Seq<u32>,
    v: Seq<u32>,
    y2: Seq<u32>,
    s1b: Seq<u32>,
    s1hi: Seq<u32>,
    r: Seq<u32>,
    m0: Seq<u32>,
    m1: Seq<u32>,
    tt: int,
)
    requires
        16 <= tt,
        x0 == seq![
            crate::spec::schedule(m0, tt - 16), crate::spec::schedule(m0, tt - 15), crate::spec::schedule(m0, tt - 14), crate::spec::schedule(m0, tt - 13),
            crate::spec::schedule(m1, tt - 16), crate::spec::schedule(m1, tt - 15), crate::spec::schedule(m1, tt - 14), crate::spec::schedule(m1, tt - 13),
        ],
        x1 == seq![
            crate::spec::schedule(m0, tt - 12), crate::spec::schedule(m0, tt - 11), crate::spec::schedule(m0, tt - 10), crate::spec::schedule(m0, tt - 9),
            crate::spec::schedule(m1, tt - 12), crate::spec::schedule(m1, tt - 11), crate::spec::schedule(m1, tt - 10), crate::spec::schedule(m1, tt - 9),
        ],
        x2 == seq![
            crate::spec::schedule(m0, tt - 8), crate::spec::schedule(m0, tt - 7), crate::spec::schedule(m0, tt - 6), crate::spec::schedule(m0, tt - 5),
            crate::spec::schedule(m1, tt - 8), crate::spec::schedule(m1, tt - 7), crate::spec::schedule(m1, tt - 6), crate::spec::schedule(m1, tt - 5),
        ],
        x3 == seq![
            crate::spec::schedule(m0, tt - 4), crate::spec::schedule(m0, tt - 3), crate::spec::schedule(m0, tt - 2), crate::spec::schedule(m0, tt - 1),
            crate::spec::schedule(m1, tt - 4), crate::spec::schedule(m1, tt - 3), crate::spec::schedule(m1, tt - 2), crate::spec::schedule(m1, tt - 1),
        ],
        w15 == seq![x0[1], x0[2], x0[3], x1[0], x0[5], x0[6], x0[7], x1[4]],
        w7 == seq![x2[1], x2[2], x2[3], x3[0], x2[5], x2[6], x2[7], x3[4]],
        s0.len() == 8,
        forall|i: int| 0 <= i < 8 ==> #[trigger] s0[i] == crate::spec::small_sigma0(w15[i]),
        t == add32(add32(x0, s0), w7),
        lo == seq![0xffff_ffffu32, 0xffff_ffffu32, 0u32, 0u32, 0xffff_ffffu32, 0xffff_ffffu32, 0u32, 0u32],
        s1.len() == 8,
        y == seq![x3[2], x3[3], x3[2], x3[3], x3[6], x3[7], x3[6], x3[7]],
        forall|i: int| 0 <= i < 8 ==> #[trigger] s1[i] == crate::spec::small_sigma1(y[i]),
        s1lo.len() == 8,
        forall|i: int| 0 <= i < 8 ==> #[trigger] s1lo[i] == s1[i] & lo[i],
        v == add32(t, s1lo),
        s1b.len() == 8,
        y2 == seq![v[0], v[1], v[0], v[1], v[4], v[5], v[4], v[5]],
        forall|i: int| 0 <= i < 8 ==> #[trigger] s1b[i] == crate::spec::small_sigma1(y2[i]),
        s1hi.len() == 8,
        forall|i: int| 0 <= i < 8 ==> #[trigger] s1hi[i] == !lo[i] & s1b[i],
        r == add32(v, s1hi),
    ensures
        r == seq![
            crate::spec::schedule(m0, tt), crate::spec::schedule(m0, tt + 1), crate::spec::schedule(m0, tt + 2), crate::spec::schedule(m0, tt + 3),
            crate::spec::schedule(m1, tt), crate::spec::schedule(m1, tt + 1), crate::spec::schedule(m1, tt + 2), crate::spec::schedule(m1, tt + 3),
        ],
{
    hide(crate::spec::schedule);
    assert(s0[0] == crate::spec::small_sigma0(w15[0]) && s1lo[0] == s1[0] & lo[0] && s1hi[0] == !lo[0] & s1b[0]);
    assert(s1[0] == crate::spec::small_sigma1(y[0]) && s1b[0] == crate::spec::small_sigma1(y2[0]));
    assert(s0[1] == crate::spec::small_sigma0(w15[1]) && s1lo[1] == s1[1] & lo[1] && s1hi[1] == !lo[1] & s1b[1]);
    assert(s1[1] == crate::spec::small_sigma1(y[1]) && s1b[1] == crate::spec::small_sigma1(y2[1]));
    assert(s0[2] == crate::spec::small_sigma0(w15[2]) && s1lo[2] == s1[2] & lo[2] && s1hi[2] == !lo[2] & s1b[2]);
    assert(s1[2] == crate::spec::small_sigma1(y[2]) && s1b[2] == crate::spec::small_sigma1(y2[2]));
    assert(s0[3] == crate::spec::small_sigma0(w15[3]) && s1lo[3] == s1[3] & lo[3] && s1hi[3] == !lo[3] & s1b[3]);
    assert(s1[3] == crate::spec::small_sigma1(y[3]) && s1b[3] == crate::spec::small_sigma1(y2[3]));
    assert(s0[4] == crate::spec::small_sigma0(w15[4]) && s1lo[4] == s1[4] & lo[4] && s1hi[4] == !lo[4] & s1b[4]);
    assert(s1[4] == crate::spec::small_sigma1(y[4]) && s1b[4] == crate::spec::small_sigma1(y2[4]));
    assert(s0[5] == crate::spec::small_sigma0(w15[5]) && s1lo[5] == s1[5] & lo[5] && s1hi[5] == !lo[5] & s1b[5]);
    assert(s1[5] == crate::spec::small_sigma1(y[5]) && s1b[5] == crate::spec::small_sigma1(y2[5]));
    assert(s0[6] == crate::spec::small_sigma0(w15[6]) && s1lo[6] == s1[6] & lo[6] && s1hi[6] == !lo[6] & s1b[6]);
    assert(s1[6] == crate::spec::small_sigma1(y[6]) && s1b[6] == crate::spec::small_sigma1(y2[6]));
    assert(s0[7] == crate::spec::small_sigma0(w15[7]) && s1lo[7] == s1[7] & lo[7] && s1hi[7] == !lo[7] & s1b[7]);
    assert(s1[7] == crate::spec::small_sigma1(y[7]) && s1b[7] == crate::spec::small_sigma1(y2[7]));
    lemma_block256(
        m0, tt, x0[0], x0[1], x0[2], x0[3], x1[0], x2[1], x2[2], x2[3], x3[0], x3[2], x3[3],
        v[0], v[1], v[2], v[3], r[0], r[1], r[2], r[3],
    );
    lemma_block256(
        m1, tt, x0[4], x0[5], x0[6], x0[7], x1[4], x2[5], x2[6], x2[7], x3[4], x3[6], x3[7],
        v[4], v[5], v[6], v[7], r[4], r[5], r[6], r[7],
    );
    assert(r =~= seq![
        crate::spec::schedule(m0, tt), crate::spec::schedule(m0, tt + 1), crate::spec::schedule(m0, tt + 2), crate::spec::schedule(m0, tt + 3),
        crate::spec::schedule(m1, tt), crate::spec::schedule(m1, tt + 1), crate::spec::schedule(m1, tt + 2), crate::spec::schedule(m1, tt + 3),
    ]);
}

/// One block's four words of a SHA-256 step, from the words before them:
/// a = W_{t-16..t-12}, b0 = W_{t-12}, c = W_{t-8..t-4}, d = W_{t-4..t}.
proof fn lemma_block256(
    m: Seq<u32>, tt: int,
    a0: u32, a1: u32, a2: u32, a3: u32, b0: u32, c1: u32, c2: u32, c3: u32, d0: u32, d2: u32, d3: u32,
    v0: u32, v1: u32, v2: u32, v3: u32, r0: u32, r1: u32, r2: u32, r3: u32,
)
    requires
        16 <= tt,
        a0 == crate::spec::schedule(m, tt - 16), a1 == crate::spec::schedule(m, tt - 15), a2 == crate::spec::schedule(m, tt - 14), a3 == crate::spec::schedule(m, tt - 13),
        b0 == crate::spec::schedule(m, tt - 12),
        c1 == crate::spec::schedule(m, tt - 7), c2 == crate::spec::schedule(m, tt - 6), c3 == crate::spec::schedule(m, tt - 5),
        d0 == crate::spec::schedule(m, tt - 4), d2 == crate::spec::schedule(m, tt - 2), d3 == crate::spec::schedule(m, tt - 1),
        v0 == crate::spec::add(crate::spec::add(crate::spec::add(a0, crate::spec::small_sigma0(a1)), c1), crate::spec::small_sigma1(d2) & 0xffff_ffff),
        v1 == crate::spec::add(crate::spec::add(crate::spec::add(a1, crate::spec::small_sigma0(a2)), c2), crate::spec::small_sigma1(d3) & 0xffff_ffff),
        v2 == crate::spec::add(crate::spec::add(crate::spec::add(a2, crate::spec::small_sigma0(a3)), c3), crate::spec::small_sigma1(d2) & 0),
        v3 == crate::spec::add(crate::spec::add(crate::spec::add(a3, crate::spec::small_sigma0(b0)), d0), crate::spec::small_sigma1(d3) & 0),
        r0 == crate::spec::add(v0, !0xffff_ffffu32 & crate::spec::small_sigma1(v0)),
        r1 == crate::spec::add(v1, !0xffff_ffffu32 & crate::spec::small_sigma1(v1)),
        r2 == crate::spec::add(v2, !0u32 & crate::spec::small_sigma1(v0)),
        r3 == crate::spec::add(v3, !0u32 & crate::spec::small_sigma1(v1)),
    ensures
        r0 == crate::spec::schedule(m, tt), r1 == crate::spec::schedule(m, tt + 1), r2 == crate::spec::schedule(m, tt + 2), r3 == crate::spec::schedule(m, tt + 3),
{
    hide(crate::spec::schedule);
    lemma_mask32(crate::spec::small_sigma1(d2));
    lemma_mask32(crate::spec::small_sigma1(d3));
    lemma_mask32(crate::spec::small_sigma1(v0));
    lemma_mask32(crate::spec::small_sigma1(v1));
    lemma_add4_256(0, 0, 0, v0);
    lemma_add4_256(0, 0, 0, v1);
    let t2 = crate::spec::add(crate::spec::add(a2, crate::spec::small_sigma0(a3)), c3);
    let t3 = crate::spec::add(crate::spec::add(a3, crate::spec::small_sigma0(b0)), d0);
    lemma_add4_256(0, 0, 0, t2);
    lemma_add4_256(0, 0, 0, t3);
    lemma_lane256(m, tt, a0, a1, c1, d2, v0);
    lemma_lane256(m, tt + 1, a1, a2, c2, d3, v1);
    lemma_lane256(m, tt + 2, a2, a3, c3, v0, r2);
    lemma_lane256(m, tt + 3, a3, b0, d0, v1, r3);
}

/// The window after step `s`, whose words `v` replace those of step `s - 4`.
proof fn lemma_window256(st: Sched256, st2: Sched256, m0: Seq<u32>, m1: Seq<u32>, s: int, v: __m256i)
    requires
        sched256_at(st, m0, m1, s),
        s < 16,
        holds256(v, m0, m1, 4 * s),
        st2.x@ == st.x@.update(s % 4, v),
    ensures
        sched256_at(st2, m0, m1, s + 1),
{
    assert forall|k: int| 0 <= k < 4 implies #[trigger] holds256(st2.x@[k], m0, m1, slot256(s + 1, k)) by {
        lemma_slot256_next(s, k);
        if k != s % 4 {
            assert(holds256(st.x@[k], m0, m1, slot256(s, k)));
        }
    }
}

/// Starts the SHA-256 schedule of the blocks at `o0` and `o1`.
#[inline(always)]
pub fn sched256_start(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64]) -> (r: Sched256)
    requires
        avx2(),
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
    let ghost m0 = crate::spec::words(p@.subrange(o0 as int, o0 + 64));
    let ghost m1 = crate::spec::words(p@.subrange(o1 as int, o1 + 64));
    let mut x = [_mm256_setzero_si256(); 4];
    let mut s: usize = 0;
    while s < 4
        invariant
            avx2(),
            s <= 4,
            o0 + 64 <= p@.len(),
            o1 + 64 <= p@.len(),
            m0 == crate::spec::words(p@.subrange(o0 as int, o0 + 64)),
            m1 == crate::spec::words(p@.subrange(o1 as int, o1 + 64)),
            forall|k: int| 0 <= k < s ==> #[trigger] holds256(x@[k], m0, m1, 4 * k),
            crate::compress::kw256_upto(w0@, m0, 4 * s),
            crate::compress::kw256_upto(w1@, m1, 4 * s),
        decreases 4 - s,
    {
        let v = load256(p, o0, o1, s);
        x[s] = v;
        store256(v, s, w0, w1, Ghost(m0), Ghost(m1));
        s = s + 1;
    }
    let r = Sched256 { x };
    proof {
        assert forall|k: int| 0 <= k < 4 implies #[trigger] holds256(r.x@[k], m0, m1, slot256(4, k)) by {
            assert((k - 4) % 4 == k);
        }
    }
    r
}

/// Step `s`: words `4s` to `4s + 4` of both blocks, through `barrier`.
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
    let v = next256(st, s, Ghost(m0), Ghost(m1));
    let v = barrier(v);
    let ghost st0 = *st;
    st.x[s % 4] = v;
    proof {
        lemma_window256(st0, *st, m0, m1, s as int, v);
    }
    store256(v, s, w0, w1, Ghost(m0), Ghost(m1));
}

/// The whole SHA-256 schedule of the 64-byte blocks at `o0` and `o1`.
#[inline(always)]
fn schedule256x2_body(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64])
    requires
        avx2(),
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        crate::compress::kw256_upto(final(w0)@, crate::spec::words(p@.subrange(o0 as int, o0 + 64)), 64),
        crate::compress::kw256_upto(final(w1)@, crate::spec::words(p@.subrange(o1 as int, o1 + 64)), 64),
{
    let ghost m0 = crate::spec::words(p@.subrange(o0 as int, o0 + 64));
    let ghost m1 = crate::spec::words(p@.subrange(o1 as int, o1 + 64));
    let mut st = sched256_start(p, o0, o1, w0, w1);
    sched256_step(&mut st, 4, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 5, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 6, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 7, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 8, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 9, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 10, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 11, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 12, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 13, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 14, w0, w1, Ghost(m0), Ghost(m1));
    sched256_step(&mut st, 15, w0, w1, Ghost(m0), Ghost(m1));
}

/// The whole SHA-256 schedule of the 64-byte blocks at `o0` and `o1`:
/// `schedule256x2_body` compiled with AVX2 and out of line (see
/// [`schedule512x2`]).
#[verifier::external_body]
#[inline(always)]
pub fn schedule256x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64])
    requires
        avx2(),
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        crate::compress::kw256_upto(final(w0)@, crate::spec::words(p@.subrange(o0 as int, o0 + 64)), 64),
        crate::compress::kw256_upto(final(w1)@, crate::spec::words(p@.subrange(o1 as int, o1 + 64)), 64),
{
    // SAFETY: the CPU has AVX2 (`avx2()`).
    unsafe { tf::schedule256x2(p, o0, o1, w0, w1) }
}

} // verus!

mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx2")]
    #[inline]
    pub(super) unsafe fn barrier(mut v: __m256i) -> __m256i {
        // SAFETY: an empty asm that only names the register.
        unsafe { core::arch::asm!("/* {0} */", inout(ymm_reg) v, options(nostack, preserves_flags)) };
        v
    }

    #[target_feature(enable = "avx2")]
    #[inline(never)]
    pub(super) unsafe fn schedule512x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u64; 80], w1: &mut [u64; 80]) {
        schedule512x2_body(p, o0, o1, w0, w1)
    }

    #[target_feature(enable = "avx2")]
    #[inline(never)]
    pub(super) unsafe fn schedule256x2(p: &[u8], o0: usize, o1: usize, w0: &mut [u32; 64], w1: &mut [u32; 64]) {
        schedule256x2_body(p, o0, o1, w0, w1)
    }
}
