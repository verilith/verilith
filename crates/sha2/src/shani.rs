//! The SHA-256 kernel with the x86-64 SHA extensions (SHA-NI), proven to
//! compute FIPS 180-4's H(n) over the specifications of `SHA256RNDS2`,
//! `SHA256MSG1` and `SHA256MSG2` in [`crate::isa`] and verilith-simd's of
//! the SSE intrinsics.
//!
//! The method is Intel's ("New Instructions Supporting the Secure Hash
//! Algorithm on Intel Architecture Processors", 2013). `sha256rnds2` keeps
//! the working variables as two vectors, (a, b, e, f) and (c, d, g, h),
//! most significant lane first, and does two rounds; so four rounds are two
//! of them, the second with the other two words of K + W and the vectors'
//! roles swapped. `sha256msg1`, an `alignr` and `sha256msg2` compute the
//! next four words of the schedule.
//!
//! Trusted here: the three instruction wrappers and `pblendw`'s (each one
//! intrinsic, with the specification of [`crate::isa`]), run-time detection
//! (`has_shani`), and the trampoline that compiles [`compress_blocks_body`]
//! with the SHA extensions enabled.
use crate::isa;
use crate::lanes::*;
use crate::sha_lemmas::*;
use crate::spec::{self, Vars, K};
use verilith_simd::arch::*;
#[cfg(verus_only)]
use verilith_simd::cpu::{sse41, ssse3};
use verilith_simd::lanes::*;
use verilith_simd::mem::{load128_u32, load128_u8, store128_u32};
use verilith_simd::ops::*;
use vstd::prelude::*;

// Run-time detection needs `std`; a `no_std` build uses only the features
// the target is compiled for.
#[cfg(feature = "std")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(not(feature = "std"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// The CPU running this program has the SHA extensions.
pub uninterp spec fn shani() -> bool;

/// Whether the CPU has the SHA extensions and SSE4.1 (and so SSSE3),
/// detected at run time.
#[verifier::external_body]
#[inline]
pub fn has_shani() -> (r: bool)
    ensures
        r ==> shani() && sse41() && ssse3(),
{
    x86_has!("sha") && x86_has!("sse4.1")
}

/// [`_mm_sha256rnds2_epu32`](core::arch::x86_64::_mm_sha256rnds2_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256rnds2(a: __m128i, b: __m128i, k: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256rnds2(u32x4(a), u32x4(b), u32x4(k)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256rnds2_epu32(a, b, k) }
}

/// [`_mm_sha256msg1_epu32`](core::arch::x86_64::_mm_sha256msg1_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256msg1(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256msg1(u32x4(a), u32x4(b)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256msg1_epu32(a, b) }
}

/// [`_mm_sha256msg2_epu32`](core::arch::x86_64::_mm_sha256msg2_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256msg2(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256msg2(u32x4(a), u32x4(b)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256msg2_epu32(a, b) }
}

/// [`_mm_blend_epi16`](core::arch::x86_64::_mm_blend_epi16).
#[verifier::external_body]
#[inline(always)]
pub fn blend_epi16<const IMM8: i32>(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        sse41(),
        0 <= IMM8 <= 255,
    ensures
        b128(r) == isa::blend16(b128(a), b128(b), IMM8 as int),
{
    // SAFETY: the CPU has SSE4.1 (the precondition).
    unsafe { core::arch::x86_64::_mm_blend_epi16::<IMM8>(a, b) }
}

// ---------------------------------------------------------------------------
// Proof
// ---------------------------------------------------------------------------

/// The working variables in `sha256rnds2`'s two vectors: `abef` is
/// (f, e, b, a) and `cdgh` is (h, g, d, c), lane 0 first.
pub open spec fn vars_of(abef: Seq<u32>, cdgh: Seq<u32>) -> Vars {
    Vars { a: abef[3], b: abef[2], c: cdgh[3], d: cdgh[2], e: abef[1], f: abef[0], g: cdgh[1], h: cdgh[0] }
}

/// The same as a hash value, a to h.
pub open spec fn hv(abef: Seq<u32>, cdgh: Seq<u32>) -> Seq<u32> {
    seq![abef[3], abef[2], cdgh[3], cdgh[2], abef[1], abef[0], cdgh[1], cdgh[0]]
}

/// `v` holds W_t to W_{t+3} of block words `m`.
#[verifier::opaque]
pub open spec fn holds(v: __m128i, m: Seq<u32>, t: int) -> bool {
    u32x4(v) == seq![spec::schedule(m, t), spec::schedule(m, t + 1), spec::schedule(m, t + 2), spec::schedule(m, t + 3)]
}

spec fn rs(v: Vars) -> isa::Rnds2 {
    isa::Rnds2 { a: v.a, b: v.b, c: v.c, d: v.d, e: v.e, f: v.f, g: v.g, h: v.h }
}

/// The SDM's Ch, Maj, Σ0 and Σ1 are FIPS 180-4's.
proof fn lemma_funcs(e: u32, f: u32, g: u32)
    ensures
        isa::x_ch(e, f, g) == spec::ch(e, f, g),
        isa::x_maj(e, f, g) == spec::maj(e, f, g),
        isa::x_big_s0(e) == spec::big_sigma0(e),
        isa::x_big_s1(e) == spec::big_sigma1(e),
{
}

/// Five words added in two orders.
proof fn lemma_add5(ch: u32, s1: u32, k: u32, w: u32, h: u32)
    ensures
        spec::add(spec::add(spec::add(ch, s1), spec::add(k, w)), h) == spec::add(spec::add(spec::add(spec::add(h, s1), ch), k), w),
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(ch + s1, k + w, M32);
    lemma_mod_add(ch + s1 + k + w, h as int);
    lemma_mod_add(h + s1, ch as int);
    lemma_mod_add(h + s1 + ch, k as int);
    lemma_mod_add(h + s1 + ch + k, w as int);
}

/// (T + Maj) + Σ0 = T + (Σ0 + Maj).
proof fn lemma_add3(t: u32, mj: u32, s0: u32)
    ensures
        spec::add(spec::add(t, mj), s0) == spec::add(t, spec::add(s0, mj)),
{
    lemma_mod_add(t + mj, s0 as int);
    lemma_mod_add(t as int, s0 + mj);
}

/// One iteration of `SHA256RNDS2`'s loop, with WK = K + W, is one round.
proof fn lemma_step(v: Vars, k: u32, w: u32)
    ensures
        isa::rnds2_step(rs(v), spec::add(k, w)) == rs(spec::round(v, k, w)),
{
    hide(spec::ch);
    hide(spec::maj);
    hide(spec::big_sigma0);
    hide(spec::big_sigma1);
    hide(isa::x_ch);
    hide(isa::x_maj);
    hide(isa::x_big_s0);
    hide(isa::x_big_s1);
    lemma_funcs(v.e, v.f, v.g);
    lemma_funcs(v.a, v.b, v.c);
    let ch = spec::ch(v.e, v.f, v.g);
    let s1 = spec::big_sigma1(v.e);
    let s0 = spec::big_sigma0(v.a);
    let mj = spec::maj(v.a, v.b, v.c);
    lemma_add5(ch, s1, k, w, v.h);
    let t = spec::add(spec::add(spec::add(ch, s1), spec::add(k, w)), v.h);
    lemma_add3(t, mj, s0);
}

/// `sha256rnds2(cdgh, abef, wk)` is two rounds, with K + W in `wk`'s two
/// low lanes; the vector it returns is the new (a, b, e, f), and `abef`
/// becomes (c, d, g, h).
proof fn lemma_rnds2(abef: Seq<u32>, cdgh: Seq<u32>, wk: Seq<u32>, k0: u32, w0: u32, k1: u32, w1: u32)
    requires
        abef.len() == 4,
        cdgh.len() == 4,
        wk.len() == 4,
        wk[0] == spec::add(k0, w0),
        wk[1] == spec::add(k1, w1),
    ensures
        vars_of(isa::sha256rnds2(cdgh, abef, wk), abef) == spec::round(spec::round(vars_of(abef, cdgh), k0, w0), k1, w1),
{
    hide(isa::rnds2_step);
    hide(spec::round);
    hide(spec::add);
    let v = vars_of(abef, cdgh);
    lemma_step(v, k0, w0);
    lemma_step(spec::round(v, k0, w0), k1, w1);
    lemma_round_shift(v, k0, w0);
    lemma_round_shift(spec::round(v, k0, w0), k1, w1);
    assert(isa::sha256rnds2(cdgh, abef, wk).len() == 4);
}

/// The SDM's σ0 and σ1 are FIPS 180-4's.
proof fn lemma_sigmas(x: u32)
    ensures
        isa::x_small_s0(x) == spec::small_sigma0(x),
        isa::x_small_s1(x) == spec::small_sigma1(x),
{
}

/// Four terms added in two orders.
proof fn lemma_add4(a: u32, b: u32, c: u32, d: u32)
    ensures
        spec::add(spec::add(spec::add(a, b), c), d) == spec::add(spec::add(spec::add(d, c), b), a),
{
    lemma_mod_add(a + b, c as int);
    lemma_mod_add(a + b + c, d as int);
    lemma_mod_add(d + c, b as int);
    lemma_mod_add(d + c + b, a as int);
}

/// The four rounds of [`rounds4`], on lanes.
proof fn lemma_rounds4(ab: Seq<u32>, cd: Seq<u32>, tv: Seq<u32>, c2: Seq<u32>, t2: Seq<u32>, a2: Seq<u32>, ti: int, v0: Vars, m: Seq<u32>)
    requires
        ab.len() == 4,
        cd.len() == 4,
        tv.len() == 4,
        0 <= ti,
        ti + 4 <= 64,
        forall|j: int| 0 <= j < 4 ==> #[trigger] tv[j] == spec::add(K[ti + j], spec::schedule(m, ti + j)),
        t2 == seq![tv[2], tv[3], tv[0], tv[0]],
        c2 == isa::sha256rnds2(cd, ab, tv),
        a2 == isa::sha256rnds2(ab, c2, t2),
        vars_of(ab, cd) == spec::rounds(v0, m, ti as nat),
    ensures
        vars_of(a2, c2) == spec::rounds(v0, m, (ti + 4) as nat),
{
    hide(isa::sha256rnds2);
    hide(spec::round);
    hide(spec::schedule);
    hide(spec::add);
    assert(tv[0] == spec::add(K[ti + 0], spec::schedule(m, ti + 0)));
    assert(tv[1] == spec::add(K[ti + 1], spec::schedule(m, ti + 1)));
    assert(tv[2] == spec::add(K[ti + 2], spec::schedule(m, ti + 2)));
    assert(tv[3] == spec::add(K[ti + 3], spec::schedule(m, ti + 3)));
    lemma_rnds2(ab, cd, tv, K[ti], spec::schedule(m, ti), K[ti + 1], spec::schedule(m, ti + 1));
    assert(c2.len() == 4) by {
        reveal(isa::sha256rnds2);
    }
    lemma_rnds2(c2, ab, t2, K[ti + 2], spec::schedule(m, ti + 2), K[ti + 3], spec::schedule(m, ti + 3));
    assert(spec::rounds(v0, m, (ti + 1) as nat) == spec::round(spec::rounds(v0, m, ti as nat), K[ti], spec::schedule(m, ti)));
    assert(spec::rounds(v0, m, (ti + 2) as nat) == spec::round(spec::rounds(v0, m, (ti + 1) as nat), K[ti + 1], spec::schedule(m, ti + 1)));
    assert(spec::rounds(v0, m, (ti + 3) as nat) == spec::round(spec::rounds(v0, m, (ti + 2) as nat), K[ti + 2], spec::schedule(m, ti + 2)));
    assert(spec::rounds(v0, m, (ti + 4) as nat) == spec::round(spec::rounds(v0, m, (ti + 3) as nat), K[ti + 3], spec::schedule(m, ti + 3)));
}

/// Rounds 4i to 4i + 3 with W_{4i..4i+3} in `w`.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds4(abef: &mut __m128i, cdgh: &mut __m128i, w: __m128i, i: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u32>>)
    requires
        shani(),
        i < 16,
        holds(w, m, 4 * i),
        vars_of(u32x4(*old(abef)), u32x4(*old(cdgh))) == spec::rounds(v0, m, (4 * i) as nat),
    ensures
        vars_of(u32x4(*final(abef)), u32x4(*final(cdgh))) == spec::rounds(v0, m, (4 * i + 4) as nat),
{
    hide(isa::sha256rnds2);
    hide(spec::round);
    hide(spec::rounds);
    hide(spec::schedule);
    hide(shuffle32_lanes);
    let k = load128_u32(K.as_slice(), 4 * i);
    let t = _mm_add_epi32(w, k);
    let c2 = sha256rnds2(*cdgh, *abef, t);
    let t2 = _mm_shuffle_epi32::<0x0e>(t);
    let a2 = sha256rnds2(*abef, c2, t2);
    proof {
        reveal(holds);
        let ti = 4 * i as int;
        lemma_shuffle32_consts(u32x4(t));
        let tv = u32x4(t);
        assert forall|j: int| 0 <= j < 4 implies #[trigger] tv[j] == spec::add(K[ti + j], spec::schedule(m, ti + j)) by {
            assert(u32x4(k)[j] == K@[ti + j]);
            assert(u32x4(w)[j] == spec::schedule(m, ti + j));
        }
        lemma_rounds4(u32x4(*abef), u32x4(*cdgh), tv, u32x4(c2), u32x4(t2), u32x4(a2), ti, v0, m);
    }
    *cdgh = c2;
    *abef = a2;
}

/// The schedule step of [`schedule`], on lanes.
proof fn lemma_schedule(w0: Seq<u32>, w1: Seq<u32>, w2: Seq<u32>, w3: Seq<u32>, z: Seq<u32>, r: Seq<u32>, m: Seq<u32>, t: int)
    requires
        0 <= t,
        w0 == sched4(m, t),
        w1 == sched4(m, t + 4),
        w2 == sched4(m, t + 8),
        w3 == sched4(m, t + 12),
        z.len() == 4,
        forall|j: int| 0 <= j < 4 ==> #[trigger] z[j] == spec::add(isa::sha256msg1(w0, w1)[j], seq![w2[1], w2[2], w2[3], w3[0]][j]),
        r == isa::sha256msg2(z, w3),
    ensures
        r == sched4(m, t + 16),
{
    hide(spec::small_sigma0);
    hide(spec::small_sigma1);
    hide(isa::x_small_s0);
    hide(isa::x_small_s1);
    hide(spec::schedule);
    hide(spec::add);
    hide(isa::add32);
    let s = |j: int| spec::schedule(m, t + j);
    lemma_sched_unfold(m, t);
    lemma_add32_eq(s(0), spec::small_sigma0(s(1)));
    lemma_add32_eq(s(1), spec::small_sigma0(s(2)));
    lemma_add32_eq(s(2), spec::small_sigma0(s(3)));
    lemma_add32_eq(s(3), spec::small_sigma0(s(4)));
    lemma_add32_eq(z[0], spec::small_sigma1(s(14)));
    lemma_add32_eq(z[1], spec::small_sigma1(s(15)));
    lemma_add32_eq(z[2], spec::small_sigma1(s(16)));
    lemma_add32_eq(z[3], spec::small_sigma1(s(17)));
    lemma_sigmas(s(1));
    lemma_sigmas(s(2));
    lemma_sigmas(s(3));
    lemma_sigmas(s(4));
    lemma_sigmas(s(14));
    lemma_sigmas(s(15));
    lemma_sigmas(s(16));
    lemma_sigmas(s(17));
    assert(z[0] == spec::add(spec::add(s(0), spec::small_sigma0(s(1))), s(9)));
    assert(z[1] == spec::add(spec::add(s(1), spec::small_sigma0(s(2))), s(10)));
    assert(z[2] == spec::add(spec::add(s(2), spec::small_sigma0(s(3))), s(11)));
    assert(z[3] == spec::add(spec::add(s(3), spec::small_sigma0(s(4))), s(12)));
    lemma_add4(s(0), spec::small_sigma0(s(1)), s(9), spec::small_sigma1(s(14)));
    lemma_add4(s(1), spec::small_sigma0(s(2)), s(10), spec::small_sigma1(s(15)));
    assert(r[0] == s(16));
    assert(r[1] == s(17));
    lemma_add4(s(2), spec::small_sigma0(s(3)), s(11), spec::small_sigma1(s(16)));
    lemma_add4(s(3), spec::small_sigma0(s(4)), s(12), spec::small_sigma1(s(17)));
    assert(r[2] == s(18));
    assert(r[3] == s(19));
    assert(r =~= sched4(m, t + 16));
}

/// W_{t+16..t+20} from the four vectors before them.
#[verifier::spinoff_prover]
#[inline(always)]
fn schedule(w0: __m128i, w1: __m128i, w2: __m128i, w3: __m128i, Ghost(m): Ghost<Seq<u32>>, Ghost(t): Ghost<int>) -> (r: __m128i)
    requires
        shani(),
        ssse3(),
        0 <= t,
        holds(w0, m, t),
        holds(w1, m, t + 4),
        holds(w2, m, t + 8),
        holds(w3, m, t + 12),
    ensures
        holds(r, m, t + 16),
{
    let x = sha256msg1(w0, w1);
    let y = _mm_alignr_epi8::<4>(w3, w2);
    let z = _mm_add_epi32(x, y);
    let r = sha256msg2(z, w3);
    proof {
        reveal(holds);
        lemma_alignr4_x4(b128(w3), b128(w2));
        assert(u32x4(w0) == sched4(m, t));
        assert(u32x4(w1) == sched4(m, t + 4));
        assert(u32x4(w2) == sched4(m, t + 8));
        assert(u32x4(w3) == sched4(m, t + 12));
        lemma_schedule(u32x4(w0), u32x4(w1), u32x4(w2), u32x4(w3), u32x4(z), u32x4(r), m, t);
    }
    r
}

/// The words of the block at `off` as four vectors of big-endian words.
#[verifier::spinoff_prover]
#[inline(always)]
fn load_words(p: &[u8], off: usize, j: usize, bswap: __m128i) -> (r: __m128i)
    requires
        ssse3(),
        j < 4,
        off + 64 <= p@.len(),
        b128(bswap) == bswap32_mask16(),
    ensures
        holds(r, spec::words(p@.subrange(off as int, off + 64)), 4 * j),
{
    let _n = p.len();
    let r = _mm_shuffle_epi8(load128_u8(p, off + 16 * j), bswap);
    proof {
        reveal(holds);
        let blk = p@.subrange(off as int, off + 64);
        let src = p@.subrange(off + 16 * j, off + 16 * j + 16);
        lemma_bswap32_x4(src, b128(bswap));
        let m = spec::words(blk);
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32x4(r)[i] == spec::schedule(m, 4 * j + i) by {
            assert(spec::be32(src, 4 * i) == spec::be32(blk, 4 * (4 * j + i)));
        }
        assert(u32x4(r) =~= seq![
            spec::schedule(m, 4 * j as int), spec::schedule(m, 4 * j + 1), spec::schedule(m, 4 * j + 2), spec::schedule(m, 4 * j + 3)
        ]);
    }
    r
}

/// One block: H(i) from H(i-1) in `abef` and `cdgh`.
#[verifier::spinoff_prover]
#[inline(always)]
fn block(abef: &mut __m128i, cdgh: &mut __m128i, p: &[u8], off: usize, bswap: __m128i)
    requires
        shani(),
        sse41(),
        ssse3(),
        off + 64 <= p@.len(),
        b128(bswap) == bswap32_mask16(),
    ensures
        hv(u32x4(*final(abef)), u32x4(*final(cdgh))) == spec::compress(
            hv(u32x4(*old(abef)), u32x4(*old(cdgh))),
            p@.subrange(off as int, off + 64),
        ),
{
    let ghost blk = p@.subrange(off as int, off + 64);
    let ghost m = spec::words(blk);
    let ghost h0 = hv(u32x4(*abef), u32x4(*cdgh));
    let ghost v0 = spec::init(h0);
    let (abef0, cdgh0) = (*abef, *cdgh);
    let mut w0 = load_words(p, off, 0, bswap);
    let mut w1 = load_words(p, off, 1, bswap);
    let mut w2 = load_words(p, off, 2, bswap);
    let mut w3 = load_words(p, off, 3, bswap);
    assert(vars_of(u32x4(*abef), u32x4(*cdgh)) == spec::rounds(v0, m, 0));
    rounds4(abef, cdgh, w0, 0, Ghost(v0), Ghost(m));
    rounds4(abef, cdgh, w1, 1, Ghost(v0), Ghost(m));
    rounds4(abef, cdgh, w2, 2, Ghost(v0), Ghost(m));
    rounds4(abef, cdgh, w3, 3, Ghost(v0), Ghost(m));
    let mut i: usize = 4;
    while i < 16
        invariant
            shani(),
            sse41(),
            ssse3(),
            4 <= i <= 16,
            holds(w0, m, 4 * i - 16),
            holds(w1, m, 4 * i - 12),
            holds(w2, m, 4 * i - 8),
            holds(w3, m, 4 * i - 4),
            vars_of(u32x4(*abef), u32x4(*cdgh)) == spec::rounds(v0, m, (4 * i) as nat),
        decreases 16 - i,
    {
        let w4 = schedule(w0, w1, w2, w3, Ghost(m), Ghost(4 * i - 16));
        rounds4(abef, cdgh, w4, i, Ghost(v0), Ghost(m));
        w0 = w1;
        w1 = w2;
        w2 = w3;
        w3 = w4;
        i = i + 1;
    }
    *abef = _mm_add_epi32(*abef, abef0);
    *cdgh = _mm_add_epi32(*cdgh, cdgh0);
    proof {
        reveal(spec::compress);
        assert(hv(u32x4(*abef), u32x4(*cdgh)) =~= spec::compress(h0, blk));
    }
}

/// The `pshufb` control that reads each 32-bit lane big-endian.
#[verifier::spinoff_prover]
#[inline(always)]
fn bswap_mask() -> (r: __m128i)
    ensures
        b128(r) == bswap32_mask16(),
{
    let r = _mm_setr_epi8(3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12);
    assert(b128(r) =~= bswap32_mask16());
    r
}

/// The state in `sha256rnds2`'s layout: (f, e, b, a) and (h, g, d, c).
#[verifier::spinoff_prover]
#[inline(always)]
fn load_state(st: &[u32; 8]) -> (r: (__m128i, __m128i))
    requires
        sse41(),
        ssse3(),
    ensures
        hv(u32x4(r.0), u32x4(r.1)) == st@,
{
    let dcba = load128_u32(st, 0);
    let hgfe = load128_u32(st, 4);
    let cdab = _mm_shuffle_epi32::<0xb1>(dcba);
    let efgh = _mm_shuffle_epi32::<0x1b>(hgfe);
    let abef = _mm_alignr_epi8::<8>(cdab, efgh);
    let cdgh = blend_epi16::<0xf0>(efgh, cdab);
    proof {
        lemma_shuffle32_consts(u32x4(dcba));
        lemma_shuffle32_consts(u32x4(hgfe));
        lemma_alignr8_x4(b128(cdab), b128(efgh));
        lemma_blend_f0(b128(efgh), b128(cdab));
        assert(hv(u32x4(abef), u32x4(cdgh)) =~= st@);
    }
    (abef, cdgh)
}

/// Stores the state back in order, a to h.
#[verifier::spinoff_prover]
#[inline(always)]
fn store_state(st: &mut [u32; 8], abef: __m128i, cdgh: __m128i)
    requires
        sse41(),
        ssse3(),
    ensures
        final(st)@ == hv(u32x4(abef), u32x4(cdgh)),
{
    hide(isa::blend16);
    hide(shuffle32_lanes);
    hide(alignr_lanes);
    let feba = _mm_shuffle_epi32::<0x1b>(abef);
    let dchg = _mm_shuffle_epi32::<0xb1>(cdgh);
    let dcba = blend_epi16::<0xf0>(feba, dchg);
    let hgfe = _mm_alignr_epi8::<8>(dchg, feba);
    proof {
        lemma_shuffle32_consts(u32x4(abef));
        lemma_shuffle32_consts(u32x4(cdgh));
        lemma_blend_f0(b128(feba), b128(dchg));
        lemma_alignr8_x4(b128(dchg), b128(feba));
        let (x, y) = (u32x4(abef), u32x4(cdgh));
        assert(u32x4(dcba) == seq![x[3], x[2], y[3], y[2]]);
        assert(u32x4(hgfe) == seq![x[1], x[0], y[1], y[0]]);
    }
    store128_u32(st, 0, dcba);
    store128_u32(st, 4, hgfe);
    assert(st@ =~= hv(u32x4(abef), u32x4(cdgh)));
}

/// H(n) from H(0) = `st` over the `n = p.len() / 64` whole blocks of `p`.
/// Run through [`compress_blocks`], which compiles it with the SHA
/// extensions enabled.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress_blocks_body(st: &mut [u32; 8], p: &[u8])
    requires
        shani(),
        sse41(),
        ssse3(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    let ghost h0 = st@;
    // Big-endian words from little-endian lanes.
    let bswap = bswap_mask();
    let (mut abef, mut cdgh) = load_state(st);
    let n = p.len() / 64;
    let mut j: usize = 0;
    while j < n
        invariant
            shani(),
            sse41(),
            ssse3(),
            b128(bswap) == bswap32_mask16(),
            n == p@.len() / 64,
            p@.len() <= usize::MAX,
            j <= n,
            hv(u32x4(abef), u32x4(cdgh)) == spec::hash_blocks(h0, p@, j as nat),
        decreases n - j,
    {
        block(&mut abef, &mut cdgh, p, 64 * j, bswap);
        j = j + 1;
    }
    store_state(st, abef, cdgh);
}

/// [`compress_blocks_body`] compiled with the SHA extensions (trusted only
/// to be that function).
#[verifier::external_body]
#[inline]
pub fn compress_blocks(st: &mut [u32; 8], p: &[u8])
    requires
        shani(),
        sse41(),
        ssse3(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    // SAFETY: the CPU has SHA-NI and SSE4.1 (the precondition).
    unsafe { tf::compress_blocks(st, p) }
}

} // verus!

mod tf {
    /// Never inlined: the SHA instructions have only legacy SSE encodings,
    /// and run many times slower while the upper halves of the YMM
    /// registers are dirty (seen as about 5 µs per call on an AVX-512
    /// Xeon). Built with AVX2 enabled (`target-cpu=native`), the callers
    /// use 256-bit stores, and inlined into them this ran after those with
    /// no `vzeroupper` in between. A call gets one: LLVM puts a
    /// `vzeroupper` before every call made with the upper halves dirty.
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        super::compress_blocks_body(st, p)
    }
}
