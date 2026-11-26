//! A lane-level model of the x86 SIMD instructions the parser uses.
//!
//! The register types, their lane views and the specification of each
//! instruction are vsimd's (trusted there, and tested there against the
//! CPU). Each function here wraps one or two instructions and proves, from
//! vsimd's specification, the contract the rest of the parser is verified
//! against. The AVX2 and AVX-512 ones require vsimd's CPU-feature
//! predicate.
//!
//! What this file still trusts (`external_body`): the two stores of a
//! vector register into a `Vec`'s reserved space (`append16_spare`,
//! `append16_spare_neon`), stated with verilith-core's model of capacity
//! (`verilith_core::spare`), and `opaque64`.
#[allow(unused_imports)]
use crate::spec::*;
use vstd::prelude::*;

// The 16-byte SSE2 wrappers and `bit`, shared with verilith-xml.
pub use verilith_simd::sse2::*;
// The model of a `Vec`'s spare capacity, and the stores into it.
pub use verilith_core::spare::*;

#[cfg(target_arch = "x86_64")]
use verilith_simd::arch::*;
#[cfg(target_arch = "x86_64")]
#[allow(unused_imports)]
use verilith_simd::avx512::*;
#[cfg(target_arch = "x86_64")]
#[allow(unused_imports)]
use verilith_simd::mem::*;
#[allow(unused_imports)]
use verilith_simd::cpu::*;
#[allow(unused_imports)]
use verilith_simd::lanes::*;
#[allow(unused_imports)]
use verilith_simd::mask as vm;
#[allow(unused_imports)]
use verilith_simd::ops as vo;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

/// Bit `k` of a 64-bit mask.
pub open spec fn bit64(m: u64, k: u64) -> bool {
    (m >> k) & 1u64 == 1u64
}

/// The positions `base + k` of the set bits `k < j` of `m`, in order.
pub open spec fn bits_upto(m: u64, base: int, j: int) -> Seq<u32>
    decreases j,
{
    if j <= 0 {
        Seq::empty()
    } else {
        let p = bits_upto(m, base, j - 1);
        if bit64(m, (j - 1) as u64) {
            p.push((base + j - 1) as u32)
        } else {
            p
        }
    }
}

// ---------------------------------------------------------------------------
// Scalar instructions
// ---------------------------------------------------------------------------

/// `bits_upto` is vsimd's `set_bits`, offset by `base`.
pub proof fn lemma_bits_same(m: u64, base: int, j: int)
    requires
        0 <= j <= 64,
        0 <= base,
        base + 64 <= u32::MAX,
    ensures
        bits_upto(m, base, j).len() == vo::set_bits(m, j as nat).len(),
        forall|i: int|
            0 <= i < bits_upto(m, base, j).len() ==> #[trigger] bits_upto(m, base, j)[i] == (base + vo::set_bits(
                m,
                j as nat,
            )[i]) as u32,
    decreases j,
{
    if j > 0 {
        lemma_bits_same(m, base, j - 1);
    }
}

/// `popcnt`: the number of set bits.
#[inline(always)]
pub fn popcnt64(m: u64) -> (r: u32)
    ensures
        r == bits_upto(m, 0, 64).len(),
{
    proof {
        lemma_bits_same(m, 0, 64);
    }
    verilith_simd::scalar::popcnt64(m)
}

/// Carry-less multiplication: the XOR of `a << i` over the set bits `i`
/// of `b`, below bit `n`.
pub open spec fn clmul_upto(a: u64, b: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        0
    } else {
        clmul_upto(a, b, (n - 1) as nat) ^ (if bit64(b, (n - 1) as u64) {
            a << ((n - 1) as u64)
        } else {
            0
        })
    }
}

pub proof fn lemma_clmul_same(a: u64, b: u64, n: nat)
    ensures
        clmul_upto(a, b, n) == vo::clmul_lo(a, b, n),
    decreases n,
{
    if n > 0 {
        lemma_clmul_same(a, b, (n - 1) as nat);
    }
}

/// `pclmulqdq` on the low quadwords, low half of the product.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn clmul_lo(a: u64, b: u64) -> (r: u64)
    requires
        pclmul(),
    ensures
        r == clmul_upto(a, b, 64),
{
    let x = _mm_cvtsi64_si128(i64_of(a));
    let y = _mm_cvtsi64_si128(i64_of(b));
    let p = _mm_clmulepi64_si128::<0>(x, y);
    proof {
        lemma_clmul_same(a, b, 64);
    }
    u64_from(_mm_cvtsi128_si64(p))
}

/// The identity, hidden from LLVM. LLVM otherwise rewrites bit arithmetic
/// on movemask results into slow per-lane vector code.
#[verifier::external_body]
#[inline(always)]
pub fn opaque64(x: u64) -> (r: u64)
    ensures
        r == x,
{
    #[allow(unused_mut)] // Only x86_64 writes it.
    let mut m = x;
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) m, options(pure, nomem, nostack));
    }
    m
}

// ---------------------------------------------------------------------------
// Vec capacity: verilith-core's model (`verilith_core::spare`), and the
// two stores of a vector register into reserved space
// ---------------------------------------------------------------------------

/// A 16-byte store of the NEON vector `a` into reserved space, keeping the
/// first `n` bytes. (Off AArch64, where `uint8x16_t` is vsimd's emulation,
/// it copies the bytes.)
#[verifier::external_body]
#[inline(always)]
pub fn append16_spare_neon(v: &mut Vec<u8>, a: verilith_simd::neon::uint8x16_t, n: usize)
    requires
        spare(*old(v)) >= 16,
        n <= 16,
    ensures
        final(v)@ == old(v)@ + verilith_simd::neon::n8(a).subrange(0, n as int),
        spare(*final(v)) == spare(*old(v)) - n,
{
    #[cfg(target_arch = "aarch64")]
    unsafe {
        let l = v.len();
        core::arch::aarch64::vst1q_u8(v.as_mut_ptr().add(l), a);
        v.set_len(l + n);
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let mut t = [0u8; 16];
        verilith_simd::neon::vst1q_u8_at(&mut t, 0, a);
        v.extend_from_slice(&t[..n]);
    }
}

} // verus!

// ---------------------------------------------------------------------------
// SIMD registers
// ---------------------------------------------------------------------------

#[cfg(target_arch = "x86_64")]
verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::avx512::axiom_b512_len, verilith_simd::cpu::group_cpu};

// The register types and their lane views are vsimd's. The names below
// are this crate's older ones for them.

/// The 32 bytes of a 256-bit register.
pub open spec fn b32(v: __m256i) -> Seq<u8> {
    b256(v)
}

/// The 64 bytes of a 512-bit register.
pub open spec fn b64(v: __m512i) -> Seq<u8> {
    b512(v)
}

/// The 16 dwords of a 512-bit register.
pub open spec fn d16(v: __m512i) -> Seq<u32> {
    u32x16(v)
}

#[inline(always)]
fn i32_of(c: u32) -> (r: i32)
    ensures
        vo::u32_of_i32(r) == c,
{
    if c < 0x8000_0000 {
        c as i32
    } else {
        (c as i64 - 0x1_0000_0000) as i32
    }
}

#[inline(always)]
fn i64_of(c: u64) -> (r: i64)
    ensures
        vo::u64_of_i64(r) == c,
{
    if c < 0x8000_0000_0000_0000 {
        c as i64
    } else {
        (c as i128 - 0x1_0000_0000_0000_0000) as i64
    }
}

#[inline(always)]
fn u64_from(x: i64) -> (r: u64)
    ensures
        r == vo::u64_of_i64(x),
{
    if x >= 0 {
        x as u64
    } else {
        (x as i128 + 0x1_0000_0000_0000_0000) as u64
    }
}

proof fn lemma_wrapping_sub8(a: u8, b: u8)
    ensures
        a.wrapping_sub(b) == ((a - b + 256) % 256) as u8,
{
}

proof fn lemma_wrapping_add32(a: u32, b: u32)
    ensures
        a.wrapping_add(b) == ((a + b) % 0x1_0000_0000) as u32,
{
}

/// A logical shift of the word lanes right by 4, masked to the low
/// nibble of each byte, is each byte's high nibble.
proof fn lemma_nibhi(a: Seq<u8>, t: Seq<u8>, r: Seq<u8>)
    requires
        a.len() % 2 == 0,
        t.len() == a.len(),
        r.len() == a.len(),
        u16s(t) == vo::srli16(u16s(a), 4),
        r == vo::and8(t, vo::splat8(0x0Fu8, a.len())),
    ensures
        r =~= Seq::new(a.len(), |k: int| a[k] / 16),
{
    assert(vo::pow2_spec(4) == 16) by {
        reveal_with_fuel(vo::pow2_spec, 5);
    }
    assert forall|k: int| 0 <= k < a.len() implies r[k] == a[k] / 16 by {
        let i = k / 2;
        lemma_u16_lane_bytes(a, i);
        lemma_u16_lane_bytes(t, i);
        let x = u16s(a)[i];
        let y = u16s(t)[i];
        assert(y == vo::srli16(u16s(a), 4)[i]);
        assert(y == x / 16);
        assert(r[k] == t[k] & 0x0Fu8);
        if k % 2 == 0 {
            assert(k == 2 * i);
            assert((((y & 0xff) as u8) & 0x0Fu8) == ((x & 0xff) as u8) / 16) by (bit_vector)
                requires
                    y == x / 16,
            ;
        } else {
            assert(k == 2 * i + 1);
            assert(((((y >> 8u16) & 0xff) as u8) & 0x0Fu8) == (((x >> 8u16) & 0xff) as u8) / 16) by (bit_vector)
                requires
                    y == x / 16,
            ;
        }
    }
}

/// Lanes 0 to 63.
pub const IOTA64: [u8; 64] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
    58, 59, 60, 61, 62, 63,
];

/// Sixteen `0xFF` bytes, then sixteen zeros.
pub const MASK_FIRST: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

// --- SSE2 -----------------------------------------------------------------

/// A 16-byte store of `a` into reserved space, keeping the first `n`
/// bytes.
#[verifier::external_body]
#[inline(always)]
pub fn append16_spare(v: &mut Vec<u8>, a: __m128i, n: usize)
    requires
        spare(*old(v)) >= 16,
        n <= 16,
    ensures
        final(v)@ == old(v)@ + b16(a).subrange(0, n as int),
        spare(*final(v)) == spare(*old(v)) - n,
{
    let l = v.len();
    unsafe {
        _mm_storeu_si128(v.as_mut_ptr().add(l) as *mut __m128i, a);
        v.set_len(l + n);
    }
}

/// `pmaxub`: unsigned maximum.
#[inline(always)]
pub fn max16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| if b16(a)[k] >= b16(b)[k] { b16(a)[k] } else { b16(b)[k] }),
{
    let r = _mm_max_epu8(a, b);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| if b16(a)[k] >= b16(b)[k] { b16(a)[k] } else { b16(b)[k] }));
    }
    r
}

/// `psubb`: wrapping subtraction.
#[inline(always)]
pub fn sub16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| b16(a)[k].wrapping_sub(b16(b)[k])),
{
    let r = _mm_sub_epi8(a, b);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] b16(r)[k] == b16(a)[k].wrapping_sub(b16(b)[k]) by {
            lemma_wrapping_sub8(b16(a)[k], b16(b)[k]);
        }
        assert(b16(r) =~= Seq::new(16, |k: int| b16(a)[k].wrapping_sub(b16(b)[k])));
    }
    r
}

// --- AVX2 -----------------------------------------------------------------

/// `vmovdqu`: `s[i..i + 32]`.
#[inline(always)]
pub fn load32(s: &[u8], i: usize) -> (r: __m256i)
    requires
        avx2(),
        i + 32 <= s@.len(),
    ensures
        b32(r) == s@.subrange(i as int, i + 32),
{
    let r = load256_u8(s, i);
    proof {
        assert(b32(r) =~= s@.subrange(i as int, i + 32));
    }
    r
}

/// Every lane is `c`.
#[inline(always)]
pub fn splat32(c: u8) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| c),
{
    let r = _mm256_set1_epi8(i8_of(c));
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| c));
    }
    r
}

/// `vpcmpeqb`: `0xFF` where the lanes are equal, else 0.
#[inline(always)]
pub fn eq32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| if b32(a)[k] == b32(b)[k] { 0xFFu8 } else { 0u8 }),
{
    let r = _mm256_cmpeq_epi8(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| if b32(a)[k] == b32(b)[k] { 0xFFu8 } else { 0u8 }));
    }
    r
}

/// `vpor`.
#[inline(always)]
pub fn or32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| b32(a)[k] | b32(b)[k]),
{
    let r = _mm256_or_si256(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| b32(a)[k] | b32(b)[k]));
    }
    r
}

/// `vpmaxub`: unsigned maximum.
#[inline(always)]
pub fn max32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| if b32(a)[k] >= b32(b)[k] { b32(a)[k] } else { b32(b)[k] }),
{
    let r = _mm256_max_epu8(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| if b32(a)[k] >= b32(b)[k] { b32(a)[k] } else { b32(b)[k] }));
    }
    r
}

/// `vpmovmskb`: bit `k` is the top bit of lane `k`.
#[inline(always)]
pub fn movemask32(a: __m256i) -> (r: u32)
    requires
        avx2(),
    ensures
        forall|k: u32| k < 32 ==> #[trigger] bit(r, k) == (b32(a)[k as int] >= 0x80),
{
    let m = _mm256_movemask_epi8(a);
    let r = u32_from(m);
    proof {
        vm::lemma_movemask_bits(b256(a), r as u64);
        assert forall|k: u32| k < 32 implies #[trigger] bit(r, k) == (b32(a)[k as int] >= 0x80) by {
            assert(vm::bit64(r as u64, k as int) == (b256(a)[k as int] >= 128));
            lemma_bit_u32(r, k);
        }
    }
    r
}

/// `vbroadcasti128` of a 16-byte table: lane `k` is `t[k % 16]`.
#[inline(always)]
pub fn table32(t: &[u8; 16]) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| t@[k % 16]),
{
    let x = load128_u8(t.as_slice(), 0);
    let r = _mm256_broadcastsi128_si256(x);
    proof {
        assert(b128(x) =~= t@);
        assert(b32(r) =~= Seq::new(32, |k: int| t@[k % 16]));
    }
    r
}

/// `vpshufb`: within each 16-lane half, lane `k` is the lane of `t` that
/// the low four bits of `v[k]` pick, or zero when `v[k]` has its top bit set.
#[inline(always)]
pub fn shuffle32(t: __m256i, v: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r).len() == 32,
        forall|k: int|
            0 <= k < 32 ==> #[trigger] b32(r)[k] == if b32(v)[k] >= 0x80 {
                0u8
            } else {
                b32(t)[k / 16 * 16 + b32(v)[k] % 16]
            },
{
    _mm256_shuffle_epi8(t, v)
}

// --- AVX-512 --------------------------------------------------------------

/// `vmovdqu8`: `s[i..i + 64]`.
#[inline(always)]
pub fn load64(s: &[u8], i: usize) -> (r: __m512i)
    requires
        avx512bw(),
        i + 64 <= s@.len(),
    ensures
        b64(r) == s@.subrange(i as int, i + 64),
{
    let r = load512_u8(s, i);
    proof {
        assert(b64(r) =~= s@.subrange(i as int, i + 64));
    }
    r
}

/// Every lane is `c`.
#[inline(always)]
pub fn splat64(c: u8) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| c),
{
    let r = _mm512_set1_epi8(i8_of(c));
    proof {
        assert(b64(r) =~= Seq::new(64, |k: int| c));
    }
    r
}

/// Lane `k` is `k`.
#[inline(always)]
pub fn iota64() -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| k as u8),
{
    let r = load512_u8(IOTA64.as_slice(), 0);
    proof {
        assert(b64(r) =~= IOTA64@);
        assert(b64(r) =~= Seq::new(64, |k: int| k as u8));
    }
    r
}

/// `vbroadcasti32x4` of a 16-byte table: lane `k` is `t[k % 16]`.
#[inline(always)]
pub fn table64(t: &[u8; 16]) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| t@[k % 16]),
{
    let x = load128_u8(t.as_slice(), 0);
    let r = _mm512_broadcast_i32x4(x);
    proof {
        assert(b128(x) =~= t@);
        assert(b64(r) =~= Seq::new(64, |k: int| t@[k % 16]));
    }
    r
}

/// `vpshufb`: within each 16-lane group, lane `k` is the lane of `t` that
/// the low four bits of `v[k]` pick, or zero when `v[k]` has its top bit set.
#[inline(always)]
pub fn shuffle64(t: __m512i, v: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r).len() == 64,
        forall|k: int|
            0 <= k < 64 ==> #[trigger] b64(r)[k] == if b64(v)[k] >= 0x80 {
                0u8
            } else {
                b64(t)[k / 16 * 16 + b64(v)[k] % 16]
            },
{
    _mm512_shuffle_epi8(t, v)
}

/// `vpord`.
#[inline(always)]
pub fn or64(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| b64(a)[k] | b64(b)[k]),
{
    let r = _mm512_or_si512(a, b);
    proof {
        assert(b64(r) =~= Seq::new(64, |k: int| b64(a)[k] | b64(b)[k]));
    }
    r
}

/// `vpcmpeqb` into a mask register.
#[inline(always)]
pub fn eq_mask64(a: __m512i, b: __m512i) -> (r: u64)
    requires
        avx512bw(),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(r, k) == (b64(a)[k as int] == b64(b)[k as int]),
{
    let r = _mm512_cmpeq_epi8_mask(a, b);
    proof {
        let c = vo::cmpeq8(b512(a), b512(b));
        vm::lemma_movemask_bits(c, r);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(r, k) == (b64(a)[k as int] == b64(b)[k as int]) by {
            assert(vm::bit64(r, k as int) == (c[k as int] >= 128));
        }
    }
    r
}

/// `vpcmpub` with "less or equal" into a mask register.
#[inline(always)]
pub fn le_mask64(a: __m512i, b: __m512i) -> (r: u64)
    requires
        avx512bw(),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(r, k) == (b64(a)[k as int] <= b64(b)[k as int]),
{
    let r = _mm512_cmple_epu8_mask(a, b);
    proof {
        let c = vo::cmple_u8(b512(a), b512(b));
        vm::lemma_movemask_bits(c, r);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(r, k) == (b64(a)[k as int] <= b64(b)[k as int]) by {
            assert(vm::bit64(r, k as int) == (c[k as int] >= 128));
        }
    }
    r
}

/// `vpcompressb` with zero masking: the lanes of `a` that `m` selects,
/// packed into the low lanes in order; the other lanes are zero.
#[inline(always)]
pub fn compress64(m: u64, a: __m512i) -> (r: __m512i)
    requires
        avx512vbmi2(),
    ensures
        b64(r).len() == 64,
        forall|j: int|
            0 <= j < 64 ==> #[trigger] b64(r)[j] == if j < bits_upto(m, 0, 64).len() {
                b64(a)[bits_upto(m, 0, 64)[j] as int]
            } else {
                0u8
            },
{
    let r = _mm512_maskz_compress_epi8(m, a);
    proof {
        lemma_bits_same(m, 0, 64);
        verilith_simd::refs::lemma_set_bits(m, 64);
    }
    r
}

/// Bytes `16 * n .. 16 * n + 16` (`vextracti32x4`, or a register rename
/// for `n == 0`).
#[inline(always)]
pub fn extract128(a: __m512i, n: usize) -> (r: __m128i)
    requires
        avx512bw(),
        n < 4,
    ensures
        b16(r) == b64(a).subrange(16 * n as int, 16 * n + 16),
{
    match n {
        0 => _mm512_castsi512_si128(a),
        1 => _mm512_extracti32x4_epi32::<1>(a),
        2 => _mm512_extracti32x4_epi32::<2>(a),
        _ => _mm512_extracti32x4_epi32::<3>(a),
    }
}

/// `vpmovzxbd`: zero-extends 16 bytes to 16 dwords.
#[inline(always)]
pub fn widen16(a: __m128i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        d16(r) == Seq::new(16, |k: int| b16(a)[k] as u32),
{
    let r = _mm512_cvtepu8_epi32(a);
    proof {
        assert(d16(r) =~= Seq::new(16, |k: int| b16(a)[k] as u32));
    }
    r
}

/// `vpaddd` with a broadcast: adds `b` to every dword.
#[inline(always)]
pub fn add_d16(a: __m512i, b: u32) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        d16(r) == Seq::new(16, |k: int| d16(a)[k].wrapping_add(b)),
{
    let r = _mm512_add_epi32(a, _mm512_set1_epi32(i32_of(b)));
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] d16(r)[k] == d16(a)[k].wrapping_add(b) by {
            lemma_wrapping_add32(d16(a)[k], b);
        }
        assert(d16(r) =~= Seq::new(16, |k: int| d16(a)[k].wrapping_add(b)));
    }
    r
}

/// `vmovdqu32` to `v[at..at + 16]`.
#[inline(always)]
pub fn store_d16(v: &mut Vec<u32>, at: usize, a: __m512i)
    requires
        avx512bw(),
        at + 16 <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int|
            0 <= j < old(v)@.len() ==> #[trigger] final(v)@[j] == if at <= j < at + 16 {
                d16(a)[j - at]
            } else {
                old(v)@[j]
            },
{
    store512_u32(v.as_mut_slice(), at, a);
}


// --- Used by the UTF-8 validator ------------------------------------------

/// `vpand`.
#[inline(always)]
pub fn and32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| b32(a)[k] & b32(b)[k]),
{
    let r = _mm256_and_si256(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| b32(a)[k] & b32(b)[k]));
    }
    r
}

/// `vpxor`.
#[inline(always)]
pub fn xor32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| b32(a)[k] ^ b32(b)[k]),
{
    let r = _mm256_xor_si256(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| b32(a)[k] ^ b32(b)[k]));
    }
    r
}

/// `vpsubusb`: unsigned subtraction, saturating at 0.
#[inline(always)]
pub fn subs32(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| if b32(a)[k] >= b32(b)[k] { (b32(a)[k] - b32(b)[k]) as u8 } else { 0u8 }),
{
    let r = _mm256_subs_epu8(a, b);
    proof {
        assert(b32(r) =~= Seq::new(32, |k: int| if b32(a)[k] >= b32(b)[k] { (b32(a)[k] - b32(b)[k]) as u8 } else { 0u8 }));
    }
    r
}

/// The high nibble of each byte (`vpsrlw` by 4, then `vpand` with 0x0F).
#[inline(always)]
pub fn nibhi32(a: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        b32(r) == Seq::new(32, |k: int| b32(a)[k] / 16),
{
    let t = _mm256_srli_epi16::<4>(a);
    let r = _mm256_and_si256(t, _mm256_set1_epi8(0x0F));
    proof {
        lemma_nibhi(b256(a), b256(t), b256(r));
    }
    r
}

/// `vptest`: whether `a & b` is zero in every lane.
#[inline(always)]
pub fn testz32(a: __m256i, b: __m256i) -> (r: bool)
    requires
        avx2(),
    ensures
        r == forall|k: int| 0 <= k < 32 ==> #[trigger] (b32(a)[k] & b32(b)[k]) == 0,
{
    let z = _mm256_testz_si256(a, b);
    proof {
        let c = vo::and8(b256(a), b256(b));
        if z == 1 {
            assert forall|k: int| 0 <= k < 32 implies #[trigger] (b32(a)[k] & b32(b)[k]) == 0 by {
                assert(c[k] == 0u8);
            }
        }
        if forall|k: int| 0 <= k < 32 ==> #[trigger] (b32(a)[k] & b32(b)[k]) == 0 {
            assert forall|i: int| 0 <= i < 32 implies #[trigger] c[i] == 0u8 by {
                assert((b32(a)[i] & b32(b)[i]) == 0);
            }
        }
    }
    z == 1
}

/// `vpandd`.
#[inline(always)]
pub fn and64(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| b64(a)[k] & b64(b)[k]),
{
    let r = _mm512_and_si512(a, b);
    proof {
        assert(b64(r) =~= Seq::new(64, |k: int| b64(a)[k] & b64(b)[k]));
    }
    r
}

/// `vpxord`.
#[inline(always)]
pub fn xor64(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| b64(a)[k] ^ b64(b)[k]),
{
    let r = _mm512_xor_si512(a, b);
    proof {
        assert(b64(r) =~= Seq::new(64, |k: int| b64(a)[k] ^ b64(b)[k]));
    }
    r
}

/// `vpsubusb`: unsigned subtraction, saturating at 0.
#[inline(always)]
pub fn subs64(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| if b64(a)[k] >= b64(b)[k] { (b64(a)[k] - b64(b)[k]) as u8 } else { 0u8 }),
{
    let r = _mm512_subs_epu8(a, b);
    proof {
        assert(b64(r) =~= Seq::new(64, |k: int| if b64(a)[k] >= b64(b)[k] { (b64(a)[k] - b64(b)[k]) as u8 } else { 0u8 }));
    }
    r
}

/// The high nibble of each byte (`vpsrlw` by 4, then `vpandd` with 0x0F).
#[inline(always)]
pub fn nibhi64(a: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b64(r) == Seq::new(64, |k: int| b64(a)[k] / 16),
{
    let t = _mm512_srli_epi16::<4>(a);
    let r = _mm512_and_si512(t, _mm512_set1_epi8(0x0F));
    proof {
        lemma_nibhi(b512(a), b512(t), b512(r));
    }
    r
}

// --- SSE2 words, for combining digits ------------------------------------

/// The eight 16-bit lanes of a 128-bit register, signed.
pub open spec fn w16(v: __m128i) -> Seq<i16> {
    Seq::new(8, |k: int| s16(u16x8(v)[k]) as i16)
}

/// The four 32-bit lanes of a 128-bit register, signed.
pub open spec fn w32(v: __m128i) -> Seq<i32> {
    Seq::new(4, |k: int| s32(u32x4(v)[k]) as i32)
}

/// `x` modulo 2^32, as a signed dword.
pub open spec fn wrap32(x: int) -> i32 {
    s32((x % 0x1_0000_0000) as u32) as i32
}

/// A signed dword's bits, as an unsigned number.
pub open spec fn u32v(x: i32) -> int {
    if x < 0 {
        x + 0x1_0000_0000
    } else {
        x as int
    }
}

/// `movdqu` from a constant table: `0xFF` in the first `n` byte lanes, 0
/// in the rest.
#[inline(always)]
pub fn mask_first16(n: usize) -> (r: __m128i)
    requires
        n <= 16,
    ensures
        b16(r) == Seq::new(16, |k: int| if k < n { 0xFFu8 } else { 0u8 }),
{
    let r = load128_u8(MASK_FIRST.as_slice(), 16 - n);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| if k < n { 0xFFu8 } else { 0u8 }));
    }
    r
}

/// `pand`.
#[inline(always)]
pub fn and16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| b16(a)[k] & b16(b)[k]),
{
    let r = _mm_and_si128(a, b);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| b16(a)[k] & b16(b)[k]));
    }
    r
}

/// `punpcklbw` with zero: the low eight byte lanes, zero-extended to words.
#[inline(always)]
pub fn widen_lo16(a: __m128i) -> (r: __m128i)
    ensures
        w16(r) == Seq::new(8, |k: int| b16(a)[k] as i16),
{
    let r = _mm_unpacklo_epi8(a, _mm_setzero_si128());
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] w16(r)[k] == b16(a)[k] as i16 by {
            assert(b128(r)[2 * k] == b128(a)[k]);
            assert(b128(r)[2 * k + 1] == 0u8);
            lemma_le16_value(b128(r)[2 * k], b128(r)[2 * k + 1]);
        }
        assert(w16(r) =~= Seq::new(8, |k: int| b16(a)[k] as i16));
    }
    r
}

/// `punpckhbw` with zero: the high eight byte lanes, zero-extended.
#[inline(always)]
pub fn widen_hi16(a: __m128i) -> (r: __m128i)
    ensures
        w16(r) == Seq::new(8, |k: int| b16(a)[k + 8] as i16),
{
    let r = _mm_unpackhi_epi8(a, _mm_setzero_si128());
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] w16(r)[k] == b16(a)[k + 8] as i16 by {
            assert(b128(r)[2 * k] == b128(a)[k + 8]);
            assert(b128(r)[2 * k + 1] == 0u8);
            lemma_le16_value(b128(r)[2 * k], b128(r)[2 * k + 1]);
        }
        assert(w16(r) =~= Seq::new(8, |k: int| b16(a)[k + 8] as i16));
    }
    r
}

/// Words `x, y` repeated four times.
#[inline(always)]
pub fn pair16(x: i16, y: i16) -> (r: __m128i)
    ensures
        w16(r) == Seq::new(8, |k: int| if k % 2 == 0 { x } else { y }),
{
    let r = _mm_setr_epi16(x, y, x, y, x, y, x, y);
    proof {
        let u = u16x8(r);
        assert(u[0] == vo::u16_of_i16(x) && u[2] == u[0] && u[4] == u[0] && u[6] == u[0]);
        assert(u[1] == vo::u16_of_i16(y) && u[3] == u[1] && u[5] == u[1] && u[7] == u[1]);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] w16(r)[k] == (if k % 2 == 0 { x } else { y }) by {
            assert(u[k] == (if k % 2 == 0 { vo::u16_of_i16(x) } else { vo::u16_of_i16(y) }));
        }
        assert(w16(r) =~= Seq::new(8, |k: int| if k % 2 == 0 { x } else { y }));
    }
    r
}

/// `pmaddwd`: each dword lane is the sum of the products of its two word
/// lanes (signed), wrapping.
#[inline(always)]
pub fn madd16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        w32(r) == Seq::new(4, |k: int|
            wrap32(w16(a)[2 * k] * w16(b)[2 * k] + w16(a)[2 * k + 1] * w16(b)[2 * k + 1])),
{
    let r = _mm_madd_epi16(a, b);
    proof {
        assert(w32(r) =~= Seq::new(
            4,
            |k: int| wrap32(w16(a)[2 * k] * w16(b)[2 * k] + w16(a)[2 * k + 1] * w16(b)[2 * k + 1]),
        ));
    }
    r
}

/// A dword saturated to a signed word.
pub open spec fn sat16(x: i32) -> i16 {
    if x > 32767 { 32767i16 } else if x < -32768 { -32768i16 } else { x as i16 }
}

/// `packssdw`: the dwords of `a` then of `b`, saturated to words.
#[inline(always)]
pub fn packs16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        w16(r) == Seq::new(8, |k: int| if k < 4 { sat16(w32(a)[k]) } else { sat16(w32(b)[k - 4]) }),
{
    let r = _mm_packs_epi32(a, b);
    proof {
        assert(w16(r) =~= Seq::new(8, |k: int| if k < 4 { sat16(w32(a)[k]) } else { sat16(w32(b)[k - 4]) }));
    }
    r
}

/// `movq`: the low 64 bits, dword 0 low.
#[inline(always)]
pub fn low64(a: __m128i) -> (r: u64)
    ensures
        r as int == u32v(w32(a)[0]) + u32v(w32(a)[1]) * 0x1_0000_0000,
{
    let r = u64_from(_mm_cvtsi128_si64(a));
    proof {
        let (w0, w1) = (u32x4(a)[0], u32x4(a)[1]);
        assert(u64x2(a)[0] == le64(w0, w1));
        assert((w0 as u64) | ((w1 as u64) << 32u64) == (w0 as u64) + (w1 as u64) * 0x1_0000_0000) by (bit_vector);
    }
    r
}

/// `vptestmb`: whether `a & b` is zero in every lane.
#[inline(always)]
pub fn testz64(a: __m512i, b: __m512i) -> (r: bool)
    requires
        avx512bw(),
    ensures
        r == forall|k: int| 0 <= k < 64 ==> #[trigger] (b64(a)[k] & b64(b)[k]) == 0,
{
    let m = _mm512_test_epi8_mask(a, b);
    proof {
        let c = vo::testm8(b512(a), b512(b));
        vm::lemma_movemask_zero(c);
        if m == 0 {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] (b64(a)[k] & b64(b)[k]) == 0 by {
                assert(c[k] < 128);
            }
        }
        if forall|k: int| 0 <= k < 64 ==> #[trigger] (b64(a)[k] & b64(b)[k]) == 0 {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] c[k] < 128 by {
                assert((b64(a)[k] & b64(b)[k]) == 0);
            }
        }
    }
    m == 0
}

} // verus!
