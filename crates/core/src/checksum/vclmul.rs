//! Carry-less multiplication for the CRC-32 fold (TRUSTED, x86-64 only).
//!
//! Each function is one intrinsic, or for `x_fold`/`z_fold` the two
//! carry-less products and the XOR that make one fold step, with an
//! `ensures` stating what it computes on the 128-bit blocks of a vector
//! (`xv`, `zl`), in terms of `fold::clmul` and `fold::bytes16`. Verus takes
//! these on trust. `tests/vclmul.rs` checks each against the verified
//! scalar reference `fold::clmul_ref` on random inputs, on a CPU that has
//! the instructions.
//!
//! Each requires `pclmul()` or `vpclmul()`, which `has_pclmul()` and
//! `has_vpclmul()` ensure after run-time detection, so verified code
//! reaches them only on a CPU that has them.
#![allow(unused_imports, unused_unsafe)]
#[cfg(verus_only)]
use super::fold::{bytes16, clmul, flat, fold_with, lo64};
use core::arch::x86_64::*;
use vstd::prelude::*;

// Run-time detection needs `std`; a `no_std` build uses only the features
// the target is compiled for.
#[cfg(feature = "std")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(not(feature = "std"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

/// The CPU running this program has PCLMULQDQ (and SSE2, the x86-64
/// baseline).
pub uninterp spec fn pclmul() -> bool;

/// The CPU running this program has AVX-512F and VPCLMULQDQ.
pub uninterp spec fn vpclmul() -> bool;

/// The CPU running this program has AVX2 and VPCLMULQDQ (AMD Zen 3 and
/// Intel's cores without AVX-512, such as Alder Lake).
pub uninterp spec fn vpclmul256() -> bool;

/// VPCLMULQDQ implies PCLMULQDQ (Rust's `target_feature` implications).
pub broadcast axiom fn axiom_vpclmul_pclmul()
    ensures
        #[trigger] vpclmul() ==> pclmul(),
        #[trigger] vpclmul256() ==> pclmul(),
;

#[verifier::external_body]
#[inline]
pub fn has_pclmul() -> (r: bool)
    ensures
        r ==> pclmul(),
{
    x86_has!("pclmulqdq")
}

#[verifier::external_body]
#[inline]
pub fn has_vpclmul() -> (r: bool)
    ensures
        r ==> vpclmul(),
{
    x86_has!("avx512f") && x86_has!("vpclmulqdq") && x86_has!("pclmulqdq")
}

#[verifier::external_body]
#[inline]
pub fn has_vpclmul256() -> (r: bool)
    ensures
        r ==> vpclmul256(),
{
    x86_has!("avx2") && x86_has!("vpclmulqdq") && x86_has!("pclmulqdq")
}

/// A 128-bit vector.
#[verifier::external_body]
pub struct X128(__m128i);

/// A 256-bit vector.
#[verifier::external_body]
pub struct Y256(__m256i);

/// A 512-bit vector.
#[verifier::external_body]
pub struct Z512(__m512i);

/// The vector as a 128-bit integer, byte 0 least significant.
pub uninterp spec fn xv(x: X128) -> u128;

/// The four 128-bit blocks of the vector, lowest first, each with byte 0
/// least significant.
pub uninterp spec fn zl(z: Z512) -> Seq<u128>;

/// The two 128-bit blocks of the vector, lowest first.
pub uninterp spec fn yl(y: Y256) -> Seq<u128>;

pub broadcast axiom fn axiom_zl_len(z: Z512)
    ensures
        #[trigger] zl(z).len() == 4,
;

pub broadcast axiom fn axiom_yl_len(y: Y256)
    ensures
        #[trigger] yl(y).len() == 2,
;

pub broadcast group group_vclmul {
    axiom_vpclmul_pclmul,
    axiom_zl_len,
    axiom_yl_len,
}

// ---------------------------------------------------------------------------
// 128 bits (PCLMULQDQ, SSE2)
// ---------------------------------------------------------------------------

/// The sixteen bytes at `d[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn x_load(d: &[u8], i: usize) -> (r: X128)
    requires
        pclmul(),
        i + 16 <= d@.len(),
    ensures
        bytes16(xv(r)) == d@.subrange(i as int, i + 16),
{
    debug_assert!(i + 16 <= d.len());
    X128(unsafe { _mm_loadu_si128(d.as_ptr().add(i) as *const __m128i) })
}

#[verifier::external_body]
#[inline(always)]
pub fn x_set(v: u128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == v,
{
    X128(unsafe { _mm_set_epi64x((v >> 64) as u64 as i64, v as u64 as i64) })
}

#[verifier::external_body]
#[inline(always)]
pub fn x_get(x: &X128) -> (r: u128)
    requires
        pclmul(),
    ensures
        r == xv(*x),
{
    let lo = unsafe { _mm_cvtsi128_si64(x.0) } as u64;
    let hi = unsafe { _mm_cvtsi128_si64(_mm_unpackhi_epi64(x.0, x.0)) } as u64;
    ((hi as u128) << 64) | lo as u128
}

#[verifier::external_body]
#[inline(always)]
pub fn x_xor(a: &X128, b: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == xv(*a) ^ xv(*b),
{
    X128(unsafe { _mm_xor_si128(a.0, b.0) })
}

/// One fold step: `pclmulqdq` with immediates 0x00 and 0x11, XORed.
#[verifier::external_body]
#[inline(always)]
pub fn x_fold(a: &X128, k: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == fold_with(xv(*a), xv(*k)),
{
    X128(unsafe { _mm_xor_si128(_mm_clmulepi64_si128::<0x00>(a.0, k.0), _mm_clmulepi64_si128::<0x11>(a.0, k.0)) })
}

/// The carry-less product of the low quadwords: `pclmulqdq` with
/// immediate 0x00.
#[verifier::external_body]
#[inline(always)]
pub fn x_clmul_lo(a: &X128, k: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == clmul(lo64(xv(*a)), lo64(xv(*k))),
{
    X128(unsafe { _mm_clmulepi64_si128::<0x00>(a.0, k.0) })
}

/// The vector shifted down eight bytes (`psrldq` by 8).
#[verifier::external_body]
#[inline(always)]
pub fn x_shr64(a: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == xv(*a) >> 64u128,
{
    X128(unsafe { _mm_srli_si128::<8>(a.0) })
}

/// The vector shifted down four bytes (`psrldq` by 4).
#[verifier::external_body]
#[inline(always)]
pub fn x_shr32(a: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == xv(*a) >> 32u128,
{
    X128(unsafe { _mm_srli_si128::<4>(a.0) })
}

#[verifier::external_body]
#[inline(always)]
pub fn x_and(a: &X128, b: &X128) -> (r: X128)
    requires
        pclmul(),
    ensures
        xv(r) == xv(*a) & xv(*b),
{
    X128(unsafe { _mm_and_si128(a.0, b.0) })
}

/// The low 64 bits (`movq`).
#[verifier::external_body]
#[inline(always)]
pub fn x_low64(a: &X128) -> (r: u64)
    requires
        pclmul(),
    ensures
        r == xv(*a) as u64,
{
    (unsafe { _mm_cvtsi128_si64(a.0) }) as u64
}

// ---------------------------------------------------------------------------
// 256 bits (AVX2, VPCLMULQDQ)
// ---------------------------------------------------------------------------

/// The 32 bytes at `d[i..i + 32]`, as two blocks.
#[verifier::external_body]
#[inline(always)]
pub fn y_load(d: &[u8], i: usize) -> (r: Y256)
    requires
        vpclmul256(),
        i + 32 <= d@.len(),
    ensures
        flat(yl(r)) == d@.subrange(i as int, i + 32),
{
    debug_assert!(i + 32 <= d.len());
    Y256(unsafe { _mm256_loadu_si256(d.as_ptr().add(i) as *const __m256i) })
}

/// `c` in the low 32 bits of block 0, zero elsewhere.
#[verifier::external_body]
#[inline(always)]
pub fn y_reg(c: u32) -> (r: Y256)
    requires
        vpclmul256(),
    ensures
        yl(r) == seq![c as u128, 0u128],
{
    Y256(unsafe { _mm256_zextsi128_si256(_mm_cvtsi32_si128(c as i32)) })
}

/// `v` in both blocks.
#[verifier::external_body]
#[inline(always)]
pub fn y_splat(v: u128) -> (r: Y256)
    requires
        vpclmul256(),
    ensures
        yl(r) == seq![v, v],
{
    Y256(unsafe { _mm256_broadcastsi128_si256(_mm_set_epi64x((v >> 64) as u64 as i64, v as u64 as i64)) })
}

#[verifier::external_body]
#[inline(always)]
pub fn y_xor(a: &Y256, b: &Y256) -> (r: Y256)
    requires
        vpclmul256(),
    ensures
        yl(r) == Seq::new(2, |j: int| yl(*a)[j] ^ yl(*b)[j]),
{
    Y256(unsafe { _mm256_xor_si256(a.0, b.0) })
}

/// One fold step on each block: `vpclmulqdq` with immediates 0x00 and
/// 0x11, XORed.
#[verifier::external_body]
#[inline(always)]
pub fn y_fold(a: &Y256, k: &Y256) -> (r: Y256)
    requires
        vpclmul256(),
    ensures
        yl(r) == Seq::new(2, |j: int| fold_with(yl(*a)[j], yl(*k)[j])),
{
    Y256(unsafe {
        _mm256_xor_si256(_mm256_clmulepi64_epi128::<0x00>(a.0, k.0), _mm256_clmulepi64_epi128::<0x11>(a.0, k.0))
    })
}

/// Block `J` of the vector.
#[verifier::external_body]
#[inline(always)]
pub fn y_block<const J: i32>(a: &Y256) -> (r: X128)
    requires
        vpclmul256(),
        0 <= J < 2,
    ensures
        xv(r) == yl(*a)[J as int],
{
    X128(unsafe { _mm256_extracti128_si256::<J>(a.0) })
}

// ---------------------------------------------------------------------------
// 512 bits (AVX-512F, VPCLMULQDQ)
// ---------------------------------------------------------------------------

/// The 64 bytes at `d[i..i + 64]`, as four blocks.
#[verifier::external_body]
#[inline(always)]
pub fn z_load(d: &[u8], i: usize) -> (r: Z512)
    requires
        vpclmul(),
        i + 64 <= d@.len(),
    ensures
        flat(zl(r)) == d@.subrange(i as int, i + 64),
{
    debug_assert!(i + 64 <= d.len());
    Z512(unsafe { _mm512_loadu_si512(d.as_ptr().add(i) as *const __m512i) })
}

/// `c` in the low 32 bits of block 0, zero elsewhere.
#[verifier::external_body]
#[inline(always)]
pub fn z_reg(c: u32) -> (r: Z512)
    requires
        vpclmul(),
    ensures
        zl(r) == seq![c as u128, 0u128, 0u128, 0u128],
{
    Z512(unsafe { _mm512_zextsi128_si512(_mm_cvtsi32_si128(c as i32)) })
}

/// `v` in every block.
#[verifier::external_body]
#[inline(always)]
pub fn z_splat(v: u128) -> (r: Z512)
    requires
        vpclmul(),
    ensures
        zl(r) == seq![v, v, v, v],
{
    Z512(unsafe { _mm512_broadcast_i32x4(_mm_set_epi64x((v >> 64) as u64 as i64, v as u64 as i64)) })
}

#[verifier::external_body]
#[inline(always)]
pub fn z_xor(a: &Z512, b: &Z512) -> (r: Z512)
    requires
        vpclmul(),
    ensures
        zl(r) == Seq::new(4, |j: int| zl(*a)[j] ^ zl(*b)[j]),
{
    Z512(unsafe { _mm512_xor_si512(a.0, b.0) })
}

/// One fold step on each block: `vpclmulqdq` with immediates 0x00 and
/// 0x11, XORed.
#[verifier::external_body]
#[inline(always)]
pub fn z_fold(a: &Z512, k: &Z512) -> (r: Z512)
    requires
        vpclmul(),
    ensures
        zl(r) == Seq::new(4, |j: int| fold_with(zl(*a)[j], zl(*k)[j])),
{
    Z512(unsafe {
        _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x00>(a.0, k.0), _mm512_clmulepi64_epi128::<0x11>(a.0, k.0))
    })
}

/// Block `J` of the vector.
#[verifier::external_body]
#[inline(always)]
pub fn z_block<const J: i32>(a: &Z512) -> (r: X128)
    requires
        vpclmul(),
        0 <= J < 4,
    ensures
        xv(r) == zl(*a)[J as int],
{
    X128(unsafe { _mm512_extracti32x4_epi32::<J>(a.0) })
}

} // verus!
