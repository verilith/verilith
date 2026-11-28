//! The x86-64 instructions the kernels use, one wrapper each (TRUSTED):
//! each is one intrinsic, with an `ensures` stating what it computes in
//! the terms of [`crate::aes`] on the register as a 128-bit integer
//! (`xv`) or, for the 512-bit registers, on its four 128-bit lanes
//! (`zl`). Verus takes these on trust; `tests/isa.rs` checks each
//! against a verified reference on random inputs.
//!
//! Each requires `ni` (AES-NI, PCLMULQDQ, SSSE3, SSE4.1) or `vaes`
//! (also AVX-512F/BW/VL, VAES and VPCLMULQDQ), which [`has_ni`] and
//! [`has_vaes`] ensure after run-time detection, so verified code reaches
//! them only on a CPU that has them.
#![allow(unused_imports, unused_unsafe, unused_parens, missing_docs)]
use crate::aes::*;
use core::arch::x86_64::*;
use vstd::prelude::*;

// Run-time detection needs `std`; a `no_std` build uses only the features
// the target is compiled for.
#[cfg(feature = "std")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(not(feature = "std"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

/// The CPU has AES-NI, PCLMULQDQ, SSSE3 and SSE4.1.
pub uninterp spec fn ni() -> bool;

/// The CPU also has AVX-512F, AVX-512BW, AVX-512VL, VAES and VPCLMULQDQ.
pub uninterp spec fn vaes() -> bool;

/// Whether the CPU has what `ni` says, detected at run time.
#[verifier::external_body]
#[inline]
pub fn has_ni() -> (r: bool)
    ensures
        r ==> ni(),
{
    x86_has!("aes") && x86_has!("pclmulqdq") && x86_has!("ssse3") && x86_has!("sse4.1")
}

/// Whether the CPU has what `vaes` and `ni` say, detected at run time.
#[verifier::external_body]
#[inline]
pub fn has_vaes() -> (r: bool)
    ensures
        r ==> vaes() && ni(),
{
    x86_has!("aes") && x86_has!("pclmulqdq") && x86_has!("ssse3") && x86_has!("sse4.1") && x86_has!("avx512f")
        && x86_has!("avx512bw") && x86_has!("avx512vl") && x86_has!("vaes") && x86_has!("vpclmulqdq")
}

// ---------------------------------------------------------------------------
// 128 bits
// ---------------------------------------------------------------------------

/// A 128-bit register.
pub type X128 = __m128i;

/// The register as a 128-bit integer, byte 0 least significant.
pub uninterp spec fn xv(x: X128) -> u128;

/// The register's bytes.
pub open spec fn xb(x: X128) -> Seq<u8> {
    bytes16(xv(x))
}

/// `MOVDQU` from `d[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn x_load(d: &[u8], i: usize) -> (r: X128)
    requires
        ni(),
        i + 16 <= d@.len(),
    ensures
        xb(r) == d@.subrange(i as int, i + 16),
{
    debug_assert!(i + 16 <= d.len());
    (unsafe { _mm_loadu_si128(d.as_ptr().add(i) as *const __m128i) })
}

/// `MOVDQU` to `d[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn x_store(d: &mut [u8], i: usize, x: X128)
    requires
        ni(),
        i + 16 <= old(d)@.len(),
    ensures
        final(d)@.len() == old(d)@.len(),
        forall|k: int| 0 <= k < final(d)@.len() ==> #[trigger] final(d)@[k] == if i <= k < i + 16 {
            xb(x)[k - i]
        } else {
            old(d)@[k]
        },
{
    debug_assert!(i + 16 <= d.len());
    unsafe { _mm_storeu_si128(d.as_mut_ptr().add(i) as *mut __m128i, x) }
}

/// `MOVDQU` from a 16-byte array.
#[verifier::external_body]
#[inline(always)]
pub fn x_load16(a: &[u8; 16]) -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == a@,
{
    (unsafe { _mm_loadu_si128(a.as_ptr() as *const __m128i) })
}

/// `MOVDQU` to a 16-byte array.
#[verifier::external_body]
#[inline(always)]
pub fn x_store16(a: &mut [u8; 16], x: X128)
    requires
        ni(),
    ensures
        final(a)@ == xb(x),
{
    unsafe { _mm_storeu_si128(a.as_mut_ptr() as *mut __m128i, x) }
}

/// `MOVDQU` from `a[i]`: a `u128` in memory is its bytes, least
/// significant first.
#[verifier::external_body]
#[inline(always)]
pub fn x_load_u128(a: &[u128], i: usize) -> (r: X128)
    requires
        ni(),
        i < a@.len(),
    ensures
        xv(r) == a@[i as int],
{
    debug_assert!(i < a.len());
    (unsafe { _mm_loadu_si128(a.as_ptr().add(i) as *const __m128i) })
}

/// The register holding `v`.
#[verifier::external_body]
#[inline(always)]
pub fn x_set(v: u128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == v,
{
    (unsafe { _mm_set_epi64x((v >> 64) as u64 as i64, v as u64 as i64) })
}

/// The register as a `u128`.
#[verifier::external_body]
#[inline(always)]
pub fn x_get(x: X128) -> (r: u128)
    requires
        ni(),
    ensures
        r == xv(x),
{
    let lo = unsafe { _mm_cvtsi128_si64(x) } as u64;
    let hi = unsafe { _mm_extract_epi64::<1>(x) } as u64;
    ((hi as u128) << 64) | lo as u128
}

/// `PXOR`.
#[verifier::external_body]
#[inline(always)]
pub fn x_xor(a: X128, b: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == xv(a) ^ xv(b),
{
    (unsafe { _mm_xor_si128(a, b) })
}

/// `AESENC`.
#[verifier::external_body]
#[inline(always)]
pub fn x_aesenc(a: X128, k: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == aesenc(xb(a), xb(k)),
{
    (unsafe { _mm_aesenc_si128(a, k) })
}

/// `AESENCLAST`.
#[verifier::external_body]
#[inline(always)]
pub fn x_aesenclast(a: X128, k: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == aesenclast(xb(a), xb(k)),
{
    (unsafe { _mm_aesenclast_si128(a, k) })
}

/// `PCLMULQDQ` with immediate `IMM`.
#[verifier::external_body]
#[inline(always)]
pub fn x_clmul<const IMM: i32>(a: X128, b: X128) -> (r: X128)
    requires
        ni(),
        IMM == 0x00 || IMM == 0x01 || IMM == 0x10 || IMM == 0x11,
    ensures
        xv(r) == pclmul(xv(a), xv(b), IMM),
{
    (unsafe { _mm_clmulepi64_si128::<IMM>(a, b) })
}

/// `PSHUFB`.
#[verifier::external_body]
#[inline(always)]
pub fn x_pshufb(a: X128, m: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == pshufb(xb(a), xb(m)),
{
    (unsafe { _mm_shuffle_epi8(a, m) })
}

/// `PADDD`.
#[verifier::external_body]
#[inline(always)]
pub fn x_add32(a: X128, b: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == add32x4(xv(a), xv(b)),
{
    (unsafe { _mm_add_epi32(a, b) })
}

/// `PSLLQ` by `N`.
#[verifier::external_body]
#[inline(always)]
pub fn x_sll64<const N: i32>(a: X128) -> (r: X128)
    requires
        ni(),
        0 <= N < 64,
    ensures
        xv(r) == sll64x2(xv(a), N as u64),
{
    (unsafe { _mm_slli_epi64::<N>(a) })
}

/// `PSRLQ` by `N`.
#[verifier::external_body]
#[inline(always)]
pub fn x_srl64<const N: i32>(a: X128) -> (r: X128)
    requires
        ni(),
        0 <= N < 64,
    ensures
        xv(r) == srl64x2(xv(a), N as u64),
{
    (unsafe { _mm_srli_epi64::<N>(a) })
}

/// `PSLLDQ` by 8 bytes: the low half moved to the high half.
#[verifier::external_body]
#[inline(always)]
pub fn x_bsll8(a: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == xv(a) << 64u128,
{
    (unsafe { _mm_slli_si128::<8>(a) })
}

/// `PSRLDQ` by 8 bytes: the high half moved to the low half.
#[verifier::external_body]
#[inline(always)]
pub fn x_bsrl8(a: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == xv(a) >> 64u128,
{
    (unsafe { _mm_srli_si128::<8>(a) })
}


// ---------------------------------------------------------------------------
// 512 bits (AVX-512, VAES, VPCLMULQDQ)
// ---------------------------------------------------------------------------

/// A 512-bit register.
pub type Z512 = __m512i;

/// The register's four 128-bit lanes, lane 0 (bits 127:0) first, each as
/// [`xv`] sees a 128-bit register.
pub uninterp spec fn zl(z: Z512) -> Seq<u128>;

pub broadcast axiom fn axiom_zl_len(z: Z512)
    ensures
        #[trigger] zl(z).len() == 4,
;

/// The bytes of lane l.
pub open spec fn zb(z: Z512, l: int) -> Seq<u8> {
    bytes16(zl(z)[l])
}

/// `VMOVDQU64` from `d[i..i + 64]`.
#[verifier::external_body]
#[inline(always)]
pub fn z_load(d: &[u8], i: usize) -> (r: Z512)
    requires
        vaes(),
        i + 64 <= d@.len(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r, l) == d@.subrange(i + 16 * l, i + 16 * l + 16),
{
    debug_assert!(i + 64 <= d.len());
    unsafe { _mm512_loadu_si512(d.as_ptr().add(i) as *const _) }
}

/// `VMOVDQU64` to `d[i..i + 64]`.
#[verifier::external_body]
#[inline(always)]
pub fn z_store(d: &mut [u8], i: usize, z: Z512)
    requires
        vaes(),
        i + 64 <= old(d)@.len(),
    ensures
        final(d)@.len() == old(d)@.len(),
        forall|k: int| 0 <= k < final(d)@.len() ==> #[trigger] final(d)@[k] == if i <= k < i + 64 {
            zb(z, (k - i) / 16)[(k - i) % 16]
        } else {
            old(d)@[k]
        },
{
    debug_assert!(i + 64 <= d.len());
    unsafe { _mm512_storeu_si512(d.as_mut_ptr().add(i) as *mut _, z) }
}

/// `VMOVDQU64` from `a[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn z_load_u128(a: &[u128], i: usize) -> (r: Z512)
    requires
        vaes(),
        i + 4 <= a@.len(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == a@[i + l],
{
    debug_assert!(i + 4 <= a.len());
    unsafe { _mm512_loadu_si512(a.as_ptr().add(i) as *const _) }
}

/// `VBROADCASTI32X4` of `a[i]`: it in every lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_bcast(a: &[u128], i: usize) -> (r: Z512)
    requires
        vaes(),
        i < a@.len(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == a@[i as int],
{
    debug_assert!(i < a.len());
    unsafe { _mm512_broadcast_i32x4(_mm_loadu_si128(a.as_ptr().add(i) as *const __m128i)) }
}

/// `VBROADCASTI32X4` of a register.
#[verifier::external_body]
#[inline(always)]
pub fn z_bcast_x(x: X128) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == xv(x),
{
    unsafe { _mm512_broadcast_i32x4(x) }
}

/// The register with `x` in lane 0 and zeros above (`VMOVDQA xmm`).
#[verifier::external_body]
#[inline(always)]
pub fn z_from_x(x: X128) -> (r: Z512)
    requires
        vaes(),
    ensures
        zl(r)[0] == xv(x),
        zl(r)[1] == 0,
        zl(r)[2] == 0,
        zl(r)[3] == 0,
{
    unsafe { _mm512_zextsi128_si512(x) }
}

/// Lane `L` (`VEXTRACTI32X4`).
#[verifier::external_body]
#[inline(always)]
pub fn z_lane<const L: i32>(z: Z512) -> (r: X128)
    requires
        vaes(),
        0 <= L < 4,
    ensures
        xv(r) == zl(z)[L as int],
{
    unsafe { _mm512_extracti32x4_epi32::<L>(z) }
}

/// `VPXORQ`.
#[verifier::external_body]
#[inline(always)]
pub fn z_xor(a: Z512, b: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == zl(a)[l] ^ zl(b)[l],
{
    unsafe { _mm512_xor_si512(a, b) }
}

/// `VAESENC`, on each lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_aesenc(a: Z512, k: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r, l) == aesenc(zb(a, l), zb(k, l)),
{
    unsafe { _mm512_aesenc_epi128(a, k) }
}

/// `VAESENCLAST`, on each lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_aesenclast(a: Z512, k: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r, l) == aesenclast(zb(a, l), zb(k, l)),
{
    unsafe { _mm512_aesenclast_epi128(a, k) }
}

/// `VPCLMULQDQ` with immediate `IMM`, on each lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_clmul<const IMM: i32>(a: Z512, b: Z512) -> (r: Z512)
    requires
        vaes(),
        IMM == 0x00 || IMM == 0x01 || IMM == 0x10 || IMM == 0x11,
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == pclmul(zl(a)[l], zl(b)[l], IMM),
{
    unsafe { _mm512_clmulepi64_epi128::<IMM>(a, b) }
}

/// `VPSHUFB`, on each lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_pshufb(a: Z512, m: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r, l) == pshufb(zb(a, l), zb(m, l)),
{
    unsafe { _mm512_shuffle_epi8(a, m) }
}

/// `VPADDD`, on each lane.
#[verifier::external_body]
#[inline(always)]
pub fn z_add32(a: Z512, b: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == add32x4(zl(a)[l], zl(b)[l]),
{
    unsafe { _mm512_add_epi32(a, b) }
}

/// `VPTERNLOGQ` with immediate 0x96: `a ^ b ^ c`.
#[verifier::external_body]
#[inline(always)]
pub fn z_xor3(a: Z512, b: Z512, c: Z512) -> (r: Z512)
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == zl(a)[l] ^ zl(b)[l] ^ zl(c)[l],
{
    unsafe { _mm512_ternarylogic_epi64::<0x96>(a, b, c) }
}

} // verus!
