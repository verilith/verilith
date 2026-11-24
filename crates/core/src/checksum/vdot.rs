//! Byte dot products for the Adler-32 kernels (TRUSTED, x86-64 only).
//!
//! Each function is one intrinsic, or for `yd_dot` the two (`vpmaddubsw`
//! then `vpmaddwd` by ones) and the add that make one dot-product step,
//! with an `ensures` stating what it computes on the vector's bytes (`zb`,
//! `yb`) or 32-bit lanes (`zd`, `yd`), in terms of `adlerv::dot4`. Verus
//! takes these on trust. `tests/vdot.rs` checks each against a plain
//! reference on random inputs, on a CPU that has the instructions.
//!
//! Each requires `vnni512()` or `avx2()`, which `has_vnni512()` and
//! `has_avx2()` ensure after run-time detection.
#![allow(unused_imports, unused_unsafe)]
#[cfg(verus_only)]
use super::adlerv::dot4;
use core::arch::x86_64::*;
use vstd::prelude::*;

#[cfg(feature = "std")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(not(feature = "std"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

/// The CPU running this program has AVX-512F, AVX-512BW and AVX-512 VNNI.
pub uninterp spec fn vnni512() -> bool;

/// The CPU running this program has AVX2.
pub uninterp spec fn avx2() -> bool;

/// Whether the CPU has AVX-512F, AVX-512BW and AVX-512 VNNI, detected at run time.
///
/// ```text
/// ensures  r ==> vnni512()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_vnni512() -> (r: bool)
    ensures
        r ==> vnni512(),
{
    x86_has!("avx512f") && x86_has!("avx512bw") && x86_has!("avx512vnni")
}

/// Whether the CPU has AVX2, detected at run time.
///
/// ```text
/// ensures  r ==> avx2()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_avx2() -> (r: bool)
    ensures
        r ==> avx2(),
{
    x86_has!("avx2")
}

/// 64 bytes.
#[verifier::external_body]
pub struct ZB(__m512i);

/// Sixteen 32-bit lanes.
#[verifier::external_body]
pub struct ZD(__m512i);

/// 32 bytes.
#[verifier::external_body]
pub struct YB(__m256i);

/// Eight 32-bit lanes.
#[verifier::external_body]
pub struct YD(__m256i);

pub uninterp spec fn zb(x: ZB) -> Seq<u8>;

pub uninterp spec fn zd(x: ZD) -> Seq<u32>;

pub uninterp spec fn yb(x: YB) -> Seq<u8>;

pub uninterp spec fn yd(x: YD) -> Seq<u32>;

pub broadcast axiom fn axiom_lens(a: ZB, b: ZD, c: YB, e: YD)
    ensures
        #[trigger] zb(a).len() == 64,
        #[trigger] zd(b).len() == 16,
        #[trigger] yb(c).len() == 32,
        #[trigger] yd(e).len() == 8,
;

/// The axioms of this module, for `broadcast use group_vdot`.
pub broadcast group group_vdot {
    axiom_lens,
}

/// `a + b` in a 32-bit lane, wrapping.
pub open spec fn add32(a: int, b: int) -> u32 {
    super::vdot_add32(a, b)
}

// ---------------------------------------------------------------------------
// 512 bits (AVX-512 VNNI)
// ---------------------------------------------------------------------------

/// The 64 bytes at `d[i..i + 64]`.
///
/// ```text
/// requires vnni512()
///          i + 64 <= d@.len()
/// ensures  zb(r) == d@.subrange(i as int, i + 64)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn zb_load(d: &[u8], i: usize) -> (r: ZB)
    requires
        vnni512(),
        i + 64 <= d@.len(),
    ensures
        zb(r) == d@.subrange(i as int, i + 64),
{
    debug_assert!(i + 64 <= d.len());
    ZB(unsafe { _mm512_loadu_si512(d.as_ptr().add(i) as *const __m512i) })
}

/// Sixteen zero lanes.
///
/// ```text
/// requires vnni512()
/// ensures  zd(r) == Seq::new(16, |j: int| 0u32)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn zd_zero() -> (r: ZD)
    requires
        vnni512(),
    ensures
        zd(r) == Seq::new(16, |j: int| 0u32),
{
    ZD(unsafe { _mm512_setzero_si512() })
}

/// `a + b`, lane by lane, wrapping.
///
/// ```text
/// requires vnni512()
/// ensures  zd(r) == Seq::new(16, |j: int| add32(zd(*a)[j] as int, zd(*b)[j] as int))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn zd_add(a: &ZD, b: &ZD) -> (r: ZD)
    requires
        vnni512(),
    ensures
        zd(r) == Seq::new(16, |j: int| add32(zd(*a)[j] as int, zd(*b)[j] as int)),
{
    ZD(unsafe { _mm512_add_epi32(a.0, b.0) })
}

/// `vpdpbusd`: each lane plus the dot product of its four bytes of `x`
/// (unsigned) with the four of `w` (signed, so `w`'s bytes are below 128).
#[verifier::external_body]
#[inline(always)]
pub fn zd_dot(acc: &ZD, x: &ZB, w: &ZB) -> (r: ZD)
    requires
        vnni512(),
        forall|k: int| 0 <= k < 64 ==> #[trigger] zb(*w)[k] < 128,
    ensures
        zd(r) == Seq::new(16, |j: int| add32(zd(*acc)[j] as int, dot4(zb(*x), zb(*w), j) as int)),
{
    ZD(unsafe { _mm512_dpbusd_epi32(acc.0, x.0, w.0) })
}

/// The lanes, lowest first.
///
/// ```text
/// requires vnni512()
/// ensures  r@ == zd(*a)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn zd_store(a: &ZD) -> (r: [u32; 16])
    requires
        vnni512(),
    ensures
        r@ == zd(*a),
{
    let mut r = [0u32; 16];
    unsafe { _mm512_storeu_si512(r.as_mut_ptr() as *mut __m512i, a.0) };
    r
}

// ---------------------------------------------------------------------------
// 256 bits (AVX2)
// ---------------------------------------------------------------------------

/// The 32 bytes at `d[i..i + 32]`.
///
/// ```text
/// requires avx2()
///          i + 32 <= d@.len()
/// ensures  yb(r) == d@.subrange(i as int, i + 32)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn yb_load(d: &[u8], i: usize) -> (r: YB)
    requires
        avx2(),
        i + 32 <= d@.len(),
    ensures
        yb(r) == d@.subrange(i as int, i + 32),
{
    debug_assert!(i + 32 <= d.len());
    YB(unsafe { _mm256_loadu_si256(d.as_ptr().add(i) as *const __m256i) })
}

/// Eight zero lanes.
///
/// ```text
/// requires avx2()
/// ensures  yd(r) == Seq::new(8, |j: int| 0u32)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn yd_zero() -> (r: YD)
    requires
        avx2(),
    ensures
        yd(r) == Seq::new(8, |j: int| 0u32),
{
    YD(unsafe { _mm256_setzero_si256() })
}

/// `a + b`, lane by lane, wrapping.
///
/// ```text
/// requires avx2()
/// ensures  yd(r) == Seq::new(8, |j: int| add32(yd(*a)[j] as int, yd(*b)[j] as int))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn yd_add(a: &YD, b: &YD) -> (r: YD)
    requires
        avx2(),
    ensures
        yd(r) == Seq::new(8, |j: int| add32(yd(*a)[j] as int, yd(*b)[j] as int)),
{
    YD(unsafe { _mm256_add_epi32(a.0, b.0) })
}

/// `vpmaddubsw` (pairs of unsigned `x` times signed `w`, added, saturated
/// to 16 bits), `vpmaddwd` by ones (pairs of those, added), and the add.
/// With `w`'s bytes at most 64 a pair is at most `255 * 127`, so nothing
/// saturates and each lane gains the dot product of its four bytes.
#[verifier::external_body]
#[inline(always)]
pub fn yd_dot(acc: &YD, x: &YB, w: &YB) -> (r: YD)
    requires
        avx2(),
        forall|k: int| 0 <= k < 32 ==> #[trigger] yb(*w)[k] <= 64,
    ensures
        yd(r) == Seq::new(8, |j: int| add32(yd(*acc)[j] as int, dot4(yb(*x), yb(*w), j) as int)),
{
    YD(unsafe { _mm256_add_epi32(acc.0, _mm256_madd_epi16(_mm256_maddubs_epi16(x.0, w.0), _mm256_set1_epi16(1))) })
}

/// The lanes, lowest first.
///
/// ```text
/// requires avx2()
/// ensures  r@ == yd(*a)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn yd_store(a: &YD) -> (r: [u32; 8])
    requires
        avx2(),
    ensures
        r@ == yd(*a),
{
    let mut r = [0u32; 8];
    unsafe { _mm256_storeu_si256(r.as_mut_ptr() as *mut __m256i, a.0) };
    r
}

} // verus!
