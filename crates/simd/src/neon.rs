//! Specifications of the AArch64 NEON intrinsics (TRUSTED).
//!
//! NEON kernels work on one type, `uint8x16_t`, viewed as its 16 bytes in
//! memory order (`n8`); 16-bit work reads the same bytes as `u16s`, the
//! little-endian view that AArch64 uses. Each function here is a one-line
//! wrapper over a `core::arch::aarch64` intrinsic (with a `vreinterpretq`
//! where the intrinsic takes 16-bit lanes), stated in terms of the lane
//! functions in `crate::ops`. Verus takes the wrappers on trust.
//! `tests/neon.rs` runs each one on AArch64 against the verified reference
//! implementation of its spec.
//!
//! Off AArch64 the wrappers call the emulation in `crate::emu_neon`, so
//! NEON kernels build, and their proofs are checked, on every target.
//! Run-time selection uses `has_neon`, which is true on AArch64, where
//! NEON is part of the baseline, and on WebAssembly built with `simd128`,
//! where the wrappers call `crate::wasm_neon`, the same operations on
//! SIMD128 (WebAssembly has no run-time feature detection: a module built
//! with `simd128` needs a host that has it, as every current browser does).
//! Every wrapper forwards there, so each contract is proven on SIMD128.
#![allow(unused_unsafe)]
use crate::lanes::*;
use crate::ops::*;
use vstd::prelude::*;

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64 as a64;
#[cfg(not(target_arch = "aarch64"))]
use crate::emu_neon as a64;

#[cfg(target_arch = "aarch64")]
pub use core::arch::aarch64::uint8x16_t;
#[cfg(not(target_arch = "aarch64"))]
pub use crate::emu_neon::uint8x16_t;

/// On WebAssembly with SIMD128, the verified implementation of the same
/// contract in `crate::wasm_neon`; elsewhere, the intrinsic.
macro_rules! wasm_or {
    ($w:expr, $n:expr) => {{
        #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))]
        let r = $w;
        #[cfg(not(all(target_arch = "wasm32", target_feature = "simd128")))]
        #[allow(unused_unsafe)]
        let r = $n;
        r
    }};
}

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint8x16(uint8x16_t);

/// The 16 bytes of a NEON vector, lane 0 first.
pub uninterp spec fn n8(v: uint8x16_t) -> Seq<u8>;

pub broadcast axiom fn axiom_n8_len(v: uint8x16_t)
    ensures
        #[trigger] n8(v).len() == 16,
;

pub broadcast group group_neon {
    axiom_n8_len,
}

/// The CPU running this program has NEON (Advanced SIMD).
pub uninterp spec fn neon() -> bool;

/// True on AArch64, where NEON is always present.
#[verifier::external_body]
#[inline(always)]
pub fn has_neon() -> (r: bool)
    ensures
        r ==> neon(),
{
    cfg!(any(target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))
}

// ---------------------------------------------------------------------------
// Loads and stores
// ---------------------------------------------------------------------------

/// The 16 bytes at `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u8_at(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        n8(r) == s@.subrange(i as int, i + 16),
{
    debug_assert!(i + 16 <= s.len());
    wasm_or!(crate::wasm_neon::vld1q_u8_at(s, i), unsafe { a64::vld1q_u8(s.as_ptr().add(i)) })
}

/// Stores `v` at `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u8_at(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    debug_assert!(i + 16 <= s.len());
    wasm_or!(crate::wasm_neon::vst1q_u8_at(s, i, v), unsafe { a64::vst1q_u8(s.as_mut_ptr().add(i), v) })
}

/// The eight 16-bit values at `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u16_at(s: &[u16], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        u16s(n8(r)) == s@.subrange(i as int, i + 8),
{
    debug_assert!(i + 8 <= s.len());
    wasm_or!(crate::wasm_neon::vld1q_u16_at(s, i), unsafe { a64::vreinterpretq_u8_u16(a64::vld1q_u16(s.as_ptr().add(i))) })
}

/// Stores `v` as eight 16-bit values at `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u16_at(s: &mut [u16], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16s(n8(v)) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    debug_assert!(i + 8 <= s.len());
    wasm_or!(crate::wasm_neon::vst1q_u16_at(s, i, v), unsafe { a64::vst1q_u16(s.as_mut_ptr().add(i), a64::vreinterpretq_u16_u8(v)) })
}

/// The four 32-bit values at `s[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u32_at(s: &[u32], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 4 <= s@.len(),
    ensures
        u32s(n8(r)) == s@.subrange(i as int, i + 4),
{
    debug_assert!(i + 4 <= s.len());
    wasm_or!(crate::wasm_neon::vld1q_u32_at(s, i), unsafe { a64::vreinterpretq_u8_u32(a64::vld1q_u32(s.as_ptr().add(i))) })
}

/// Stores `v` as four 32-bit values at `s[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u32_at(s: &mut [u32], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u32s(n8(v)) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    wasm_or!(crate::wasm_neon::vst1q_u32_at(s, i, v), {
        debug_assert!(i + 4 <= s.len());
        unsafe { a64::vst1q_u32(s.as_mut_ptr().add(i), a64::vreinterpretq_u32_u8(v)) }
    })
}

// ---------------------------------------------------------------------------
// Lane operations
// ---------------------------------------------------------------------------

#[verifier::external_body]
#[inline(always)]
pub fn vdupq_n_u8(x: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == splat8(x, 16),
{
    wasm_or!(crate::wasm_neon::vdupq_n_u8(x), unsafe { a64::vdupq_n_u8(x) })
}

#[verifier::external_body]
#[inline(always)]
pub fn vandq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == and8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vandq_u8(a, b), unsafe { a64::vandq_u8(a, b) })
}

#[verifier::external_body]
#[inline(always)]
pub fn vorrq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == or8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vorrq_u8(a, b), unsafe { a64::vorrq_u8(a, b) })
}

#[verifier::external_body]
#[inline(always)]
pub fn veorq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == xor8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::veorq_u8(a, b), unsafe { a64::veorq_u8(a, b) })
}

#[verifier::external_body]
#[inline(always)]
pub fn vaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == add8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vaddq_u8(a, b), unsafe { a64::vaddq_u8(a, b) })
}

/// Unsigned saturating subtraction (`uqsub`).
#[verifier::external_body]
#[inline(always)]
pub fn vqsubq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == subs_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vqsubq_u8(a, b), unsafe { a64::vqsubq_u8(a, b) })
}

#[verifier::external_body]
#[inline(always)]
pub fn vceqq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == cmpeq8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vceqq_u8(a, b), unsafe { a64::vceqq_u8(a, b) })
}

/// Logical shift right of each byte by `N` (1 to 8).
#[verifier::external_body]
#[inline(always)]
pub fn vshrq_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == shr8(n8(a), N as int),
{
    wasm_or!(crate::wasm_neon::vshrq_n_u8::<N>(a), unsafe { a64::vshrq_n_u8::<N>(a) })
}

/// Table lookup in one 16-byte table; indices past it give 0.
#[verifier::external_body]
#[inline(always)]
pub fn vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == tbl1(n8(t), n8(idx)),
{
    wasm_or!(crate::wasm_neon::vqtbl1q_u8(t, idx), unsafe { a64::vqtbl1q_u8(t, idx) })
}

/// Bytes `N..N + 16` of `a` followed by `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vextq_u8<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 15,
    ensures
        n8(r) == alignr_lanes(n8(b), n8(a), N as int),
{
    wasm_or!(crate::wasm_neon::vextq_u8::<N>(a, b), unsafe { a64::vextq_u8::<N>(a, b) })
}

/// Interleaves the low halves of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip1q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == unpacklo8_lanes(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vzip1q_u8(a, b), unsafe { a64::vzip1q_u8(a, b) })
}

/// Interleaves the high halves of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip2q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == unpackhi8_lanes(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vzip2q_u8(a, b), unsafe { a64::vzip2q_u8(a, b) })
}

/// The even bytes of `a`, then those of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vuzp1q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == uzp1_8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vuzp1q_u8(a, b), unsafe { a64::vuzp1q_u8(a, b) })
}

/// The largest byte.
#[verifier::external_body]
#[inline(always)]
pub fn vmaxvq_u8(a: uint8x16_t) -> (r: u8)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] n8(a)[i] <= r,
        exists|i: int| 0 <= i < 16 && #[trigger] n8(a)[i] == r,
{
    wasm_or!(crate::wasm_neon::vmaxvq_u8(a), unsafe { a64::vmaxvq_u8(a) })
}

/// The largest of the eight 16-bit lanes.
#[verifier::external_body]
#[inline(always)]
pub fn vmaxvq_u16(a: uint8x16_t) -> (r: u16)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u16s(n8(a))[i] <= r,
        exists|i: int| 0 <= i < 8 && #[trigger] u16s(n8(a))[i] == r,
{
    wasm_or!(crate::wasm_neon::vmaxvq_u16(a), unsafe { a64::vmaxvq_u16(a64::vreinterpretq_u16_u8(a)) })
}

/// Sums of adjacent byte pairs of `a`, then of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vpaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == padd8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vpaddq_u8(a, b), unsafe { a64::vpaddq_u8(a, b) })
}

/// Each 16-bit lane shifted right by 4 and narrowed to its low 8 bits,
/// read as a 64-bit number (`shrn #4` then `fmov`): nibble `k` of the
/// result is the high nibble of byte `k` for even `k`, the low nibble of
/// byte `k` for odd `k`.
#[verifier::external_body]
#[inline(always)]
pub fn vshrn4_u64(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        forall|k: u64|
            k < 16 ==> #[trigger] ((r >> (4 * k)) & 15) == (if k % 2 == 0 {
                (n8(a)[k as int] >> 4u8) as u64
            } else {
                (n8(a)[k as int] & 15u8) as u64
            }),
{
    wasm_or!(crate::wasm_neon::vshrn4_u64(a), unsafe { a64::vget_lane_u64::<0>(a64::vreinterpret_u64_u8(a64::vshrn_n_u16::<4>(a64::vreinterpretq_u16_u8(a)))) })
}

/// The low 64 bits, little-endian.
#[verifier::external_body]
#[inline(always)]
pub fn vgetq_lane_u64_0(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        r == u64s(n8(a))[0],
{
    wasm_or!(crate::wasm_neon::vgetq_lane_u64_0(a), unsafe { a64::vgetq_lane_u64::<0>(a64::vreinterpretq_u64_u8(a)) })
}

/// `x` in each 32-bit lane.
#[verifier::external_body]
#[inline(always)]
pub fn vdupq_n_u32(x: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == splat32(x, 4),
{
    wasm_or!(crate::wasm_neon::vdupq_n_u32(x), unsafe { a64::vreinterpretq_u8_u32(a64::vdupq_n_u32(x)) })
}

/// 32-bit lane 3 of `a` in each 32-bit lane.
#[verifier::external_body]
#[inline(always)]
pub fn vdupq_laneq_u32_3(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == splat32(u32s(n8(a))[3], 4),
{
    wasm_or!(crate::wasm_neon::vdupq_laneq_u32_3(a), unsafe { a64::vreinterpretq_u8_u32(a64::vdupq_laneq_u32::<3>(a64::vreinterpretq_u32_u8(a))) })
}

/// The eight 16-bit values at `s[i..i + 8]`, as their bits.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_s16_at(s: &[i16], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        u16s(n8(r)) == s@.subrange(i as int, i + 8).map_values(|x: i16| x as u16),
{
    wasm_or!(crate::wasm_neon::vld1q_s16_at(s, i), {
        debug_assert!(i + 8 <= s.len());
        unsafe { a64::vreinterpretq_u8_u16(a64::vld1q_u16(s.as_ptr().add(i) as *const u16)) }
    })
}

/// Stores `v` as eight 16-bit values at `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_s16_at(s: &mut [i16], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16s(n8(v)).map_values(|x: u16| x as i16)
            + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    wasm_or!(crate::wasm_neon::vst1q_s16_at(s, i, v), {
        debug_assert!(i + 8 <= s.len());
        unsafe { a64::vst1q_u16(s.as_mut_ptr().add(i) as *mut u16, a64::vreinterpretq_u16_u8(v)) }
    })
}

// ---------------------------------------------------------------------------
// Signed 16-bit arithmetic
// ---------------------------------------------------------------------------

/// `x` in each 16-bit lane.
#[verifier::external_body]
#[inline(always)]
pub fn vdupq_n_s16(x: i16) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == splat16(u16_of_i16(x), 8),
{
    wasm_or!(crate::wasm_neon::vdupq_n_s16(x), unsafe { a64::vreinterpretq_u8_u16(a64::vdupq_n_u16(x as u16)) })
}

/// Wrapping 16-bit addition.
#[verifier::external_body]
#[inline(always)]
pub fn vaddq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == add16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vaddq_s16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vaddq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// Wrapping 16-bit subtraction.
#[verifier::external_body]
#[inline(always)]
pub fn vsubq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == sub16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vsubq_s16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vsubq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// Arithmetic shift right of each signed 16-bit lane by `N` (1 to 15).
#[verifier::external_body]
#[inline(always)]
pub fn vshrq_n_s16<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 15,
    ensures
        u16s(n8(r)) == srai16(u16s(n8(a)), N as int),
{
    wasm_or!(crate::wasm_neon::vshrq_n_s16::<N>(a), unsafe { a64::vreinterpretq_u8_s16(a64::vshrq_n_s16::<N>(a64::vreinterpretq_s16_u8(a))) })
}

/// Signed saturating doubling multiply, high half (`sqdmulh`).
#[verifier::external_body]
#[inline(always)]
pub fn vqdmulhq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == qdmulh_s16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vqdmulhq_s16(a, b), unsafe { a64::vreinterpretq_u8_s16(a64::vqdmulhq_s16(a64::vreinterpretq_s16_u8(a), a64::vreinterpretq_s16_u8(b))) })
}

/// Interleaves the low four 16-bit lanes of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip1q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == unpacklo16_lanes(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip1q_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vzip1q_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// Interleaves the high four 16-bit lanes of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip2q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == unpackhi16_lanes(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip2q_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vzip2q_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// Interleaves the low two 32-bit lanes of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip1q_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == unpacklo32_lanes(u32s(n8(a)), u32s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip1q_u32(a, b), unsafe { a64::vreinterpretq_u8_u32(a64::vzip1q_u32(a64::vreinterpretq_u32_u8(a), a64::vreinterpretq_u32_u8(b))) })
}

/// Interleaves the high two 32-bit lanes of `a` and `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip2q_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == unpackhi32_lanes(u32s(n8(a)), u32s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip2q_u32(a, b), unsafe { a64::vreinterpretq_u8_u32(a64::vzip2q_u32(a64::vreinterpretq_u32_u8(a), a64::vreinterpretq_u32_u8(b))) })
}

/// The low 64 bits of `a`, then those of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip1q_u64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == unpacklo64_lanes(u64s(n8(a)), u64s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip1q_u64(a, b), unsafe { a64::vreinterpretq_u8_u64(a64::vzip1q_u64(a64::vreinterpretq_u64_u8(a), a64::vreinterpretq_u64_u8(b))) })
}

/// The high 64 bits of `a`, then those of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn vzip2q_u64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == unpackhi64_lanes(u64s(n8(a)), u64s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vzip2q_u64(a, b), unsafe { a64::vreinterpretq_u8_u64(a64::vzip2q_u64(a64::vreinterpretq_u64_u8(a), a64::vreinterpretq_u64_u8(b))) })
}

// ---------------------------------------------------------------------------
// Byte averages, widening and narrowing
// ---------------------------------------------------------------------------

/// Unsigned rounding halving add (`urhadd`): `(a + b + 1) >> 1` per byte.
#[verifier::external_body]
#[inline(always)]
pub fn vrhaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == avg_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vrhaddq_u8(a, b), unsafe { a64::vrhaddq_u8(a, b) })
}

/// Wrapping byte subtraction.
#[verifier::external_body]
#[inline(always)]
pub fn vsubq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == sub8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vsubq_u8(a, b), unsafe { a64::vsubq_u8(a, b) })
}

/// Unsigned saturating 16-bit subtraction (`uqsub`).
#[verifier::external_body]
#[inline(always)]
pub fn vqsubq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == subs_u16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vqsubq_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vqsubq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// The low eight bytes of `a`, zero-extended to 16-bit lanes and shifted
/// left by `N` (0 to 8) (`ushll`; `vshll_n_u8` of `vget_low_u8`). The
/// 16-bit view of `a`'s low bytes interleaved with zeros is those bytes
/// zero-extended.
#[verifier::external_body]
#[inline(always)]
pub fn vshll_low_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 8,
    ensures
        u16s(n8(r)) == slli16(u16s(unpacklo8_lanes(n8(a), splat8(0, 16))), N as int),
{
    wasm_or!(crate::wasm_neon::vshll_low_n_u8::<N>(a), unsafe { a64::vreinterpretq_u8_u16(a64::vshll_n_u8::<N>(a64::vget_low_u8(a))) })
}

/// The high eight bytes of `a`, zero-extended to 16-bit lanes and shifted
/// left by `N` (0 to 8) (`ushll2`).
#[verifier::external_body]
#[inline(always)]
pub fn vshll_high_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 8,
    ensures
        u16s(n8(r)) == slli16(u16s(unpackhi8_lanes(n8(a), splat8(0, 16))), N as int),
{
    wasm_or!(crate::wasm_neon::vshll_high_n_u8::<N>(a), unsafe { a64::vreinterpretq_u8_u16(a64::vshll_high_n_u8::<N>(a)) })
}

/// Each signed 16-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 8) and saturated to an unsigned byte (`sqshrun` and `sqshrun2`;
/// `vqshrun_high_n_s16` of `vqshrun_n_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vqshrun2_n_s16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packus16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)),
{
    wasm_or!(crate::wasm_neon::vqshrun2_n_s16::<N>(a, b), {
        unsafe {
            a64::vqshrun_high_n_s16::<N>(a64::vqshrun_n_s16::<N>(a64::vreinterpretq_s16_u8(a)), a64::vreinterpretq_s16_u8(b))
        }
    })
}

/// Each unsigned 16-bit lane of `a`, then of `b`, shifted right by `N` (1
/// to 8) and saturated to a byte (`uqshrn` and `uqshrn2`;
/// `vqshrn_high_n_u16` of `vqshrn_n_u16`). A lane shifted right by at least
/// one is below 2^15, so the signed saturation of `packus16_lanes` sees it
/// as it is.
#[verifier::external_body]
#[inline(always)]
pub fn vqshrn2_n_u16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packus16_lanes(srli16(u16s(n8(a)), N as int), srli16(u16s(n8(b)), N as int)),
{
    wasm_or!(crate::wasm_neon::vqshrn2_n_u16::<N>(a, b), {
        unsafe {
            a64::vqshrn_high_n_u16::<N>(a64::vqshrn_n_u16::<N>(a64::vreinterpretq_u16_u8(a)), a64::vreinterpretq_u16_u8(b))
        }
    })
}

// ---------------------------------------------------------------------------
// Saturating and signed byte arithmetic, compares, and 8-byte loads and
// stores (for the VP8 loop filter)
// ---------------------------------------------------------------------------

/// Unsigned byte maximum (`umax`).
#[verifier::external_body]
#[inline(always)]
pub fn vmaxq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == max_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vmaxq_u8(a, b), unsafe { a64::vmaxq_u8(a, b) })
}

/// Absolute difference of unsigned bytes (`uabd`).
#[verifier::external_body]
#[inline(always)]
pub fn vabdq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == abd_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vabdq_u8(a, b), unsafe { a64::vabdq_u8(a, b) })
}

/// `a <= b` on unsigned bytes, as a byte mask (`cmhs` with the operands
/// swapped).
#[verifier::external_body]
#[inline(always)]
pub fn vcleq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == cmple_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vcleq_u8(a, b), unsafe { a64::vcleq_u8(a, b) })
}

/// Unsigned saturating byte addition (`uqadd`).
#[verifier::external_body]
#[inline(always)]
pub fn vqaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == adds_u8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vqaddq_u8(a, b), unsafe { a64::vqaddq_u8(a, b) })
}

/// `a & !b` (`bic`: the second operand is the one complemented).
#[verifier::external_body]
#[inline(always)]
pub fn vbicq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == andnot8(n8(b), n8(a)),
{
    wasm_or!(crate::wasm_neon::vbicq_u8(a, b), unsafe { a64::vbicq_u8(a, b) })
}

/// Signed saturating byte addition (`sqadd`).
#[verifier::external_body]
#[inline(always)]
pub fn vqaddq_s8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == adds_s8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vqaddq_s8(a, b), unsafe { a64::vreinterpretq_u8_s8(a64::vqaddq_s8(a64::vreinterpretq_s8_u8(a), a64::vreinterpretq_s8_u8(b))) })
}

/// Signed saturating byte subtraction (`sqsub`).
#[verifier::external_body]
#[inline(always)]
pub fn vqsubq_s8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == subs_s8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vqsubq_s8(a, b), unsafe { a64::vreinterpretq_u8_s8(a64::vqsubq_s8(a64::vreinterpretq_s8_u8(a), a64::vreinterpretq_s8_u8(b))) })
}

/// Arithmetic shift right of each signed byte by `N` (1 to 8) (`sshr`).
#[verifier::external_body]
#[inline(always)]
pub fn vshrq_n_s8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == sra8(n8(a), N as int),
{
    wasm_or!(crate::wasm_neon::vshrq_n_s8::<N>(a), unsafe { a64::vreinterpretq_u8_s8(a64::vshrq_n_s8::<N>(a64::vreinterpretq_s8_u8(a))) })
}

/// Each signed 16-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 8) and saturated to a signed byte (`sqshrn` and `sqshrn2`;
/// `vqshrn_high_n_s16` of `vqshrn_n_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vqshrn2_n_s16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packs16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)),
{
    wasm_or!(crate::wasm_neon::vqshrn2_n_s16::<N>(a, b), {
        unsafe {
            a64::vreinterpretq_u8_s8(
                a64::vqshrn_high_n_s16::<N>(a64::vqshrn_n_s16::<N>(a64::vreinterpretq_s16_u8(a)), a64::vreinterpretq_s16_u8(b)),
            )
        }
    })
}

/// The 8 bytes at `s[i..i + 8]` in the low half, zeros in the high half
/// (`ldr d`; `vcombine_u8` of `vld1_u8` and zero).
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u8_low_at(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        n8(r) == s@.subrange(i as int, i + 8) + splat8(0u8, 8),
{
    wasm_or!(crate::wasm_neon::vld1q_u8_low_at(s, i), {
        debug_assert!(i + 8 <= s.len());
        unsafe { a64::vcombine_u8(a64::vld1_u8(s.as_ptr().add(i)), a64::vdup_n_u8(0)) }
    })
}

/// Stores the low 8 bytes of `v` at `s[i..i + 8]` (`str d`; `vst1_u8` of
/// `vget_low_u8`).
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u8_low_at(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v).subrange(0, 8) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    wasm_or!(crate::wasm_neon::vst1q_u8_low_at(s, i, v), {
        debug_assert!(i + 8 <= s.len());
        unsafe { a64::vst1_u8(s.as_mut_ptr().add(i), a64::vget_low_u8(v)) }
    })
}

// ---------------------------------------------------------------------------
// A vector from two 64-bit halves, and 4-byte lane stores (for VP8 4x4
// intra prediction)
// ---------------------------------------------------------------------------

/// The vector whose low 64 bits are `lo` and whose high 64 bits are `hi`,
/// little-endian (`fmov d, x` and `mov v.d[1], x`; `vcombine_u64` of two
/// `vcreate_u64`).
#[verifier::external_body]
#[inline(always)]
pub fn vcombine_u64(lo: u64, hi: u64) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![lo, hi],
{
    wasm_or!(crate::wasm_neon::vcombine_u64(lo, hi), unsafe { a64::vreinterpretq_u8_u64(a64::vcombine_u64(a64::vcreate_u64(lo), a64::vcreate_u64(hi))) })
}

/// Stores 32-bit lane `N` of `v`, its bytes `4 * N..4 * N + 4`, at
/// `s[i..i + 4]` (`str s` for lane 0, `st1 v.s[N]` otherwise;
/// `vgetq_lane_u32` and an unaligned store).
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_lane_u32_at<const N: i32>(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        0 <= N <= 3,
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v).subrange(4 * N, 4 * N + 4) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    wasm_or!(crate::wasm_neon::vst1q_lane_u32_at::<N>(s, i, v), {
        debug_assert!(i + 4 <= s.len());
        unsafe { core::ptr::write_unaligned(s.as_mut_ptr().add(i) as *mut u32, a64::vgetq_lane_u32::<N>(a64::vreinterpretq_u32_u8(v))) }
    })
}

// ---------------------------------------------------------------------------
// Multiplies and widening pairwise sums (decimal digits to an integer)
// ---------------------------------------------------------------------------

/// The low 8 bits of the bytewise products (`mul`).
#[verifier::external_body]
#[inline(always)]
pub fn vmulq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == mullo8(n8(a), n8(b)),
{
    wasm_or!(crate::wasm_neon::vmulq_u8(a, b), unsafe { a64::vmulq_u8(a, b) })
}

/// The low 16 bits of the products of the 16-bit lanes (`mul`).
#[verifier::external_body]
#[inline(always)]
pub fn vmulq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == mullo16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vmulq_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vmulq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// The low 32 bits of the products of the 32-bit lanes (`mul`).
#[verifier::external_body]
#[inline(always)]
pub fn vmulq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mullo32(u32s(n8(a)), u32s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vmulq_u32(a, b), unsafe { a64::vreinterpretq_u8_u32(a64::vmulq_u32(a64::vreinterpretq_u32_u8(a), a64::vreinterpretq_u32_u8(b))) })
}

/// The sums of adjacent bytes, as eight 16-bit lanes (`uaddlp`).
#[verifier::external_body]
#[inline(always)]
pub fn vpaddlq_u8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == paddl8(n8(a)),
{
    wasm_or!(crate::wasm_neon::vpaddlq_u8(a), unsafe { a64::vreinterpretq_u8_u16(a64::vpaddlq_u8(a)) })
}

/// The sums of adjacent 16-bit lanes, as four 32-bit lanes (`uaddlp`).
#[verifier::external_body]
#[inline(always)]
pub fn vpaddlq_u16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == paddl16(u16s(n8(a))),
{
    wasm_or!(crate::wasm_neon::vpaddlq_u16(a), unsafe { a64::vreinterpretq_u8_u32(a64::vpaddlq_u16(a64::vreinterpretq_u16_u8(a))) })
}

/// The sums of adjacent 32-bit lanes, as two 64-bit lanes (`uaddlp`).
#[verifier::external_body]
#[inline(always)]
pub fn vpaddlq_u32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == paddl32(u32s(n8(a))),
{
    wasm_or!(crate::wasm_neon::vpaddlq_u32(a), unsafe { a64::vreinterpretq_u8_u64(a64::vpaddlq_u32(a64::vreinterpretq_u32_u8(a))) })
}

/// The high 64 bits, little-endian.
#[verifier::external_body]
#[inline(always)]
pub fn vgetq_lane_u64_1(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        r == u64s(n8(a))[1],
{
    wasm_or!(crate::wasm_neon::vgetq_lane_u64_1(a), unsafe { a64::vgetq_lane_u64::<1>(a64::vreinterpretq_u64_u8(a)) })
}

// ---------------------------------------------------------------------------
// Integer transforms (the JPEG inverse DCT)
// ---------------------------------------------------------------------------

/// Absolute value of each signed 16-bit lane (`abs`); `-0x8000` stays
/// `0x8000`.
#[verifier::external_body]
#[inline(always)]
pub fn vabsq_s16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == abs16(u16s(n8(a))),
{
    wasm_or!(crate::wasm_neon::vabsq_s16(a), unsafe { a64::vreinterpretq_u8_s16(a64::vabsq_s16(a64::vreinterpretq_s16_u8(a))) })
}

/// Unsigned 16-bit maximum (`umax`).
#[verifier::external_body]
#[inline(always)]
pub fn vmaxq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == max_u16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vmaxq_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vmaxq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// The signed products of the low four 16-bit lanes, as 32-bit lanes
/// (`smull`; `vmull_s16` of `vget_low_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmull_lo_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mull_lo_s16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vmull_lo_s16(a, b), unsafe { a64::vreinterpretq_u8_s32(a64::vmull_s16(a64::vget_low_s16(a64::vreinterpretq_s16_u8(a)), a64::vget_low_s16(a64::vreinterpretq_s16_u8(b)))) })
}

/// The signed products of the high four 16-bit lanes, as 32-bit lanes
/// (`smull2`; `vmull_high_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmull_hi_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mull_hi_s16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vmull_hi_s16(a, b), unsafe { a64::vreinterpretq_u8_s32(a64::vmull_high_s16(a64::vreinterpretq_s16_u8(a), a64::vreinterpretq_s16_u8(b))) })
}

/// Wrapping 32-bit addition.
#[verifier::external_body]
#[inline(always)]
pub fn vaddq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == add32(u32s(n8(a)), u32s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vaddq_u32(a, b), unsafe { a64::vreinterpretq_u8_u32(a64::vaddq_u32(a64::vreinterpretq_u32_u8(a), a64::vreinterpretq_u32_u8(b))) })
}

/// Wrapping 32-bit subtraction.
#[verifier::external_body]
#[inline(always)]
pub fn vsubq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == sub32(u32s(n8(a)), u32s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vsubq_u32(a, b), unsafe { a64::vreinterpretq_u8_u32(a64::vsubq_u32(a64::vreinterpretq_u32_u8(a), a64::vreinterpretq_u32_u8(b))) })
}

/// Rounding arithmetic shift right of each signed 32-bit lane by `N` (1 to
/// 31) (`srshr`).
#[verifier::external_body]
#[inline(always)]
pub fn vrshrq_n_s32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 31,
    ensures
        u32s(n8(r)) == rshr_s32(u32s(n8(a)), N as int),
{
    wasm_or!(crate::wasm_neon::vrshrq_n_s32::<N>(a), unsafe { a64::vreinterpretq_u8_s32(a64::vrshrq_n_s32::<N>(a64::vreinterpretq_s32_u8(a))) })
}

/// Shift left of each 32-bit lane by `N` (0 to 31).
#[verifier::external_body]
#[inline(always)]
pub fn vshlq_n_u32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 31,
    ensures
        u32s(n8(r)) == slli32(u32s(n8(a)), N as int),
{
    wasm_or!(crate::wasm_neon::vshlq_n_u32::<N>(a), unsafe { a64::vreinterpretq_u8_u32(a64::vshlq_n_u32::<N>(a64::vreinterpretq_u32_u8(a))) })
}

/// The odd 16-bit lanes of `a`, then those of `b` (`uzp2`).
#[verifier::external_body]
#[inline(always)]
pub fn vuzp2q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == uzp2_16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vuzp2q_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vuzp2q_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// Stores the bytes of `a`, `b` and `c` interleaved at `s[i..i + 48]`
/// (`st3`): `a[0], b[0], c[0], a[1], ...`.
#[verifier::external_body]
#[inline(always)]
pub fn vst3q_u8_at(s: &mut [u8], i: usize, a: uint8x16_t, b: uint8x16_t, c: uint8x16_t)
    requires
        neon(),
        i + 48 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + interleave3(n8(a), n8(b), n8(c)) + old(s)@.subrange(
            i + 48,
            old(s)@.len() as int,
        ),
{
    wasm_or!(crate::wasm_neon::vst3q_u8_at(s, i, a, b, c), {
        debug_assert!(i + 48 <= s.len());
        unsafe { a64::vst3q_u8(s.as_mut_ptr().add(i), a64::uint8x16x3_t(a, b, c)) }
    })
}

// ---------------------------------------------------------------------------
// The 16-bit inverse DCT
// ---------------------------------------------------------------------------

/// The signed products of the low four 16-bit lanes of `a` with lane `L`
/// of `c`, as 32-bit lanes (`smull` by element; `vmull_laneq_s16` of
/// `vget_low_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmull_lo_laneq_s16<const L: i32>(a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mull_lo_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int),
{
    wasm_or!(crate::wasm_neon::vmull_lo_laneq_s16::<L>(a, c), unsafe { a64::vreinterpretq_u8_s32(a64::vmull_laneq_s16::<L>(a64::vget_low_s16(a64::vreinterpretq_s16_u8(a)), a64::vreinterpretq_s16_u8(c))) })
}

/// The signed products of the high four 16-bit lanes of `a` with lane `L`
/// of `c`, as 32-bit lanes (`smull2` by element; `vmull_high_laneq_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmull_hi_laneq_s16<const L: i32>(a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mull_hi_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int),
{
    wasm_or!(crate::wasm_neon::vmull_hi_laneq_s16::<L>(a, c), unsafe { a64::vreinterpretq_u8_s32(a64::vmull_high_laneq_s16::<L>(a64::vreinterpretq_s16_u8(a), a64::vreinterpretq_s16_u8(c))) })
}

/// `acc` plus the signed products of the low four 16-bit lanes of `a` with
/// lane `L` of `c`, wrapping (`smlal` by element; `vmlal_laneq_s16` of
/// `vget_low_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmlal_lo_laneq_s16<const L: i32>(acc: uint8x16_t, a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mlal_lo_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int),
{
    wasm_or!(crate::wasm_neon::vmlal_lo_laneq_s16::<L>(acc, a, c), unsafe { a64::vreinterpretq_u8_s32(a64::vmlal_laneq_s16::<L>(a64::vreinterpretq_s32_u8(acc), a64::vget_low_s16(a64::vreinterpretq_s16_u8(a)), a64::vreinterpretq_s16_u8(c))) })
}

/// `acc` plus the signed products of the high four 16-bit lanes of `a`
/// with lane `L` of `c`, wrapping (`smlal2` by element;
/// `vmlal_high_laneq_s16`).
#[verifier::external_body]
#[inline(always)]
pub fn vmlal_hi_laneq_s16<const L: i32>(acc: uint8x16_t, a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mlal_hi_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int),
{
    wasm_or!(crate::wasm_neon::vmlal_hi_laneq_s16::<L>(acc, a, c), unsafe { a64::vreinterpretq_u8_s32(a64::vmlal_high_laneq_s16::<L>(a64::vreinterpretq_s32_u8(acc), a64::vreinterpretq_s16_u8(a), a64::vreinterpretq_s16_u8(c))) })
}

/// Each signed 32-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 16) with rounding and cut to 16 bits (`rshrn` and `rshrn2`;
/// `vrshrn_high_n_s32` of `vrshrn_n_s32`).
#[verifier::external_body]
#[inline(always)]
pub fn vrshrn2_n_s32<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 16,
    ensures
        u16s(n8(r)) == rshrn_s32(u32s(n8(a)), N as int) + rshrn_s32(u32s(n8(b)), N as int),
{
    wasm_or!(crate::wasm_neon::vrshrn2_n_s32::<N>(a, b), unsafe { a64::vreinterpretq_u8_s16(a64::vrshrn_high_n_s32::<N>(a64::vrshrn_n_s32::<N>(a64::vreinterpretq_s32_u8(a)), a64::vreinterpretq_s32_u8(b))) })
}

/// Each signed 32-bit lane of `a` shifted right by `N` (1 to 16) with
/// rounding and cut to 16 bits, in the low half; zeros in the high half
/// (`rshrn`; `vcombine_s16` of `vrshrn_n_s32` and zero).
#[verifier::external_body]
#[inline(always)]
pub fn vrshrn_lo_n_s32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 16,
    ensures
        u16s(n8(r)) == rshrn_s32(u32s(n8(a)), N as int) + splat16(0, 4),
{
    wasm_or!(crate::wasm_neon::vrshrn_lo_n_s32::<N>(a), unsafe { a64::vreinterpretq_u8_s16(a64::vcombine_s16(a64::vrshrn_n_s32::<N>(a64::vreinterpretq_s32_u8(a)), a64::vdup_n_s16(0))) })
}

/// Unsigned saturating 16-bit addition (`uqadd`).
#[verifier::external_body]
#[inline(always)]
pub fn vqaddq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == adds_u16(u16s(n8(a)), u16s(n8(b))),
{
    wasm_or!(crate::wasm_neon::vqaddq_u16(a, b), unsafe { a64::vreinterpretq_u8_u16(a64::vqaddq_u16(a64::vreinterpretq_u16_u8(a), a64::vreinterpretq_u16_u8(b))) })
}

/// The sum of the eight 16-bit lanes (`uaddlv`).
#[verifier::external_body]
#[inline(always)]
pub fn vaddlvq_u16(a: uint8x16_t) -> (r: u32)
    requires
        neon(),
    ensures
        r as int == sum_u16(u16s(n8(a))),
{
    wasm_or!(crate::wasm_neon::vaddlvq_u16(a), unsafe { a64::vaddlvq_u16(a64::vreinterpretq_u16_u8(a)) })
}

} // verus!
