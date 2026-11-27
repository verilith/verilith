//! The AArch64 instructions the kernels use, one wrapper each (TRUSTED):
//! each is one intrinsic (FEAT_AES `AESE`, `AESMC`, FEAT_PMULL `PMULL`,
//! and Advanced SIMD), with an `ensures` stating what it computes in the
//! terms of [`crate::isa`] on the register as a 128-bit integer ([`nv`]),
//! byte element 0 in bits 7:0. Little-endian AArch64 only: `LD1 {Vt.16B}`
//! puts the byte at the lowest address in element 0, and a `u128` in
//! memory has its least significant byte there.
//!
//! Each requires [`arm_aes`], which [`has_arm_aes`] ensures after run-time
//! detection. The module is compiled on other targets too, so that Verus
//! checks the Arm proofs on any host, with bodies that are never run.
#![allow(unused_imports, unused_unsafe, unused_parens, unused_variables, dead_code)]
use crate::gf::*;
use crate::isa::*;
#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
use vstd::prelude::*;

#[cfg(target_arch = "aarch64")]
type Inner = uint8x16_t;
// Elsewhere a stand-in, never used: no `N128` is made without `arm_aes`.
#[cfg(not(target_arch = "aarch64"))]
type Inner = u128;

#[cfg(all(target_arch = "aarch64", feature = "std"))]
macro_rules! arm_has { ($f:tt) => { std::arch::is_aarch64_feature_detected!($f) }; }
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
macro_rules! arm_has { ($f:tt) => { cfg!(target_feature = $f) }; }

// On other targets each wrapper's body is this.
#[cfg(not(target_arch = "aarch64"))]
macro_rules! arm_only { ($($t:tt)*) => { unreachable!() }; }
#[cfg(target_arch = "aarch64")]
macro_rules! arm_only { ($($t:tt)*) => { $($t)* }; }

verus! {

/// The CPU has FEAT_AES and FEAT_PMULL (and Advanced SIMD).
pub uninterp spec fn arm_aes() -> bool;

/// Whether the CPU has what [`arm_aes`] says, detected at run time.
#[verifier::external_body]
#[inline]
pub fn has_arm_aes() -> (r: bool)
    ensures
        r ==> arm_aes(),
{
    arm_only! { arm_has!("aes") && arm_has!("pmull") && arm_has!("neon") }
}

/// A 128-bit register.
#[verifier::external_body]
#[repr(transparent)]
pub struct N128(Inner);

impl Clone for N128 {
    #[verifier::external_body]
    #[inline(always)]
    fn clone(&self) -> Self {
        N128(self.0)
    }
}

impl Copy for N128 {}

/// The register as a 128-bit integer, byte element 0 least significant.
pub uninterp spec fn nv(x: N128) -> u128;

/// The register's bytes.
pub open spec fn nb(x: N128) -> Seq<u8> {
    bytes16(nv(x))
}

/// `LD1 {Vt.16B}` from `d[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn n_load(d: &[u8], i: usize) -> (r: N128)
    requires
        arm_aes(),
        i + 16 <= d@.len(),
    ensures
        nb(r) == d@.subrange(i as int, i + 16),
{
    arm_only! { debug_assert!(i + 16 <= d.len());
    N128(unsafe { vld1q_u8(d.as_ptr().add(i)) }) }
}

/// `ST1 {Vt.16B}` to `d[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn n_store(d: &mut [u8], i: usize, x: N128)
    requires
        arm_aes(),
        i + 16 <= old(d)@.len(),
    ensures
        final(d)@.len() == old(d)@.len(),
        forall|k: int| 0 <= k < final(d)@.len() ==> #[trigger] final(d)@[k] == if i <= k < i + 16 {
            nb(x)[k - i]
        } else {
            old(d)@[k]
        },
{
    arm_only! { debug_assert!(i + 16 <= d.len());
    unsafe { vst1q_u8(d.as_mut_ptr().add(i), x.0) } }
}

/// `LD1` from a 16-byte array.
#[verifier::external_body]
#[inline(always)]
pub fn n_load16(a: &[u8; 16]) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nb(r) == a@,
{
    arm_only! { N128(unsafe { vld1q_u8(a.as_ptr()) }) }
}

/// `ST1` to a 16-byte array.
#[verifier::external_body]
#[inline(always)]
pub fn n_store16(a: &mut [u8; 16], x: N128)
    requires
        arm_aes(),
    ensures
        final(a)@ == nb(x),
{
    arm_only! { unsafe { vst1q_u8(a.as_mut_ptr(), x.0) } }
}

/// `LD1` of `a[i]` (little-endian: byte 0 is bits 7:0).
#[verifier::external_body]
#[inline(always)]
pub fn n_load_u128(a: &[u128], i: usize) -> (r: N128)
    requires
        arm_aes(),
        i < a@.len(),
    ensures
        nv(r) == a@[i as int],
{
    arm_only! { debug_assert!(i < a.len());
    N128(unsafe { vld1q_u8(a.as_ptr().add(i) as *const u8) }) }
}

/// The register holding `v`.
#[verifier::external_body]
#[inline(always)]
pub fn n_set(v: u128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nv(r) == v,
{
    arm_only! { N128(unsafe { vreinterpretq_u8_p128(v) }) }
}

/// The register as a `u128`.
#[verifier::external_body]
#[inline(always)]
pub fn n_get(x: N128) -> (r: u128)
    requires
        arm_aes(),
    ensures
        r == nv(x),
{
    arm_only! { unsafe { vreinterpretq_p128_u8(x.0) } }
}

/// `EOR Vd.16B`.
#[verifier::external_body]
#[inline(always)]
pub fn n_xor(a: N128, b: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nv(r) == nv(a) ^ nv(b),
{
    arm_only! { N128(unsafe { veorq_u8(a.0, b.0) }) }
}

/// `AESE`.
#[verifier::external_body]
#[inline(always)]
pub fn n_aese(d: N128, k: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nb(r) == aese(nb(d), nb(k)),
{
    arm_only! { N128(unsafe { vaeseq_u8(d.0, k.0) }) }
}

/// `AESMC`.
#[verifier::external_body]
#[inline(always)]
pub fn n_aesmc(d: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nb(r) == aesmc(nb(d)),
{
    arm_only! { N128(unsafe { vaesmcq_u8(d.0) }) }
}

/// `PMULL`/`PMULL2 Vd.1Q` of the 64-bit elements `IMM` picks as `PCLMULQDQ`'s
/// immediate does (bit 0 for `a`, bit 4 for `b`).
#[verifier::external_body]
#[inline(always)]
pub fn n_clmul<const IMM: i32>(a: N128, b: N128) -> (r: N128)
    requires
        arm_aes(),
        IMM == 0x00 || IMM == 0x01 || IMM == 0x10 || IMM == 0x11,
    ensures
        nv(r) == pclmul(nv(a), nv(b), IMM),
{
    arm_only! { unsafe {
        // Kept in vector registers: PMULL2 multiplies the high elements, so
        // a high-low product swaps the halves of the low operand's register.
        let p = if IMM == 0x00 {
            vmull_p64(vgetq_lane_u64::<0>(vreinterpretq_u64_u8(a.0)), vgetq_lane_u64::<0>(vreinterpretq_u64_u8(b.0)))
        } else if IMM == 0x11 {
            vmull_high_p64(vreinterpretq_p64_u8(a.0), vreinterpretq_p64_u8(b.0))
        } else if IMM == 0x01 {
            vmull_high_p64(vreinterpretq_p64_u8(a.0), vreinterpretq_p64_u8(vextq_u8::<8>(b.0, b.0)))
        } else {
            vmull_high_p64(vreinterpretq_p64_u8(vextq_u8::<8>(a.0, a.0)), vreinterpretq_p64_u8(b.0))
        };
        N128(vreinterpretq_u8_p128(p))
    } }
}

/// `TBL` with the indices `m & 0x8f`: index `m[k] & 15`, or one out of
/// range (so 0) if bit 7 of `m[k]` is set, which is `PSHUFB`.
#[verifier::external_body]
#[inline(always)]
pub fn n_tbl(a: N128, m: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nb(r) == pshufb(nb(a), nb(m)),
{
    arm_only! { N128(unsafe { vqtbl1q_u8(a.0, vandq_u8(m.0, vdupq_n_u8(0x8f))) }) }
}

/// `ADD Vd.4S`.
#[verifier::external_body]
#[inline(always)]
pub fn n_add32(a: N128, b: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nv(r) == add32x4(nv(a), nv(b)),
{
    arm_only! { N128(unsafe { vreinterpretq_u8_u32(vaddq_u32(vreinterpretq_u32_u8(a.0), vreinterpretq_u32_u8(b.0))) }) }
}

/// `SHL Vd.2D, #N`.
#[verifier::external_body]
#[inline(always)]
pub fn n_sll64<const N: i32>(a: N128) -> (r: N128)
    requires
        arm_aes(),
        0 < N < 64,
    ensures
        nv(r) == sll64x2(nv(a), N as u64),
{
    arm_only! { N128(unsafe { vreinterpretq_u8_u64(vshlq_n_u64::<N>(vreinterpretq_u64_u8(a.0))) }) }
}

/// `USHR Vd.2D, #N`.
#[verifier::external_body]
#[inline(always)]
pub fn n_srl64<const N: i32>(a: N128) -> (r: N128)
    requires
        arm_aes(),
        0 < N < 64,
    ensures
        nv(r) == srl64x2(nv(a), N as u64),
{
    arm_only! { N128(unsafe { vreinterpretq_u8_u64(vshrq_n_u64::<N>(vreinterpretq_u64_u8(a.0))) }) }
}

/// `EXT` with zero: the register shifted up 8 bytes.
#[verifier::external_body]
#[inline(always)]
pub fn n_bsll8(a: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nv(r) == nv(a) << 64u128,
{
    arm_only! { N128(unsafe { vextq_u8::<8>(vdupq_n_u8(0), a.0) }) }
}

/// `EXT` with zero: the register shifted down 8 bytes.
#[verifier::external_body]
#[inline(always)]
pub fn n_bsrl8(a: N128) -> (r: N128)
    requires
        arm_aes(),
    ensures
        nv(r) == nv(a) >> 64u128,
{
    arm_only! { N128(unsafe { vextq_u8::<8>(a.0, vdupq_n_u8(0)) }) }
}

} // verus!
