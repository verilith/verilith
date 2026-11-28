//! The AArch64 SHA instructions (TRUSTED): the SHA2 extension (`sha256h`,
//! `sha256h2`, `sha256su0`, `sha256su1`) and FEAT_SHA512 (`sha512h`,
//! `sha512h2`, `sha512su0`, `sha512su1`), with `rev32`, `rev64`, 64-bit
//! `add` and the `u64` loads and stores the kernels need, one wrapper each
//! with the specification of [`crate::sha`], and run-time detection
//! (`has_sha2`, `has_sha512`). On other targets the wrappers run
//! [`crate::sha_ref`], verified implementations of the same
//! specifications, so kernels written against them verify, and run in the
//! tests, on any machine, and nothing about them is trusted there.
//! verilith-sha2's `tests/isa.rs` checks every one against
//! [`crate::sha_ref`] on random operands.
#![allow(missing_docs)]
use crate::sha as isa;
use crate::lanes::*;
use crate::neon::*;
use crate::ops::*;
use vstd::prelude::*;

#[cfg(all(feature = "std", target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { std::arch::is_aarch64_feature_detected!($f) }; }
#[cfg(all(not(feature = "std"), target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { cfg!(target_feature = $f) }; }
#[cfg(not(target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { false }; }


#[cfg(target_arch = "aarch64")]
use core::arch::aarch64 as a64;

verus! {

broadcast use crate::neon::group_neon;

/// The CPU running this program has the SHA2 extension (FEAT_SHA256).
pub uninterp spec fn sha2_ext() -> bool;

/// The CPU running this program has the SHA-512 instructions (FEAT_SHA512).
pub uninterp spec fn sha512_ext() -> bool;

/// Whether the CPU has the SHA2 extension, detected at run time (NEON is
/// in the AArch64 baseline). False on other targets.
#[verifier::external_body]
#[inline]
pub fn has_sha2() -> (r: bool)
    ensures
        r ==> sha2_ext() && neon(),
{
    arm_has!("sha2")
}

/// Whether the CPU has the SHA-512 instructions, detected at run time
/// (Rust names them with the SHA-3 ones, `sha3`). False on other targets.
#[verifier::external_body]
#[inline]
pub fn has_sha512() -> (r: bool)
    ensures
        r ==> sha512_ext() && neon(),
{
    arm_has!("sha3")
}

// ---------------------------------------------------------------------------
// The instructions
// ---------------------------------------------------------------------------

/// `vsha256hq_u32`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha256hq(abcd: uint8x16_t, efgh: uint8x16_t, wk: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha2_ext(),
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256h(u32s(n8(abcd)), u32s(n8(efgh)), u32s(n8(wk))),
{
    // SAFETY: the CPU has the SHA2 extension (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u32(a64::vsha256hq_u32(
            a64::vreinterpretq_u32_u8(abcd),
            a64::vreinterpretq_u32_u8(efgh),
            a64::vreinterpretq_u32_u8(wk),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha256h(abcd, efgh, wk);
    r
}

/// `vsha256h2q_u32`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha256h2q(efgh: uint8x16_t, abcd: uint8x16_t, wk: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha2_ext(),
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256h2(u32s(n8(efgh)), u32s(n8(abcd)), u32s(n8(wk))),
{
    // SAFETY: the CPU has the SHA2 extension (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u32(a64::vsha256h2q_u32(
            a64::vreinterpretq_u32_u8(efgh),
            a64::vreinterpretq_u32_u8(abcd),
            a64::vreinterpretq_u32_u8(wk),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha256h2(efgh, abcd, wk);
    r
}

/// `vsha256su0q_u32`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha256su0q(w0_3: uint8x16_t, w4_7: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha2_ext(),
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su0(u32s(n8(w0_3)), u32s(n8(w4_7))),
{
    // SAFETY: the CPU has the SHA2 extension (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u32(a64::vsha256su0q_u32(a64::vreinterpretq_u32_u8(w0_3), a64::vreinterpretq_u32_u8(w4_7)))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha256su0(w0_3, w4_7);
    r
}

/// `vsha256su1q_u32`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha256su1q(tw0_3: uint8x16_t, w8_11: uint8x16_t, w12_15: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha2_ext(),
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su1(u32s(n8(tw0_3)), u32s(n8(w8_11)), u32s(n8(w12_15))),
{
    // SAFETY: the CPU has the SHA2 extension (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u32(a64::vsha256su1q_u32(
            a64::vreinterpretq_u32_u8(tw0_3),
            a64::vreinterpretq_u32_u8(w8_11),
            a64::vreinterpretq_u32_u8(w12_15),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha256su1(tw0_3, w8_11, w12_15);
    r
}

/// `vsha512hq_u64`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha512hq(d: uint8x16_t, n: uint8x16_t, m: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha512_ext(),
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h(u64s(n8(d)), u64s(n8(n)), u64s(n8(m))),
{
    // SAFETY: the CPU has the SHA-512 instructions (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u64(a64::vsha512hq_u64(
            a64::vreinterpretq_u64_u8(d),
            a64::vreinterpretq_u64_u8(n),
            a64::vreinterpretq_u64_u8(m),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha512h(d, n, m);
    r
}

/// `vsha512h2q_u64`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha512h2q(d: uint8x16_t, n: uint8x16_t, m: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha512_ext(),
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h2(u64s(n8(d)), u64s(n8(n)), u64s(n8(m))),
{
    // SAFETY: the CPU has the SHA-512 instructions (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u64(a64::vsha512h2q_u64(
            a64::vreinterpretq_u64_u8(d),
            a64::vreinterpretq_u64_u8(n),
            a64::vreinterpretq_u64_u8(m),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha512h2(d, n, m);
    r
}

/// `vsha512su0q_u64`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha512su0q(d: uint8x16_t, n: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha512_ext(),
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su0(u64s(n8(d)), u64s(n8(n))),
{
    // SAFETY: the CPU has the SHA-512 instructions (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u64(a64::vsha512su0q_u64(a64::vreinterpretq_u64_u8(d), a64::vreinterpretq_u64_u8(n)))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha512su0(d, n);
    r
}

/// `vsha512su1q_u64`.
#[verifier::external_body]
#[inline(always)]
pub fn vsha512su1q(d: uint8x16_t, n: uint8x16_t, m: uint8x16_t) -> (r: uint8x16_t)
    requires
        sha512_ext(),
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su1(u64s(n8(d)), u64s(n8(n)), u64s(n8(m))),
{
    // SAFETY: the CPU has the SHA-512 instructions (the precondition).
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u64(a64::vsha512su1q_u64(
            a64::vreinterpretq_u64_u8(d),
            a64::vreinterpretq_u64_u8(n),
            a64::vreinterpretq_u64_u8(m),
        ))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_sha512su1(d, n, m);
    r
}

/// `vrev32q_u8`.
#[verifier::external_body]
#[inline(always)]
pub fn vrev32q_u8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev32(n8(a)),
{
    // SAFETY: NEON is in the AArch64 baseline.
    #[cfg(target_arch = "aarch64")]
    let r = unsafe { a64::vrev32q_u8(a) };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_rev32(a);
    r
}

/// `vrev64q_u8`.
#[verifier::external_body]
#[inline(always)]
pub fn vrev64q_u8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev64(n8(a)),
{
    // SAFETY: NEON is in the AArch64 baseline.
    #[cfg(target_arch = "aarch64")]
    let r = unsafe { a64::vrev64q_u8(a) };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_rev64(a);
    r
}

/// `vaddq_u64`.
#[verifier::external_body]
#[inline(always)]
pub fn vaddq_u64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::add64x2(u64s(n8(a)), u64s(n8(b))),
{
    // SAFETY: NEON is in the AArch64 baseline.
    #[cfg(target_arch = "aarch64")]
    let r = unsafe {
        a64::vreinterpretq_u8_u64(a64::vaddq_u64(a64::vreinterpretq_u64_u8(a), a64::vreinterpretq_u64_u8(b)))
    };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_add64(a, b);
    r
}

/// `vld1q_u64` at `s[i..i + 2]`.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u64_at(s: &[u64], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 2 <= s@.len(),
    ensures
        u64s(n8(r)) == s@.subrange(i as int, i + 2),
{
    debug_assert!(i + 2 <= s.len());
    // SAFETY: `i + 2 <= s.len()` (the precondition); NEON is in the AArch64
    // baseline.
    #[cfg(target_arch = "aarch64")]
    let r = unsafe { a64::vreinterpretq_u8_u64(a64::vld1q_u64(s.as_ptr().add(i))) };
    #[cfg(not(target_arch = "aarch64"))]
    let r = emu_ld64(s, i);
    r
}

/// `vst1q_u64` at `s[i..i + 2]`.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u64_at(s: &mut [u64], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 2 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u64s(n8(v)) + old(s)@.subrange(i + 2, old(s)@.len() as int),
{
    debug_assert!(i + 2 <= s.len());
    // SAFETY: `i + 2 <= s.len()` (the precondition); NEON is in the AArch64
    // baseline.
    #[cfg(target_arch = "aarch64")]
    unsafe {
        a64::vst1q_u64(s.as_mut_ptr().add(i), a64::vreinterpretq_u64_u8(v))
    };
    #[cfg(not(target_arch = "aarch64"))]
    emu_st64(s, i, v);
}

// ---------------------------------------------------------------------------
// Off AArch64: the instructions from their verified references
// ---------------------------------------------------------------------------

#[cfg(not(target_arch = "aarch64"))]
fn to32(v: uint8x16_t) -> (r: [u32; 4])
    requires
        neon(),
    ensures
        r@ == u32s(n8(v)),
{
    let mut a = [0u32; 4];
    vst1q_u32_at(&mut a, 0, v);
    assert(a@ =~= u32s(n8(v)));
    a
}

#[cfg(not(target_arch = "aarch64"))]
fn from32(a: [u32; 4]) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == a@,
{
    let r = vld1q_u32_at(&a, 0);
    assert(a@.subrange(0, 4) =~= a@);
    r
}

#[cfg(not(target_arch = "aarch64"))]
fn to64(v: uint8x16_t) -> (r: [u64; 2])
    requires
        neon(),
    ensures
        r@ == u64s(n8(v)),
{
    let a = to32(v);
    let r = [(a[0] as u64) | ((a[1] as u64) << 32), (a[2] as u64) | ((a[3] as u64) << 32)];
    assert(r@ =~= u64s(n8(v)));
    r
}

#[cfg(not(target_arch = "aarch64"))]
proof fn lemma_split64(x: u64)
    ensures
        le64(x as u32, (x >> 32u64) as u32) == x,
{
    assert(((x as u32) as u64) | ((((x >> 32u64) as u32) as u64) << 32u64) == x) by (bit_vector);
}

#[cfg(not(target_arch = "aarch64"))]
fn from64(a: [u64; 2]) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == a@,
{
    let w = [a[0] as u32, (a[0] >> 32) as u32, a[1] as u32, (a[1] >> 32) as u32];
    let r = from32(w);
    proof {
        lemma_split64(a[0]);
        lemma_split64(a[1]);
        assert(u64s(n8(r)) =~= a@);
    }
    r
}

#[cfg(not(target_arch = "aarch64"))]
fn to8(v: uint8x16_t) -> (r: [u8; 16])
    requires
        neon(),
    ensures
        r@ == n8(v),
{
    let mut a = [0u8; 16];
    vst1q_u8_at(&mut a, 0, v);
    assert(a@ =~= n8(v));
    a
}

#[cfg(not(target_arch = "aarch64"))]
fn from8(a: [u8; 16]) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == a@,
{
    let r = vld1q_u8_at(&a, 0);
    assert(a@.subrange(0, 16) =~= a@);
    r
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256h(abcd: uint8x16_t, efgh: uint8x16_t, wk: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256h(u32s(n8(abcd)), u32s(n8(efgh)), u32s(n8(wk))),
{
    from32(crate::sha_ref::sha256h(to32(abcd), to32(efgh), to32(wk)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256h2(efgh: uint8x16_t, abcd: uint8x16_t, wk: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256h2(u32s(n8(efgh)), u32s(n8(abcd)), u32s(n8(wk))),
{
    from32(crate::sha_ref::sha256h2(to32(efgh), to32(abcd), to32(wk)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256su0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su0(u32s(n8(a)), u32s(n8(b))),
{
    from32(crate::sha_ref::sha256su0(to32(a), to32(b)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256su1(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su1(u32s(n8(a)), u32s(n8(b)), u32s(n8(c))),
{
    from32(crate::sha_ref::sha256su1(to32(a), to32(b), to32(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512h(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::sha_ref::sha512h(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512h2(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h2(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::sha_ref::sha512h2(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512su0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su0(u64s(n8(a)), u64s(n8(b))),
{
    from64(crate::sha_ref::sha512su0(to64(a), to64(b)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512su1(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su1(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::sha_ref::sha512su1(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_rev32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev32(n8(a)),
{
    from8(crate::sha_ref::rev32(to8(a)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_rev64(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev64(n8(a)),
{
    from8(crate::sha_ref::rev64(to8(a)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_add64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::add64x2(u64s(n8(a)), u64s(n8(b))),
{
    from64(crate::sha_ref::add64x2(to64(a), to64(b)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_ld64(s: &[u64], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 2 <= s@.len(),
    ensures
        u64s(n8(r)) == s@.subrange(i as int, i + 2),
{
    let a = [s[i], s[i + 1]];
    assert(a@ =~= s@.subrange(i as int, i + 2));
    from64(a)
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_st64(s: &mut [u64], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 2 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u64s(n8(v)) + old(s)@.subrange(i + 2, old(s)@.len() as int),
{
    let a = to64(v);
    let ghost s0 = s@;
    s[i] = a[0];
    s[i + 1] = a[1];
    assert(s@ =~= s0.subrange(0, i as int) + u64s(n8(v)) + s0.subrange(i + 2, s0.len() as int));
}

} // verus!
