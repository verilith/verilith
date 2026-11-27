//! The AArch64 SHA-256 and SHA-512 kernels, with the SHA2 extension
//! (`sha256h`, `sha256h2`, `sha256su0`, `sha256su1`) and the SHA-512
//! instructions (FEAT_SHA512: `sha512h`, `sha512h2`, `sha512su0`,
//! `sha512su1`), proven to compute FIPS 180-4's H(n) over the
//! specifications of those instructions in [`crate::isa`] and
//! verilith-simd's of the NEON intrinsics.
//!
//! Trusted here, on AArch64: the instruction wrappers (each one intrinsic,
//! with the specification of [`crate::isa`]), run-time detection
//! (`has_sha2`, `has_sha512`), and the trampolines that compile the
//! verified kernels with the extensions enabled. On other targets the
//! wrappers run [`crate::isa_ref`], verified implementations of the same
//! specifications, so these kernels verify, and run in the tests, on any
//! machine (slowly), and nothing about them is trusted there.
use crate::isa;
use crate::sha_lemmas::*;
use crate::spec::{self, Vars, K};
use crate::spec512;
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
use verilith_simd::ops::*;
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

broadcast use verilith_simd::neon::group_neon;

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
    from32(crate::isa_ref::sha256h(to32(abcd), to32(efgh), to32(wk)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256h2(efgh: uint8x16_t, abcd: uint8x16_t, wk: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256h2(u32s(n8(efgh)), u32s(n8(abcd)), u32s(n8(wk))),
{
    from32(crate::isa_ref::sha256h2(to32(efgh), to32(abcd), to32(wk)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256su0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su0(u32s(n8(a)), u32s(n8(b))),
{
    from32(crate::isa_ref::sha256su0(to32(a), to32(b)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha256su1(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == isa::sha256su1(u32s(n8(a)), u32s(n8(b)), u32s(n8(c))),
{
    from32(crate::isa_ref::sha256su1(to32(a), to32(b), to32(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512h(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::isa_ref::sha512h(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512h2(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512h2(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::isa_ref::sha512h2(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512su0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su0(u64s(n8(a)), u64s(n8(b))),
{
    from64(crate::isa_ref::sha512su0(to64(a), to64(b)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_sha512su1(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::sha512su1(u64s(n8(a)), u64s(n8(b)), u64s(n8(c))),
{
    from64(crate::isa_ref::sha512su1(to64(a), to64(b), to64(c)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_rev32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev32(n8(a)),
{
    from8(crate::isa_ref::rev32(to8(a)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_rev64(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == isa::rev64(n8(a)),
{
    from8(crate::isa_ref::rev64(to8(a)))
}

#[cfg(not(target_arch = "aarch64"))]
fn emu_add64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == isa::add64x2(u64s(n8(a)), u64s(n8(b))),
{
    from64(crate::isa_ref::add64x2(to64(a), to64(b)))
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

// ---------------------------------------------------------------------------
// SHA-256: proof
// ---------------------------------------------------------------------------

/// The working variables in `sha256h`'s two vectors: `abcd` is (a, b, c, d)
/// and `efgh` is (e, f, g, h), lane 0 first.
pub open spec fn vars2(x: Seq<u32>, y: Seq<u32>) -> Vars {
    Vars { a: x[0], b: x[1], c: x[2], d: x[3], e: y[0], f: y[1], g: y[2], h: y[3] }
}

/// The same as a hash value.
pub open spec fn hv2(x: Seq<u32>, y: Seq<u32>) -> Seq<u32> {
    seq![x[0], x[1], x[2], x[3], y[0], y[1], y[2], y[3]]
}

/// The Arm ARM's `SHAchoose`, `SHAmajority` and Σs are FIPS 180-4's Ch, Maj,
/// Σ0 and Σ1.
proof fn lemma_arm_funcs(x: u32, y: u32, z: u32)
    ensures
        isa::a_choose(x, y, z) == spec::ch(x, y, z),
        isa::a_majority(x, y, z) == spec::maj(x, y, z),
        isa::a_sigma0(x) == spec::big_sigma0(x),
        isa::a_sigma1(x) == spec::big_sigma1(x),
{
    assert(((y ^ z) & x) ^ z == (x & y) ^ (!x & z)) by (bit_vector);
    assert((x & y) | ((x | y) & z) == (x & y) ^ (x & z) ^ (y & z)) by (bit_vector);
}

/// x + (y + z) = (x + y) + z modulo 2^32.
proof fn lemma_assoc(x: u32, y: u32, z: u32)
    ensures
        spec::add(x, spec::add(y, z)) == spec::add(spec::add(x, y), z),
{
    lemma_mod_add(x as int, y + z);
    lemma_mod_add(x + y, z as int);
}

/// The pseudocode's `+` is FIPS 180-4's.
proof fn lemma_add_eq(x: u32, y: u32)
    ensures
        isa::add32(x, y) == spec::add(x, y),
        spec::add(x, y) == spec::add(y, x),
{
}

/// One iteration of `SHA256hash`, with K + W, is one round.
proof fn lemma_hstep(v: Vars, k: u32, w: u32)
    ensures
        ({
            let s = isa::sha256hash_step(
                seq![v.a, v.b, v.c, v.d], seq![v.e, v.f, v.g, v.h], spec::add(k, w));
            vars2(s.0, s.1) == spec::round(v, k, w) && s.0.len() == 4 && s.1.len() == 4
        }),
{
    hide(spec::ch);
    hide(spec::maj);
    hide(spec::big_sigma0);
    hide(spec::big_sigma1);
    hide(isa::a_choose);
    hide(isa::a_majority);
    hide(isa::a_sigma0);
    hide(isa::a_sigma1);
    hide(spec::add);
    hide(isa::add32);
    lemma_arm_funcs(v.e, v.f, v.g);
    lemma_arm_funcs(v.a, v.b, v.c);
    let kw = spec::add(k, w);
    let s1 = spec::big_sigma1(v.e);
    let ch = spec::ch(v.e, v.f, v.g);
    let s0 = spec::big_sigma0(v.a);
    let mj = spec::maj(v.a, v.b, v.c);
    let p1 = spec::add(v.h, s1);
    let x = spec::add(p1, ch);
    let t = spec::add(x, kw);
    lemma_add_eq(v.h, s1);
    lemma_add_eq(p1, ch);
    lemma_add_eq(x, kw);
    lemma_add_eq(t, v.d);
    lemma_add_eq(t, s0);
    lemma_add_eq(spec::add(t, s0), mj);
    lemma_assoc(x, k, w);
    lemma_assoc(t, s0, mj);
}

/// Four rounds of `sha256h`/`sha256h2` with K + W in `wk`.
proof fn lemma_hash4(x: Seq<u32>, y: Seq<u32>, wk: Seq<u32>, ti: int, v0: Vars, m: Seq<u32>)
    requires
        x.len() == 4,
        y.len() == 4,
        wk.len() == 4,
        0 <= ti,
        ti + 4 <= 64,
        forall|j: int| 0 <= j < 4 ==> #[trigger] wk[j] == spec::add(K[ti + j], spec::schedule(m, ti + j)),
        vars2(x, y) == spec::rounds(v0, m, ti as nat),
    ensures
        vars2(isa::sha256h(x, y, wk), isa::sha256h2(y, x, wk)) == spec::rounds(v0, m, (ti + 4) as nat),
{
    hide(spec::round);
    hide(spec::schedule);
    hide(spec::add);
    hide(isa::sha256hash_step);
    assert(wk[0] == spec::add(K[ti + 0], spec::schedule(m, ti + 0)));
    assert(wk[1] == spec::add(K[ti + 1], spec::schedule(m, ti + 1)));
    assert(wk[2] == spec::add(K[ti + 2], spec::schedule(m, ti + 2)));
    assert(wk[3] == spec::add(K[ti + 3], spec::schedule(m, ti + 3)));
    let r0 = spec::rounds(v0, m, ti as nat);
    let r1 = spec::rounds(v0, m, (ti + 1) as nat);
    let r2 = spec::rounds(v0, m, (ti + 2) as nat);
    let r3 = spec::rounds(v0, m, (ti + 3) as nat);
    let r4 = spec::rounds(v0, m, (ti + 4) as nat);
    assert(r1 == spec::round(r0, K[ti], spec::schedule(m, ti)));
    assert(r2 == spec::round(r1, K[ti + 1], spec::schedule(m, ti + 1)));
    assert(r3 == spec::round(r2, K[ti + 2], spec::schedule(m, ti + 2)));
    assert(r4 == spec::round(r3, K[ti + 3], spec::schedule(m, ti + 3)));
    lemma_hstep(r0, K[ti], spec::schedule(m, ti));
    lemma_hstep(r1, K[ti + 1], spec::schedule(m, ti + 1));
    lemma_hstep(r2, K[ti + 2], spec::schedule(m, ti + 2));
    lemma_hstep(r3, K[ti + 3], spec::schedule(m, ti + 3));
    assert(x =~= seq![r0.a, r0.b, r0.c, r0.d]);
    assert(y =~= seq![r0.e, r0.f, r0.g, r0.h]);
    let s1 = isa::sha256hash_step(x, y, wk[0]);
    assert(s1.0 =~= seq![r1.a, r1.b, r1.c, r1.d]);
    assert(s1.1 =~= seq![r1.e, r1.f, r1.g, r1.h]);
    let s2 = isa::sha256hash_step(s1.0, s1.1, wk[1]);
    assert(s2.0 =~= seq![r2.a, r2.b, r2.c, r2.d]);
    assert(s2.1 =~= seq![r2.e, r2.f, r2.g, r2.h]);
    let s3 = isa::sha256hash_step(s2.0, s2.1, wk[2]);
    assert(s3.0 =~= seq![r3.a, r3.b, r3.c, r3.d]);
    assert(s3.1 =~= seq![r3.e, r3.f, r3.g, r3.h]);
}

/// The Arm ARM's σ0 and σ1 forms are FIPS 180-4's.
proof fn lemma_arm_sigmas(x: u32)
    ensures
        isa::ror32(x, 7) ^ isa::ror32(x, 18) ^ (x >> 3u32) == spec::small_sigma0(x),
        isa::su1_sig(x) == spec::small_sigma1(x),
{
}

/// σ1 + (σ0 + W_t) + W_{t+9}, as `sha256su0` then `sha256su1` add, is
/// the schedule's sum.
proof fn lemma_su_sum(s1: u32, s0: u32, w0: u32, w9: u32)
    ensures
        spec::add(spec::add(s1, spec::add(s0, w0)), w9) == spec::add(spec::add(spec::add(s1, w9), s0), w0),
{
    lemma_mod_add(s1 as int, s0 + w0);
    lemma_mod_add(s1 + s0 + w0, w9 as int);
    lemma_mod_add(s1 + w9, s0 as int);
    lemma_mod_add(s1 + w9 + s0, w0 as int);
}

/// `sha256su1(sha256su0(w0, w1), w2, w3)` is the next four words.
proof fn lemma_su(w0: Seq<u32>, w1: Seq<u32>, w2: Seq<u32>, w3: Seq<u32>, m: Seq<u32>, t: int)
    requires
        0 <= t,
        w0 == sched4(m, t),
        w1 == sched4(m, t + 4),
        w2 == sched4(m, t + 8),
        w3 == sched4(m, t + 12),
    ensures
        isa::sha256su1(isa::sha256su0(w0, w1), w2, w3) == sched4(m, t + 16),
{
    hide(spec::small_sigma0);
    hide(spec::small_sigma1);
    hide(isa::su1_sig);
    hide(spec::schedule);
    hide(spec::add);
    hide(isa::add32);
    let s = |j: int| spec::schedule(m, t + j);
    lemma_sched_unfold(m, t);
    lemma_add32_eq(spec::small_sigma0(s(1)), s(0));
    lemma_add32_eq(spec::small_sigma0(s(2)), s(1));
    lemma_add32_eq(spec::small_sigma0(s(3)), s(2));
    lemma_add32_eq(spec::small_sigma0(s(4)), s(3));
    lemma_arm_sigmas(s(1));
    lemma_arm_sigmas(s(2));
    lemma_arm_sigmas(s(3));
    lemma_arm_sigmas(s(4));
    lemma_arm_sigmas(s(14));
    lemma_arm_sigmas(s(15));
    lemma_arm_sigmas(s(16));
    lemma_arm_sigmas(s(17));
    let tw = isa::sha256su0(w0, w1);
    assert(tw[0] == spec::add(spec::small_sigma0(s(1)), s(0)));
    assert(tw[1] == spec::add(spec::small_sigma0(s(2)), s(1)));
    assert(tw[2] == spec::add(spec::small_sigma0(s(3)), s(2)));
    assert(tw[3] == spec::add(spec::small_sigma0(s(4)), s(3)));
    let r = isa::sha256su1(tw, w2, w3);
    lemma_add32_eq(spec::small_sigma1(s(14)), tw[0]);
    lemma_add32_eq(spec::add(spec::small_sigma1(s(14)), tw[0]), s(9));
    lemma_add32_eq(spec::small_sigma1(s(15)), tw[1]);
    lemma_add32_eq(spec::add(spec::small_sigma1(s(15)), tw[1]), s(10));
    lemma_add32_eq(spec::small_sigma1(s(16)), tw[2]);
    lemma_add32_eq(spec::add(spec::small_sigma1(s(16)), tw[2]), s(11));
    lemma_add32_eq(spec::small_sigma1(s(17)), tw[3]);
    lemma_add32_eq(spec::add(spec::small_sigma1(s(17)), tw[3]), s(12));
    lemma_su_sum(spec::small_sigma1(s(14)), spec::small_sigma0(s(1)), s(0), s(9));
    lemma_su_sum(spec::small_sigma1(s(15)), spec::small_sigma0(s(2)), s(1), s(10));
    assert(r[0] == s(16));
    assert(r[1] == s(17));
    lemma_su_sum(spec::small_sigma1(s(16)), spec::small_sigma0(s(3)), s(2), s(11));
    lemma_su_sum(spec::small_sigma1(s(17)), spec::small_sigma0(s(4)), s(3), s(12));
    assert(r[2] == s(18));
    assert(r[3] == s(19));
    assert(r =~= sched4(m, t + 16));
}

// ---------------------------------------------------------------------------
// SHA-256: the kernel
// ---------------------------------------------------------------------------

/// Rounds 4i to 4i + 3 with W_{4i..4i+3} in `w`.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds4(abcd: &mut uint8x16_t, efgh: &mut uint8x16_t, w: uint8x16_t, i: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u32>>)
    requires
        sha2_ext(),
        neon(),
        i < 16,
        u32s(n8(w)) == sched4(m, 4 * i),
        vars2(u32s(n8(*old(abcd))), u32s(n8(*old(efgh)))) == spec::rounds(v0, m, (4 * i) as nat),
    ensures
        vars2(u32s(n8(*final(abcd))), u32s(n8(*final(efgh)))) == spec::rounds(v0, m, (4 * i + 4) as nat),
{
    hide(isa::sha256h);
    hide(isa::sha256h2);
    hide(spec::rounds);
    hide(spec::schedule);
    let t = vaddq_u32(w, vld1q_u32_at(K.as_slice(), 4 * i));
    let abcd0 = *abcd;
    *abcd = vsha256hq(abcd0, *efgh, t);
    *efgh = vsha256h2q(*efgh, abcd0, t);
    proof {
        let ti = 4 * i as int;
        let tv = u32s(n8(t));
        assert forall|j: int| 0 <= j < 4 implies #[trigger] tv[j] == spec::add(K[ti + j], spec::schedule(m, ti + j)) by {
            assert(K@[ti + j] == K[ti + j]);
        }
        lemma_hash4(u32s(n8(abcd0)), u32s(n8(*old(efgh))), tv, ti, v0, m);
    }
}

/// The words of the block at `off`, `16 j` bytes in, big-endian.
#[verifier::spinoff_prover]
#[inline(always)]
fn load_words(p: &[u8], off: usize, j: usize) -> (r: uint8x16_t)
    requires
        neon(),
        j < 4,
        off + 64 <= p@.len(),
    ensures
        u32s(n8(r)) == sched4(spec::words(p@.subrange(off as int, off + 64)), 4 * j),
{
    let _n = p.len();
    let r = vrev32q_u8(vld1q_u8_at(p, off + 16 * j));
    proof {
        let blk = p@.subrange(off as int, off + 64);
        let src = p@.subrange(off + 16 * j, off + 16 * j + 16);
        crate::lanes::lemma_rev32(src);
        let m = spec::words(blk);
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == spec::schedule(m, 4 * j + i) by {
            assert(spec::be32(src, 4 * i) == spec::be32(blk, 4 * (4 * j + i)));
        }
        assert(u32s(n8(r)) =~= sched4(m, 4 * j as int));
    }
    r
}

/// One block: H(i) from H(i-1) in `abcd` and `efgh`.
#[verifier::spinoff_prover]
#[inline(always)]
fn block(abcd: &mut uint8x16_t, efgh: &mut uint8x16_t, p: &[u8], off: usize)
    requires
        sha2_ext(),
        neon(),
        off + 64 <= p@.len(),
    ensures
        hv2(u32s(n8(*final(abcd))), u32s(n8(*final(efgh)))) == spec::compress(
            hv2(u32s(n8(*old(abcd))), u32s(n8(*old(efgh)))),
            p@.subrange(off as int, off + 64),
        ),
{
    let ghost blk = p@.subrange(off as int, off + 64);
    let ghost m = spec::words(blk);
    let ghost h0 = hv2(u32s(n8(*abcd)), u32s(n8(*efgh)));
    let ghost v0 = spec::init(h0);
    let (abcd0, efgh0) = (*abcd, *efgh);
    let mut w0 = load_words(p, off, 0);
    let mut w1 = load_words(p, off, 1);
    let mut w2 = load_words(p, off, 2);
    let mut w3 = load_words(p, off, 3);
    assert(vars2(u32s(n8(*abcd)), u32s(n8(*efgh))) == spec::rounds(v0, m, 0));
    rounds4(abcd, efgh, w0, 0, Ghost(v0), Ghost(m));
    rounds4(abcd, efgh, w1, 1, Ghost(v0), Ghost(m));
    rounds4(abcd, efgh, w2, 2, Ghost(v0), Ghost(m));
    rounds4(abcd, efgh, w3, 3, Ghost(v0), Ghost(m));
    let mut i: usize = 4;
    while i < 16
        invariant
            sha2_ext(),
            neon(),
            4 <= i <= 16,
            u32s(n8(w0)) == sched4(m, 4 * i - 16),
            u32s(n8(w1)) == sched4(m, 4 * i - 12),
            u32s(n8(w2)) == sched4(m, 4 * i - 8),
            u32s(n8(w3)) == sched4(m, 4 * i - 4),
            vars2(u32s(n8(*abcd)), u32s(n8(*efgh))) == spec::rounds(v0, m, (4 * i) as nat),
        decreases 16 - i,
    {
        let w4 = vsha256su1q(vsha256su0q(w0, w1), w2, w3);
        proof {
            lemma_su(u32s(n8(w0)), u32s(n8(w1)), u32s(n8(w2)), u32s(n8(w3)), m, 4 * i - 16);
        }
        rounds4(abcd, efgh, w4, i, Ghost(v0), Ghost(m));
        w0 = w1;
        w1 = w2;
        w2 = w3;
        w3 = w4;
        i = i + 1;
    }
    *abcd = vaddq_u32(*abcd, abcd0);
    *efgh = vaddq_u32(*efgh, efgh0);
    proof {
        reveal(spec::compress);
        assert(hv2(u32s(n8(*abcd)), u32s(n8(*efgh))) =~= spec::compress(h0, blk));
    }
}

/// SHA-256's H(n) from H(0) = `st` over the `n = p.len() / 64` whole blocks
/// of `p`. Run through [`compress_blocks`], which compiles it with the SHA2
/// extension enabled.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress_blocks_body(st: &mut [u32; 8], p: &[u8])
    requires
        sha2_ext(),
        neon(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    let ghost h0 = st@;
    let mut abcd = vld1q_u32_at(st, 0);
    let mut efgh = vld1q_u32_at(st, 4);
    assert(hv2(u32s(n8(abcd)), u32s(n8(efgh))) =~= h0);
    let n = p.len() / 64;
    let mut j: usize = 0;
    while j < n
        invariant
            sha2_ext(),
            neon(),
            n == p@.len() / 64,
            p@.len() <= usize::MAX,
            j <= n,
            st@ == h0,
            hv2(u32s(n8(abcd)), u32s(n8(efgh))) == spec::hash_blocks(h0, p@, j as nat),
        decreases n - j,
    {
        block(&mut abcd, &mut efgh, p, 64 * j);
        j = j + 1;
    }
    vst1q_u32_at(st, 0, abcd);
    vst1q_u32_at(st, 4, efgh);
    assert(st@ =~= spec::hash_blocks(h0, p@, n as nat));
}

/// [`compress_blocks_body`] compiled with the SHA2 extension (trusted only
/// to be that function).
#[verifier::external_body]
#[inline]
pub fn compress_blocks(st: &mut [u32; 8], p: &[u8])
    requires
        sha2_ext(),
        neon(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    // SAFETY: the CPU has the SHA2 extension (the precondition).
    #[cfg(target_arch = "aarch64")]
    unsafe {
        tf::compress_blocks(st, p)
    };
    #[cfg(not(target_arch = "aarch64"))]
    compress_blocks_body(st, p);
}

// ---------------------------------------------------------------------------
// SHA-512: proof
// ---------------------------------------------------------------------------

/// The working variables in the four vectors playing (a, b), (c, d),
/// (e, f), (g, h), lane 0 first.
pub open spec fn vars4(ab: Seq<u64>, cd: Seq<u64>, ef: Seq<u64>, gh: Seq<u64>) -> spec512::Vars {
    spec512::Vars { a: ab[0], b: ab[1], c: cd[0], d: cd[1], e: ef[0], f: ef[1], g: gh[0], h: gh[1] }
}

/// The same as a hash value.
pub open spec fn hv4(ab: Seq<u64>, cd: Seq<u64>, ef: Seq<u64>, gh: Seq<u64>) -> Seq<u64> {
    seq![ab[0], ab[1], cd[0], cd[1], ef[0], ef[1], gh[0], gh[1]]
}

/// W_{2k} and W_{2k+1} of `m`.
pub open spec fn pair(m: Seq<u64>, k: int) -> Seq<u64> {
    seq![spec512::schedule(m, 2 * k), spec512::schedule(m, 2 * k + 1)]
}

pub spec const M64: int = 0x1_0000_0000_0000_0000int;

proof fn lemma_mod_add64(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        ((x % M64) + y) % M64 == (x + y) % M64,
        (x + (y % M64)) % M64 == (x + y) % M64,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, y, M64);
    vstd::arithmetic::div_mod::lemma_mod_twice(x, M64);
    vstd::arithmetic::div_mod::lemma_mod_twice(y, M64);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x % M64, y, M64);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, y % M64, M64);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, M64);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(y, M64);
}

/// The Arm ARM's forms of the SHA-512 functions are FIPS 180-4's.
proof fn lemma_funcs512(x: u64, y: u64, z: u64)
    ensures
        (x & y) ^ (!x & z) == spec512::ch(x, y, z),
        (z & y) ^ (z & x) ^ (y & x) == spec512::maj(x, y, z),
        (x & y) ^ (x & z) ^ (z & y) == spec512::maj(x, y, z),
        isa::ror64(x, 14) ^ isa::ror64(x, 18) ^ isa::ror64(x, 41) == spec512::big_sigma1(x),
        isa::ror64(x, 28) ^ isa::ror64(x, 34) ^ isa::ror64(x, 39) == spec512::big_sigma0(x),
        isa::ror64(x, 1) ^ isa::ror64(x, 8) ^ (x >> 7u64) == spec512::small_sigma0(x),
        isa::ror64(x, 19) ^ isa::ror64(x, 61) ^ (x >> 6u64) == spec512::small_sigma1(x),
{
    assert((z & y) ^ (z & x) ^ (y & x) == (x & y) ^ (x & z) ^ (y & z)) by (bit_vector);
    assert((x & y) ^ (x & z) ^ (z & y) == (x & y) ^ (x & z) ^ (y & z)) by (bit_vector);
}

/// The pseudocode's 64-bit `+` is FIPS 180-4's.
proof fn lemma_eq64(x: u64, y: u64)
    ensures
        isa::add64(x, y) == spec512::add(x, y),
        spec512::add(x, y) == spec512::add(y, x),
{
}

/// (Ch + Σ1) + (K + W + H) is T1 = H + Σ1 + Ch + K + W.
proof fn lemma_t1(ch: u64, s1: u64, k: u64, w: u64, h: u64)
    ensures
        spec512::add(spec512::add(ch, s1), spec512::add(spec512::add(w, k), h))
            == spec512::add(spec512::add(spec512::add(spec512::add(h, s1), ch), k), w),
{
    lemma_mod_add64(w + k, h as int);
    lemma_mod_add64(ch + s1, w + k + h);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(ch + s1, (w + k + h), M64);
    lemma_mod_add64(ch as int + s1, ((w + k) % M64 + h));
    lemma_mod_add64(h + s1, ch as int);
    lemma_mod_add64(h + s1 + ch, k as int);
    lemma_mod_add64(h + s1 + ch + k, w as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(ch + s1, (w + k) % M64 + h, M64);
}

/// (Maj + Σ0) + T1 is T1 + (Σ0 + Maj).
proof fn lemma_a512(mj: u64, s0: u64, t1: u64)
    ensures
        spec512::add(spec512::add(mj, s0), t1) == spec512::add(t1, spec512::add(s0, mj)),
{
    lemma_mod_add64(mj + s0, t1 as int);
    lemma_mod_add64(t1 as int, s0 + mj);
}

/// A round of SHA-512 moves a, b, c to b, c, d and e, f, g to f, g, h.
proof fn lemma_round_shift512(v: spec512::Vars, k: u64, w: u64)
    ensures
        spec512::round(v, k, w).b == v.a,
        spec512::round(v, k, w).c == v.b,
        spec512::round(v, k, w).d == v.c,
        spec512::round(v, k, w).f == v.e,
        spec512::round(v, k, w).g == v.f,
        spec512::round(v, k, w).h == v.g,
{
    hide(spec512::add);
    hide(spec512::ch);
    hide(spec512::maj);
    hide(spec512::big_sigma0);
    hide(spec512::big_sigma1);
}

/// `sha512h` then `sha512h2` are two rounds: `kw` holds K + W of rounds
/// 2i and 2i + 1, and the vectors trade roles as in the kernel.
proof fn lemma_hh(
    ab: Seq<u64>, cd: Seq<u64>, ef: Seq<u64>, gh: Seq<u64>, kw: Seq<u64>,
    k0: u64, w0: u64, k1: u64, w1: u64,
)
    requires
        ab.len() == 2,
        cd.len() == 2,
        ef.len() == 2,
        gh.len() == 2,
        kw == seq![spec512::add(w0, k0), spec512::add(w1, k1)],
    ensures
        ({
            let sum = isa::add64x2(seq![kw[1], kw[0]], gh);
            let t = isa::sha512h(sum, seq![ef[1], gh[0]], seq![cd[1], ef[0]]);
            let gh2 = isa::sha512h2(t, cd, ab);
            let cd2 = isa::add64x2(cd, t);
            vars4(gh2, ab, cd2, ef) == spec512::round(spec512::round(vars4(ab, cd, ef, gh), k0, w0), k1, w1)
                && gh2.len() == 2 && cd2.len() == 2
        }),
{
    hide(spec512::ch);
    hide(spec512::maj);
    hide(spec512::big_sigma0);
    hide(spec512::big_sigma1);
    hide(spec512::small_sigma0);
    hide(spec512::small_sigma1);
    hide(spec512::round);
    hide(spec512::add);
    hide(isa::add64);
    hide(isa::ror64);
    let v = vars4(ab, cd, ef, gh);
    let (a, b, c, d, e, f, g, h) = (ab[0], ab[1], cd[0], cd[1], ef[0], ef[1], gh[0], gh[1]);
    let sum = isa::add64x2(seq![kw[1], kw[0]], gh);
    let t = isa::sha512h(sum, seq![ef[1], gh[0]], seq![cd[1], ef[0]]);
    let gh2 = isa::sha512h2(t, cd, ab);
    let cd2 = isa::add64x2(cd, t);
    let v1 = spec512::round(v, k0, w0);
    let v2 = spec512::round(v1, k1, w1);
    lemma_round_shift512(v, k0, w0);
    lemma_round_shift512(v1, k1, w1);
    lemma_eq64(kw[1], g);
    lemma_eq64(kw[0], h);
    // Round 2i: sha512h's high lane is T1.
    lemma_funcs512(e, f, g);
    lemma_funcs512(a, b, c);
    let (ch0, s10) = (spec512::ch(e, f, g), spec512::big_sigma1(e));
    let t1 = spec512::add(spec512::add(spec512::add(spec512::add(h, s10), ch0), k0), w0);
    let t2 = spec512::add(spec512::big_sigma0(a), spec512::maj(a, b, c));
    lemma_eq64(ch0, s10);
    lemma_eq64(spec512::add(ch0, s10), sum[1]);
    lemma_t1(ch0, s10, k0, w0, h);
    assert(t[1] == t1);
    assert(v1.a == spec512::add(t1, t2) && v1.e == spec512::add(d, t1)) by {
        reveal(spec512::round);
    }
    // Round 2i + 1: its low lane is T1 of (a', a, b, c, e', e, f, g).
    let e1 = v1.e;
    lemma_eq64(t1, d);
    assert(e1 == spec512::add(t[1], d));
    lemma_funcs512(e1, e, f);
    let (ch1, s11) = (spec512::ch(e1, e, f), spec512::big_sigma1(e1));
    let u1 = spec512::add(spec512::add(spec512::add(spec512::add(g, s11), ch1), k1), w1);
    lemma_eq64(ch1, s11);
    lemma_eq64(spec512::add(ch1, s11), sum[0]);
    lemma_t1(ch1, s11, k1, w1, g);
    assert(t[0] == u1);
    // sha512h2: the new a and a'.
    let (mj0, s00) = (spec512::maj(a, b, c), spec512::big_sigma0(a));
    lemma_eq64(mj0, s00);
    lemma_eq64(spec512::add(mj0, s00), t1);
    lemma_a512(mj0, s00, t1);
    assert(gh2[1] == v1.a);
    let a1 = v1.a;
    lemma_funcs512(a1, a, b);
    let u2 = spec512::add(spec512::big_sigma0(a1), spec512::maj(a1, a, b));
    assert(v2.a == spec512::add(u1, u2) && v2.e == spec512::add(c, u1)) by {
        reveal(spec512::round);
    }
    let (mj1, s01) = (spec512::maj(a1, a, b), spec512::big_sigma0(a1));
    lemma_eq64(mj1, s01);
    lemma_eq64(spec512::add(mj1, s01), u1);
    lemma_a512(mj1, s01, u1);
    assert(gh2[0] == v2.a);
    lemma_eq64(c, u1);
    lemma_eq64(d, t1);
    assert(cd2[0] == v2.e);
    assert(cd2[1] == v1.e);
}

/// Words 2i and 2i + 1 by the schedule's definition.
proof fn lemma_sched_unfold512(m: Seq<u64>, i: int)
    requires
        8 <= i,
    ensures
        spec512::schedule(m, 2 * i) == spec512::add(spec512::add(spec512::add(
            spec512::small_sigma1(spec512::schedule(m, 2 * i - 2)), spec512::schedule(m, 2 * i - 7)),
            spec512::small_sigma0(spec512::schedule(m, 2 * i - 15))), spec512::schedule(m, 2 * i - 16)),
        spec512::schedule(m, 2 * i + 1) == spec512::add(spec512::add(spec512::add(
            spec512::small_sigma1(spec512::schedule(m, 2 * i - 1)), spec512::schedule(m, 2 * i - 6)),
            spec512::small_sigma0(spec512::schedule(m, 2 * i - 14))), spec512::schedule(m, 2 * i - 15)),
{
    hide(spec512::add);
    hide(spec512::small_sigma0);
    hide(spec512::small_sigma1);
}

/// (W + σ0) + σ1 + W', as `sha512su0` then `sha512su1` add, is the
/// schedule's sum.
proof fn lemma_su512_sum(w16: u64, s0: u64, s1: u64, w7: u64)
    ensures
        spec512::add(spec512::add(spec512::add(w16, s0), s1), w7)
            == spec512::add(spec512::add(spec512::add(s1, w7), s0), w16),
{
    lemma_mod_add64(w16 + s0, s1 as int);
    lemma_mod_add64(w16 + s0 + s1, w7 as int);
    lemma_mod_add64(s1 + w7, s0 as int);
    lemma_mod_add64(s1 + w7 + s0, w16 as int);
}

/// `sha512su1(sha512su0(cur, nx), prev, ext)` is pair i.
proof fn lemma_su512(cur: Seq<u64>, nx: Seq<u64>, prev: Seq<u64>, a4: Seq<u64>, a5: Seq<u64>, m: Seq<u64>, i: int)
    requires
        8 <= i,
        cur == pair(m, i - 8),
        nx == pair(m, i - 7),
        prev == pair(m, i - 1),
        a4 == pair(m, i - 4),
        a5 == pair(m, i - 3),
    ensures
        isa::sha512su1(isa::sha512su0(cur, nx), prev, seq![a4[1], a5[0]]) == pair(m, i),
{
    hide(spec512::small_sigma0);
    hide(spec512::small_sigma1);
    hide(spec512::schedule);
    lemma_sched_unfold512(m, i);
    let s = |j: int| spec512::schedule(m, j);
    lemma_funcs512(s(2 * i - 15), 0, 0);
    lemma_funcs512(s(2 * i - 14), 0, 0);
    lemma_funcs512(s(2 * i - 2), 0, 0);
    lemma_funcs512(s(2 * i - 1), 0, 0);
    let r = isa::sha512su1(isa::sha512su0(cur, nx), prev, seq![a4[1], a5[0]]);
    lemma_su512_sum(s(2 * i - 16), spec512::small_sigma0(s(2 * i - 15)), spec512::small_sigma1(s(2 * i - 2)), s(2 * i - 7));
    lemma_su512_sum(s(2 * i - 15), spec512::small_sigma0(s(2 * i - 14)), spec512::small_sigma1(s(2 * i - 1)), s(2 * i - 6));
    assert(r =~= pair(m, i));
}

// ---------------------------------------------------------------------------
// SHA-512: the kernel
// ---------------------------------------------------------------------------

/// `v` holds pair k of `m`.
#[verifier::opaque]
pub open spec fn holds2(v: uint8x16_t, m: Seq<u64>, k: int) -> bool {
    u64s(n8(v)) == pair(m, k)
}

/// Rounds 2i and 2i + 1, with W_{2i} and W_{2i+1} in `cur`. `cd` and `gh`
/// are updated, and the next step plays (a, b) .. (g, h) with `gh`, `ab`,
/// `cd`, `ef`.
#[verifier::spinoff_prover]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn rounds2(
    ab: uint8x16_t, cd: &mut uint8x16_t, ef: uint8x16_t, gh: &mut uint8x16_t, cur: uint8x16_t, i: usize,
    Ghost(v0): Ghost<spec512::Vars>, Ghost(m): Ghost<Seq<u64>>,
)
    requires
        sha512_ext(),
        neon(),
        i < 40,
        holds2(cur, m, i as int),
        vars4(u64s(n8(ab)), u64s(n8(*old(cd))), u64s(n8(ef)), u64s(n8(*old(gh)))) == spec512::rounds(v0, m, (2 * i) as nat),
    ensures
        vars4(u64s(n8(*final(gh))), u64s(n8(ab)), u64s(n8(*final(cd))), u64s(n8(ef))) == spec512::rounds(v0, m, (2 * i + 2) as nat),
{
    hide(isa::sha512h);
    hide(isa::sha512h2);
    hide(spec512::rounds);
    hide(spec512::schedule);
    hide(spec512::round);
    reveal(holds2);
    let kw = vaddq_u64(cur, vld1q_u64_at(spec512::K.as_slice(), 2 * i));
    let sum = vaddq_u64(vextq_u8::<8>(kw, kw), *gh);
    let x = vextq_u8::<8>(ef, *gh);
    let y = vextq_u8::<8>(*cd, ef);
    let t = vsha512hq(sum, x, y);
    let gh2 = vsha512h2q(t, *cd, ab);
    let cd2 = vaddq_u64(*cd, t);
    proof {
        let ti = 2 * i as int;
        crate::lanes::lemma_alignr8_x4(n8(kw), n8(kw));
        crate::lanes::lemma_alignr8_x4(n8(*gh), n8(ef));
        crate::lanes::lemma_alignr8_x4(n8(ef), n8(*cd));
        let kv = u64s(n8(kw));
        assert(spec512::K@[ti] == spec512::K[ti] && spec512::K@[ti + 1] == spec512::K[ti + 1]);
        assert(kv =~= seq![
            spec512::add(spec512::schedule(m, ti), spec512::K[ti]),
            spec512::add(spec512::schedule(m, ti + 1), spec512::K[ti + 1]),
        ]);
        lemma_hh(
            u64s(n8(ab)), u64s(n8(*cd)), u64s(n8(ef)), u64s(n8(*gh)), kv,
            spec512::K[ti], spec512::schedule(m, ti), spec512::K[ti + 1], spec512::schedule(m, ti + 1),
        );
        assert(spec512::rounds(v0, m, (ti + 1) as nat) == spec512::round(spec512::rounds(v0, m, ti as nat), spec512::K[ti], spec512::schedule(m, ti))) by {
            reveal_with_fuel(spec512::rounds, 1);
        }
        assert(spec512::rounds(v0, m, (ti + 2) as nat) == spec512::round(spec512::rounds(v0, m, (ti + 1) as nat), spec512::K[ti + 1], spec512::schedule(m, ti + 1))) by {
            reveal_with_fuel(spec512::rounds, 1);
        }
    }
    *gh = gh2;
    *cd = cd2;
}

/// The next pair of schedule words, over `cur`.
#[verifier::spinoff_prover]
#[inline(always)]
fn sched2(cur: &mut uint8x16_t, nx: uint8x16_t, prev: uint8x16_t, a4: uint8x16_t, a5: uint8x16_t, i: usize, Ghost(m): Ghost<Seq<u64>>)
    requires
        sha512_ext(),
        neon(),
        8 <= i,
        holds2(*old(cur), m, i - 8),
        holds2(nx, m, i - 7),
        holds2(prev, m, i - 1),
        holds2(a4, m, i - 4),
        holds2(a5, m, i - 3),
    ensures
        holds2(*final(cur), m, i as int),
{
    let r = vsha512su1q(vsha512su0q(*cur, nx), prev, vextq_u8::<8>(a4, a5));
    proof {
        reveal(holds2);
        crate::lanes::lemma_alignr8_x4(n8(a5), n8(a4));
        lemma_su512(u64s(n8(*cur)), u64s(n8(nx)), u64s(n8(prev)), u64s(n8(a4)), u64s(n8(a5)), m, i as int);
    }
    *cur = r;
}

/// Pair `j` of the block at `off` (j < 8), big-endian.
#[verifier::spinoff_prover]
#[inline(always)]
fn load_pair(p: &[u8], off: usize, j: usize) -> (r: uint8x16_t)
    requires
        neon(),
        j < 8,
        off + 128 <= p@.len(),
    ensures
        holds2(r, spec512::words(p@.subrange(off as int, off + 128)), j as int),
{
    let _n = p.len();
    let r = vrev64q_u8(vld1q_u8_at(p, off + 16 * j));
    proof {
        let blk = p@.subrange(off as int, off + 128);
        let src = p@.subrange(off + 16 * j, off + 16 * j + 16);
        reveal(holds2);
        crate::lanes::lemma_rev64(src);
        let m = spec512::words(blk);
        assert(spec512::be64_at(src, 0) == spec512::be64_at(blk, 8 * (2 * j)));
        assert(spec512::be64_at(src, 8) == spec512::be64_at(blk, 8 * (2 * j + 1)));
        assert(u64s(n8(r)) =~= pair(m, j as int));
    }
    r
}

/// `s0` to `s7` hold pairs b to b + 7.
#[verifier::opaque]
pub open spec fn win(
    s0: uint8x16_t, s1: uint8x16_t, s2: uint8x16_t, s3: uint8x16_t,
    s4: uint8x16_t, s5: uint8x16_t, s6: uint8x16_t, s7: uint8x16_t, m: Seq<u64>, b: int,
) -> bool {
    holds2(s0, m, b) && holds2(s1, m, b + 1) && holds2(s2, m, b + 2) && holds2(s3, m, b + 3)
        && holds2(s4, m, b + 4) && holds2(s5, m, b + 5) && holds2(s6, m, b + 6) && holds2(s7, m, b + 7)
}

/// The 16 pairs of rounds 8g to 8g + 7 (g < 5), the schedule computed over
/// `s` from g = 1 on. The four state vectors are back in their roles at the
/// end.
#[verifier::spinoff_prover]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn group(
    v0: &mut uint8x16_t, v1: &mut uint8x16_t, v2: &mut uint8x16_t, v3: &mut uint8x16_t,
    s0: &mut uint8x16_t, s1: &mut uint8x16_t, s2: &mut uint8x16_t, s3: &mut uint8x16_t,
    s4: &mut uint8x16_t, s5: &mut uint8x16_t, s6: &mut uint8x16_t, s7: &mut uint8x16_t,
    g: usize, Ghost(h): Ghost<spec512::Vars>, Ghost(m): Ghost<Seq<u64>>,
)
    requires
        sha512_ext(),
        neon(),
        g < 5,
        win(*old(s0), *old(s1), *old(s2), *old(s3), *old(s4), *old(s5), *old(s6), *old(s7), m,
            if g == 0 { 0int } else { 8 * g - 8 }),
        vars4(u64s(n8(*old(v0))), u64s(n8(*old(v1))), u64s(n8(*old(v2))), u64s(n8(*old(v3))))
            == spec512::rounds(h, m, (16 * g) as nat),
    ensures
        win(*final(s0), *final(s1), *final(s2), *final(s3), *final(s4), *final(s5), *final(s6), *final(s7), m, 8 * g as int),
        vars4(u64s(n8(*final(v0))), u64s(n8(*final(v1))), u64s(n8(*final(v2))), u64s(n8(*final(v3))))
            == spec512::rounds(h, m, (16 * g + 16) as nat),
{
    hide(spec512::rounds);
    hide(vars4);
    reveal(win);
    let i = 8 * g;
    if g > 0 { sched2(s0, *s1, *s7, *s4, *s5, i, Ghost(m)); }
    rounds2(*v0, v1, *v2, v3, *s0, i, Ghost(h), Ghost(m));
    if g > 0 { sched2(s1, *s2, *s0, *s5, *s6, i + 1, Ghost(m)); }
    rounds2(*v3, v0, *v1, v2, *s1, i + 1, Ghost(h), Ghost(m));
    if g > 0 { sched2(s2, *s3, *s1, *s6, *s7, i + 2, Ghost(m)); }
    rounds2(*v2, v3, *v0, v1, *s2, i + 2, Ghost(h), Ghost(m));
    if g > 0 { sched2(s3, *s4, *s2, *s7, *s0, i + 3, Ghost(m)); }
    rounds2(*v1, v2, *v3, v0, *s3, i + 3, Ghost(h), Ghost(m));
    if g > 0 { sched2(s4, *s5, *s3, *s0, *s1, i + 4, Ghost(m)); }
    rounds2(*v0, v1, *v2, v3, *s4, i + 4, Ghost(h), Ghost(m));
    if g > 0 { sched2(s5, *s6, *s4, *s1, *s2, i + 5, Ghost(m)); }
    rounds2(*v3, v0, *v1, v2, *s5, i + 5, Ghost(h), Ghost(m));
    if g > 0 { sched2(s6, *s7, *s5, *s2, *s3, i + 6, Ghost(m)); }
    rounds2(*v2, v3, *v0, v1, *s6, i + 6, Ghost(h), Ghost(m));
    if g > 0 { sched2(s7, *s0, *s6, *s3, *s4, i + 7, Ghost(m)); }
    rounds2(*v1, v2, *v3, v0, *s7, i + 7, Ghost(h), Ghost(m));
}

/// The 80 rounds of the block at `off`, from `h`.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds80(v0: &mut uint8x16_t, v1: &mut uint8x16_t, v2: &mut uint8x16_t, v3: &mut uint8x16_t, p: &[u8], off: usize, Ghost(h): Ghost<spec512::Vars>)
    requires
        sha512_ext(),
        neon(),
        off + 128 <= p@.len(),
        vars4(u64s(n8(*old(v0))), u64s(n8(*old(v1))), u64s(n8(*old(v2))), u64s(n8(*old(v3)))) == h,
    ensures
        vars4(u64s(n8(*final(v0))), u64s(n8(*final(v1))), u64s(n8(*final(v2))), u64s(n8(*final(v3))))
            == spec512::rounds(h, spec512::words(p@.subrange(off as int, off + 128)), 80),
{
    hide(spec512::rounds);
    hide(spec512::schedule);
    hide(spec512::words);
    hide(vars4);
    let ghost m = spec512::words(p@.subrange(off as int, off + 128));
    let mut s0 = load_pair(p, off, 0);
    let mut s1 = load_pair(p, off, 1);
    let mut s2 = load_pair(p, off, 2);
    let mut s3 = load_pair(p, off, 3);
    let mut s4 = load_pair(p, off, 4);
    let mut s5 = load_pair(p, off, 5);
    let mut s6 = load_pair(p, off, 6);
    let mut s7 = load_pair(p, off, 7);
    assert(win(s0, s1, s2, s3, s4, s5, s6, s7, m, 0)) by {
        reveal(win);
    }
    assert(spec512::rounds(h, m, 0) == h) by {
        reveal_with_fuel(spec512::rounds, 1);
    }
    group(v0, v1, v2, v3, &mut s0, &mut s1, &mut s2, &mut s3, &mut s4, &mut s5, &mut s6, &mut s7, 0, Ghost(h), Ghost(m));
    group(v0, v1, v2, v3, &mut s0, &mut s1, &mut s2, &mut s3, &mut s4, &mut s5, &mut s6, &mut s7, 1, Ghost(h), Ghost(m));
    group(v0, v1, v2, v3, &mut s0, &mut s1, &mut s2, &mut s3, &mut s4, &mut s5, &mut s6, &mut s7, 2, Ghost(h), Ghost(m));
    group(v0, v1, v2, v3, &mut s0, &mut s1, &mut s2, &mut s3, &mut s4, &mut s5, &mut s6, &mut s7, 3, Ghost(h), Ghost(m));
    group(v0, v1, v2, v3, &mut s0, &mut s1, &mut s2, &mut s3, &mut s4, &mut s5, &mut s6, &mut s7, 4, Ghost(h), Ghost(m));
}

/// One block: H(i) from H(i-1) in the four state vectors.
#[verifier::spinoff_prover]
#[inline(always)]
fn block512(v0: &mut uint8x16_t, v1: &mut uint8x16_t, v2: &mut uint8x16_t, v3: &mut uint8x16_t, p: &[u8], off: usize)
    requires
        sha512_ext(),
        neon(),
        off + 128 <= p@.len(),
    ensures
        hv4(u64s(n8(*final(v0))), u64s(n8(*final(v1))), u64s(n8(*final(v2))), u64s(n8(*final(v3)))) == spec512::compress(
            hv4(u64s(n8(*old(v0))), u64s(n8(*old(v1))), u64s(n8(*old(v2))), u64s(n8(*old(v3)))),
            p@.subrange(off as int, off + 128),
        ),
{
    hide(spec512::rounds);
    let ghost blk = p@.subrange(off as int, off + 128);
    let ghost h0 = hv4(u64s(n8(*v0)), u64s(n8(*v1)), u64s(n8(*v2)), u64s(n8(*v3)));
    let (a0, a1, a2, a3) = (*v0, *v1, *v2, *v3);
    rounds80(v0, v1, v2, v3, p, off, Ghost(spec512::init(h0)));
    *v0 = vaddq_u64(*v0, a0);
    *v1 = vaddq_u64(*v1, a1);
    *v2 = vaddq_u64(*v2, a2);
    *v3 = vaddq_u64(*v3, a3);
    proof {
        reveal(spec512::compress);
        assert(hv4(u64s(n8(*v0)), u64s(n8(*v1)), u64s(n8(*v2)), u64s(n8(*v3))) =~= spec512::compress(h0, blk));
    }
}

/// SHA-512's H(n) from H(0) = `st` over the `n = p.len() / 128` whole
/// blocks of `p`. Run through [`compress512_blocks`], which compiles it with
/// the SHA-512 instructions enabled.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress512_blocks_body(st: &mut [u64; 8], p: &[u8])
    requires
        sha512_ext(),
        neon(),
    ensures
        final(st)@ == spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    let ghost h0 = st@;
    let mut v0 = vld1q_u64_at(st, 0);
    let mut v1 = vld1q_u64_at(st, 2);
    let mut v2 = vld1q_u64_at(st, 4);
    let mut v3 = vld1q_u64_at(st, 6);
    assert(hv4(u64s(n8(v0)), u64s(n8(v1)), u64s(n8(v2)), u64s(n8(v3))) =~= h0);
    let n = p.len() / 128;
    let mut j: usize = 0;
    while j < n
        invariant
            sha512_ext(),
            neon(),
            n == p@.len() / 128,
            p@.len() <= usize::MAX,
            j <= n,
            st@ == h0,
            hv4(u64s(n8(v0)), u64s(n8(v1)), u64s(n8(v2)), u64s(n8(v3))) == spec512::hash_blocks(h0, p@, j as nat),
        decreases n - j,
    {
        block512(&mut v0, &mut v1, &mut v2, &mut v3, p, 128 * j);
        j = j + 1;
    }
    vst1q_u64_at(st, 0, v0);
    vst1q_u64_at(st, 2, v1);
    vst1q_u64_at(st, 4, v2);
    vst1q_u64_at(st, 6, v3);
    assert(st@ =~= spec512::hash_blocks(h0, p@, n as nat));
}

/// [`compress512_blocks_body`] compiled with the SHA-512 instructions
/// (trusted only to be that function).
#[verifier::external_body]
#[inline]
pub fn compress512_blocks(st: &mut [u64; 8], p: &[u8])
    requires
        sha512_ext(),
        neon(),
    ensures
        final(st)@ == spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    // SAFETY: the CPU has the SHA-512 instructions (the precondition).
    #[cfg(target_arch = "aarch64")]
    unsafe {
        tf::compress512_blocks(st, p)
    };
    #[cfg(not(target_arch = "aarch64"))]
    compress512_blocks_body(st, p);
}

} // verus!

#[cfg(target_arch = "aarch64")]
mod tf {
    #[target_feature(enable = "sha2")]
    pub(super) unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        let _dit = crate::dit::Dit::on();
        super::compress_blocks_body(st, p)
    }

    #[target_feature(enable = "sha3")]
    pub(super) unsafe fn compress512_blocks(st: &mut [u64; 8], p: &[u8]) {
        let _dit = crate::dit::Dit::on();
        super::compress512_blocks_body(st, p)
    }
}
