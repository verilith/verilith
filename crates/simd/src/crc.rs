//! The CRC instructions: SSE4.2's `crc32` (CRC-32C) on x86-64, and on
//! AArch64 the CRC extension's `crc32cb`/`crc32cx` (CRC-32C) and `crc32x`
//! (CRC-32, the zlib one).
//!
//! Each is specified as the bit-reflected CRC with its polynomial, no
//! pre- or post-inversion, over its operand taken little endian (Intel SDM,
//! "CRC32"; Arm ARM, "CRC32CX", "CRC32X"): `crc_bytes(poly, c, bytes)`,
//! built from one-bit steps exactly as the RFCs define the register
//! update. A library proves its own CRC specification equal to these.
//!
//! Trusted: the specifications of the wrappers below, and the detection
//! functions. Off the matching architecture each wrapper is a portable
//! bit-by-bit loop of the same definition, which is what `tests/crc.rs`
//! checks the instructions against on the machines that have them.
use vstd::prelude::*;

verus! {

/// CRC-32C's reversed polynomial (Castagnoli, RFC 3720 §B.4).
pub spec const POLY_CRC32C: u32 = 0x82f6_3b78;

/// CRC-32's reversed polynomial (RFC 1952 §8, ISO 3309).
pub spec const POLY_CRC32: u32 = 0xedb8_8320;

/// One bit of a reflected CRC register update.
pub open spec fn crc_bit(poly: u32, c: u32) -> u32 {
    if c & 1 == 1 {
        (c >> 1u32) ^ poly
    } else {
        c >> 1u32
    }
}

/// `n` bit steps.
pub open spec fn crc_bits(poly: u32, c: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        c
    } else {
        crc_bits(poly, crc_bit(poly, c), (n - 1) as nat)
    }
}

/// The register after the bytes `s`, from `c`.
pub open spec fn crc_bytes(poly: u32, c: u32, s: Seq<u8>) -> u32
    decreases s.len(),
{
    if s.len() == 0 {
        c
    } else {
        crc_bits(poly, crc_bytes(poly, c, s.drop_last()) ^ (s.last() as u32), 8)
    }
}

/// The CPU has a CRC-32C instruction: SSE4.2 on x86-64, the CRC
/// extension on AArch64. Only [`has_crc32c`] establishes it.
pub uninterp spec fn crc32c_cpu() -> bool;

/// The CPU has AArch64's CRC extension (`crc32x`). Only [`has_crc_arm`]
/// establishes it.
pub uninterp spec fn crc_arm() -> bool;

} // verus!

/// The definition, a bit at a time: what runs where the instruction is
/// missing.
#[allow(dead_code)]
fn bits_loop(poly: u32, mut c: u32, d: &[u8]) -> u32 {
    for &x in d {
        c ^= x as u32;
        for _ in 0..8 {
            c = if c & 1 == 1 { (c >> 1) ^ poly } else { c >> 1 };
        }
    }
    c
}

verus! {

/// Whether this CPU has a CRC-32C instruction (run-time detection, or
/// without `std` the target's compile-time features). Always false on
/// other architectures.
#[verifier::external_body]
#[inline]
pub fn has_crc32c() -> (r: bool)
    ensures
        r ==> crc32c_cpu(),
{
    #[cfg(all(feature = "std", target_arch = "x86_64"))]
    return std::is_x86_feature_detected!("sse4.2");
    #[cfg(all(not(feature = "std"), target_arch = "x86_64"))]
    return cfg!(target_feature = "sse4.2");
    #[cfg(all(feature = "std", target_arch = "aarch64"))]
    return std::arch::is_aarch64_feature_detected!("crc");
    #[cfg(all(not(feature = "std"), target_arch = "aarch64"))]
    return cfg!(target_feature = "crc");
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    return false;
}

/// Whether this CPU has AArch64's CRC extension. Always false elsewhere.
#[verifier::external_body]
#[inline]
pub fn has_crc_arm() -> (r: bool)
    ensures
        r ==> crc_arm(),
{
    #[cfg(all(feature = "std", target_arch = "aarch64"))]
    return std::arch::is_aarch64_feature_detected!("crc");
    #[cfg(all(not(feature = "std"), target_arch = "aarch64"))]
    return cfg!(target_feature = "crc");
    #[cfg(not(target_arch = "aarch64"))]
    return false;
}

/// **CRC-32C of eight bytes** (trusted): SSE4.2's `crc32` with a 64-bit
/// operand on x86-64, `crc32cx` on AArch64, over `d[i..i + 8]`. The
/// register is kept 64 bits wide, as x86's instruction takes and returns
/// it, so that no zero extension sits on a dependency chain.
#[verifier::external_body]
#[inline(always)]
pub fn crc32c_u64(c: u64, d: &[u8], i: usize) -> (r: u64)
    requires
        crc32c_cpu(),
        c < 0x1_0000_0000,
        i + 8 <= d@.len(),
    ensures
        r < 0x1_0000_0000,
        r as u32 == crc_bytes(POLY_CRC32C, c as u32, d@.subrange(i as int, i + 8)),
{
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: `i + 8 <= d.len()` (the precondition), and `crc32c_cpu()`
        // means the CPU has SSE4.2.
        unsafe {
            let w = u64::from_le(core::ptr::read_unaligned(d.as_ptr().add(i) as *const u64));
            core::arch::x86_64::_mm_crc32_u64(c, w)
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: as above; `crc32c_cpu()` means the CPU has the CRC
        // extension.
        unsafe {
            let w = u64::from_le(core::ptr::read_unaligned(d.as_ptr().add(i) as *const u64));
            core::arch::aarch64::__crc32cd(c as u32, w) as u64
        }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        bits_loop(0x82f6_3b78, c as u32, &d[i..i + 8]) as u64
    }
}

/// **CRC-32C of one byte** (trusted): `crc32` with an 8-bit operand on
/// x86-64, `crc32cb` on AArch64.
#[verifier::external_body]
#[inline(always)]
pub fn crc32c_u8(c: u32, x: u8) -> (r: u32)
    requires
        crc32c_cpu(),
    ensures
        r == crc_bits(POLY_CRC32C, c ^ (x as u32), 8),
{
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: `crc32c_cpu()` means the CPU has SSE4.2.
        unsafe { core::arch::x86_64::_mm_crc32_u8(c, x) }
    }
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: `crc32c_cpu()` means the CPU has the CRC extension.
        unsafe { core::arch::aarch64::__crc32cb(c, x) }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        bits_loop(0x82f6_3b78, c, &[x])
    }
}

/// **CRC-32 of eight bytes** (trusted): AArch64's `crc32x` over
/// `d[i..i + 8]`. Elsewhere, where `has_crc_arm` is false, the portable
/// loop.
#[verifier::external_body]
#[inline(always)]
pub fn crc32_u64(c: u32, d: &[u8], i: usize) -> (r: u32)
    requires
        crc_arm(),
        i + 8 <= d@.len(),
    ensures
        r == crc_bytes(POLY_CRC32, c, d@.subrange(i as int, i + 8)),
{
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: `i + 8 <= d.len()` (the precondition), and `crc_arm()`
        // means the CPU has the CRC extension.
        unsafe {
            let w = u64::from_le(core::ptr::read_unaligned(d.as_ptr().add(i) as *const u64));
            core::arch::aarch64::__crc32d(c, w)
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        bits_loop(0xedb8_8320, c, &d[i..i + 8])
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        bits_loop(0xedb8_8320, c, &d[i..i + 8])
    }
}

} // verus!
