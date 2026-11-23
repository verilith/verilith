//! CPU-specific checksum kernels (part of the trusted base).
//!
//! - `adler32_update` is verified. On x86-64 it runs the verified byte
//!   dot-product kernels in `adlerv`: `vpdpbusd` on 64-byte rows
//!   with AVX-512 VNNI, `vpmaddubsw`/`vpmaddwd` on 32-byte rows with AVX2.
//!   Trusted are verilith-simd's `vdot` (the instructions' contracts) and the two
//!   trampolines below. On AArch64 with the dot-product extension (every Apple
//!   Silicon CPU, Graviton 2 and later) it runs `adlerv::udot`, `udot`
//!   on 64-byte rows, trusting verilith-simd's `vudot`; NEON is in the AArch64
//!   baseline and the `udot` instruction names its extension itself, so
//!   no trampoline is needed.
//! - `crc32_update` is verified. On x86-64 it folds with carry-less
//!   multiplication (`fold`): 256 bytes at a time with
//!   VPCLMULQDQ on 512-bit vectors when the CPU has AVX-512 and
//!   VPCLMULQDQ, 128 bytes at a time on 256-bit vectors when it has
//!   VPCLMULQDQ without AVX-512 (Zen 3, Alder Lake), 64 bytes at a time
//!   with PCLMULQDQ otherwise. What that trusts is verilith-simd's `clmul` (the
//!   instructions' contracts) and the three trampolines below that compile the kernels with those features. On
//!   AArch64 with the CRC extension (every Apple Silicon CPU) it runs
//!   `lanes::crc32_update`, verified down to one assumption: that
//!   the `crc32x` instruction computes this CRC-32 over its eight bytes
//!   (`lanes::crc_word`). Short inputs and other CPUs get the table code.
//! - `crc32c_update` is verified. With SSE4.2 (x86-64) or the CRC
//!   extension (AArch64) it runs `crc32c::crc32c_words`, eight
//!   bytes per instruction, verified down to one assumption: that the
//!   instruction computes CRC-32C over its eight bytes
//!   (`crc32c::crc32c_word`). Trusted here is the trampoline that compiles
//!   it with the feature enabled. Other CPUs get the table code.
#![allow(unsafe_op_in_unsafe_fn)]
#[cfg(verus_only)]
use crate::crc32c::crc32c_from;
#[cfg(verus_only)]
use crate::{adler_from, crc_from};
use vstd::prelude::*;

// Run-time CPU feature detection needs `std`; a `no_std` build uses only
// the features the target is compiled for.
#[cfg(all(feature = "std", target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { std::arch::is_aarch64_feature_detected!($f) }; }
#[cfg(all(not(feature = "std"), target_arch = "aarch64"))]
macro_rules! arm_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

/// Adds `d` to the Adler-32 sums `(a, b)` with AVX2. Call only after `has_avx2` returned true.
///
/// ```text
/// requires a < super::ADLER_MOD
///          b < super::ADLER_MOD
/// ensures  (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@)
/// ```
pub fn adler32_update(a: u32, b: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@),
{
    #[cfg(target_arch = "x86_64")]
    {
        if d.len() >= 64 && verilith_simd::vdot::has_vnni512() {
            return adler32_vnni(a, b, d);
        }
        if d.len() >= 32 && verilith_simd::vdot::has_avx2() {
            return adler32_avx2(a, b, d);
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if d.len() >= 64 && verilith_simd::vudot::has_dotprod() {
            return super::adlerv::udot::adler32_udot(a, b, d);
        }
    }
    super::adler32_update(a, b, d)
}

/// Trusted: `adlerv::adler32_vnni` compiled with `avx512f,avx512bw,avx512vnni`
/// enabled, through `tf::adler32_vnni`; the contract is the verified
/// kernel's. The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn adler32_vnni(a: u32, b: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        verilith_simd::vdot::vnni512(),
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@),
{
    // SAFETY: only called after `has_vnni512` returned true.
    unsafe { tf::adler32_vnni(a, b, d) }
}

/// Trusted: `adlerv::adler32_avx2` compiled with `avx2` enabled, through
/// `tf::adler32_avx2`; the contract is the verified kernel's.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn adler32_avx2(a: u32, b: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        verilith_simd::vdot::avx2(),
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@),
{
    // SAFETY: only called after `has_avx2` returned true.
    unsafe { tf::adler32_avx2(a, b, d) }
}

/// Adds `d` to the CRC-32 register `reg` with the Arm CRC instructions. Call only after `has_arm_crc` returned true.
///
/// ```text
/// ensures  r == crc_from(reg, d@)
/// ```
pub fn crc32_update(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc_from(reg, d@),
{
    #[cfg(target_arch = "x86_64")]
    {
        if d.len() >= VPCLMUL_MIN && verilith_simd::clmul::has_vpclmul() {
            return crc32_vpclmul(reg, d);
        }
        if d.len() >= VPCLMUL256_MIN && verilith_simd::clmul::has_vpclmul256() {
            return crc32_vpclmul256(reg, d);
        }
        if d.len() >= PCLMUL_MIN && verilith_simd::clmul::has_pclmul() {
            return crc32_pclmul(reg, d);
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if d.len() >= 16 && has_arm_crc() {
            return crc32_arm(reg, d);
        }
    }
    super::crc32_update(reg, d)
}

/// The shortest input the 512-bit kernel takes (it needs 256 bytes; below
/// 512 the 256-bit kernel is as fast).
#[cfg(target_arch = "x86_64")]
pub const VPCLMUL_MIN: usize = 512;

/// The shortest input the 256-bit kernel takes (it needs 128 bytes).
#[cfg(target_arch = "x86_64")]
pub const VPCLMUL256_MIN: usize = 128;

/// The shortest input the 128-bit kernel takes (it needs 64 bytes).
#[cfg(target_arch = "x86_64")]
pub const PCLMUL_MIN: usize = 64;

/// Trusted: `fold::crc32_vpclmul` compiled with `avx512f,vpclmulqdq`
/// enabled, through `tf::crc32_vpclmul`; the contract is the verified
/// kernel's. The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn crc32_vpclmul(reg: u32, d: &[u8]) -> (r: u32)
    requires
        verilith_simd::clmul::vpclmul(),
        d@.len() >= 256,
    ensures
        r == crc_from(reg, d@),
{
    // SAFETY: only called after `has_vpclmul` returned true.
    unsafe { tf::crc32_vpclmul(reg, d) }
}

/// Trusted: `fold::crc32_vpclmul256` compiled with `avx2,vpclmulqdq`
/// enabled, through `tf::crc32_vpclmul256`; the contract is the verified
/// kernel's.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn crc32_vpclmul256(reg: u32, d: &[u8]) -> (r: u32)
    requires
        verilith_simd::clmul::vpclmul256(),
        d@.len() >= 128,
    ensures
        r == crc_from(reg, d@),
{
    // SAFETY: only called after `has_vpclmul256` returned true.
    unsafe { tf::crc32_vpclmul256(reg, d) }
}

/// Trusted: `fold::crc32_pclmul` compiled with `pclmulqdq` enabled,
/// through `tf::crc32_pclmul`; the contract is the verified kernel's.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn crc32_pclmul(reg: u32, d: &[u8]) -> (r: u32)
    requires
        verilith_simd::clmul::pclmul(),
        d@.len() >= 64,
    ensures
        r == crc_from(reg, d@),
{
    // SAFETY: only called after `has_pclmul` returned true.
    unsafe { tf::crc32_pclmul(reg, d) }
}

/// The CPU has the CRC32 instructions (`crc32x`); what `lanes::crc_word`
/// needs.
#[cfg(target_arch = "aarch64")]
#[verifier::external_body]
#[inline]
fn has_arm_crc() -> bool {
    arm_has!("crc")
}

/// Trusted: `lanes::crc32_update` compiled with the CRC extension, so
/// that `lanes::crc_word` is one `crc32x`. The caller checks the CPU.
#[cfg(target_arch = "aarch64")]
#[verifier::external_body]
fn crc32_arm(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc_from(reg, d@),
{
    // SAFETY: only called after `has_arm_crc` returned true.
    unsafe { arm_crc::crc32_update(reg, d) }
}

/// Adds `d` to the CRC-32C register `reg`, with SSE4.2 or the Arm CRC instructions when the CPU has them, else in software.
///
/// ```text
/// ensures  r == crc32c_from(reg, d@)
/// ```
pub fn crc32c_update(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc32c_from(reg, d@),
{
    if d.len() >= 8 && super::crc32c::has_crc32c() {
        return crc32c_hw(reg, d);
    }
    super::crc32c_update(reg, d)
}

/// Trusted: `crc32c::crc32c_words` compiled with SSE4.2 (x86-64) or the
/// CRC extension (AArch64) enabled, so that `crc32c::crc32c_word` is one
/// instruction; the contract is the verified kernel's. The caller checks
/// the CPU first.
#[verifier::external_body]
fn crc32c_hw(reg: u32, d: &[u8]) -> (r: u32)
    requires
        super::crc32c::crc32c_cpu(),
    ensures
        r == crc32c_from(reg, d@),
{
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: only called after `has_crc32c` returned true.
        unsafe { tf::crc32c_sse42(reg, d) }
    }
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: only called after `has_crc32c` returned true.
        unsafe { arm_crc::crc32c_words(reg, d) }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        super::crc32c::crc32c_words(reg, d)
    }
}

} // verus!

/// Trampolines that compile a verified kernel with the target features
/// its instructions need. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[target_feature(enable = "avx512f,avx512bw,avx512vnni")]
    pub(super) unsafe fn adler32_vnni(a: u32, b: u32, d: &[u8]) -> (u32, u32) {
        crate::adlerv::adler32_vnni(a, b, d)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn adler32_avx2(a: u32, b: u32, d: &[u8]) -> (u32, u32) {
        crate::adlerv::adler32_avx2(a, b, d)
    }

    #[target_feature(enable = "avx512f,vpclmulqdq,pclmulqdq")]
    pub(super) unsafe fn crc32_vpclmul(reg: u32, d: &[u8]) -> u32 {
        crate::fold::crc32_vpclmul(reg, d)
    }

    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    pub(super) unsafe fn crc32_vpclmul256(reg: u32, d: &[u8]) -> u32 {
        crate::fold::crc32_vpclmul256(reg, d)
    }

    #[target_feature(enable = "pclmulqdq")]
    pub(super) unsafe fn crc32_pclmul(reg: u32, d: &[u8]) -> u32 {
        crate::fold::crc32_pclmul(reg, d)
    }

    #[target_feature(enable = "sse4.2")]
    pub(super) unsafe fn crc32c_sse42(reg: u32, d: &[u8]) -> u32 {
        crate::crc32c::crc32c_words(reg, d)
    }
}

#[cfg(target_arch = "aarch64")]
mod arm_crc {
    /// `lanes::crc32_update`, compiled with the CRC extension enabled so
    /// that `lanes::crc_word` becomes one `crc32x` instruction.
    #[target_feature(enable = "crc")]
    pub unsafe fn crc32_update(reg: u32, d: &[u8]) -> u32 {
        crate::lanes::crc32_update(reg, d)
    }

    /// `crc32c::crc32c_words`, compiled with the CRC extension enabled so
    /// that `crc32c::crc32c_word` becomes one `crc32cx` instruction.
    #[target_feature(enable = "crc")]
    pub unsafe fn crc32c_words(reg: u32, d: &[u8]) -> u32 {
        crate::crc32c::crc32c_words(reg, d)
    }
}
