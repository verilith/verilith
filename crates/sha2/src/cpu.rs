//! The kernel dispatch: [`compress_blocks`] and [`compress512_blocks`] run
//! the fastest kernel the CPU has, all of them verified.
//!
//! - On x86-64 with the SHA extensions (SHA-NI: Intel since Goldmont and
//!   Ice Lake, AMD since Zen), [`crate::shani`]: `sha256rnds2`,
//!   `sha256msg1` and `sha256msg2`, the method of Intel's "New Instructions
//!   Supporting the Secure Hash Algorithm on Intel Architecture Processors"
//!   (2013).
//! - On AArch64 with the SHA2 extension (every Apple Silicon CPU, and most
//!   ARMv8 server and phone cores), [`crate::armv8`]: `sha256h`,
//!   `sha256h2`, `sha256su0` and `sha256su1`; and for the SHA-512 family
//!   with the ARMv8.2 SHA-512 instructions (`sha512h`, `sha512h2`,
//!   `sha512su0`, `sha512su1`; Apple M1 and later, Neoverse V1 and later).
//! - On x86-64 with AVX2 (and no SHA-NI for SHA-256), the verified rounds
//!   with the message schedule computed for two blocks at once with AVX2 and
//!   pipelined into the rounds (`crate::avx2`).
//! - Otherwise the verified portable kernel, compiled with BMI2 where the
//!   CPU has it (as verilith-core does for Adler-32 with AVX2: the same
//!   verified code, other instruction selection).
//!
//! The instruction kernels are proven against the instructions'
//! specifications in [`crate::isa`]. The dispatch is verified too: each
//! kernel requires its CPU-feature predicate, which only run-time detection
//! establishes. What is trusted here is that detection, and the
//! trampolines below that compile a verified kernel with the target
//! features it needs (Verus does not accept `#[target_feature]` on verified
//! code): each is one call of that kernel, with its contract. x86-64 has
//! SHA-512 instructions only on its newest CPUs (Arrow Lake, Lunar Lake),
//! and no kernel for them is written yet.
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::spec;

// Run-time CPU feature detection needs `std`; a `no_std` build uses only
// the features the target is compiled for, as in verilith-core. (For the
// test helpers below; the dispatch uses the `has_*` functions.)
#[cfg(all(feature = "std", target_arch = "x86_64"))]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(all(not(feature = "std"), target_arch = "x86_64"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

/// H(n) from H(0) = `st` over the `n = p.len() / 64` whole blocks of `p`,
/// with the fastest kernel this CPU has.
#[inline]
pub fn compress_blocks(st: &mut [u32; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    #[cfg(target_arch = "x86_64")]
    {
        if crate::shani::has_shani() {
            crate::shani::compress_blocks(st, p);
            return;
        }
    }
    if crate::armv8::has_sha2() {
        crate::armv8::compress_blocks(st, p);
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        if verilith_simd::cpu::has_avx2() && verilith_simd::cpu::has_bmi2() {
            avx2_256(st, p);
            return;
        }
        if verilith_simd::cpu::has_bmi2() {
            bmi2_256(st, p);
            return;
        }
    }
    crate::compress::compress_blocks(st, p)
}

/// SHA-512's H(n) from H(0) = `st` over the `n = p.len() / 128` whole
/// blocks of `p`, with the fastest kernel this CPU has.
#[inline]
pub fn compress512_blocks(st: &mut [u64; 8], p: &[u8])
    ensures
        final(st)@ == crate::spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    if crate::armv8::has_sha512() {
        crate::armv8::compress512_blocks(st, p);
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        if verilith_simd::cpu::has_avx2() && verilith_simd::cpu::has_bmi2() {
            avx2_512(st, p);
            return;
        }
        if verilith_simd::cpu::has_bmi2() {
            bmi2_512(st, p);
            return;
        }
    }
    crate::compress512::compress_blocks(st, p)
}

/// [`crate::compress::compress_blocks`] compiled with BMI2.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline]
fn bmi2_256(st: &mut [u32; 8], p: &[u8])
    requires
        verilith_simd::cpu::bmi2(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    // SAFETY: the CPU has BMI2 (the precondition).
    unsafe { bmi2::compress_blocks(st, p) }
}

/// [`crate::compress512::compress_blocks`] compiled with BMI2.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline]
fn bmi2_512(st: &mut [u64; 8], p: &[u8])
    requires
        verilith_simd::cpu::bmi2(),
    ensures
        final(st)@ == crate::spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    // SAFETY: the CPU has BMI2 (the precondition).
    unsafe { bmi2::compress512_blocks(st, p) }
}

/// [`crate::compress::compress_blocks_pipe`] compiled with AVX2 and BMI2.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline]
fn avx2_256(st: &mut [u32; 8], p: &[u8])
    requires
        verilith_simd::cpu::avx2(),
        verilith_simd::cpu::bmi2(),
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    // SAFETY: the CPU has AVX2 and BMI2 (the precondition).
    unsafe { bmi2::compress_blocks_avx2(st, p) }
}

/// [`crate::compress512::compress_blocks_pipe`] compiled with AVX2 and BMI2.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline]
fn avx2_512(st: &mut [u64; 8], p: &[u8])
    requires
        verilith_simd::cpu::avx2(),
        verilith_simd::cpu::bmi2(),
    ensures
        final(st)@ == crate::spec512::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    // SAFETY: the CPU has AVX2 and BMI2 (the precondition).
    unsafe { bmi2::compress512_blocks_avx2(st, p) }
}

/// [`crate::compress::pair_kw`], compiled with AVX2 and BMI2 and out of
/// line (see [`pair_avx2`]).
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub fn pair256_avx2(
    st: &mut [u32; 8],
    cur0: &[u32; 64],
    cur1: &[u32; 64],
    b0: Ghost<Seq<u8>>,
    b1: Ghost<Seq<u8>>,
    p: &[u8],
    o0: usize,
    o1: usize,
    nxt0: &mut [u32; 64],
    nxt1: &mut [u32; 64],
)
    requires
        verilith_simd::cpu::avx2(),
        crate::compress::kw_schedule(cur0@, crate::spec::words(b0@)),
        crate::compress::kw_schedule(cur1@, crate::spec::words(b1@)),
        o0 + 64 <= p@.len(),
        o1 + 64 <= p@.len(),
    ensures
        final(st)@ == crate::spec::compress(crate::spec::compress(old(st)@, b0@), b1@),
        crate::compress::kw_schedule(final(nxt0)@, crate::spec::words(p@.subrange(o0 as int, o0 + 64))),
        crate::compress::kw_schedule(final(nxt1)@, crate::spec::words(p@.subrange(o1 as int, o1 + 64))),
{
    // SAFETY: only reached from `compress_blocks_avx2`, which runs where
    // the CPU has AVX2 and BMI2.
    unsafe { bmi2::pair256_avx2(st, cur0, cur1, b0, b1, p, o0, o1, nxt0, nxt1) }
}

/// [`crate::compress512::pair_kw`], compiled with AVX2 and BMI2 and out of
/// line, so that the pipelined loop calls one copy of it. Trusted only to
/// be that function: its contract is the verified function's.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub fn pair_avx2(
    st: &mut [u64; 8],
    cur0: &[u64; 80],
    cur1: &[u64; 80],
    b0: Ghost<Seq<u8>>,
    b1: Ghost<Seq<u8>>,
    p: &[u8],
    o0: usize,
    o1: usize,
    nxt0: &mut [u64; 80],
    nxt1: &mut [u64; 80],
)
    requires
        verilith_simd::cpu::avx2(),
        crate::compress512::kw_schedule(cur0@, crate::spec512::words(b0@)),
        crate::compress512::kw_schedule(cur1@, crate::spec512::words(b1@)),
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        final(st)@ == crate::spec512::compress(crate::spec512::compress(old(st)@, b0@), b1@),
        crate::compress512::kw_schedule(final(nxt0)@, crate::spec512::words(p@.subrange(o0 as int, o0 + 128))),
        crate::compress512::kw_schedule(final(nxt1)@, crate::spec512::words(p@.subrange(o1 as int, o1 + 128))),
{
    // SAFETY: only reached from `compress512_blocks_avx2`, which runs where
    // the CPU has AVX2 and BMI2.
    unsafe { bmi2::pair_avx2(st, cur0, cur1, b0, b1, p, o0, o1, nxt0, nxt1) }
}

} // verus!

/// Which kernel [`compress512_blocks`] runs on this CPU: `"armv8-sha512"`
/// or `"portable"`.
pub fn kernel512() -> &'static str {
    if crate::armv8::has_sha512() {
        return "armv8-sha512";
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") && x86_has!("bmi2") {
            return "avx2 schedule";
        }
        if x86_has!("bmi2") {
            return "portable (bmi2)";
        }
    }
    "portable"
}

/// Which kernel [`compress_blocks`] runs on this CPU: `"sha-ni"`,
/// `"armv8-sha2"` or `"portable"`.
pub fn kernel() -> &'static str {
    #[cfg(target_arch = "x86_64")]
    {
        if crate::shani::has_shani() {
            return "sha-ni";
        }
    }
    if crate::armv8::has_sha2() {
        return "armv8-sha2";
    }
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") && x86_has!("bmi2") {
            return "avx2 schedule";
        }
        if x86_has!("bmi2") {
            return "portable (bmi2)";
        }
    }
    "portable"
}

/// The verified portable kernels, compiled a second time with BMI2, whose
/// three-operand rotate (`rorx`) saves the moves around each rotation.
/// The code is the same; only instruction selection differs.
#[cfg(target_arch = "x86_64")]
pub(crate) mod bmi2 {
    #[target_feature(enable = "bmi2")]
    pub unsafe fn compress_blocks(st: &mut [u32; 8], p: &[u8]) {
        crate::compress::compress_blocks(st, p)
    }

    #[target_feature(enable = "bmi2")]
    pub unsafe fn compress512_blocks(st: &mut [u64; 8], p: &[u8]) {
        crate::compress512::compress_blocks(st, p)
    }

    /// The verified rounds over the AVX2 schedule (`crate::avx2`), which
    /// needs AVX2 enabled for its intrinsics to be inlined.
    /// SHA-256's pipelined kernel, for CPUs with AVX2 and no SHA-NI.
    #[target_feature(enable = "avx2,bmi2")]
    pub unsafe fn compress_blocks_avx2(st: &mut [u32; 8], p: &[u8]) {
        crate::compress::compress_blocks_pipe(st, p)
    }

    /// One pair of SHA-256's pipelined loop (see `cpu::pair256_avx2`).
    #[target_feature(enable = "avx2,bmi2")]
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    pub unsafe fn pair256_avx2(
        st: &mut [u32; 8],
        cur0: &[u32; 64],
        cur1: &[u32; 64],
        b0: vstd::prelude::Ghost<vstd::prelude::Seq<u8>>,
        b1: vstd::prelude::Ghost<vstd::prelude::Seq<u8>>,
        p: &[u8],
        o0: usize,
        o1: usize,
        nxt0: &mut [u32; 64],
        nxt1: &mut [u32; 64],
    ) {
        crate::compress::pair_kw(st, cur0, cur1, b0, b1, p, o0, o1, nxt0, nxt1)
    }

    #[target_feature(enable = "avx2,bmi2")]
    pub unsafe fn compress512_blocks_avx2(st: &mut [u64; 8], p: &[u8]) {
        crate::compress512::compress_blocks_pipe(st, p)
    }

    /// One pair of the pipelined loop (see `cpu::pair_avx2`).
    #[target_feature(enable = "avx2,bmi2")]
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    pub unsafe fn pair_avx2(
        st: &mut [u64; 8],
        cur0: &[u64; 80],
        cur1: &[u64; 80],
        b0: vstd::prelude::Ghost<vstd::prelude::Seq<u8>>,
        b1: vstd::prelude::Ghost<vstd::prelude::Seq<u8>>,
        p: &[u8],
        o0: usize,
        o1: usize,
        nxt0: &mut [u64; 80],
        nxt1: &mut [u64; 80],
    ) {
        crate::compress512::pair_kw(st, cur0, cur1, b0, b1, p, o0, o1, nxt0, nxt1)
    }
}

/// For the tests: the verified portable kernels as compiled with BMI2, if
/// the CPU has it (on a CPU with SHA-NI, `compress_blocks` never runs it).
#[doc(hidden)]
pub type Kernel256 = fn(&mut [u32; 8], &[u8]);
#[doc(hidden)]
pub type Kernel512 = fn(&mut [u64; 8], &[u8]);

#[doc(hidden)]
pub fn bmi2_kernels() -> Option<(Kernel256, Kernel512)> {
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("bmi2") {
            // SAFETY: only returned when the CPU has BMI2.
            return Some((
                |st, p| unsafe { bmi2::compress_blocks(st, p) },
                |st, p| unsafe { bmi2::compress512_blocks(st, p) },
            ));
        }
    }
    None
}

/// For the tests: the AVX2 kernels (the pipelined schedule), if the CPU has
/// AVX2 and BMI2. On a CPU with SHA-NI, `compress_blocks` never runs the
/// SHA-256 one.
#[doc(hidden)]
pub fn avx2_kernels() -> Option<(Kernel256, Kernel512)> {
    #[cfg(target_arch = "x86_64")]
    {
        if x86_has!("avx2") && x86_has!("bmi2") {
            // SAFETY: only returned when the CPU has AVX2 and BMI2.
            return Some((
                |st, p| unsafe { bmi2::compress_blocks_avx2(st, p) },
                |st, p| unsafe { bmi2::compress512_blocks_avx2(st, p) },
            ));
        }
    }
    None
}
