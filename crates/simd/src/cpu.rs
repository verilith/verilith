//! CPU features.
//!
//! An intrinsic that needs a feature beyond x86-64's baseline SSE2 requires
//! the matching spec predicate, so verified code can only reach it on a path
//! where run-time detection (`has_avx2`, ...) said the CPU has the feature.
//! The predicates are uninterpreted; the detection functions and the
//! implications between features (as `#[target_feature]` defines them) are
//! trusted.
use vstd::prelude::*;

/// Run-time detection of an x86 feature; always false on other targets.
/// Without `std`, the features the target is compiled with.
#[cfg(all(target_arch = "x86_64", feature = "std"))]
macro_rules! detect {
    ($f:tt) => {
        std::is_x86_feature_detected!($f)
    };
}
#[cfg(all(target_arch = "x86_64", not(feature = "std")))]
macro_rules! detect {
    ($f:tt) => {
        cfg!(target_feature = $f)
    };
}
#[cfg(not(target_arch = "x86_64"))]
macro_rules! detect {
    ($f:tt) => {
        false
    };
}

verus! {

/// The CPU running this program supports SSSE3.
pub uninterp spec fn ssse3() -> bool;

/// The CPU running this program supports SSE4.1.
pub uninterp spec fn sse41() -> bool;

/// The CPU running this program supports AVX2.
pub uninterp spec fn avx2() -> bool;

/// The CPU running this program supports BMI1 and BMI2.
pub uninterp spec fn bmi2() -> bool;

/// The CPU running this program supports PCLMULQDQ.
pub uninterp spec fn pclmul() -> bool;

/// The CPU running this program supports POPCNT.
pub uninterp spec fn popcnt() -> bool;

/// The CPU running this program supports AVX-512F.
pub uninterp spec fn avx512f() -> bool;

/// The CPU running this program supports AVX-512BW.
pub uninterp spec fn avx512bw() -> bool;

/// The CPU running this program supports AVX-512 VBMI2.
pub uninterp spec fn avx512vbmi2() -> bool;

/// AVX2 implies SSE4.1, which implies SSSE3 (Rust's `target_feature`
/// implications).
pub broadcast axiom fn axiom_feature_implications()
    ensures
        #[trigger] avx2() ==> sse41(),
        #[trigger] sse41() ==> ssse3(),
;

/// AVX-512 VBMI2 implies AVX-512BW, which implies AVX-512F, which implies
/// AVX2 (Rust's `target_feature` implications).
pub broadcast axiom fn axiom_avx512_implications()
    ensures
        #[trigger] avx512vbmi2() ==> avx512bw(),
        #[trigger] avx512bw() ==> avx512f(),
        #[trigger] avx512f() ==> avx2(),
;

/// The axioms of this module, for `broadcast use group_cpu`.
pub broadcast group group_cpu {
    axiom_feature_implications,
    axiom_avx512_implications,
}

/// Whether the CPU has AVX2, detected at run time; true proves the feature predicate:
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
    detect!("avx2")
}

/// Whether the CPU has SSE4.1, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> sse41()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_sse41() -> (r: bool)
    ensures
        r ==> sse41(),
{
    detect!("sse4.1")
}

/// Whether the CPU has SSSE3, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> ssse3()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_ssse3() -> (r: bool)
    ensures
        r ==> ssse3(),
{
    detect!("ssse3")
}

/// True when this build is compiled for SSSE3 (`-C target-feature=+ssse3`
/// or a `target-cpu` that has it): every CPU the program may run on then
/// has SSSE3, and the compiler inlines its intrinsics anywhere. False
/// otherwise, whatever the CPU; there is no run-time check. For code too
/// small to be worth a call through a `#[target_feature]` function.
#[verifier::external_body]
#[inline(always)]
pub fn compiled_with_ssse3() -> (r: bool)
    ensures
        r ==> ssse3(),
{
    cfg!(all(target_arch = "x86_64", target_feature = "ssse3"))
}

/// Whether the CPU has BMI1 and BMI2, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> bmi2()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_bmi2() -> (r: bool)
    ensures
        r ==> bmi2(),
{
    detect!("bmi1") && detect!("bmi2")
}

/// Whether the CPU has PCLMULQDQ, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> pclmul()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_pclmul() -> (r: bool)
    ensures
        r ==> pclmul(),
{
    detect!("pclmulqdq")
}

/// Whether the CPU has AVX-512F and AVX-512BW, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> avx512bw()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_avx512bw() -> (r: bool)
    ensures
        r ==> avx512bw(),
{
    detect!("avx512f") && detect!("avx512bw")
}

/// Whether the CPU has AVX-512F, BW and VBMI2, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> avx512vbmi2()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_avx512vbmi2() -> (r: bool)
    ensures
        r ==> avx512vbmi2(),
{
    detect!("avx512f") && detect!("avx512bw") && detect!("avx512vbmi2")
}

/// Whether the CPU has POPCNT, detected at run time; true proves the feature predicate:
///
/// ```text
/// ensures  r ==> popcnt()
/// ```
#[verifier::external_body]
#[inline]
pub fn has_popcnt() -> (r: bool)
    ensures
        r ==> popcnt(),
{
    detect!("popcnt")
}

} // verus!
