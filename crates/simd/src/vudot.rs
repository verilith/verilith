//! Byte dot products on AArch64, as verilith-checksum's Adler-32 kernel
//! uses them (TRUSTED).
//!
//! The Armv8.4 dot-product extension's `udot` adds, to each 32-bit lane,
//! the dot product of that lane's four unsigned bytes of two vectors. A
//! row here is 64 bytes, four NEON registers (`NB`), with sixteen 32-bit
//! lanes (`ND`), so verilith-checksum's verified kernel `adlerv::adler32_udot` has the
//! same shape as the AVX-512 one. Each function below is the same NEON
//! instruction on each of the four registers, with an `ensures` on the
//! row's bytes (`nb`) or lanes (`nd`) in terms of `dot::dot4`. Verus
//! takes these on trust. verilith-checksum's `tests/vudot.rs` checks each against a plain
//! reference on random inputs.
//!
//! Each requires `dotprod()`, which `has_dotprod()` ensures after
//! run-time detection. On other CPUs `has_dotprod()` is false and the
//! bodies are plain Rust with the same meaning, so the verified kernel
//! still compiles, and the tests run it, everywhere.
#![allow(unused_imports, unused_unsafe, unsafe_op_in_unsafe_fn)]
#[cfg(verus_only)]
use crate::dot::dot4;
use vstd::prelude::*;

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;

verus! {

/// The CPU running this program has NEON and the dot-product extension.
pub uninterp spec fn dotprod() -> bool;

#[verifier::external_body]
#[inline]
pub fn has_dotprod() -> (r: bool)
    ensures
        r ==> dotprod(),
{
    raw::has()
}

/// 64 bytes.
#[verifier::external_body]
pub struct NB(raw::B);

/// Sixteen 32-bit lanes.
#[verifier::external_body]
pub struct ND(raw::D);

pub uninterp spec fn nb(x: NB) -> Seq<u8>;

pub uninterp spec fn nd(x: ND) -> Seq<u32>;

pub broadcast axiom fn axiom_nlens(a: NB, b: ND)
    ensures
        #[trigger] nb(a).len() == 64,
        #[trigger] nd(b).len() == 16,
;

pub broadcast group group_vudot {
    axiom_nlens,
}

#[verifier::external_body]
#[inline(always)]
pub fn nb_load(d: &[u8], i: usize) -> (r: NB)
    requires
        dotprod(),
        i + 64 <= d@.len(),
    ensures
        nb(r) == d@.subrange(i as int, i + 64),
{
    debug_assert!(i + 64 <= d.len());
    // SAFETY: the 64 bytes from `i` are in `d`.
    NB(unsafe { raw::load(d.as_ptr().add(i)) })
}

#[verifier::external_body]
#[inline(always)]
pub fn nd_zero() -> (r: ND)
    requires
        dotprod(),
    ensures
        nd(r) == Seq::new(16, |j: int| 0u32),
{
    ND(unsafe { raw::zero() })
}

#[verifier::external_body]
#[inline(always)]
pub fn nd_add(a: &ND, b: &ND) -> (r: ND)
    requires
        dotprod(),
    ensures
        nd(r) == Seq::new(16, |j: int| crate::dot::add32(nd(*a)[j] as int, nd(*b)[j] as int)),
{
    ND(unsafe { raw::add(&a.0, &b.0) })
}

/// `udot`: each lane plus the dot product of its four bytes of `x` and of
/// `w`, both unsigned.
#[verifier::external_body]
#[inline(always)]
pub fn nd_dot(acc: &ND, x: &NB, w: &NB) -> (r: ND)
    requires
        dotprod(),
    ensures
        nd(r) == Seq::new(16, |j: int| crate::dot::add32(nd(*acc)[j] as int, dot4(nb(*x), nb(*w), j) as int)),
{
    ND(unsafe { raw::dot(&acc.0, &x.0, &w.0) })
}

#[verifier::external_body]
#[inline(always)]
pub fn nd_store(a: &ND) -> (r: [u32; 16])
    requires
        dotprod(),
    ensures
        r@ == nd(*a),
{
    unsafe { raw::store(&a.0) }
}

} // verus!

/// The instructions, lane `4 * r + l` being lane `l` of register `r` (and
/// byte `16 * r + k` byte `k`), which is how `vld1q_u8_x4` and
/// `vst1q_u32_x4` lay them out.
#[cfg(target_arch = "aarch64")]
mod raw {
    use core::arch::aarch64::*;
    use core::arch::asm;

    pub type B = uint8x16x4_t;
    pub type D = uint32x4x4_t;

    #[inline]
    pub fn has() -> bool {
        std::arch::is_aarch64_feature_detected!("dotprod")
    }

    #[inline(always)]
    pub unsafe fn load(p: *const u8) -> B {
        vld1q_u8_x4(p)
    }

    #[inline(always)]
    pub unsafe fn zero() -> D {
        let z = vdupq_n_u32(0);
        uint32x4x4_t(z, z, z, z)
    }

    #[inline(always)]
    pub unsafe fn add(a: &D, b: &D) -> D {
        uint32x4x4_t(vaddq_u32(a.0, b.0), vaddq_u32(a.1, b.1), vaddq_u32(a.2, b.2), vaddq_u32(a.3, b.3))
    }

    // `vdotq_u32` is not stable Rust yet, so the instruction is written
    // out; `.arch_extension` lets the assembler take it in any function.
    #[inline(always)]
    unsafe fn udot(mut acc: uint32x4_t, x: uint8x16_t, w: uint8x16_t) -> uint32x4_t {
        asm!(
            ".arch_extension dotprod",
            "udot {0:v}.4s, {1:v}.16b, {2:v}.16b",
            inout(vreg) acc,
            in(vreg) x,
            in(vreg) w,
            options(pure, nomem, nostack, preserves_flags),
        );
        acc
    }

    #[inline(always)]
    pub unsafe fn dot(a: &D, x: &B, w: &B) -> D {
        uint32x4x4_t(udot(a.0, x.0, w.0), udot(a.1, x.1, w.1), udot(a.2, x.2, w.2), udot(a.3, x.3, w.3))
    }

    #[inline(always)]
    pub unsafe fn store(a: &D) -> [u32; 16] {
        let mut r = [0u32; 16];
        vst1q_u32_x4(r.as_mut_ptr(), *a);
        r
    }
}

/// Elsewhere: the same operations on arrays, never selected at run time
/// (`has()` is false) but kept so the kernel builds and can be tested.
#[cfg(not(target_arch = "aarch64"))]
mod raw {
    pub type B = [u8; 64];
    pub type D = [u32; 16];

    #[inline]
    pub fn has() -> bool {
        false
    }

    #[inline(always)]
    pub unsafe fn load(p: *const u8) -> B {
        let mut r = [0u8; 64];
        core::ptr::copy_nonoverlapping(p, r.as_mut_ptr(), 64);
        r
    }

    #[inline(always)]
    pub unsafe fn zero() -> D {
        [0; 16]
    }

    #[inline(always)]
    pub unsafe fn add(a: &D, b: &D) -> D {
        core::array::from_fn(|j| a[j].wrapping_add(b[j]))
    }

    #[inline(always)]
    pub unsafe fn dot(a: &D, x: &B, w: &B) -> D {
        core::array::from_fn(|j| {
            (0..4).fold(a[j], |s, k| s.wrapping_add(x[4 * j + k] as u32 * w[4 * j + k] as u32))
        })
    }

    #[inline(always)]
    pub unsafe fn store(a: &D) -> [u32; 16] {
        *a
    }
}
