//! The SSE2 instructions the scanners use: verilith-simd's `sse2`
//! wrappers (proven there from verilith-simd's specification of each
//! instruction, and shared with verilith-json), and one lemma on masks.
//! Nothing in this file is trusted. SSE2 is part of x86-64, so no feature
//! detection is needed; other targets use the scalar code.
use vstd::prelude::*;

pub use verilith_simd::sse2::*;

verus! {

/// `a & !b` on masks, bit by bit.
pub proof fn lemma_andnot_bit(a: u32, b: u32, k: u32)
    requires
        k < 32,
    ensures
        bit(a & !b, k) == (bit(a, k) && !bit(b, k)),
        bit(a | b, k) == (bit(a, k) || bit(b, k)),
{
    assert(k < 32 ==> ((((a & !b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) && !((b >> k) & 1u32
        == 1u32)))) by (bit_vector);
    assert(k < 32 ==> ((((a | b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) || ((b >> k) & 1u32
        == 1u32)))) by (bit_vector);
}

} // verus!
