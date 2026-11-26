//! Memory primitives vzlib needs beyond `verilith_core::prims`, verified
//! against vstd's specs and verilith-core's trusted `spare` stores.
use vstd::prelude::*;

verus! {

/// Appends the low `k` bytes of `w`, least significant first, with one
/// unaligned 8-byte store (verilith-core's `spare::append8_spare`).
#[inline(always)]
pub fn push_word(v: &mut Vec<u8>, w: u64, k: usize)
    requires
        k <= 8,
    ensures
        final(v)@ == old(v)@ + Seq::new(k as nat, |j: int| ((w >> (8 * j) as u64) & 0xff) as u8),
{
    verilith_core::spare::reserve_spare(v, 8);
    verilith_core::spare::append8_spare(v, w, k);
}

#[inline(always)]
pub fn get16(b: &[u16], i: usize) -> (r: u16)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

#[inline(always)]
pub fn set16(b: &mut [u16], i: usize, v: u16)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

} // verus!
