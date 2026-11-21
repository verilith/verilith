//! Memory primitives vzlib needs beyond `verilith_core::prims`. Trusted: each is
//! `#[verifier::external_body]`, and its `requires` clause is the fact Verus
//! proves at every call site.
use vstd::prelude::*;

verus! {

/// Appends the low `k` bytes of `w`, least significant first, with one
/// unaligned 8-byte store.
#[verifier::external_body]
#[inline(always)]
pub fn push_word(v: &mut Vec<u8>, w: u64, k: usize)
    requires
        k <= 8,
    ensures
        final(v)@ == old(v)@ + Seq::new(k as nat, |j: int| ((w >> (8 * j) as u64) & 0xff) as u8),
{
    v.reserve(8);
    // SAFETY: `reserve` made room for 8 more bytes; `k <= 8` of them are
    // kept, and they are initialized by the store.
    unsafe {
        let n = v.len();
        std::ptr::write_unaligned(v.as_mut_ptr().add(n) as *mut u64, w.to_le());
        v.set_len(n + k);
    }
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
