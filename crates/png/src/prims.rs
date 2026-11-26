//! Memory primitives.
//!
//! The indexing ones skip Rust's bounds check: their `requires` clause is
//! the bounds check, and Verus proves it at every call site, so they cannot
//! go out of bounds in verified code. `get` and `set` are verified against
//! vstd's spec of `get_unchecked`/`get_unchecked_mut`. `copy` is verified
//! against verilith-core's `copy_in`, whose contract it restates byte by
//! byte. Zeroed allocations are verilith-core's `alloc_u8`, re-exported.
pub use verilith_core::prims::alloc_u8;
use vstd::prelude::*;

verus! {

#[inline(always)]
pub fn get(b: &[u8], i: usize) -> (r: u8)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

#[inline(always)]
pub fn set(b: &mut [u8], i: usize, v: u8)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// Copies `src[s..s + n]` to `dst[d..d + n]`.
#[inline(always)]
pub fn copy(dst: &mut [u8], d: usize, src: &[u8], s: usize, n: usize)
    requires
        d + n <= old(dst)@.len(),
        s + n <= src@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|k: int|
            0 <= k < final(dst)@.len() ==> #[trigger] final(dst)@[k] == if d <= k < d + n {
                src@[s + k - d]
            } else {
                old(dst)@[k]
            },
{
    verilith_core::prims::copy_in(dst, d, src, s, n);
}

} // verus!
