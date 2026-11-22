//! Indexing without Rust's bounds check. Each function's `requires` clause
//! is the bounds check, and Verus proves it at every call, so verified code
//! cannot go out of bounds through them. They are verified against vstd's
//! specifications of `get_unchecked` and `get_unchecked_mut`.
use vstd::prelude::*;

verus! {

#[inline(always)]
pub fn sget<T: Copy>(b: &[T], i: usize) -> (r: T)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

/// A reference to element `i`.
#[inline(always)]
pub fn sref<T>(b: &[T], i: usize) -> (r: &T)
    requires
        i < b@.len(),
    ensures
        *r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { b.get_unchecked(i) }
}

#[inline(always)]
pub fn sset<T: Copy>(b: &mut [T], i: usize, v: T)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// Element `i` of a vector.
#[inline(always)]
pub fn vget<T: Copy>(b: &Vec<T>, i: usize) -> (r: T)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    sget(b.as_slice(), i)
}

/// Sets element `i` of a vector.
#[inline(always)]
pub fn vset<T: Copy>(b: &mut Vec<T>, i: usize, v: T)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    sset(b.as_mut_slice(), i, v)
}

} // verus!
