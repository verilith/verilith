//! Memory primitives.
//!
//! The indexing ones skip Rust's bounds check: their `requires` clause is
//! the bounds check, and Verus proves it at every call site, so they cannot
//! go out of bounds in verified code. `get` and `set` are verified against
//! vstd's spec of `get_unchecked`/`get_unchecked_mut`. `copy` and
//! `alloc_zeroed` are trusted (`external_body`): each is a one-line wrapper
//! that Verus has no spec for, and keeps a `debug_assert!` of its
//! precondition for unverified callers.
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
#[verifier::external_body]
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
    debug_assert!(d + n <= dst.len() && s + n <= src.len());
    // SAFETY: both ranges are in bounds by the precondition, and `dst` and
    // `src` cannot overlap (one is borrowed mutably).
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr().add(s), dst.as_mut_ptr().add(d), n) }
}

/// A vector of `n` zeros, or `None` if the allocation fails. Large
/// allocations come from `calloc`, which maps zeroed pages lazily.
#[verifier::external_body]
pub fn alloc_zeroed(n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u8),
{
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match std::alloc::Layout::array::<u8>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    // SAFETY: `layout` has non-zero size. On success the block holds `n`
    // initialised (zero) bytes allocated by the global allocator with the
    // layout `Vec<u8>` uses for capacity `n`.
    unsafe {
        let p = std::alloc::alloc_zeroed(layout);
        if p.is_null() {
            return None;
        }
        Some(Vec::from_raw_parts(p, n, n))
    }
}

} // verus!
