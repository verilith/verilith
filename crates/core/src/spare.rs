//! A `Vec`'s spare capacity, which vstd does not model, and stores into it
//! without a capacity check. A caller reserves room once (`reserve_spare`)
//! and each store's `requires` says the bytes fit, which Verus proves at
//! the call site, so the store is only the write.
//!
//! This file is part of the trusted base: `spare` is uninterpreted, and
//! every function is `external_body`, its `ensures` the spec of the lines
//! under it. verilith-json and verilith-zlib use it (json adds two stores
//! of vector registers, stated with the same `spare`). To audit: check
//! each store against its `requires`, taking `spare(v)` to be
//! `v.capacity() - v.len()`.
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// How many more elements `v` takes without reallocating. vstd does not
/// model capacity, so this is left uninterpreted; the functions below are
/// its whole contract.
pub uninterp spec fn spare<T>(v: Vec<T>) -> int;

/// `Vec::capacity`: the length plus the spare room.
#[verifier::external_body]
#[inline(always)]
pub fn len_spare<T>(v: &Vec<T>) -> (n: usize)
    ensures
        n == v@.len() + spare(*v),
{
    v.capacity()
}

/// `Vec::reserve`.
#[verifier::external_body]
#[inline]
pub fn reserve_spare<T>(v: &mut Vec<T>, n: usize)
    ensures
        final(v)@ == old(v)@,
        spare(*final(v)) >= n,
{
    v.reserve(n)
}

/// `Vec::reserve` of `n + extra` (which panics, like `reserve` itself
/// past `isize::MAX`, if the sum overflows).
#[verifier::external_body]
#[inline]
pub fn reserve_spare_plus<T>(v: &mut Vec<T>, n: usize, extra: usize)
    ensures
        final(v)@ == old(v)@,
        spare(*final(v)) >= n + extra,
{
    v.reserve(n.checked_add(extra).expect("capacity overflow"))
}

/// `Vec::push` into reserved space: no capacity check, no reallocation.
#[verifier::external_body]
#[inline(always)]
pub fn push_spare<T>(v: &mut Vec<T>, x: T)
    requires
        spare(*old(v)) > 0,
    ensures
        final(v)@ == old(v)@.push(x),
        spare(*final(v)) == spare(*old(v)) - 1,
{
    let l = v.len();
    unsafe {
        v.as_mut_ptr().add(l).write(x);
        v.set_len(l + 1);
    }
}

/// The four bytes of `x`, least significant first.
pub open spec fn le4(x: u32) -> Seq<u8> {
    seq![x as u8, (x >> 8u32) as u8, (x >> 16u32) as u8, (x >> 24u32) as u8]
}

/// A four-byte store of `x` (little endian) into reserved space, keeping
/// the first `n` bytes.
#[verifier::external_body]
#[inline(always)]
pub fn append4_spare(v: &mut Vec<u8>, x: u32, n: usize)
    requires
        spare(*old(v)) >= 4,
        n <= 4,
    ensures
        final(v)@ == old(v)@ + le4(x).subrange(0, n as int),
        spare(*final(v)) == spare(*old(v)) - n,
{
    let l = v.len();
    unsafe {
        (v.as_mut_ptr().add(l) as *mut [u8; 4]).write_unaligned(x.to_le_bytes());
        v.set_len(l + n);
    }
}

/// `s[a..b]` appended into reserved space (a `memcpy`).
#[verifier::external_body]
#[inline(always)]
pub fn append_slice_spare(v: &mut Vec<u8>, s: &[u8], a: usize, b: usize)
    requires
        a <= b <= s@.len(),
        spare(*old(v)) >= b - a,
    ensures
        final(v)@ == old(v)@ + s@.subrange(a as int, b as int),
        spare(*final(v)) == spare(*old(v)) - (b - a),
{
    let l = v.len();
    unsafe {
        core::ptr::copy_nonoverlapping(s.as_ptr().add(a), v.as_mut_ptr().add(l), b - a);
        v.set_len(l + (b - a));
    }
}

/// `Vec::truncate`, which leaves the spare capacity at least as large.
#[verifier::external_body]
#[inline(always)]
pub fn truncate_spare<T>(v: &mut Vec<T>, n: usize)
    requires
        n <= old(v)@.len(),
    ensures
        final(v)@ == old(v)@.subrange(0, n as int),
        spare(*final(v)) >= spare(*old(v)),
{
    v.truncate(n)
}

/// `v[i] = x`, which leaves the capacity alone.
#[verifier::external_body]
#[inline(always)]
pub fn set_spare<T>(v: &mut Vec<T>, i: usize, x: T)
    requires
        i < old(v)@.len(),
    ensures
        final(v)@ == old(v)@.update(i as int, x),
        spare(*final(v)) == spare(*old(v)),
{
    v[i] = x;
}

/// An eight-byte store of `w` (little endian) into reserved space, keeping
/// the low `k` bytes.
#[verifier::external_body]
#[inline(always)]
pub fn append8_spare(v: &mut Vec<u8>, w: u64, k: usize)
    requires
        spare(*old(v)) >= 8,
        k <= 8,
    ensures
        final(v)@ == old(v)@ + Seq::new(k as nat, |j: int| ((w >> (8 * j) as u64) & 0xff) as u8),
        spare(*final(v)) == spare(*old(v)) - k,
{
    let l = v.len();
    // SAFETY: eight bytes from `l` are reserved; `k <= 8` of them are
    // kept, and they are initialized by the store.
    unsafe {
        core::ptr::write_unaligned(v.as_mut_ptr().add(l) as *mut u64, w.to_le());
        v.set_len(l + k);
    }
}

} // verus!
