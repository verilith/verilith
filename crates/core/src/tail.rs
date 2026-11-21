//! `Tail`: a byte vector that is only appended to, with room reserved in
//! advance. LZ77 decoders append a few bytes per match, millions of times;
//! on a `Vec` each append tests the capacity and may call the allocator,
//! which costs a branch and keeps the vector's fields in memory. A `Tail`
//! reserves once, and each append's `requires` clause says the bytes fit,
//! which Verus proves at every call site, so the append is only the copy.
//!
//! This file is part of the trusted base: every function is
//! `external_body`, and its `ensures` clause is the spec of the lines under
//! it. The appends copy 16 bytes at a time, so they may write up to 32
//! bytes past the new end, into reserved room (hence the 32 in each
//! `requires`); nothing past the length is visible in the contents. To
//! audit: check each function's bounds against its `requires`, taking
//! `cap()` to be the vector's capacity.
use vstd::prelude::*;
use alloc::vec::Vec;

verus! {

/// A byte vector with reserved room. Its view is its contents.
#[verifier::external_body]
pub struct Tail {
    v: Vec<u8>,
}

impl View for Tail {
    type V = Seq<u8>;

    uninterp spec fn view(&self) -> Seq<u8>;
}

impl Tail {
    /// How long the contents may grow without allocating. Appending does
    /// not change it.
    pub uninterp spec fn cap(&self) -> nat;

    /// Takes the contents of `v`, which is left empty, and reserves room
    /// for `extra` more bytes.
    #[verifier::external_body]
    #[inline(always)]
    pub fn take(v: &mut Vec<u8>, extra: usize) -> (t: Tail)
        ensures
            t@ == old(v)@,
            final(v)@.len() == 0,
            t.cap() >= t@.len() + extra,
    {
        let mut w = core::mem::take(v);
        w.reserve(extra);
        Tail { v: w }
    }

    /// Gives the contents back as a vector, replacing what `v` held.
    #[verifier::external_body]
    #[inline(always)]
    pub fn put_back(self, v: &mut Vec<u8>)
        ensures
            final(v)@ == self@,
    {
        *v = self.v;
    }

    /// The length of the contents.
    #[verifier::external_body]
    #[inline(always)]
    pub fn len(&self) -> (r: usize)
        ensures
            r == self@.len(),
    {
        self.v.len()
    }

    /// Appends `s[i..i + n]`.
    #[verifier::external_body]
    #[inline(always)]
    pub fn append_from(&mut self, s: &[u8], i: usize, n: usize)
        requires
            i + n <= s@.len(),
            old(self)@.len() + n + 32 <= old(self).cap(),
        ensures
            final(self)@ == old(self)@ + s@.subrange(i as int, i + n),
            final(self).cap() == old(self).cap(),
    {
        let len = self.v.len();
        debug_assert!(i + n <= s.len() && len + n + 32 <= self.v.capacity());
        // SAFETY: reads stay inside `s` (each branch tests the bytes it
        // reads beyond `i + n`), writes stay below `len + n + 32`, which is
        // within the capacity, and `s` is a distinct borrow.
        unsafe {
            let p = self.v.as_mut_ptr().add(len);
            let q = s.as_ptr().add(i);
            if n <= 32 && s.len() - i >= 32 {
                core::ptr::copy_nonoverlapping(q, p, 16);
                core::ptr::copy_nonoverlapping(q.add(16), p.add(16), 16);
            } else if n <= 64 && s.len() - i >= n + 16 {
                let mut k = 0;
                while k < n {
                    core::ptr::copy_nonoverlapping(q.add(k), p.add(k), 16);
                    k += 16;
                }
            } else {
                core::ptr::copy_nonoverlapping(q, p, n);
            }
            self.v.set_len(len + n);
        }
    }

    /// `append_from` for at most 32 bytes with 32 readable: two 16-byte
    /// copies and no tests.
    #[verifier::external_body]
    #[inline(always)]
    pub fn append_from32(&mut self, s: &[u8], i: usize, n: usize)
        requires
            n <= 32,
            i + 32 <= s@.len(),
            old(self)@.len() + 32 <= old(self).cap(),
        ensures
            final(self)@ == old(self)@ + s@.subrange(i as int, i + n),
            final(self).cap() == old(self).cap(),
    {
        let len = self.v.len();
        debug_assert!(n <= 32 && i + 32 <= s.len() && len + 32 <= self.v.capacity());
        // SAFETY: reads `s[i..i + 32]`, writes below `len + 32`, both in
        // bounds by the precondition.
        unsafe {
            let p = self.v.as_mut_ptr().add(len);
            let q = s.as_ptr().add(i);
            core::ptr::copy_nonoverlapping(q, p, 16);
            core::ptr::copy_nonoverlapping(q.add(16), p.add(16), 16);
            self.v.set_len(len + n);
        }
    }

    /// Appends a copy of the contents' own bytes `src..src + n`.
    #[verifier::external_body]
    #[inline(always)]
    pub fn append_within(&mut self, src: usize, n: usize)
        requires
            src + n <= old(self)@.len(),
            old(self)@.len() + n + 32 <= old(self).cap(),
        ensures
            final(self)@ == old(self)@ + old(self)@.subrange(src as int, src + n),
            final(self).cap() == old(self).cap(),
    {
        let len = self.v.len();
        debug_assert!(src + n <= len && len + n + 32 <= self.v.capacity());
        // SAFETY: the bytes wanted are below `len`, and every write is at
        // or above `len`, so no wanted byte is overwritten before it is
        // read. With `len - src >= 16` each 16-byte chunk ends at or before
        // the place it is copied to. A chunk may read past `len`, but only
        // bytes an earlier chunk wrote, and below `len + n + 32`.
        unsafe {
            let b = self.v.as_mut_ptr();
            let p = b.add(len);
            let q = b.add(src);
            if len - src >= 16 {
                if n <= 32 {
                    core::ptr::copy_nonoverlapping(q, p, 16);
                    core::ptr::copy_nonoverlapping(q.add(16), p.add(16), 16);
                } else if n <= 64 {
                    let mut k = 0;
                    while k < n {
                        core::ptr::copy_nonoverlapping(q.add(k), p.add(k), 16);
                        k += 16;
                    }
                } else {
                    core::ptr::copy_nonoverlapping(q, p, n);
                }
            } else {
                // Here `n < 16`, as `src + n <= len`.
                let mut k = 0;
                while k < n {
                    *p.add(k) = *q.add(k);
                    k += 1;
                }
            }
            self.v.set_len(len + n);
        }
    }

    /// `append_within` for at most 32 bytes from at least 16 back: two
    /// 16-byte copies and no tests.
    #[verifier::external_body]
    #[inline(always)]
    pub fn append_within32(&mut self, src: usize, n: usize)
        requires
            n <= 32,
            src + n <= old(self)@.len(),
            src + 16 <= old(self)@.len(),
            old(self)@.len() + 32 <= old(self).cap(),
        ensures
            final(self)@ == old(self)@ + old(self)@.subrange(src as int, src + n),
            final(self).cap() == old(self).cap(),
    {
        let len = self.v.len();
        debug_assert!(n <= 32 && src + n <= len && src + 16 <= len && len + 32 <= self.v.capacity());
        // SAFETY: as in `append_within`. The second chunk reads
        // `src + 16..src + 32`, which may pass `len` by up to 16 bytes the
        // first chunk has just written.
        unsafe {
            let b = self.v.as_mut_ptr();
            core::ptr::copy_nonoverlapping(b.add(src), b.add(len), 16);
            core::ptr::copy_nonoverlapping(b.add(src + 16), b.add(len + 16), 16);
            self.v.set_len(len + n);
        }
    }
}

} // verus!
