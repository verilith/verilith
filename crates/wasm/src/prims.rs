//! Memory primitives with hand-written specs (part of the trusted base).
//!
//! Each is a one-line wrapper around an unchecked access. The `requires`
//! clause is the bounds check, which Verus proves at every call site, so
//! verified code can only reach the linear memory and the value stack
//! within their bounds. Without verification they keep a `debug_assert!`.
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::sem::*;

verus! {

#[inline(always)]
pub fn vget<T: Copy>(v: &Vec<T>, i: usize) -> (r: T)
    requires i < v@.len(),
    ensures r == v@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *v.get_unchecked(i) }
}

#[inline(always)]
pub fn sref<T>(v: &[T], i: usize) -> (r: &T)
    requires i < v@.len(),
    ensures *r == v@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { v.get_unchecked(i) }
}

#[inline(always)]
pub fn vset<T>(v: &mut Vec<T>, i: usize, x: T)
    requires i < old(v)@.len(),
    ensures final(v)@ == old(v)@.update(i as int, x),
{
    v[i] = x;
}

#[inline(always)]
pub fn sget(s: &Vec<u64>, i: usize) -> (r: u64)
    requires i < s@.len(),
    ensures r == s@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *s.get_unchecked(i) }
}

#[inline(always)]
pub fn sset(s: &mut Vec<u64>, i: usize, v: u64)
    requires i < old(s)@.len(),
    ensures final(s)@ == old(s)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *s.get_unchecked_mut(i) = v }
}

/// Copies `n` slots from `src` to `dst` (`dst <= src`), as `memmove`.
#[verifier::external_body]
#[inline(always)]
pub fn scopy_down(s: &mut Vec<u64>, dst: usize, src: usize, n: usize)
    requires dst <= src, src + n <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|i: int| 0 <= i < final(s)@.len() ==> #[trigger] final(s)@[i] ==
            if dst <= i < dst + n { old(s)@[src + (i - dst)] } else { old(s)@[i] },
{
    debug_assert!(dst <= src && src + n <= s.len());
    // SAFETY: both ranges are inside `s`; `copy` allows overlap.
    unsafe {
        let p = s.as_mut_ptr();
        core::ptr::copy(p.add(src), p.add(dst), n)
    }
}

/// Sets `n` slots from `i` to zero.
#[verifier::external_body]
#[inline(always)]
pub fn szero(s: &mut Vec<u64>, i: usize, n: usize)
    requires i + n <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + n { 0 } else { old(s)@[j] },
{
    debug_assert!(i + n <= s.len());
    // SAFETY: the range is inside `s`.
    unsafe { core::ptr::write_bytes(s.as_mut_ptr().add(i), 0, n) }
}

/// Loads `n` (1, 2, 4 or 8) little-endian bytes at `i`.
#[verifier::external_body]
#[inline(always)]
pub fn load(m: &Vec<u8>, i: usize, n: usize) -> (r: u64)
    requires i + n <= m@.len(), n == 1 || n == 2 || n == 4 || n == 8,
    ensures r as nat == le(m@, i as int, n as nat),
{
    debug_assert!(i + n <= m.len());
    // SAFETY: the `n` bytes at `i` are inside `m`.
    unsafe {
        let p = m.as_ptr().add(i);
        match n {
            1 => *p as u64,
            2 => u16::from_le(core::ptr::read_unaligned(p as *const u16)) as u64,
            4 => u32::from_le(core::ptr::read_unaligned(p as *const u32)) as u64,
            _ => u64::from_le(core::ptr::read_unaligned(p as *const u64)),
        }
    }
}

/// Stores the low `n` (1, 2, 4 or 8) bytes of `v` at `i`, little-endian.
#[verifier::external_body]
#[inline(always)]
pub fn store(m: &mut Vec<u8>, i: usize, v: u64, n: usize)
    requires i + n <= old(m)@.len(), n == 1 || n == 2 || n == 4 || n == 8,
    ensures final(m)@ == write_le(old(m)@, i as int, store_value(v, n as nat), n as nat),
{
    debug_assert!(i + n <= m.len());
    // SAFETY: the `n` bytes at `i` are inside `m`.
    unsafe {
        let p = m.as_mut_ptr().add(i);
        match n {
            1 => *p = v as u8,
            2 => core::ptr::write_unaligned(p as *mut u16, (v as u16).to_le()),
            4 => core::ptr::write_unaligned(p as *mut u32, (v as u32).to_le()),
            _ => core::ptr::write_unaligned(p as *mut u64, v.to_le()),
        }
    }
}

/// `memory.fill`.
#[verifier::external_body]
#[inline(always)]
pub fn fill(m: &mut Vec<u8>, d: usize, v: u8, n: usize)
    requires d + n <= old(m)@.len(),
    ensures final(m)@ == old(m)@.subrange(0, d as int) + Seq::new(n as nat, |_i| v)
        + old(m)@.subrange((d + n) as int, old(m)@.len() as int),
{
    debug_assert!(d + n <= m.len());
    // SAFETY: the range is inside `m`.
    unsafe { core::ptr::write_bytes(m.as_mut_ptr().add(d), v, n) }
}

/// `memory.copy` (the ranges may overlap).
#[verifier::external_body]
#[inline(always)]
pub fn copy_within(m: &mut Vec<u8>, d: usize, s: usize, n: usize)
    requires d + n <= old(m)@.len(), s + n <= old(m)@.len(),
    ensures final(m)@ == old(m)@.subrange(0, d as int) + old(m)@.subrange(s as int, (s + n) as int)
        + old(m)@.subrange((d + n) as int, old(m)@.len() as int),
{
    debug_assert!(d + n <= m.len() && s + n <= m.len());
    // SAFETY: both ranges are inside `m`; `copy` allows overlap.
    unsafe {
        let p = m.as_mut_ptr();
        core::ptr::copy(p.add(s), p.add(d), n)
    }
}

/// `memory.init`: copies `data[s..s + n]` to `d`.
#[verifier::external_body]
#[inline(always)]
pub fn copy_in(m: &mut Vec<u8>, d: usize, data: &[u8], s: usize, n: usize)
    requires d + n <= old(m)@.len(), s + n <= data@.len(),
    ensures final(m)@ == old(m)@.subrange(0, d as int) + data@.subrange(s as int, (s + n) as int)
        + old(m)@.subrange((d + n) as int, old(m)@.len() as int),
{
    debug_assert!(d + n <= m.len() && s + n <= data.len());
    m[d..d + n].copy_from_slice(&data[s..s + n]);
}

/// Appends `n` zero bytes (`memory.grow`).
#[verifier::external_body]
#[inline(always)]
pub fn grow(m: &mut Vec<u8>, n: usize)
    ensures final(m)@ == old(m)@ + Seq::new(n as nat, |_i| 0u8),
{
    m.resize(m.len() + n, 0);
}


/// The size of a [`crate::reg::ROp`] in bytes (checked at compile time
/// below the `verus!` block).
pub const ROP_SIZE: u32 = 48;

/// A position in a slice of register operations, kept as a pointer so the
/// dispatch steps to the next operation with one add. `seq` is the slice
/// it points into and `idx` the position; it reads only at
/// `idx < seq.len()`, and the slice is borrowed for `'a`.
#[verifier::external_body]
#[derive(Clone, Copy)]
pub struct Cur<'a> {
    p: *const crate::reg::ROp,
    _l: core::marker::PhantomData<&'a [crate::reg::ROp]>,
}

impl<'a> Cur<'a> {
    pub uninterp spec fn idx(&self) -> int;
    pub uninterp spec fn seq(&self) -> Seq<crate::reg::ROp>;
}

/// Position `i` of `v`.
#[verifier::external_body]
#[inline(always)]
pub fn cur_at<'a>(v: &'a [crate::reg::ROp], i: usize) -> (c: Cur<'a>)
    ensures c.idx() == i, c.seq() == v@,
{
    Cur { p: v.as_ptr().wrapping_add(i), _l: core::marker::PhantomData }
}

/// Position `i` of `v`, given its byte offset `off`.
#[verifier::external_body]
#[inline(always)]
pub fn cur_off<'a>(v: &'a [crate::reg::ROp], i: u32, off: u32) -> (c: Cur<'a>)
    requires off as int == i as int * ROP_SIZE as int,
    ensures c.idx() == i, c.seq() == v@,
{
    Cur { p: (v.as_ptr() as *const u8).wrapping_add(off as usize) as *const crate::reg::ROp,
        _l: core::marker::PhantomData }
}

/// The next position.
#[verifier::external_body]
#[inline(always)]
pub fn cur_next<'a>(c: Cur<'a>) -> (c2: Cur<'a>)
    ensures c2.idx() == c.idx() + 1, c2.seq() == c.seq(),
{
    Cur { p: c.p.wrapping_add(1), _l: core::marker::PhantomData }
}

/// The operation at the position.
#[verifier::external_body]
#[inline(always)]
pub fn cur_get<'a>(c: Cur<'a>) -> (r: &'a crate::reg::ROp)
    requires 0 <= c.idx() < c.seq().len(),
    ensures *r == c.seq()[c.idx()],
{
    // SAFETY: `c` points at element `idx` of a slice borrowed for `'a`
    // (made by `cur_at`, `cur_off` with the element's offset, or
    // `cur_next`), and `idx` is in bounds by the precondition.
    unsafe { &*c.p }
}

} // verus!

const _: () = assert!(core::mem::size_of::<crate::reg::ROp>() == ROP_SIZE as usize);
