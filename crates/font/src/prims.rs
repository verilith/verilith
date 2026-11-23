//! Verified big-endian readers and writers.
//!
//! The readers skip Rust's bounds check: the `requires` clause is the
//! bounds check, and Verus proves it at every call. They are verified
//! against vstd's specification of `get_unchecked`.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The longest table `lay::small` allows: the 32-bit
/// lengths of a font directory on a 64-bit target. On a 32-bit one, half
/// the address space, which leaves room for the offset sums of the table
/// checks; no slice there is longer (Rust caps them at `isize::MAX` bytes).
#[cfg(target_pointer_width = "64")]
pub const TABLE_MAX: usize = 0xFFFF_FFFF;

#[cfg(target_pointer_width = "32")]
pub const TABLE_MAX: usize = 0x7FFF_FFFF;

/// A slice as long as one can be on this target: any slice on a 64-bit
/// target, and at most `isize::MAX` bytes on a 32-bit one.
#[cfg(target_pointer_width = "64")]
pub open spec fn fits(s: Seq<u8>) -> bool {
    true
}

#[cfg(target_pointer_width = "32")]
pub open spec fn fits(s: Seq<u8>) -> bool {
    s.len() <= TABLE_MAX
}

#[inline(always)]
pub fn rd8(s: &[u8], i: usize) -> (r: u8)
    requires
        i < s.len(),
    ensures
        r == s@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *s.get_unchecked(i) }
}

#[inline(always)]
pub fn rd16(s: &[u8], i: usize) -> (r: u16)
    requires
        i + 2 <= s.len(),
    ensures
        r as int == u16_at(s@, i as int),
{
    (rd8(s, i) as u16) * 256 + (rd8(s, i + 1) as u16)
}

#[inline(always)]
pub fn rdi16(s: &[u8], i: usize) -> (r: i32)
    requires
        i + 2 <= s.len(),
    ensures
        r as int == i16_at(s@, i as int),
{
    let v = rd16(s, i) as i32;
    if v >= 32768 {
        v - 65536
    } else {
        v
    }
}

#[inline(always)]
pub fn rd24(s: &[u8], i: usize) -> (r: u32)
    requires
        i + 3 <= s.len(),
    ensures
        r as int == u24_at(s@, i as int),
        r < 0x100_0000,
{
    (rd8(s, i) as u32) * 65536 + (rd16(s, i + 1) as u32)
}

#[inline(always)]
pub fn rd32(s: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= s.len(),
    ensures
        r as int == u32_at(s@, i as int),
{
    (rd16(s, i) as u32) * 65536 + (rd16(s, i + 2) as u32)
}

/// `&s[i..j]`.
#[inline(always)]
pub fn slice<'a>(s: &'a [u8], i: usize, j: usize) -> (out: &'a [u8])
    requires
        i <= j <= s.len(),
    ensures
        out@ == s@.subrange(i as int, j as int),
{
    vstd::slice::slice_subrange(s, i, j)
}

/// Whether bytes `a..b` of `s` are all zero.
pub fn check_zeros(s: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        a <= b <= s.len(),
    ensures
        r == zeros(s@, a as int, b as int),
{
    let mut j = a;
    while j < b
        invariant
            a <= j <= b <= s.len(),
            zeros(s@, a as int, j as int),
        decreases b - j,
    {
        if rd8(s, j) != 0 {
            return false;
        }
        j += 1;
    }
    true
}

/// The OpenType checksum of words `lo..hi` of `s`.
pub fn sum_words(s: &[u8], lo: usize, hi: usize) -> (r: u32)
    requires
        lo <= hi,
        4 * hi <= s.len(),
    ensures
        r as int == words_sum(s@, lo as int, hi as int),
{
    let mut i = lo;
    let mut r: u32 = 0;
    while i < hi
        invariant
            lo <= i <= hi,
            4 * hi <= s.len(),
            r as int == words_sum(s@, lo as int, i as int),
        decreases hi - i,
    {
        let w = rd32(s, 4 * i);
        r = ((r as u64 + w as u64) % 0x1_0000_0000) as u32;
        i += 1;
    }
    r
}

} // verus!
