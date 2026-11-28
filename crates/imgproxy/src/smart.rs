//! Smart gravity's choice, proven to compute `spec_smart`'s for every map
//! and every size: no overflow, no out-of-bounds access.
use crate::spec_smart::*;
use vstd::prelude::*;

verus! {

/// `fkey`.
pub fn fkey_x(b: u32) -> (r: u64)
    ensures
        r as int == fkey(b),
{
    if b == 0x8000_0000 {
        0x8000_0000
    } else if b > 0x8000_0000 {
        (0xFFFF_FFFFu32 - b) as u64
    } else {
        b as u64 + 0x8000_0000
    }
}

/// `first_max` of the whole map.
pub fn first_max_x(v: &[u32]) -> (r: usize)
    requires
        v@.len() >= 1,
    ensures
        r as int == first_max(v@, v@.len() as int),
        r < v@.len(),
{
    let mut b: usize = 0;
    let mut bk = fkey_x(v[0]);
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v@.len(),
            b < i,
            b as int == first_max(v@, i as int),
            bk as int == fkey(v@[b as int]),
        decreases v.len() - i,
    {
        let k = fkey_x(v[i]);
        if k > bk {
            b = i;
            bk = k;
        }
        i = i + 1;
    }
    b
}

/// `centred`.
pub fn centred_x(a: u64, s: u64, c: u64) -> (r: u64)
    requires
        a <= 0x1_0000_0000,
        s <= 0x1_0000_0000,
        c <= s,
    ensures
        r as int == centred(a as int, s as int, c as int),
        r + c <= s,
{
    let t = a as i64 - (c / 2) as i64;
    let hi = (s - c) as i64;
    if t > hi {
        hi as u64
    } else if t < 0 {
        0
    } else {
        t as u64
    }
}

} // verus!
