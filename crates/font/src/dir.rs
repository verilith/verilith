//! The table directory: the verified check of `wf_directory` and table
//! lookup.
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The largest power of two at most `n`, and its logarithm.
pub fn pow2(n: u16) -> (r: (u32, u32))
    requires
        n >= 1,
    ensures
        r.0 as int == pow2_floor(n as int, 1, 0).0,
        r.1 as int == pow2_floor(n as int, 1, 0).1,
        r.1 < r.0 <= n,
{
    let mut p: u32 = 1;
    let mut e: u32 = 0;
    while 2 * p <= n as u32
        invariant
            e < p <= n,
            pow2_floor(n as int, 1, 0) == pow2_floor(n as int, p as int, e as int),
        decreases n - p,
    {
        p = 2 * p;
        e = e + 1;
    }
    (p, e)
}

/// The index of the record with tag `t`, or `num_tables` if there is none.
pub fn find(s: &[u8], t: u32) -> (r: usize)
    requires
        s@.len() >= 12,
        12 + 16 * num_tables(s@) <= s@.len(),
    ensures
        r as int == find_from(s@, t as int, 0),
        r <= num_tables(s@),
        r < num_tables(s@) ==> rec_tag(s@, r as int) == t,
{
    let n = rd16(s, 4) as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n as int == num_tables(s@),
            12 + 16 * n <= s@.len(),
            find_from(s@, t as int, 0) == find_from(s@, t as int, i as int),
        decreases n - i,
    {
        if rd32(s, 12 + 16 * i) == t {
            return i;
        }
        i += 1;
    }
    n
}

/// The checksum of table `i`: see `table_sum`.
pub fn table_checksum(s: &[u8], i: usize) -> (r: u32)
    requires
        12 + 16 * (i + 1) <= s.len(),
        pad4(rec_end(s@, i as int)) <= s.len(),
    ensures
        r as int == table_sum(s@, i as int),
{
    let rp = 12 + 16 * i;
    let off = rd32(s, rp + 8) as usize;
    let len = rd32(s, rp + 12) as usize;
    let pend = (off + len + 3) / 4 * 4;
    let sum = sum_words(s, off / 4, pend / 4);
    if rd32(s, rp) == 0x6865_6164 && len >= 12 {
        let adj = rd32(s, off + 8);
        if sum >= adj {
            sum - adj
        } else {
            (sum as u64 + 0x1_0000_0000 - adj as u64) as u32
        }
    } else {
        sum
    }
}

/// Whether record `i` and its table are as [`rec_ok`] requires.
fn check_rec(s: &[u8], n: usize, i: usize) -> (b: bool)
    requires
        s@.len() >= 12,
        n as int == num_tables(s@),
        12 + 16 * n <= s@.len(),
        i < n,
        i > 0 ==> rec_ok(s@, i - 1),
    ensures
        b == rec_ok(s@, i as int),
{
    let r = 12 + 16 * i;
    let off = rd32(s, r + 8) as usize;
    let len = rd32(s, r + 12) as usize;
    if i == 0 {
        if off != 12 + 16 * n {
            return false;
        }
    } else {
        let poff = rd32(s, r - 16 + 8) as usize;
        let plen = rd32(s, r - 16 + 12) as usize;
        if off != (poff + plen + 3) / 4 * 4 {
            return false;
        }
        if rd32(s, r - 16) >= rd32(s, r) {
            return false;
        }
    }
    let end = off + len;
    let pend = (end + 3) / 4 * 4;
    if pend > s.len() {
        return false;
    }
    if !check_zeros(s, end, pend) {
        return false;
    }
    rd32(s, r + 4) == table_checksum(s, i)
}

/// Decides `wf_directory`.
pub fn check_directory(s: &[u8]) -> (b: bool)
    ensures
        b == wf_directory(s@),
{
    if s.len() < 12 {
        return false;
    }
    let v = rd32(s, 0);
    if v != TAG_TRUETYPE && v != TAG_OTTO {
        return false;
    }
    let n16 = rd16(s, 4);
    let n = n16 as usize;
    if n < 1 {
        return false;
    }
    let (p, e) = pow2(n16);
    if rd16(s, 6) as u32 != 16 * p || rd16(s, 8) as u32 != e || rd16(s, 10) as u32 != 16 * (n as u32)
        - 16 * p {
        return false;
    }
    if 12 + 16 * n > s.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            s@.len() >= 12,
            n as int == num_tables(s@),
            12 + 16 * n <= s@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] rec_ok(s@, k),
        decreases n - i,
    {
        if !check_rec(s, n, i) {
            return false;
        }
        i += 1;
    }
    let r = 12 + 16 * (n - 1);
    let off = rd32(s, r + 8) as usize;
    let len = rd32(s, r + 12) as usize;
    s.len() == (off + len + 3) / 4 * 4
}

} // verus!
