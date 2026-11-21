//! Verified checks for the fixed-layout tables: each function decides its
//! predicate in `spec` exactly.
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub fn check_head(t: &[u8]) -> (b: bool)
    ensures
        b == wf_head(t@),
{
    if t.len() != 54 {
        return false;
    }
    rd32(t, 0) == 0x0001_0000 && rd32(t, 12) == 0x5F0F_3CF5 && rd16(t, 18) >= 16 && rd16(t, 18)
        <= 16384 && rdi16(t, 36) <= rdi16(t, 40) && rdi16(t, 38) <= rdi16(t, 42) && rd16(t, 50)
        <= 1 && rd16(t, 52) == 0
}

pub fn check_maxp(t: &[u8], truetype: bool) -> (b: bool)
    ensures
        b == wf_maxp(t@, truetype),
{
    if t.len() < 6 {
        return false;
    }
    if rd16(t, 4) < 1 {
        return false;
    }
    let v = rd32(t, 0);
    if v == 0x0000_5000 {
        t.len() == 6 && !truetype
    } else {
        v == 0x0001_0000 && t.len() == 32 && rd16(t, 14) >= 1 && rd16(t, 14) <= 2
    }
}

pub fn check_hhea(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_hhea(t@, ng as int),
{
    if t.len() != 36 {
        return false;
    }
    rd16(t, 0) == 1 && rd16(t, 32) == 0 && rd16(t, 34) >= 1 && rd16(t, 34) <= ng
}

pub fn check_hmtx(t: &[u8], ng: u16, nhm: u16) -> (b: bool)
    requires
        nhm <= ng,
    ensures
        b == wf_hmtx(t@, ng as int, nhm as int),
{
    t.len() == 4 * (nhm as usize) + 2 * (ng as usize - nhm as usize)
}

pub fn check_os2(t: &[u8]) -> (b: bool)
    ensures
        b == wf_os2(t@),
{
    if t.len() < 78 {
        return false;
    }
    let v = rd16(t, 0);
    let want: usize = if v == 0 {
        78
    } else if v == 1 {
        86
    } else if v <= 4 {
        96
    } else {
        100
    };
    t.len() == want && v <= 5
}

pub fn check_cvt(t: &[u8]) -> (b: bool)
    ensures
        b == wf_cvt(t@),
{
    t.len() % 2 == 0
}

pub fn check_gasp(t: &[u8]) -> (b: bool)
    ensures
        b == wf_gasp(t@),
{
    if t.len() < 4 {
        return false;
    }
    let n = rd16(t, 2) as usize;
    if rd16(t, 0) > 1 || t.len() != 4 + 4 * n {
        return false;
    }
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            i <= n,
            n <= 65535,
            t.len() == 4 + 4 * n,
            n == u16_at(t@, 2),
            forall|k: int|
                0 <= k < i ==> #[trigger] u16_at(t@, 4 + 4 * k) < u16_at(t@, 4 + 4 * (k + 1)),
        decreases n - i,
    {
        if rd16(t, 4 + 4 * i) >= rd16(t, 4 + 4 * (i + 1)) {
            return false;
        }
        i += 1;
    }
    true
}

pub fn check_vhea(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_vhea(t@, ng as int),
{
    if t.len() != 36 {
        return false;
    }
    (rd32(t, 0) == 0x0001_0000 || rd32(t, 0) == 0x0001_1000) && rd16(t, 32) == 0 && rd16(t, 34) >= 1
        && rd16(t, 34) <= ng
}

/// Checks the pairs of the `kern` subtable at `p`.
fn check_kern_pairs(t: &[u8], p: usize, np: usize, ng: u16) -> (b: bool)
    requires
        p + 14 + 6 * np <= t.len(),
    ensures
        b == forall|k: int| 0 <= k < np ==> #[trigger] kern_pair_ok(t@, p as int, k, ng as int),
{
    let mut k: usize = 0;
    while k < np
        invariant
            k <= np,
            p + 14 + 6 * np <= t.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] kern_pair_ok(t@, p as int, j, ng as int),
        decreases np - k,
    {
        let r = p + 14 + 6 * k;
        if rd16(t, r) >= ng || rd16(t, r + 2) >= ng || (k > 0 && rd32(t, r - 6) >= rd32(t, r)) {
            assert(!kern_pair_ok(t@, p as int, k as int, ng as int));
            return false;
        }
        assert(kern_pair_ok(t@, p as int, k as int, ng as int));
        k += 1;
    }
    true
}

pub fn check_kern(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_kern(t@, ng as int),
{
    if t.len() < 4 || rd16(t, 0) != 0 {
        return false;
    }
    let n0 = rd16(t, 2) as usize;
    let mut n = n0;
    let mut p: usize = 4;
    while n > 0
        invariant
            p <= t.len(),
            t.len() >= 4,
            u16_at(t@, 0) == 0,
            n0 == u16_at(t@, 2),
            kern_subs(t@, 4, n0 as int, ng as int) == kern_subs(t@, p as int, n as int, ng as int),
        decreases n,
    {
        if 14 > t.len() - p {
            return false;
        }
        let len = rd16(t, p + 2) as usize;
        let np = rd16(t, p + 6) as usize;
        if rd16(t, p) != 0 || rd8(t, p + 4) != 0 || len != 14 + 6 * np || len > t.len() - p {
            return false;
        }
        if !check_kern_pairs(t, p, np, ng) {
            return false;
        }
        p = p + len;
        n = n - 1;
    }
    p == t.len()
}

/// Whether the (length, offset) pair at `r` stays inside the table, with
/// the storage area starting at `st`.
fn check_name_str(t: &[u8], r: usize, st: usize) -> (b: bool)
    requires
        r + 4 <= t.len(),
        st <= 65535,
    ensures
        b == name_str_ok(t@, r as int, st as int),
{
    st + rd16(t, r + 2) as usize + rd16(t, r) as usize <= t.len()
}

pub fn check_name(t: &[u8]) -> (b: bool)
    ensures
        b == wf_name(t@),
{
    if t.len() < 6 {
        return false;
    }
    let v = rd16(t, 0);
    let n = rd16(t, 2) as usize;
    let st = rd16(t, 4) as usize;
    if v > 1 || 6 + 12 * n > t.len() || st > t.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            6 + 12 * n <= t.len(),
            n == u16_at(t@, 2),
            st == u16_at(t@, 4),
            forall|k: int| 0 <= k < i ==> #[trigger] name_str_ok(t@, 6 + 12 * k + 8, st as int),
        decreases n - i,
    {
        if !check_name_str(t, 6 + 12 * i + 8, st) {
            return false;
        }
        i += 1;
    }
    let l = 6 + 12 * n;
    if v == 0 {
        return st >= l;
    }
    if l + 2 > t.len() {
        return false;
    }
    let m = rd16(t, l) as usize;
    if l + 2 + 4 * m > st {
        return false;
    }
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            l + 2 + 4 * m <= st <= t.len(),
            l == 6 + 12 * u16_at(t@, 2),
            m == u16_at(t@, l as int),
            u16_at(t@, 0) == 1,
            t.len() >= 6,
            forall|k: int|
                0 <= k < u16_at(t@, 2) ==> #[trigger] name_str_ok(t@, 6 + 12 * k + 8, st as int),
            st == u16_at(t@, 4),
            forall|k: int| 0 <= k < i ==> #[trigger] name_str_ok(t@, l + 2 + 4 * k, st as int),
        decreases m - i,
    {
        if !check_name_str(t, l + 2 + 4 * i, st) {
            return false;
        }
        i += 1;
    }
    true
}

/// `pstrings` from `p`, with `acc` strings already counted.
pub open spec fn pstrings_acc(t: Seq<u8>, p: int, acc: int) -> Option<int> {
    match pstrings(t, p) {
        Some(k) => Some(k + acc),
        None => None,
    }
}

/// Counts the Pascal strings from `p0` to the end of `t`.
fn count_pstrings(t: &[u8], p0: usize) -> (r: Option<usize>)
    requires
        p0 <= t.len(),
    ensures
        match r {
            Some(k) => pstrings(t@, p0 as int) == Some(k as int) && k <= t.len(),
            None => pstrings(t@, p0 as int) is None,
        },
{
    let mut p = p0;
    let mut k: usize = 0;
    while p < t.len()
        invariant
            p0 <= p <= t.len(),
            k <= p - p0,
            pstrings(t@, p0 as int) == pstrings_acc(t@, p as int, k as int),
        decreases t.len() - p,
    {
        let l = rd8(t, p) as usize;
        if l + 1 > t.len() - p {
            return None;
        }
        p = p + 1 + l;
        k += 1;
    }
    Some(k)
}

pub fn check_post(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_post(t@, ng as int),
{
    if t.len() < 32 {
        return false;
    }
    let v = rd32(t, 0);
    if v == 0x0001_0000 || v == 0x0003_0000 {
        return t.len() == 32;
    }
    let n = ng as usize;
    if v != 0x0002_0000 || t.len() < 34 || rd16(t, 32) != ng || 34 + 2 * n > t.len() {
        return false;
    }
    let k = match count_pstrings(t, 34 + 2 * n) {
        Some(k) => k,
        None => {
            return false;
        },
    };
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            34 + 2 * n <= t.len(),
            k <= t.len(),
            n == ng,
            pstrings(t@, 34 + 2 * ng) == Some(k as int),
            forall|j: int| 0 <= j < i ==> #[trigger] u16_at(t@, 34 + 2 * j) < 258 + k,
        decreases n - i,
    {
        let x = rd16(t, 34 + 2 * i) as usize;
        if x >= 258 && x - 258 >= k {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
