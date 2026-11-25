//! Verified check of `cmap`: decides `wf_cmap` exactly.
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

fn check_cmap0(t: &[u8], o: usize, ng: u16) -> (b: bool)
    requires
        o + 2 <= t.len(),
    ensures
        b == wf_cmap0(t@, o as int, ng as int),
{
    if 262 > t.len() - o {
        return false;
    }
    if rd16(t, o + 2) != 262 {
        return false;
    }
    let mut c: usize = 0;
    while c < 256
        invariant
            c <= 256,
            o + 262 <= t.len(),
            forall|j: int| 0 <= j < c ==> (#[trigger] t@[o + 6 + j]) < ng,
        decreases 256 - c,
    {
        if rd8(t, o + 6 + c) as u16 >= ng {
            return false;
        }
        c += 1;
    }
    true
}

/// Decides [`c4_seg_ok`] for segment `k`.
fn check_c4_seg(t: &[u8], o: usize, sc: usize, k: usize, end: usize, ng: u16) -> (b: bool)
    requires
        1 <= sc <= 32767,
        k < sc,
        o + 16 + 8 * sc <= end <= t.len(),
    ensures
        b == c4_seg_ok(t@, o as int, sc as int, k as int, end as int, ng as int),
{
    let e = rd16(t, o + 14 + 2 * k) as usize;
    let s = rd16(t, o + 16 + 2 * sc + 2 * k) as usize;
    let d = rd16(t, o + 16 + 4 * sc + 2 * k) as usize;
    let rp = o + 16 + 6 * sc + 2 * k;
    let ro = rd16(t, rp) as usize;
    if s > e {
        return false;
    }
    if k > 0 && rd16(t, o + 14 + 2 * (k - 1)) as usize >= s {
        return false;
    }
    if ro % 2 != 0 {
        return false;
    }
    let ghost oi = o as int;
    let ghost sci = sc as int;
    let ghost ki = k as int;
    let mut c = s;
    while c <= e
        invariant
            s <= c <= e + 1,
            e <= 65535,
            d <= 65535,
            ro <= 65535,
            1 <= sc <= 32767,
            k < sc,
            oi == o,
            sci == sc,
            ki == k,
            o + 16 + 8 * sc <= end <= t.len(),
            rp == c4_ro_pos(oi, sci, ki),
            rp == o + 16 + 6 * sc + 2 * k,
            e == c4_end(t@, oi, ki),
            s == c4_start(t@, oi, sci, ki),
            d == c4_delta(t@, oi, sci, ki),
            ro == c4_ro(t@, oi, sci, ki),
            forall|x: int|
                s <= x < c ==> #[trigger] c4_char_ok(t@, oi, sci, ki, x, end as int, ng as int),
        decreases e + 1 - c,
    {
        if ro == 0 {
            if (c + d) % 65536 >= ng as usize {
                assert(!c4_char_ok(t@, oi, sci, ki, c as int, end as int, ng as int));
                return false;
            }
        } else {
            if ro + 2 * (c - s) + 2 > end - rp {
                assert(!c4_char_ok(t@, oi, sci, ki, c as int, end as int, ng as int));
                return false;
            }
            let a = rp + ro + 2 * (c - s);
            let g = rd16(t, a) as usize;
            if g != 0 && (g + d) % 65536 >= ng as usize {
                assert(!c4_char_ok(t@, oi, sci, ki, c as int, end as int, ng as int));
                return false;
            }
        }
        c += 1;
    }
    true
}

fn check_cmap4(t: &[u8], o: usize, ng: u16) -> (b: bool)
    requires
        o + 2 <= t.len(),
    ensures
        b == wf_cmap4(t@, o as int, ng as int),
{
    if 16 > t.len() - o {
        return false;
    }
    let len = rd16(t, o + 2) as usize;
    let sx2 = rd16(t, o + 6) as usize;
    let sc = sx2 / 2;
    if len > t.len() - o || sx2 % 2 != 0 || sc < 1 || 16 + 8 * sc > len {
        return false;
    }
    if rd16(t, o + 14 + 2 * (sc - 1)) != 0xFFFF {
        return false;
    }
    let mut k: usize = 0;
    while k < sc
        invariant
            k <= sc,
            1 <= sc <= 32767,
            16 + 8 * sc <= len,
            o + len <= t.len(),
            o + 16 <= t.len(),
            len == u16_at(t@, o + 2),
            sc == u16_at(t@, o + 6) / 2,
            u16_at(t@, o + 6) % 2 == 0,
            c4_end(t@, o as int, sc - 1) == 0xFFFF,
            forall|j: int|
                0 <= j < k ==> #[trigger] c4_seg_ok(
                    t@,
                    o as int,
                    sc as int,
                    j,
                    o + len,
                    ng as int,
                ),
        decreases sc - k,
    {
        if !check_c4_seg(t, o, sc, k, o + len, ng) {
            return false;
        }
        k += 1;
    }
    true
}

fn check_c12_group(t: &[u8], o: usize, k: usize, many: bool, ng: u16) -> (b: bool)
    requires
        o + 16 + 12 * (k + 1) <= t.len(),
    ensures
        b == c12_group_ok(t@, o as int, k as int, many, ng as int),
{
    let g = o + 16 + 12 * k;
    let s = rd32(t, g) as u64;
    let e = rd32(t, g + 4) as u64;
    let gid = rd32(t, g + 8) as u64;
    if s > e || e > 0x10FFFF {
        return false;
    }
    if k > 0 && rd32(t, g - 8) as u64 >= s {
        return false;
    }
    if many {
        gid < ng as u64
    } else {
        gid + (e - s) < ng as u64
    }
}

fn check_cmap12(t: &[u8], o: usize, many: bool, ng: u16) -> (b: bool)
    requires
        o + 2 <= t.len(),
    ensures
        b == wf_cmap12(t@, o as int, many, ng as int),
{
    if 16 > t.len() - o {
        return false;
    }
    // In u64: 12 * n can pass a 32-bit usize.
    let n = rd32(t, o + 12) as u64;
    if rd32(t, o + 4) as u64 != 16 + 12 * n || 16 + 12 * n > (t.len() - o) as u64 {
        return false;
    }
    let n = n as usize;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            o + 16 + 12 * n <= t.len(),
            n == u32_at(t@, o + 12),
            u32_at(t@, o + 4) == 16 + 12 * n,
            forall|j: int| 0 <= j < k ==> #[trigger] c12_group_ok(t@, o as int, j, many, ng as int),
        decreases n - k,
    {
        if !check_c12_group(t, o, k, many, ng) {
            return false;
        }
        k += 1;
    }
    true
}

fn check_duvs(t: &[u8], d: usize, end: usize) -> (b: bool)
    requires
        end <= t.len(),
        d <= 2 * u32::MAX,
    ensures
        b == wf_duvs(t@, d as int, end as int),
{
    // In u64: these can pass a 32-bit usize.
    if d as u64 + 4 > end as u64 {
        return false;
    }
    let n = rd32(t, d) as u64;
    if n == 0 || d as u64 + 4 + 4 * n > end as u64 {
        return false;
    }
    let n = n as usize;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            d + 4 + 4 * n <= end <= t.len(),
            n == u32_at(t@, d as int),
            forall|j: int| 0 <= j < k ==> #[trigger] duvs_ok(t@, d as int, j),
        decreases n - k,
    {
        let r = d + 4 + 4 * k;
        if rd24(t, r) == 0 || rd24(t, r) + rd8(t, r + 3) as u32 > 0x10FFFF {
            assert(!duvs_ok(t@, d as int, k as int));
            return false;
        }
        if k > 0 && rd24(t, r - 4) + rd8(t, r - 1) as u32 >= rd24(t, r) {
            assert(!duvs_ok(t@, d as int, k as int));
            return false;
        }
        assert(duvs_ok(t@, d as int, k as int));
        k += 1;
    }
    true
}

fn check_nduvs(t: &[u8], d: usize, end: usize, ng: u16) -> (b: bool)
    requires
        end <= t.len(),
        d <= 2 * u32::MAX,
    ensures
        b == wf_nduvs(t@, d as int, end as int, ng as int),
{
    // In u64: these can pass a 32-bit usize.
    if d as u64 + 4 > end as u64 {
        return false;
    }
    let n = rd32(t, d) as u64;
    if n == 0 || d as u64 + 4 + 5 * n > end as u64 {
        return false;
    }
    let n = n as usize;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            d + 4 + 5 * n <= end <= t.len(),
            n == u32_at(t@, d as int),
            forall|j: int| 0 <= j < k ==> #[trigger] nduvs_ok(t@, d as int, j, ng as int),
        decreases n - k,
    {
        let r = d + 4 + 5 * k;
        if rd24(t, r) == 0 || rd24(t, r) > 0x10FFFF || rd16(t, r + 3) == 0 || rd16(t, r + 3) >= ng {
            assert(!nduvs_ok(t@, d as int, k as int, ng as int));
            return false;
        }
        if k > 0 && rd24(t, r - 5) >= rd24(t, r) {
            assert(!nduvs_ok(t@, d as int, k as int, ng as int));
            return false;
        }
        assert(nduvs_ok(t@, d as int, k as int, ng as int));
        k += 1;
    }
    true
}

fn check_c14_rec(t: &[u8], o: usize, k: usize, hdr: usize, end: usize, ng: u16) -> (b: bool)
    requires
        o + 10 + 11 * (k + 1) <= end <= t.len(),
        o <= u32::MAX,
    ensures
        b == c14_rec_ok(t@, o as int, k as int, hdr as int, end as int, ng as int),
{
    let r = o + 10 + 11 * k;
    let v = rd24(t, r);
    if !((0x180B <= v && v <= 0x180D) || (0xFE00 <= v && v <= 0xFE0F) || (0xE0100 <= v && v <= 0xE01EF)) {
        return false;
    }
    if k > 0 && rd24(t, r - 11) >= rd24(t, r) {
        return false;
    }
    if rd32(t, r + 3) == 0 && rd32(t, r + 7) == 0 {
        return false;
    }
    let d = rd32(t, r + 3) as usize;
    // On a 32-bit target o + d can overflow; then it is past the end.
    #[cfg(target_pointer_width = "32")]
    if d != 0 && d >= hdr && d > end - o {
        return false;
    }
    if d != 0 {
        if d < hdr || !check_duvs(t, o + d, end) {
            return false;
        }
    }
    let nd = rd32(t, r + 7) as usize;
    #[cfg(target_pointer_width = "32")]
    if nd != 0 && nd >= hdr && nd > end - o {
        return false;
    }
    if nd != 0 {
        if nd < hdr || !check_nduvs(t, o + nd, end, ng) {
            return false;
        }
    }
    true
}

/// The start and end of record `k`'s default UVS table (`nd` false) or
/// non-default one (`nd` true), from the start of the subtable.
fn c14_span(t: &[u8], o: usize, k: usize, n: usize, len: usize, ng: u16, nd: bool) -> (r: (
    usize,
    usize,
))
    requires
        o <= u32::MAX,
        k < n <= 259,
        10 + 11 * n <= len,
        o + len <= t.len(),
        len <= u32::MAX,
        c14_rec_ok(t@, o as int, k as int, 10 + 11 * n, o + len, ng as int),
    ensures
        !nd ==> r.0 == c14_doff(t@, o as int, k as int) && (r.0 != 0 ==> r.1 == c14_dend(
            t@,
            o as int,
            k as int,
        )),
        nd ==> r.0 == c14_noff(t@, o as int, k as int) && (r.0 != 0 ==> r.1 == c14_nend(
            t@,
            o as int,
            k as int,
        )),
        r.1 <= 6 * u32::MAX,
{
    let r = o + 10 + 11 * k;
    if nd {
        let a = rd32(t, r + 7) as usize;
        if a == 0 {
            return (0, 0);
        }
        (a, a + 4 + 5 * rd32(t, o + a) as usize)
    } else {
        let a = rd32(t, r + 3) as usize;
        if a == 0 {
            return (0, 0);
        }
        (a, a + 4 + 4 * rd32(t, o + a) as usize)
    }
}

fn check_c14_pair(t: &[u8], o: usize, i: usize, j: usize, n: usize, len: usize, ng: u16) -> (b:
    bool)
    requires
        o <= u32::MAX,
        i < n,
        j < n <= 259,
        10 + 11 * n <= len,
        o + len <= t.len(),
        len <= u32::MAX,
        forall|k: int|
            0 <= k < n ==> #[trigger] c14_rec_ok(t@, o as int, k, 10 + 11 * n, o + len, ng as int),
    ensures
        b == c14_pair_ok(t@, o as int, i as int, j as int),
{
    assert(c14_rec_ok(t@, o as int, i as int, 10 + 11 * n, o + len, ng as int));
    assert(c14_rec_ok(t@, o as int, j as int, 10 + 11 * n, o + len, ng as int));
    let (di, dei) = c14_span(t, o, i, n, len, ng, false);
    let (dj, dej) = c14_span(t, o, j, n, len, ng, false);
    let (ni, nei) = c14_span(t, o, i, n, len, ng, true);
    let (nj, nej) = c14_span(t, o, j, n, len, ng, true);
    if di != 0 && dj != 0 && di != dj && !(dei <= dj || dej <= di) {
        return false;
    }
    if ni != 0 && nj != 0 && ni != nj && !(nei <= nj || nej <= ni) {
        return false;
    }
    if di != 0 && nj != 0 && !(dei <= nj || nej <= di) {
        return false;
    }
    true
}

fn check_c14_row(t: &[u8], o: usize, i: usize, n: usize, len: usize, ng: u16) -> (b: bool)
    requires
        o <= u32::MAX,
        i < n <= 259,
        10 + 11 * n <= len,
        o + len <= t.len(),
        len <= u32::MAX,
        forall|k: int|
            0 <= k < n ==> #[trigger] c14_rec_ok(t@, o as int, k, 10 + 11 * n, o + len, ng as int),
    ensures
        b == forall|j: int| 0 <= j < n ==> #[trigger] c14_pair_ok(t@, o as int, i as int, j),
{
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            o <= u32::MAX,
            i < n <= 259,
            10 + 11 * n <= len,
            o + len <= t.len(),
            len <= u32::MAX,
            forall|k: int|
                0 <= k < n ==> #[trigger] c14_rec_ok(
                    t@,
                    o as int,
                    k,
                    10 + 11 * n,
                    o + len,
                    ng as int,
                ),
            forall|k: int| 0 <= k < j ==> #[trigger] c14_pair_ok(t@, o as int, i as int, k),
        decreases n - j,
    {
        if !check_c14_pair(t, o, i, j, n, len, ng) {
            return false;
        }
        j += 1;
    }
    true
}

fn check_cmap14(t: &[u8], o: usize, ng: u16) -> (b: bool)
    requires
        o + 2 <= t.len(),
        o <= u32::MAX,
    ensures
        b == wf_cmap14(t@, o as int, ng as int),
{
    if 10 > t.len() - o {
        return false;
    }
    let len = rd32(t, o + 2) as usize;
    let n = rd32(t, o + 6) as usize;
    if len > t.len() - o || n == 0 || n > 259 || 10 + 11 * n > len {
        return false;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            1 <= n <= 259,
            o <= u32::MAX,
            10 + 11 * n <= len,
            o + len <= t.len(),
            len == u32_at(t@, o + 2),
            n == u32_at(t@, o + 6),
            forall|j: int|
                0 <= j < k ==> #[trigger] c14_rec_ok(
                    t@,
                    o as int,
                    j,
                    10 + 11 * n,
                    o + len,
                    ng as int,
                ),
        decreases n - k,
    {
        if !check_c14_rec(t, o, k, 10 + 11 * n, o + len, ng) {
            return false;
        }
        k += 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            1 <= n <= 259,
            o <= u32::MAX,
            10 + 11 * n <= len,
            o + len <= t.len(),
            len == u32_at(t@, o + 2),
            n == u32_at(t@, o + 6),
            forall|j: int|
                0 <= j < n ==> #[trigger] c14_rec_ok(
                    t@,
                    o as int,
                    j,
                    10 + 11 * n,
                    o + len,
                    ng as int,
                ),
            forall|a: int, b: int|
                0 <= a < i && 0 <= b < n ==> #[trigger] c14_pair_ok(t@, o as int, a, b),
        decreases n - i,
    {
        if !check_c14_row(t, o, i, n, len, ng) {
            return false;
        }
        i += 1;
    }
    true
}

/// Decides `wf_cmap_sub` for the subtable at `o`.
pub fn check_cmap_sub(t: &[u8], o: usize, ng: u16) -> (b: bool)
    requires
        o <= u32::MAX,
    ensures
        b == wf_cmap_sub(t@, o as int, ng as int),
{
    if o > t.len() || 2 > t.len() - o {
        return false;
    }
    let f = rd16(t, o);
    if f == 0 {
        check_cmap0(t, o, ng)
    } else if f == 4 {
        check_cmap4(t, o, ng)
    } else if f == 12 {
        check_cmap12(t, o, false, ng)
    } else if f == 13 {
        check_cmap12(t, o, true, ng)
    } else if f == 14 {
        check_cmap14(t, o, ng)
    } else {
        false
    }
}

/// Decides `cmap_use_ok`.
pub fn cmap_use(pe: u32, fmt: u16) -> (b: bool)
    ensures
        b == cmap_use_ok(pe as int, fmt as int),
{
    ((pe == 0x0000_0000 || pe == 0x0000_0001 || pe == 0x0000_0003) && fmt == 4) || ((pe
        == 0x0000_0003 || pe == 0x0000_0004) && fmt == 12) || (pe == 0x0000_0005 && fmt == 14) || (pe
        == 0x0001_0000 && fmt == 0) || ((pe == 0x0003_0000 || pe == 0x0003_0001) && fmt == 4) || (pe
        == 0x0003_000A && (fmt == 12 || fmt == 13))
}

/// Decides `cmap_rec_ok` for encoding record `i`.
pub fn check_cmap_rec(t: &[u8], i: usize, ng: u16) -> (b: bool)
    requires
        t.len() >= 4,
        i < u16_at(t@, 2),
        4 + 8 * u16_at(t@, 2) <= t.len(),
    ensures
        b == cmap_rec_ok(t@, i as int, ng as int),
{
    let r = 4 + 8 * i;
    if i > 0 && rd32(t, r - 8) >= rd32(t, r) {
        return false;
    }
    let o = rd32(t, r + 4) as usize;
    o >= 4 + 8 * (rd16(t, 2) as usize) && check_cmap_sub(t, o, ng) && cmap_use(rd32(t, r), rd16(t, o))
}

/// Decides `wf_cmap`.
pub fn check_cmap(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_cmap(t@, ng as int),
{
    if t.len() < 4 {
        return false;
    }
    let n = rd16(t, 2) as usize;
    if rd16(t, 0) != 0 || n < 1 || 4 + 8 * n > t.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            t.len() >= 4,
            n == u16_at(t@, 2),
            4 + 8 * n <= t.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] cmap_rec_ok(t@, j, ng as int),
        decreases n - i,
    {
        if !check_cmap_rec(t, i, ng) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
