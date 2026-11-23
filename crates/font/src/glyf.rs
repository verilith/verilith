//! Verified checks for `loca` and `glyf`: where each glyph description
//! ends, and that it stays inside its slot.
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

#[inline(always)]
fn coord_sz(short: bool, same: bool) -> (r: usize)
    ensures
        r as int == coord_size(short, same),
        r <= 2,
{
    if short {
        1
    } else if same {
        0
    } else {
        2
    }
}

#[inline(always)]
fn flag_sz(f: u8) -> (r: usize)
    ensures
        r as int == flag_coord_size(f),
        r <= 4,
{
    coord_sz(f & 0x02 != 0, f & 0x10 != 0) + coord_sz(f & 0x04 != 0, f & 0x20 != 0)
}

/// `flags_end` from `p`, with `acc` coordinate bytes already counted.
pub open spec fn flags_acc(g: Seq<u8>, p: int, pts: int, acc: int) -> Option<(int, int)> {
    match flags_end(g, p, pts) {
        Some((e, c)) => Some((e, c + acc)),
        None => None,
    }
}

/// Scans the flags of a simple glyph: see `flags_end`.
pub fn scan_flags(g: &[u8], p0: usize, pts0: usize) -> (r: Option<(usize, usize)>)
    requires
        p0 <= g.len(),
        pts0 <= 65536,
    ensures
        match r {
            Some((e, c)) => flags_end(g@, p0 as int, pts0 as int) == Some((e as int, c as int))
                && e <= g.len() && c <= 4 * 65536,
            None => flags_end(g@, p0 as int, pts0 as int) is None,
        },
{
    let mut p = p0;
    let mut pts = pts0;
    let mut acc: usize = 0;
    while pts > 0
        invariant
            p <= g.len(),
            pts <= pts0 <= 65536,
            acc <= 4 * (pts0 - pts),
            flags_end(g@, p0 as int, pts0 as int) == flags_acc(g@, p as int, pts as int, acc as int),
        decreases pts,
    {
        if p >= g.len() {
            return None;
        }
        let f = rd8(g, p);
        if f & 0x80 != 0 {
            return None;
        }
        let sz = flag_sz(f);
        if f & 0x08 != 0 {
            if p + 1 >= g.len() {
                return None;
            }
            let cnt = 1 + rd8(g, p + 1) as usize;
            if cnt > pts {
                return None;
            }
            assert(cnt * sz <= 4 * cnt) by (nonlinear_arith)
                requires
                    sz <= 4,
            ;
            acc = acc + cnt * sz;
            p = p + 2;
            pts = pts - cnt;
        } else {
            acc = acc + sz;
            p = p + 1;
            pts = pts - 1;
        }
    }
    Some((p, acc))
}

/// Where a simple glyph with `nc` contours ends: see `simple_end`.
pub fn simple_glyph_end(g: &[u8], nc: usize) -> (r: Option<usize>)
    requires
        g.len() >= 10,
        1 <= nc <= 32767,
    ensures
        match r {
            Some(e) => simple_end(g@, nc as int) == Some(e as int) && e <= g.len(),
            None => simple_end(g@, nc as int) is None,
        },
{
    if 12 + 2 * nc > g.len() {
        return None;
    }
    let ilen = rd16(g, 10 + 2 * nc) as usize;
    let fp = 12 + 2 * nc + ilen;
    if fp > g.len() {
        return None;
    }
    let mut k: usize = 0;
    while k + 1 < nc
        invariant
            k < nc <= 32767,
            12 + 2 * nc <= g.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] end_pt(g@, j) < end_pt(g@, j + 1),
        decreases nc - k,
    {
        if rd16(g, 10 + 2 * k) >= rd16(g, 10 + 2 * (k + 1)) {
            assert(!(end_pt(g@, k as int) < end_pt(g@, k + 1)));
            return None;
        }
        k += 1;
    }
    let npts = rd16(g, 10 + 2 * (nc - 1)) as usize + 1;
    match scan_flags(g, fp, npts) {
        Some((e, c)) => {
            if c <= g.len() - e {
                Some(e + c)
            } else {
                None
            }
        },
        None => None,
    }
}

#[inline(always)]
pub fn comp_extra_sz(lo: u8) -> (r: usize)
    ensures
        r as int == comp_extra(lo),
        r <= 12,
{
    (if lo & 0x01 != 0 {
        4usize
    } else {
        2
    }) + (if lo & 0x08 != 0 {
        2usize
    } else if lo & 0x40 != 0 {
        4
    } else if lo & 0x80 != 0 {
        8
    } else {
        0
    })
}

/// Where a composite glyph ends: see `comp_end`.
pub fn composite_glyph_end(g: &[u8], ng: u16) -> (r: Option<usize>)
    requires
        g.len() >= 10,
    ensures
        match r {
            Some(e) => comp_end(g@, 10, ng as int) == Some(e as int) && e <= g.len(),
            None => comp_end(g@, 10, ng as int) is None,
        },
{
    let mut p: usize = 10;
    loop
        invariant
            10 <= p <= g.len(),
            comp_end(g@, 10, ng as int) == comp_end(g@, p as int, ng as int),
        decreases g.len() - p,
    {
        if 4 > g.len() - p {
            return None;
        }
        let hi = rd8(g, p);
        let lo = rd8(g, p + 1);
        let x = comp_extra_sz(lo);
        if rd16(g, p + 2) >= ng || 4 + x > g.len() - p {
            return None;
        }
        let q = p + 4 + x;
        if lo & 0x20 != 0 {
            p = q;
        } else if hi & 0x01 != 0 {
            if 2 > g.len() - q {
                return None;
            }
            let il = rd16(g, q) as usize;
            if il > g.len() - q - 2 {
                return None;
            }
            return Some(q + 2 + il);
        } else {
            return Some(q);
        }
    }
}

/// Where the glyph description at the start of `g` ends: see
/// `glyph_end`.
pub fn find_glyph_end(g: &[u8], ng: u16) -> (r: Option<usize>)
    ensures
        match r {
            Some(e) => glyph_end(g@, ng as int) == Some(e as int) && e <= g.len(),
            None => glyph_end(g@, ng as int) is None,
        },
{
    if g.len() < 10 {
        return None;
    }
    let nc = rdi16(g, 0);
    if nc >= 1 {
        simple_glyph_end(g, nc as usize)
    } else if nc == -1 {
        composite_glyph_end(g, ng)
    } else {
        None
    }
}

/// Decides `wf_glyph`.
pub fn check_glyph(g: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_glyph(g@, ng as int),
{
    match find_glyph_end(g, ng) {
        Some(e) => g.len() - e < 4 && check_zeros(g, e, g.len()),
        None => false,
    }
}

/// Entry `i` of `loca`.
#[inline(always)]
pub fn loca_get(loca: &[u8], fmt: u16, i: usize) -> (r: usize)
    requires
        fmt <= 1,
        (i + 1) * (if fmt == 0 {
            2int
        } else {
            4
        }) <= loca.len(),
    ensures
        r as int == loca_at(loca@, fmt as int, i as int),
        r <= u32::MAX,
{
    if fmt == 0 {
        2 * (rd16(loca, 2 * i) as usize)
    } else {
        rd32(loca, 4 * i) as usize
    }
}

/// Decides `wf_loca`.
pub fn check_loca(loca: &[u8], fmt: u16, ng: u16, glyf_len: usize) -> (b: bool)
    requires
        fmt <= 1,
    ensures
        b == wf_loca(loca@, fmt as int, ng as int, glyf_len as int),
{
    let n = ng as usize;
    let w: usize = if fmt == 0 {
        2
    } else {
        4
    };
    if loca.len() != (n + 1) * w {
        return false;
    }
    let mut prev = loca_get(loca, fmt, 0);
    if prev != 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ng,
            fmt <= 1,
            w == if fmt == 0 {
                2int
            } else {
                4
            },
            loca.len() == (n + 1) * w,
            prev as int == loca_at(loca@, fmt as int, i as int),
            forall|k: int| 0 <= k < i ==> #[trigger] loca_step(loca@, fmt as int, k),
        decreases n - i,
    {
        let next = loca_get(loca, fmt, i + 1);
        if next < prev || next % 4 != 0 {
            assert(!loca_step(loca@, fmt as int, i as int));
            return false;
        }
        prev = next;
        i += 1;
    }
    prev == glyf_len || (prev == 0 && glyf_len == 1)
}

/// Decides `wf_glyf`, given a well-formed `loca`.
pub fn check_glyf(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16) -> (b: bool)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
    ensures
        b == wf_glyf(glyf@, loca@, fmt as int, ng as int),
{
    let n = ng as usize;
    if glyf.len() == 1 && loca_get(loca, fmt, n) == 0 && rd8(glyf, 0) != 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ng,
            fmt <= 1,
            wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
            loca_at(loca@, fmt as int, ng as int) == 0 && glyf@.len() == 1 ==> glyf@[0] == 0,
            forall|k: int|
                0 <= k < i ==> #[trigger] glyph_ok(glyf@, loca@, fmt as int, ng as int, k),
        decreases n - i,
    {
        proof {
            lemma_loca_le(loca@, fmt as int, ng as int, glyf.len() as int, i as int + 1);
            assert(loca_step(loca@, fmt as int, i as int));
        }
        let a = loca_get(loca, fmt, i);
        let b = loca_get(loca, fmt, i + 1);
        if a < b {
            if !check_glyph(slice(glyf, a, b), ng) {
                assert(!glyph_ok(glyf@, loca@, fmt as int, ng as int, i as int));
                return false;
            }
        }
        i += 1;
    }
    true
}

/// In a well-formed `loca`, every entry is at most the length of `glyf`.
pub proof fn lemma_loca_le(loca: Seq<u8>, fmt: int, ng: int, glyf_len: int, i: int)
    requires
        wf_loca(loca, fmt, ng, glyf_len),
        0 <= i <= ng,
    ensures
        loca_at(loca, fmt, i) <= glyf_len,
    decreases ng - i,
{
    if i < ng {
        lemma_loca_le(loca, fmt, ng, glyf_len, i + 1);
        assert(loca_step(loca, fmt, i));
    }
}

} // verus!
