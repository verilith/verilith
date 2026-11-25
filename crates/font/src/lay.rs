//! Verified deciders for the building blocks of the layout tables
//! (`spec_layout.rs`): offsets, id arrays, coverage, class definitions,
//! device tables, script and feature lists.
use crate::prims::*;
use crate::spec::*;
use crate::spec_layout::*;
use vstd::prelude::*;

verus! {

/// Tables come out of a font directory, whose lengths are 32 bits (and
/// on a 32-bit target, out of a slice: see [`TABLE_MAX`]).
pub open spec fn small(t: &[u8]) -> bool {
    t.len() <= TABLE_MAX
}

#[inline]
pub fn room(t: &[u8], p: usize, k: usize) -> (b: bool)
    ensures
        b == (p + k <= t.len()),
{
    p <= t.len() && t.len() - p >= k
}

pub fn check_offs<F: Fn(usize) -> bool>(
    t: &[u8],
    a: usize,
    n: usize,
    w: usize,
    base: usize,
    min: usize,
    null: bool,
    f: &F,
    Ghost(p): Ghost<spec_fn(int) -> bool>,
) -> (b: bool)
    requires
        small(t),
        base <= t.len(),
        w == 2 || w == 4 || w == 6,
        forall|o: usize| o < t.len() ==> #[trigger] f.requires((o,)),
        forall|o: usize, r: bool| f.ensures((o,), r) ==> r == p(o as int),
    ensures
        b == offs(t@, a as int, n as int, w as int, base as int, min as int, null, p),
{
    if min > 65535 {
        return false;
    }
    if n == 0 {
        return true;
    }
    if a > t.len() {
        assert(!off_ok(t@, a as int, 0, w as int, base as int, min as int, null, p));
        return false;
    }
    let mut i: usize = 0;
    let mut pos: usize = a;
    while i < n
        invariant
            i <= n,
            small(t),
            base <= t.len(),
            pos <= t.len(),
            w == 2 || w == 4 || w == 6,
            i < n ==> pos == a + w * i,
            forall|o: usize| o < t.len() ==> #[trigger] f.requires((o,)),
            forall|o: usize, r: bool| f.ensures((o,), r) ==> r == p(o as int),
            forall|k: int|
                0 <= k < i ==> #[trigger] off_ok(t@, a as int, k, w as int, base as int, min as int, null, p),
        decreases n - i,
    {
        if t.len() - pos < 2 {
            assert(!off_ok(t@, a as int, i as int, w as int, base as int, min as int, null, p));
            return false;
        }
        let o = rd16(t, pos) as usize;
        if !(null && o == 0) {
            if o < min || o >= t.len() - base || !f(base + o) {
                assert(!off_ok(t@, a as int, i as int, w as int, base as int, min as int, null, p));
                return false;
            }
        }
        assert(off_ok(t@, a as int, i as int, w as int, base as int, min as int, null, p));
        i += 1;
        if i < n {
            assert(w * i == w * (i - 1) + w) by (nonlinear_arith);
            if t.len() - pos < w {
                assert(!off_ok(t@, a as int, i as int, w as int, base as int, min as int, null, p));
                return false;
            }
            pos += w;
        }
    }
    true
}

/// One offset at `a`.
pub fn check_off<F: Fn(usize) -> bool>(
    t: &[u8],
    a: usize,
    base: usize,
    min: usize,
    null: bool,
    f: &F,
    Ghost(p): Ghost<spec_fn(int) -> bool>,
) -> (b: bool)
    requires
        small(t),
        base <= t.len(),
        forall|o: usize| o < t.len() ==> #[trigger] f.requires((o,)),
        forall|o: usize, r: bool| f.ensures((o,), r) ==> r == p(o as int),
    ensures
        b == off_ok(t@, a as int, 0, 2, base as int, min as int, null, p),
{
    if !room(t, a, 2) {
        return false;
    }
    let o = rd16(t, a) as usize;
    if null && o == 0 {
        return true;
    }
    o >= min && o < t.len() - base && f(base + o)
}

pub fn check_ids(t: &[u8], a: usize, n: usize, lim: usize) -> (b: bool)
    requires
        small(t),
    ensures
        b == ids(t@, a as int, n as int, lim as int),
{
    if a > t.len() || (t.len() - a) / 2 < n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a + 2 * n <= t.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] id_ok(t@, a as int, k, lim as int),
        decreases n - i,
    {
        if rd16(t, a + 2 * i) as usize >= lim {
            assert(!id_ok(t@, a as int, i as int, lim as int));
            return false;
        }
        assert(id_ok(t@, a as int, i as int, lim as int));
        i += 1;
    }
    true
}

pub fn check_lrecs(t: &[u8], a: usize, n: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
    ensures
        b == lrecs(t@, a as int, n as int, ng as int, nl as int),
{
    if a > t.len() || (t.len() - a) / 4 < n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a + 4 * n <= t.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] lrec_ok(t@, a as int, k, ng as int, nl as int),
        decreases n - i,
    {
        if rd16(t, a + 4 * i) as usize >= ng || rd16(t, a + 4 * i + 2) as usize >= nl {
            assert(!lrec_ok(t@, a as int, i as int, ng as int, nl as int));
            return false;
        }
        assert(lrec_ok(t@, a as int, i as int, ng as int, nl as int));
        i += 1;
    }
    true
}

pub fn check_cov(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_cov(t@, o as int, ng as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let fmt = rd16(t, o);
    let n = rd16(t, o + 2) as usize;
    if n > ng {
        return false;
    }
    if fmt == 1 {
        return check_ids(t, o + 4, n, ng);
    }
    if fmt != 2 || (t.len() - (o + 4)) / 6 < n {
        return false;
    }
    let mut i: usize = 0;
    let mut cnt: u64 = 0;
    let mut prev: u16 = 0;
    while i < n
        invariant
            i <= n,
            n <= 65535,
            small(t),
            o + 4 + 6 * n <= t.len(),
            u16_at(t@, o as int) == 2,
            n == u16_at(t@, o + 2),
            n <= ng,
            cnt == cov_count(t@, o as int, i as int),
            cnt <= 65536 * i,
            i > 0 ==> prev == cov_end(t@, o as int, i - 1),
            forall|k: int| 0 <= k < i ==> #[trigger] cov_range_ok(t@, o as int, k),
        decreases n - i,
    {
        let r = o + 4 + 6 * i;
        let s = rd16(t, r);
        let e = rd16(t, r + 2);
        let ci = rd16(t, r + 4);
        if s > e || (i > 0 && s < prev) || ci as u64 != cnt {
            assert(!cov_range_ok(t@, o as int, i as int));
            return false;
        }
        assert(cov_range_ok(t@, o as int, i as int));
        cnt += (e - s) as u64 + 1;
        prev = e;
        i += 1;
        assert(cnt == cov_count(t@, o as int, i as int));
    }
    true
}

pub fn check_classdef(t: &[u8], o: usize, ng: usize, maxc: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
        maxc <= 0xFFFF,
    ensures
        b == wf_classdef(t@, o as int, ng as int, maxc as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let fmt = rd16(t, o);
    if fmt == 1 {
        if !room(t, o, 6) {
            return false;
        }
        let n = rd16(t, o + 4) as usize;
        return (rd16(t, o + 2) as usize) < ng && n <= ng && check_ids(t, o + 6, n, maxc + 1);
    }
    let n = rd16(t, o + 2) as usize;
    if fmt != 2 || n > ng || (t.len() - (o + 4)) / 6 < n {
        return false;
    }
    let mut i: usize = 0;
    let mut prev: u16 = 0;
    while i < n
        invariant
            i <= n,
            n <= 65535,
            small(t),
            o + 4 + 6 * n <= t.len(),
            u16_at(t@, o as int) == 2,
            n == u16_at(t@, o + 2),
            i > 0 ==> prev == u16_at(t@, o + 4 + 6 * (i - 1) + 2),
            forall|k: int| 0 <= k < i ==> #[trigger] cd_range_ok(t@, o as int, k, maxc as int),
        decreases n - i,
    {
        let r = o + 4 + 6 * i;
        let s = rd16(t, r);
        let e = rd16(t, r + 2);
        if s > e || (i > 0 && prev != 0 && s <= prev) || rd16(t, r + 4) as usize > maxc {
            assert(!cd_range_ok(t@, o as int, i as int, maxc as int));
            return false;
        }
        assert(cd_range_ok(t@, o as int, i as int, maxc as int));
        prev = e;
        i += 1;
    }
    true
}

pub fn check_device(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_device(t@, o as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let s = rd16(t, o) as usize;
    let e = rd16(t, o + 2) as usize;
    let f = rd16(t, o + 4);
    if f == 0x8000 {
        return true;
    }
    if s > e || f < 1 || f > 3 {
        return false;
    }
    let per: usize = if f == 1 {
        8
    } else if f == 2 {
        4
    } else {
        2
    };
    room(t, o + 6, 2 * ((e - s) / per + 1))
}

pub fn check_langsys(t: &[u8], o: usize, nf: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_langsys(t@, o as int, nf as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let req = rd16(t, o + 2);
    let n = rd16(t, o + 4) as usize;
    rd16(t, o) == 0 && (req == 0xFFFF || (req as usize) < nf) && n <= nf && check_ids(t, o + 6, n, nf)
}

pub fn check_script(t: &[u8], o: usize, dflt: bool, nf: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_script(t@, o as int, dflt, nf as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let n = rd16(t, o + 2) as usize;
    if dflt && rd16(t, o) == 0 {
        return false;
    }
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_langsys(t@, x as int, nf as int),
        { check_langsys(t, x, nf) };
    if !check_off(t, o, o, 0, true, &f, Ghost(|x: int| wf_langsys(t@, x, nf as int))) {
        return false;
    }
    if !check_offs(t, o + 8, n, 6, o, 4 + 6 * n, false, &f, Ghost(|x: int| wf_langsys(t@, x, nf as int))) {
        return false;
    }
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i,
            n <= 65535,
            small(t),
            o + 4 <= t.len(),
            n == u16_at(t@, o + 2),
            offs(
                t@,
                o + 8,
                n as int,
                6,
                o as int,
                4 + 6 * n,
                false,
                |x: int| wf_langsys(t@, x, nf as int),
            ),
            forall|k: int| 0 < k < i ==> #[trigger] tag_order_ok(t@, o + 4, k),
        decreases n - i,
    {
        assert(off_ok(t@, o + 8, i as int, 6, o as int, 4 + 6 * n, false, |x: int| wf_langsys(t@, x, nf as int)));
        let prev = rd32(t, o + 4 + 6 * (i - 1));
        let cur = rd32(t, o + 4 + 6 * i);
        if prev != 0 && prev > cur {
            assert(!tag_order_ok(t@, o + 4, i as int));
            return false;
        }
        assert(tag_order_ok(t@, o + 4, i as int));
        i += 1;
    }
    true
}

pub fn check_scriptlist(t: &[u8], o: usize, nf: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_scriptlist(t@, o as int, nf as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let min = 2 + 6 * n;
    if min > 65535 {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 65535,
            small(t),
            o + 2 <= t.len(),
            n == u16_at(t@, o as int),
            min == 2 + 6 * n,
            forall|k: int| 0 <= k < i ==> #[trigger] script_rec_ok(t@, o as int, k, min as int, nf as int),
        decreases n - i,
    {
        let r = o + 2 + 6 * i;
        if !room(t, r, 6) {
            assert(!script_rec_ok(t@, o as int, i as int, min as int, nf as int));
            return false;
        }
        let off = rd16(t, r + 4) as usize;
        if off < min || off >= t.len() - o || !check_script(t, o + off, rd32(t, r) == 0x44464c54, nf) {
            assert(!script_rec_ok(t@, o as int, i as int, min as int, nf as int));
            return false;
        }
        assert(script_rec_ok(t@, o as int, i as int, min as int, nf as int));
        i += 1;
    }
    true
}

pub fn check_feature(t: &[u8], o: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_feature(t@, o as int, nl as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let params = rd16(t, o) as usize;
    let n = rd16(t, o + 2) as usize;
    4 + 2 * n <= 65535 && (params == 0 || (4 + 2 * n <= params && params < t.len() - o)) && check_ids(
        t,
        o + 4,
        n,
        nl,
    )
}

pub fn check_featurelist(t: &[u8], o: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_featurelist(t@, o as int, nl as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_feature(t@, x as int, nl as int),
        { check_feature(t, x, nl) };
    check_offs(t, o + 6, n, 6, o, 2 + 6 * n, false, &f, Ghost(|x: int| wf_feature(t@, x, nl as int)))
}

} // verus!
