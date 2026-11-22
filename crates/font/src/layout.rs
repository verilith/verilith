//! Verified deciders for `GSUB`, `GPOS` and `GDEF` (`spec_layout.rs`).
use crate::lay::*;
use crate::prims::*;
use crate::spec::*;
use crate::spec_layout::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Contextual subtables
// ---------------------------------------------------------------------
fn check_rule(t: &[u8], o: usize, lim: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_rule(t@, o as int, lim as int, ng as int, nl as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let g = rd16(t, o) as usize;
    let l = rd16(t, o + 2) as usize;
    g >= 1 && check_ids(t, o + 4, g - 1, lim) && check_lrecs(t, o + 4 + 2 * (g - 1), l, ng, nl)
}

fn check_ruleset(t: &[u8], o: usize, lim: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_ruleset(t@, o as int, lim as int, ng as int, nl as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_rule(t@, x as int, lim as int, ng as int, nl as int),
        { check_rule(t, x, lim, ng, nl) };
    check_offs(
        t,
        o + 2,
        n,
        2,
        o,
        2 + 2 * n,
        false,
        &f,
        Ghost(|x: int| wf_rule(t@, x, lim as int, ng as int, nl as int)),
    )
}

fn check_context(t: &[u8], o: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_context(t@, o as int, ng as int, nl as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let fmt = rd16(t, o);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if fmt == 1 {
        let n = rd16(t, o + 4) as usize;
        let rs = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_ruleset(t@, x as int, ng as int, ng as int, nl as int),
            { check_ruleset(t, x, ng, ng, nl) };
        check_off(t, o + 2, o, 6 + 2 * n, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
            && check_offs(
            t,
            o + 6,
            n,
            2,
            o,
            6 + 2 * n,
            false,
            &rs,
            Ghost(|x: int| wf_ruleset(t@, x, ng as int, ng as int, nl as int)),
        )
    } else if fmt == 2 {
        if !room(t, o, 8) {
            return false;
        }
        let n = rd16(t, o + 6) as usize;
        let cd = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_classdef(t@, x as int, ng as int, 0xFFFF),
            { check_classdef(t, x, ng, 0xFFFF) };
        let rs = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_ruleset(t@, x as int, 0x10000, ng as int, nl as int),
            { check_ruleset(t, x, 0x10000, ng, nl) };
        check_off(t, o + 2, o, 8 + 2 * n, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
            && check_off(
            t,
            o + 4,
            o,
            8 + 2 * n,
            false,
            &cd,
            Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
        ) && check_offs(
            t,
            o + 8,
            n,
            2,
            o,
            8 + 2 * n,
            true,
            &rs,
            Ghost(|x: int| wf_ruleset(t@, x, 0x10000, ng as int, nl as int)),
        )
    } else if fmt == 3 {
        let g = rd16(t, o + 2) as usize;
        let l = rd16(t, o + 4) as usize;
        check_offs(
            t,
            o + 6,
            g,
            2,
            o,
            6 + 2 * g + 4 * l,
            false,
            &cov,
            Ghost(|x: int| wf_cov(t@, x, ng as int)),
        ) && check_lrecs(t, o + 6 + 2 * g, l, ng, nl)
    } else {
        false
    }
}

fn check_chainrule(t: &[u8], o: usize, lim: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_chainrule(t@, o as int, lim as int, ng as int, nl as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let b = rd16(t, o) as usize;
    if !check_ids(t, o + 2, b, lim) {
        return false;
    }
    let p1 = o + 2 + 2 * b;
    if !room(t, p1, 2) {
        return false;
    }
    let i = rd16(t, p1) as usize;
    if i < 1 || !check_ids(t, p1 + 2, i - 1, lim) {
        return false;
    }
    let p2 = p1 + 2 + 2 * (i - 1);
    if !room(t, p2, 2) {
        return false;
    }
    let a = rd16(t, p2) as usize;
    if !check_ids(t, p2 + 2, a, lim) {
        return false;
    }
    let p3 = p2 + 2 + 2 * a;
    if !room(t, p3, 2) {
        return false;
    }
    check_lrecs(t, p3 + 2, rd16(t, p3) as usize, ng, nl)
}

fn check_chainruleset(t: &[u8], o: usize, lim: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_chainruleset(t@, o as int, lim as int, ng as int, nl as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_chainrule(t@, x as int, lim as int, ng as int, nl as int),
        { check_chainrule(t, x, lim, ng, nl) };
    check_offs(
        t,
        o + 2,
        n,
        2,
        o,
        2 + 2 * n,
        false,
        &f,
        Ghost(|x: int| wf_chainrule(t@, x, lim as int, ng as int, nl as int)),
    )
}

fn check_chain3(t: &[u8], o: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o + 4 <= t.len(),
    ensures
        b == wf_chain3(t@, o as int, ng as int, nl as int),
{
    let b = rd16(t, o + 2) as usize;
    let p1 = o + 4 + 2 * b;
    if !room(t, p1, 2) {
        return false;
    }
    let i = rd16(t, p1) as usize;
    let p2 = p1 + 2 + 2 * i;
    if !room(t, p2, 2) {
        return false;
    }
    let a = rd16(t, p2) as usize;
    let p3 = p2 + 2 + 2 * a;
    if !room(t, p3, 2) {
        return false;
    }
    let l = rd16(t, p3) as usize;
    let end = 10 + 2 * (b + i + a) + 4 * l;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    check_lrecs(t, p3 + 2, l, ng, nl) && check_offs(
        t,
        o + 4,
        b,
        2,
        o,
        end,
        false,
        &cov,
        Ghost(|x: int| wf_cov(t@, x, ng as int)),
    ) && check_offs(t, p1 + 2, i, 2, o, end, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
        && check_offs(t, p2 + 2, a, 2, o, end, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
}

fn check_chain(t: &[u8], o: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_chain(t@, o as int, ng as int, nl as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let fmt = rd16(t, o);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if fmt == 1 {
        if !room(t, o, 6) {
            return false;
        }
        let n = rd16(t, o + 4) as usize;
        let rs = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_chainruleset(t@, x as int, ng as int, ng as int, nl as int),
            { check_chainruleset(t, x, ng, ng, nl) };
        check_off(t, o + 2, o, 6 + 2 * n, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
            && check_offs(
            t,
            o + 6,
            n,
            2,
            o,
            6 + 2 * n,
            false,
            &rs,
            Ghost(|x: int| wf_chainruleset(t@, x, ng as int, ng as int, nl as int)),
        )
    } else if fmt == 2 {
        if !room(t, o, 12) {
            return false;
        }
        let n = rd16(t, o + 10) as usize;
        let end = 12 + 2 * n;
        let cd = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_classdef(t@, x as int, ng as int, 0xFFFF),
            { check_classdef(t, x, ng, 0xFFFF) };
        let rs = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_chainruleset(t@, x as int, 0x10000, ng as int, nl as int),
            { check_chainruleset(t, x, 0x10000, ng, nl) };
        check_off(t, o + 2, o, end, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
            && check_off(
            t,
            o + 4,
            o,
            end,
            true,
            &cd,
            Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
        ) && check_off(
            t,
            o + 6,
            o,
            end,
            false,
            &cd,
            Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
        ) && check_off(
            t,
            o + 8,
            o,
            end,
            true,
            &cd,
            Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
        ) && check_offs(
            t,
            o + 12,
            n,
            2,
            o,
            end,
            true,
            &rs,
            Ghost(|x: int| wf_chainruleset(t@, x, 0x10000, ng as int, nl as int)),
        )
    } else {
        fmt == 3 && check_chain3(t, o, ng, nl)
    }
}

// ---------------------------------------------------------------------
// GSUB
// ---------------------------------------------------------------------
fn check_glyphs(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_glyphs(t@, o as int, ng as int),
{
    room(t, o, 2) && check_ids(t, o + 2, rd16(t, o) as usize, ng)
}

fn check_single_sub(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_single_sub(t@, o as int, ng as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let fmt = rd16(t, o);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if fmt == 1 {
        let d = rdi16(t, o + 4);
        let ad: usize = if d < 0 {
            (-d) as usize
        } else {
            d as usize
        };
        ad < ng && check_off(t, o + 2, o, 6, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
    } else if fmt == 2 {
        let n = rd16(t, o + 4) as usize;
        n <= ng && check_ids(t, o + 6, n, ng) && check_off(
            t,
            o + 2,
            o,
            6 + 2 * n,
            false,
            &cov,
            Ghost(|x: int| wf_cov(t@, x, ng as int)),
        )
    } else {
        false
    }
}

fn check_multi_sub(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_multi_sub(t@, o as int, ng as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let n = rd16(t, o + 4) as usize;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    let gl = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_glyphs(t@, x as int, ng as int),
        { check_glyphs(t, x, ng) };
    rd16(t, o) == 1 && check_off(
        t,
        o + 2,
        o,
        6 + 2 * n,
        false,
        &cov,
        Ghost(|x: int| wf_cov(t@, x, ng as int)),
    ) && check_offs(t, o + 6, n, 2, o, 6 + 2 * n, false, &gl, Ghost(|x: int| wf_glyphs(t@, x, ng as int)))
}

fn check_ligature(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_ligature(t@, o as int, ng as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let c = rd16(t, o + 2) as usize;
    (rd16(t, o) as usize) < ng && c >= 1 && check_ids(t, o + 4, c - 1, ng)
}

fn check_ligset(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_ligset(t@, o as int, ng as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_ligature(t@, x as int, ng as int),
        { check_ligature(t, x, ng) };
    check_offs(t, o + 2, n, 2, o, 2 + 2 * n, false, &f, Ghost(|x: int| wf_ligature(t@, x, ng as int)))
}

fn check_lig_sub(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_lig_sub(t@, o as int, ng as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let n = rd16(t, o + 4) as usize;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    let ls = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_ligset(t@, x as int, ng as int),
        { check_ligset(t, x, ng) };
    rd16(t, o) == 1 && check_off(
        t,
        o + 2,
        o,
        6 + 2 * n,
        false,
        &cov,
        Ghost(|x: int| wf_cov(t@, x, ng as int)),
    ) && check_offs(t, o + 6, n, 2, o, 6 + 2 * n, false, &ls, Ghost(|x: int| wf_ligset(t@, x, ng as int)))
}

fn check_rev_chain(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_rev_chain(t@, o as int, ng as int),
{
    if !room(t, o, 6) || rd16(t, o) != 1 {
        return false;
    }
    let b = rd16(t, o + 4) as usize;
    let p1 = o + 6 + 2 * b;
    if !room(t, p1, 2) {
        return false;
    }
    let a = rd16(t, p1) as usize;
    let p2 = p1 + 2 + 2 * a;
    if !room(t, p2, 2) {
        return false;
    }
    let g = rd16(t, p2) as usize;
    let end = 10 + 2 * (b + a + g);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    check_ids(t, p2 + 2, g, ng) && check_off(
        t,
        o + 2,
        o,
        end,
        false,
        &cov,
        Ghost(|x: int| wf_cov(t@, x, ng as int)),
    ) && check_offs(t, o + 6, b, 2, o, end, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
        && check_offs(t, p1 + 2, a, 2, o, end, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
}

fn check_gsub_sub(t: &[u8], o: usize, ty: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_gsub_sub(t@, o as int, ty as int, ng as int, nl as int),
{
    if ty == 1 {
        check_single_sub(t, o, ng)
    } else if ty == 2 || ty == 3 {
        check_multi_sub(t, o, ng)
    } else if ty == 4 {
        check_lig_sub(t, o, ng)
    } else if ty == 5 {
        check_context(t, o, ng, nl)
    } else if ty == 6 {
        check_chain(t, o, ng, nl)
    } else {
        ty == 8 && check_rev_chain(t, o, ng)
    }
}

// ---------------------------------------------------------------------
// GPOS
// ---------------------------------------------------------------------
fn hasx(f: u16, m: u16) -> (b: bool)
    requires
        m == 1 || m == 2 || m == 4 || m == 8 || m == 16 || m == 32 || m == 64 || m == 128,
    ensures
        b == has(f as int, m as int),
{
    assert((f & m != 0) == ((f / m) % 2 == 1)) by (bit_vector)
        requires
            m == 1 || m == 2 || m == 4 || m == 8 || m == 16 || m == 32 || m == 64 || m == 128,
    ;
    f & m != 0
}

fn szx(f: u16, m: u16) -> (r: usize)
    requires
        m == 1 || m == 2 || m == 4 || m == 8 || m == 16 || m == 32 || m == 64 || m == 128,
    ensures
        r == sz(f as int, m as int),
{
    if hasx(f, m) {
        2
    } else {
        0
    }
}

fn vsize_x(f: u16) -> (r: usize)
    ensures
        r == vsize(f as int),
        r <= 16,
{
    szx(f, 1) + szx(f, 2) + szx(f, 4) + szx(f, 8) + szx(f, 16) + szx(f, 32) + szx(f, 64) + szx(f, 128)
}

fn check_dev(t: &[u8], base: usize, p: usize) -> (b: bool)
    requires
        small(t),
        base <= t.len(),
    ensures
        b == dev_ok(t@, base as int, p as int),
{
    let f = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_device(t@, x as int),
        { check_device(t, x) };
    check_off(t, p, base, 0, true, &f, Ghost(|x: int| wf_device(t@, x)))
}

fn check_value(t: &[u8], base: usize, p: usize, f: u16) -> (b: bool)
    requires
        small(t),
        base <= t.len(),
    ensures
        b == wf_value(t@, base as int, p as int, f as int),
{
    if !room(t, p, vsize_x(f)) {
        return false;
    }
    let p4 = p + szx(f, 1) + szx(f, 2) + szx(f, 4) + szx(f, 8);
    let p5 = p4 + szx(f, 16);
    let p6 = p5 + szx(f, 32);
    let p7 = p6 + szx(f, 64);
    (!hasx(f, 16) || check_dev(t, base, p4)) && (!hasx(f, 32) || check_dev(t, base, p5)) && (!hasx(f, 64)
        || check_dev(t, base, p6)) && (!hasx(f, 128) || check_dev(t, base, p7))
}

fn check_single_pos(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_single_pos(t@, o as int, ng as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let fmt = rd16(t, o);
    let f = rd16(t, o + 4);
    let w = vsize_x(f);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if fmt == 1 {
        return check_value(t, o, o + 6, f) && check_off(
            t,
            o + 2,
            o,
            6 + w,
            false,
            &cov,
            Ghost(|x: int| wf_cov(t@, x, ng as int)),
        );
    }
    if fmt != 2 || !room(t, o, 8) {
        return false;
    }
    let n = rd16(t, o + 6) as usize;
    let mut i: usize = 0;
    let mut pos: usize = o + 8;
    while i < n
        invariant
            i <= n,
            n == u16_at(t@, o + 6),
            small(t),
            o + 8 <= t.len(),
            w == vsize(f as int),
            w <= 16,
            f == u16_at(t@, o + 4),
            u16_at(t@, o as int) == 2,
            pos == o + 8 + w * i,
            pos <= o + 8 + 16 * i,
            forall|k: int| 0 <= k < i ==> #[trigger] value_at(t@, o as int, o + 8, w as int, k, f as int),
        decreases n - i,
    {
        if !check_value(t, o, pos, f) {
            assert(!value_at(t@, o as int, o + 8, w as int, i as int, f as int));
            return false;
        }
        assert(value_at(t@, o as int, o + 8, w as int, i as int, f as int));
        assert(w * (i + 1) == w * i + w) by (nonlinear_arith);
        i += 1;
        pos += w;
    }
    assert(n * w <= 65535 * 16) by (nonlinear_arith)
        requires
            n <= 65535,
            w <= 16,
    ;
    check_off(t, o + 2, o, 8 + n * w, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
}

fn check_pairset(t: &[u8], o: usize, f1: u16, f2: u16, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_pairset(t@, o as int, f1 as int, f2 as int, ng as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let v1 = vsize_x(f1);
    let w = 2 + v1 + vsize_x(f2);
    let mut i: usize = 0;
    let mut r: usize = o + 2;
    while i < n
        invariant
            i <= n,
            n == u16_at(t@, o as int),
            small(t),
            o + 2 <= t.len(),
            v1 == vsize(f1 as int),
            w == 2 + vsize(f1 as int) + vsize(f2 as int),
            w <= 34,
            r == o + 2 + w * i,
            r <= o + 2 + 34 * i,
            forall|k: int|
                0 <= k < i ==> #[trigger] pair_rec_ok(t@, o as int, k, f1 as int, f2 as int, ng as int),
        decreases n - i,
    {
        if !room(t, r, 2) || rd16(t, r) as usize >= ng || !check_value(t, o, r + 2, f1) || !check_value(
            t,
            o,
            r + 2 + v1,
            f2,
        ) {
            assert(!pair_rec_ok(t@, o as int, i as int, f1 as int, f2 as int, ng as int));
            return false;
        }
        assert(pair_rec_ok(t@, o as int, i as int, f1 as int, f2 as int, ng as int));
        assert(w * (i + 1) == w * i + w) by (nonlinear_arith);
        i += 1;
        r += w;
    }
    true
}

fn check_pair_pos(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_pair_pos(t@, o as int, ng as int),
{
    if !room(t, o, 8) {
        return false;
    }
    let fmt = rd16(t, o);
    let f1 = rd16(t, o + 4);
    let f2 = rd16(t, o + 6);
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if !check_off(t, o + 2, o, 8, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int))) {
        return false;
    }
    if fmt == 1 {
        if !room(t, o, 10) {
            return false;
        }
        let n = rd16(t, o + 8) as usize;
        let ps = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_pairset(t@, x as int, f1 as int, f2 as int, ng as int),
            { check_pairset(t, x, f1, f2, ng) };
        return check_offs(
            t,
            o + 10,
            n,
            2,
            o,
            10 + 2 * n,
            false,
            &ps,
            Ghost(|x: int| wf_pairset(t@, x, f1 as int, f2 as int, ng as int)),
        );
    }
    if fmt != 2 || !room(t, o, 16) {
        return false;
    }
    let v1 = vsize_x(f1);
    let w = v1 + vsize_x(f2);
    let c1 = rd16(t, o + 12) as usize;
    let c2 = rd16(t, o + 14) as usize;
    assert(c1 * c2 <= 65535 * 65535) by (nonlinear_arith)
        requires
            c1 <= 65535,
            c2 <= 65535,
    ;
    let cells = c1 * c2;
    assert(cells * w <= 65535 * 65535 * 32) by (nonlinear_arith)
        requires
            cells <= 65535 * 65535,
            w <= 32,
    ;
    let min = 16 + cells * w;
    let cd = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_classdef(t@, x as int, ng as int, 0xFFFF),
        { check_classdef(t, x, ng, 0xFFFF) };
    if !check_off(t, o + 8, o, min, false, &cd, Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF)))
        || !check_off(t, o + 10, o, min, false, &cd, Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF))) {
        return false;
    }
    if w == 0 {
        return true;
    }
    let mut k: usize = 0;
    let mut r: usize = o + 16;
    while k < cells
        invariant
            k <= cells,
            cells == u16_at(t@, o + 12) * u16_at(t@, o + 14),
            cells <= 65535 * 65535,
            small(t),
            o + 16 <= t.len(),
            f1 == u16_at(t@, o + 4),
            f2 == u16_at(t@, o + 6),
            u16_at(t@, o as int) == 2,
            v1 == vsize(f1 as int),
            w == vsize(f1 as int) + vsize(f2 as int),
            0 < w <= 32,
            r == o + 16 + w * k,
            r <= o + 16 + 32 * k,
            off_ok(t@, o + 2, 0, 2, o as int, 8, false, |x: int| wf_cov(t@, x, ng as int)),
            off_ok(t@, o + 8, 0, 2, o as int, 16 + cells * w, false, |x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
            off_ok(t@, o + 10, 0, 2, o as int, 16 + cells * w, false, |x: int| wf_classdef(t@, x, ng as int, 0xFFFF)),
            forall|j: int| 0 <= j < k ==> #[trigger] class_pair_ok(t@, o as int, j, f1 as int, f2 as int),
        decreases cells - k,
    {
        if !check_value(t, o, r, f1) || !check_value(t, o, r + v1, f2) {
            assert(!class_pair_ok(t@, o as int, k as int, f1 as int, f2 as int));
            return false;
        }
        assert(class_pair_ok(t@, o as int, k as int, f1 as int, f2 as int));
        assert(w * (k + 1) == w * k + w) by (nonlinear_arith);
        k += 1;
        r += w;
    }
    true
}

fn check_anchor(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_anchor(t@, o as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let f = rd16(t, o);
    if f < 1 || f > 3 {
        return false;
    }
    if f == 2 {
        return room(t, o, 8);
    }
    if f == 3 {
        let dv = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_device(t@, x as int),
            { check_device(t, x) };
        return check_off(t, o + 6, o, 10, true, &dv, Ghost(|x: int| wf_device(t@, x))) && check_off(
            t,
            o + 8,
            o,
            10,
            true,
            &dv,
            Ghost(|x: int| wf_device(t@, x)),
        );
    }
    true
}

fn check_cursive(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_cursive(t@, o as int, ng as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let n = rd16(t, o + 4) as usize;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    let an = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_anchor(t@, x as int),
        { check_anchor(t, x) };
    rd16(t, o) == 1 && check_offs(
        t,
        o + 6,
        2 * n,
        2,
        o,
        6 + 4 * n,
        true,
        &an,
        Ghost(|x: int| wf_anchor(t@, x)),
    ) && check_off(t, o + 2, o, 6 + 4 * n, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int)))
}

fn check_markarray(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_markarray(t@, o as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let an = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_anchor(t@, x as int),
        { check_anchor(t, x) };
    check_offs(t, o + 4, n, 4, o, 2 + 4 * n, false, &an, Ghost(|x: int| wf_anchor(t@, x)))
}

fn check_anchorarray(t: &[u8], o: usize, cc: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
        cc <= 65535,
    ensures
        b == wf_anchorarray(t@, o as int, cc as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let rows = rd16(t, o) as usize;
    assert(rows * cc <= 65535 * 65535) by (nonlinear_arith)
        requires
            rows <= 65535,
            cc <= 65535,
    ;
    let n = rows * cc;
    let an = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_anchor(t@, x as int),
        { check_anchor(t, x) };
    check_offs(t, o + 2, n, 2, o, 2 + 2 * n, true, &an, Ghost(|x: int| wf_anchor(t@, x)))
}

fn check_ligarray(t: &[u8], o: usize, cc: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
        cc <= 65535,
    ensures
        b == wf_ligarray(t@, o as int, cc as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let aa = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_anchorarray(t@, x as int, cc as int),
        { check_anchorarray(t, x, cc) };
    check_offs(t, o + 2, n, 2, o, 2, false, &aa, Ghost(|x: int| wf_anchorarray(t@, x, cc as int)))
}

fn check_mark_pos(t: &[u8], o: usize, lig: bool, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_mark_pos(t@, o as int, lig, ng as int),
{
    if !room(t, o, 12) || rd16(t, o) != 1 {
        return false;
    }
    let cc = rd16(t, o + 6) as usize;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    let ma = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_markarray(t@, x as int),
        { check_markarray(t, x) };
    if !check_off(t, o + 2, o, 12, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int))) || !check_off(
        t,
        o + 4,
        o,
        12,
        false,
        &cov,
        Ghost(|x: int| wf_cov(t@, x, ng as int)),
    ) || !check_off(t, o + 8, o, 12, false, &ma, Ghost(|x: int| wf_markarray(t@, x))) {
        return false;
    }
    if lig {
        let la = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_ligarray(t@, x as int, cc as int),
            { check_ligarray(t, x, cc) };
        check_off(t, o + 10, o, 12, false, &la, Ghost(|x: int| wf_ligarray(t@, x, cc as int)))
    } else {
        let aa = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_anchorarray(t@, x as int, cc as int),
            { check_anchorarray(t, x, cc) };
        check_off(t, o + 10, o, 12, false, &aa, Ghost(|x: int| wf_anchorarray(t@, x, cc as int)))
    }
}

fn check_gpos_sub(t: &[u8], o: usize, ty: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_gpos_sub(t@, o as int, ty as int, ng as int, nl as int),
{
    if ty == 1 {
        check_single_pos(t, o, ng)
    } else if ty == 2 {
        check_pair_pos(t, o, ng)
    } else if ty == 3 {
        check_cursive(t, o, ng)
    } else if ty == 4 || ty == 6 {
        check_mark_pos(t, o, false, ng)
    } else if ty == 5 {
        check_mark_pos(t, o, true, ng)
    } else if ty == 7 {
        check_context(t, o, ng, nl)
    } else {
        ty == 8 && check_chain(t, o, ng, nl)
    }
}

// ---------------------------------------------------------------------
// Lookups and the table header
// ---------------------------------------------------------------------
fn check_plain(t: &[u8], o: usize, pos: bool, ty: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_plain(t@, o as int, pos, ty as int, ng as int, nl as int),
{
    if pos {
        check_gpos_sub(t, o, ty, ng, nl)
    } else {
        check_gsub_sub(t, o, ty, ng, nl)
    }
}

fn check_subtable(t: &[u8], o: usize, pos: bool, ty: usize, ng: usize, nl: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_subtable(t@, o as int, pos, ty as int, ng as int, nl as int),
{
    let ext: usize = if pos {
        9
    } else {
        7
    };
    if ty != ext {
        return check_plain(t, o, pos, ty, ng, nl);
    }
    if !room(t, o, 8) {
        return false;
    }
    let ety = rd16(t, o + 2) as usize;
    let eo = rd32(t, o + 4) as usize;
    rd16(t, o) == 1 && ety != ext && eo >= 8 && eo < t.len() - o && check_plain(t, o + eo, pos, ety, ng, nl)
}

fn check_lookup(t: &[u8], o: usize, pos: bool, ng: usize, nl: usize, ms: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_lookup(t@, o as int, pos, ng as int, nl as int, ms as int),
{
    if !room(t, o, 6) {
        return false;
    }
    let ty = rd16(t, o) as usize;
    let n = rd16(t, o + 4) as usize;
    let filt = hasx(rd16(t, o + 2), 16);
    let end = 6 + 2 * n + if filt {
        2usize
    } else {
        0
    };
    let ext: usize = if pos {
        9
    } else {
        7
    };
    if ty < 1 || ty > ext {
        return false;
    }
    let st = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_subtable(t@, x as int, pos, ty as int, ng as int, nl as int),
        { check_subtable(t, x, pos, ty, ng, nl) };
    if !check_offs(
        t,
        o + 6,
        n,
        2,
        o,
        end,
        false,
        &st,
        Ghost(|x: int| wf_subtable(t@, x, pos, ty as int, ng as int, nl as int)),
    ) {
        return false;
    }
    !filt || (room(t, o, 8 + 2 * n) && (rd16(t, o + 6 + 2 * n) as usize) < ms)
}

fn check_lookuplist(t: &[u8], o: usize, pos: bool, ng: usize, ms: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_lookuplist(t@, o as int, pos, ng as int, ms as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let lk = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_lookup(t@, x as int, pos, ng as int, n as int, ms as int),
        { check_lookup(t, x, pos, ng, n, ms) };
    check_offs(
        t,
        o + 2,
        n,
        2,
        o,
        2 + 2 * n,
        false,
        &lk,
        Ghost(|x: int| wf_lookup(t@, x, pos, ng as int, n as int, ms as int)),
    )
}

/// Decides [`wf_layout`]: a whole `GSUB` or `GPOS` table.
pub fn check_layout(t: &[u8], pos: bool, ng: usize, ms: usize) -> (b: bool)
    requires
        small(t),
    ensures
        b == wf_layout(t@, pos, ng as int, ms as int),
{
    if t.len() < 10 {
        return false;
    }
    let minor = rd16(t, 2);
    if rd16(t, 0) != 1 || minor > 1 {
        return false;
    }
    let hdr: usize = if minor == 0 {
        10
    } else {
        14
    };
    if t.len() < hdr || (minor == 1 && rd32(t, 10) != 0) {
        return false;
    }
    let sl = rd16(t, 4) as usize;
    let fl = rd16(t, 6) as usize;
    let ll = rd16(t, 8) as usize;
    let mut nl: usize = 0;
    if ll != 0 {
        if ll < hdr || ll >= t.len() || !check_lookuplist(t, ll, pos, ng, ms) {
            return false;
        }
        nl = rd16(t, ll) as usize;
    }
    let mut nf: usize = 0;
    if fl != 0 {
        if fl < hdr || fl >= t.len() || !check_featurelist(t, fl, nl) {
            return false;
        }
        nf = rd16(t, fl) as usize;
    }
    if sl != 0 {
        if sl < hdr || sl >= t.len() || !check_scriptlist(t, sl, nf) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------
// GDEF
// ---------------------------------------------------------------------
fn check_attachpoint(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_attachpoint(t@, o as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    if n < 1 || !room(t, o + 2, 2 * n) {
        return false;
    }
    let mut j: usize = 1;
    while j < n
        invariant
            1 <= j,
            n == u16_at(t@, o as int),
            o + 2 + 2 * n <= t.len(),
            forall|k: int| 0 < k < j ==> #[trigger] point_order_ok(t@, o as int, k),
        decreases n - j,
    {
        let prev = rd16(t, o + 2 + 2 * (j - 1));
        if prev != 0 && prev >= rd16(t, o + 2 + 2 * j) {
            assert(!point_order_ok(t@, o as int, j as int));
            return false;
        }
        assert(point_order_ok(t@, o as int, j as int));
        j += 1;
    }
    true
}

fn check_caret(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_caret(t@, o as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let f = rd16(t, o);
    if f < 1 || f > 3 {
        return false;
    }
    if f != 3 {
        return true;
    }
    let dv = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_device(t@, x as int),
        { check_device(t, x) };
    check_off(t, o + 4, o, 1, false, &dv, Ghost(|x: int| wf_device(t@, x)))
}

fn check_ligglyph(t: &[u8], o: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_ligglyph(t@, o as int),
{
    if !room(t, o, 2) {
        return false;
    }
    let n = rd16(t, o) as usize;
    let cv = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_caret(t@, x as int),
        { check_caret(t, x) };
    n >= 1 && check_offs(t, o + 2, n, 2, o, 2 + 2 * n, false, &cv, Ghost(|x: int| wf_caret(t@, x)))
}

fn check_glyphlist(t: &[u8], o: usize, lig: bool, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_glyphlist(t@, o as int, lig, ng as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let n = rd16(t, o + 2) as usize;
    let cov = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_cov(t@, x as int, ng as int),
        { check_cov(t, x, ng) };
    if n > ng || !check_off(t, o, o, 4 + 2 * n, false, &cov, Ghost(|x: int| wf_cov(t@, x, ng as int))) {
        return false;
    }
    if lig {
        let lg = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_ligglyph(t@, x as int),
            { check_ligglyph(t, x) };
        check_offs(t, o + 4, n, 2, o, 4 + 2 * n, false, &lg, Ghost(|x: int| wf_ligglyph(t@, x)))
    } else {
        let ap = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_attachpoint(t@, x as int),
            { check_attachpoint(t, x) };
        check_offs(t, o + 4, n, 2, o, 4 + 2 * n, false, &ap, Ghost(|x: int| wf_attachpoint(t@, x)))
    }
}

fn check_marksets(t: &[u8], o: usize, ng: usize) -> (b: bool)
    requires
        small(t),
        o <= t.len(),
    ensures
        b == wf_marksets(t@, o as int, ng as int),
{
    if !room(t, o, 4) {
        return false;
    }
    let n = rd16(t, o + 2) as usize;
    if rd16(t, o) != 1 || 4 + 2 * n > 65535 || !room(t, o + 4, 4 * n) {
        return false;
    }
    let min = 4 + 4 * n;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == u16_at(t@, o + 2),
            u16_at(t@, o as int) == 1,
            4 + 2 * n <= 65535,
            min == 4 + 4 * n,
            small(t),
            o + 4 + 4 * n <= t.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] markset_ok(t@, o as int, k, min as int, ng as int),
        decreases n - i,
    {
        let off = rd32(t, o + 4 + 4 * i) as usize;
        if off < min || off >= t.len() - o || !check_cov(t, o + off, ng) {
            assert(!markset_ok(t@, o as int, i as int, min as int, ng as int));
            return false;
        }
        assert(markset_ok(t@, o as int, i as int, min as int, ng as int));
        i += 1;
    }
    true
}

/// Decides [`wf_gdef`].
pub fn check_gdef(t: &[u8], ng: usize) -> (b: bool)
    requires
        small(t),
    ensures
        b == wf_gdef(t@, ng as int),
{
    if t.len() < 12 {
        return false;
    }
    let minor = rd16(t, 2);
    if rd16(t, 0) != 1 || !(minor == 0 || minor == 2 || minor == 3) {
        return false;
    }
    let hdr: usize = if minor == 0 {
        12
    } else if minor == 2 {
        14
    } else {
        18
    };
    if t.len() < hdr {
        return false;
    }
    let gc = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_classdef(t@, x as int, ng as int, 4),
        { check_classdef(t, x, ng, 4) };
    let al = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_glyphlist(t@, x as int, false, ng as int),
        { check_glyphlist(t, x, false, ng) };
    let lc = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_glyphlist(t@, x as int, true, ng as int),
        { check_glyphlist(t, x, true, ng) };
    let mc = |x: usize| -> (r: bool)
        requires
            x <= t.len(),
        ensures
            r == wf_classdef(t@, x as int, ng as int, 0xFFFF),
        { check_classdef(t, x, ng, 0xFFFF) };
    if !check_off(t, 4, 0, hdr, true, &gc, Ghost(|x: int| wf_classdef(t@, x, ng as int, 4))) || !check_off(
        t,
        6,
        0,
        hdr,
        true,
        &al,
        Ghost(|x: int| wf_glyphlist(t@, x, false, ng as int)),
    ) || !check_off(t, 8, 0, hdr, true, &lc, Ghost(|x: int| wf_glyphlist(t@, x, true, ng as int)))
        || !check_off(t, 10, 0, hdr, true, &mc, Ghost(|x: int| wf_classdef(t@, x, ng as int, 0xFFFF))) {
        return false;
    }
    if minor >= 2 {
        let ms = |x: usize| -> (r: bool)
            requires
                x <= t.len(),
            ensures
                r == wf_marksets(t@, x as int, ng as int),
            { check_marksets(t, x, ng) };
        if !check_off(t, 12, 0, hdr, true, &ms, Ghost(|x: int| wf_marksets(t@, x, ng as int))) {
            return false;
        }
    }
    minor != 3 || rd32(t, 14) == 0
}

/// The number of mark glyph sets of a well-formed `GDEF`.
pub fn mark_sets(t: &[u8], Ghost(ng): Ghost<int>) -> (r: usize)
    requires
        wf_gdef(t@, ng),
    ensures
        r == gdef_mark_sets(t@),
{
    if rd16(t, 2) >= 2 {
        let off = rd16(t, 12) as usize;
        if off != 0 {
            return rd16(t, off + 2) as usize;
        }
    }
    0
}

} // verus!
