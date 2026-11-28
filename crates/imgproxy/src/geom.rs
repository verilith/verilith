//! The geometry options, proven: `geom_x` computes `spec_geom::geom` and
//! keeps every rectangle inside the one it is cut from, and `embed_rgba`
//! and `turn_rgba` compute `spec_geom::embed` and `spec_geom::turn`.
#[cfg(verus_only)]
use crate::fit::plan;
use crate::fit::{plan_x, Mode};
use crate::lanczos::floor_div;
#[cfg(verus_only)]
use crate::resize::{lemma_idx, lemma_split};
use crate::spec::*;
use crate::spec_geom::*;
use vstd::prelude::*;

verus! {

/// The plan, in machine integers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Plan2x {
    pub x0: u32,
    pub y0: u32,
    pub cw0: u32,
    pub ch0: u32,
    pub rw: u32,
    pub rh: u32,
    pub cx: u32,
    pub cy: u32,
    pub cw: u32,
    pub ch: u32,
    pub canvas_w: u32,
    pub canvas_h: u32,
    pub ax: u32,
    pub ay: u32,
}

/// What the geometry needs of its options: offsets and sizes within
/// 65535, `dpr` from 0.0001 to 8.
pub open spec fn geo_ok(g: Geo) -> bool {
    &&& g.w <= MAX_DIM
    &&& g.h <= MAX_DIM
    &&& 1 <= g.dpr <= 80000
    &&& g.crop_w <= 655359999
    &&& g.crop_h <= 655359999
    &&& -65535 <= g.gravity.x <= 65535
    &&& -65535 <= g.gravity.y <= 65535
    &&& (g.crop_g matches Some(c) ==> -65535 <= c.x <= 65535 && -65535 <= c.y <= 65535)
    &&& (g.extend_g matches Some(e) ==> -65535 <= e.x <= 65535 && -65535 <= e.y <= 65535)
    &&& forall|i: int| 0 <= i < 4 ==> #[trigger] g.pad[i] <= MAX_DIM
}

/// `fmul`.
fn fmul_x(v: i64, f: i64) -> (r: i64)
    requires
        -0x40_0000 <= v <= 0x40_0000,
        -80000 <= f <= 80000,
    ensures
        r == fmul(v as int, f as int),
        v >= 0 && f >= 0 ==> 0 <= r,
        v >= 0 && 0 <= f <= 10000 ==> r <= v,
{
    proof {
        assert(-0x80_0000 * 80000 <= 2 * v * f <= 0x80_0000 * 80000) by (nonlinear_arith)
            requires
                -0x40_0000 <= v <= 0x40_0000,
                -80000 <= f <= 80000,
        ;
        if v >= 0 && f >= 0 {
            assert(2 * v * f >= 0) by (nonlinear_arith)
                requires
                    v >= 0,
                    f >= 0,
            ;
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(2 * v * f + 10000, 20000);
        }
        if v >= 0 && 0 <= f <= 10000 {
            assert(2 * v * f + 10000 < 20000 * (v + 1)) by (nonlinear_arith)
                requires
                    v >= 0,
                    0 <= f <= 10000,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(2 * v * f + 10000, 20000);
            vstd::arithmetic::div_mod::lemma_mod_bound(2 * v * f + 10000, 20000);
            let q = (2 * v * f + 10000) / 20000;
            assert(q <= v) by (nonlinear_arith)
                requires
                    20000 * q + (2 * v * f + 10000) % 20000 == 2 * v * f + 10000,
                    (2 * v * f + 10000) % 20000 >= 0,
                    2 * v * f + 10000 < 20000 * (v + 1),
            ;
        }
    }
    floor_div(2 * v * f + 10000, 20000)
}

fn clamp_x(v: i64, lo: i64, hi: i64) -> (r: i64)
    requires
        lo <= hi,
    ensures
        r == clamp(v as int, lo as int, hi as int),
        lo <= r <= hi,
{
    if v < lo {
        lo
    } else if v > hi {
        hi
    } else {
        v
    }
}

/// `hside` and `vside` as numbers: 0 start, 1 centre, 2 end, 3 focus.
pub open spec fn side_of(s: Side) -> int {
    match s {
        Side::Start => 0,
        Side::Centre => 1,
        Side::End => 2,
        Side::Focus => 3,
    }
}

fn hside_x(k: GKind) -> (r: u8)
    ensures
        r == side_of(hside(k)),
{
    match k {
        GKind::We | GKind::NoWe | GKind::SoWe => 0,
        GKind::Ea | GKind::NoEa | GKind::SoEa => 2,
        GKind::Fp => 3,
        _ => 1,
    }
}

fn vside_x(k: GKind) -> (r: u8)
    ensures
        r == side_of(vside(k)),
{
    match k {
        GKind::No | GKind::NoEa | GKind::NoWe => 0,
        GKind::So | GKind::SoEa | GKind::SoWe => 2,
        GKind::Fp => 3,
        _ => 1,
    }
}

pub open spec fn place_n(outer: int, inner: int, s: int, off: int, dpr: int) -> int {
    let o = fmul(off, dpr);
    let p = if s == 0 {
        o
    } else if s == 1 {
        (outer - inner + 1) / 2 + o
    } else if s == 2 {
        outer - inner - o
    } else {
        fmul(outer, off) - inner / 2
    };
    clamp(p, 0, outer - inner)
}

pub proof fn lemma_place(outer: int, inner: int, side: Side, off: int, dpr: int)
    ensures
        place(outer, inner, side, off, dpr) == place_n(outer, inner, side_of(side), off, dpr),
{
}

/// `place`, through `place_n`.
fn place_x(outer: i64, inner: i64, s: u8, off: i64, dpr: i64) -> (r: i64)
    requires
        1 <= inner <= outer <= MAX_DIM,
        -65535 <= off <= 65535,
        0 <= dpr <= 80000,
        s <= 3,
    ensures
        r == place_n(outer as int, inner as int, s as int, off as int, dpr as int),
        0 <= r <= outer - inner,
{
    let o = fmul_x(off, dpr);
    proof {
        assert(-(65535 * 80000 * 2) <= 2 * off * dpr <= 65535 * 80000 * 2) by (nonlinear_arith)
            requires
                -65535 <= off <= 65535,
                0 <= dpr <= 80000,
        ;
        assert(-(65535 * 80000 * 2) <= o <= 65535 * 80000 + 1) by {
            let n = 2 * off * dpr + 10000;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 20000);
            vstd::arithmetic::div_mod::lemma_mod_bound(n as int, 20000);
        }
    }
    let p = if s == 0 {
        o
    } else if s == 1 {
        (outer - inner + 1) / 2 + o
    } else if s == 2 {
        outer - inner - o
    } else {
        proof {
            assert(-(2 * 65535 * 65535) <= 2 * outer * off <= 2 * 65535 * 65535) by (nonlinear_arith)
                requires
                    0 <= outer <= 65535,
                    -65535 <= off <= 65535,
            ;
            let n = 2 * outer * off + 10000;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 20000);
            vstd::arithmetic::div_mod::lemma_mod_bound(n as int, 20000);
        }
        fmul_x(outer, off) - inner / 2
    };
    clamp_x(p, 0, outer - inner)
}

/// `cdim`.
fn cdim_x(v: u32, s: u32) -> (r: u32)
    requires
        1 <= s <= MAX_DIM,
        v <= 655359999,
    ensures
        r == cdim(v as int, s as int),
        1 <= r <= s,
{
    if v == 0 {
        s
    } else if v < 10000 {
        clamp_x(fmul_x(s as i64, v as i64), 1, s as i64) as u32
    } else {
        clamp_x((v / 10000) as i64, 1, s as i64) as u32
    }
}

/// `sdim`.
fn sdim_x(v: u32, dpr: u32) -> (r: u32)
    requires
        v <= MAX_DIM,
        1 <= dpr <= 80000,
    ensures
        r == sdim(v as int, dpr as int),
        r <= MAX_DIM,
{
    if v == 0 {
        0
    } else {
        clamp_x(fmul_x(v as i64, dpr as i64), 1, 65535) as u32
    }
}

/// `geom`, when the canvas is at most `MAX_DIM` on a side and every image
/// it goes through has at most `max_px` pixels; `None` otherwise.
#[verifier::rlimit(60)]
pub fn geom_x(sw: u32, sh: u32, g: Geo, max_px: u64) -> (r: Option<Plan2x>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        geo_ok(g),
    ensures
        r matches Some(p) ==> {
            let q = geom(sw as int, sh as int, g);
            &&& q.x0 == p.x0 && q.y0 == p.y0 && q.cw0 == p.cw0 && q.ch0 == p.ch0
            &&& q.rw == p.rw && q.rh == p.rh
            &&& q.cx == p.cx && q.cy == p.cy && q.cw == p.cw && q.ch == p.ch
            &&& q.canvas_w == p.canvas_w && q.canvas_h == p.canvas_h
            &&& q.ax == p.ax && q.ay == p.ay
            &&& 1 <= p.cw0 && p.x0 + p.cw0 <= sw
            &&& 1 <= p.ch0 && p.y0 + p.ch0 <= sh
            &&& 1 <= p.rw <= MAX_DIM && 1 <= p.rh <= MAX_DIM
            &&& p.rw * p.rh <= max_px
            &&& 1 <= p.cw && p.cx + p.cw <= p.rw
            &&& 1 <= p.ch && p.cy + p.ch <= p.rh
            &&& p.canvas_w <= MAX_DIM && p.canvas_h <= MAX_DIM
            &&& p.ax + p.cw <= p.canvas_w && p.ay + p.ch <= p.canvas_h
            &&& p.canvas_w * p.canvas_h <= max_px
        },
{
    let dpr = g.dpr as i64;
    let g0 = match g.crop_g {
        Some(c) => c,
        None => g.gravity,
    };
    let cw0 = cdim_x(g.crop_w, sw);
    let ch0 = cdim_x(g.crop_h, sh);
    proof {
        lemma_place(sw as int, cw0 as int, hside(g0.kind), g0.x as int, F1);
        lemma_place(sh as int, ch0 as int, vside(g0.kind), g0.y as int, F1);
    }
    let x0 = place_x(sw as i64, cw0 as i64, hside_x(g0.kind), g0.x as i64, 10000);
    let y0 = place_x(sh as i64, ch0 as i64, vside_x(g0.kind), g0.y as i64, 10000);
    let w = sdim_x(g.w, g.dpr);
    let h = sdim_x(g.h, g.dpr);
    let p = match plan_x(cw0, ch0, w, h, g.mode, g.enlarge, max_px) {
        Some(p) => p,
        None => return None,
    };
    let (rw, rh, cw, ch) = (p.rw as i64, p.rh as i64, p.cw as i64, p.ch as i64);
    proof {
        lemma_place(rw as int, cw as int, hside(g.gravity.kind), g.gravity.x as int, dpr as int);
        lemma_place(rh as int, ch as int, vside(g.gravity.kind), g.gravity.y as int, dpr as int);
    }
    let cx = place_x(rw, cw, hside_x(g.gravity.kind), g.gravity.x as i64, dpr);
    let cy = place_x(rh, ch, vside_x(g.gravity.kind), g.gravity.y as i64, dpr);
    let ew = if g.extend && w as i64 > cw { w as i64 } else { cw };
    let eh = if g.extend && h as i64 > ch { h as i64 } else { ch };
    let ge = match g.extend_g {
        Some(e) => e,
        None => Gravity { kind: GKind::Ce, x: 0, y: 0 },
    };
    proof {
        lemma_place(ew as int, cw as int, hside(ge.kind), ge.x as int, dpr as int);
        lemma_place(eh as int, ch as int, vside(ge.kind), ge.y as int, dpr as int);
    }
    let ex = place_x(ew, cw, hside_x(ge.kind), ge.x as i64, dpr);
    let ey = place_x(eh, ch, vside_x(ge.kind), ge.y as i64, dpr);
    proof {
        assert(g.pad[0] <= MAX_DIM && g.pad[1] <= MAX_DIM && g.pad[2] <= MAX_DIM && g.pad[3] <= MAX_DIM);
    }
    let pt = fmul_x(g.pad[0] as i64, dpr);
    let pr = fmul_x(g.pad[1] as i64, dpr);
    let pb = fmul_x(g.pad[2] as i64, dpr);
    let pl = fmul_x(g.pad[3] as i64, dpr);
    proof {
        // Each pad is at most 65535 * 8 + 1.
        assert forall|v: int| 0 <= v <= 65535 implies fmul(v, dpr as int) <= 524281 by {
            assert(2 * v * dpr + 10000 <= 2 * 65535 * 80000 + 10000) by (nonlinear_arith)
                requires
                    0 <= v <= 65535,
                    0 <= dpr <= 80000,
            ;
            vstd::arithmetic::div_mod::lemma_div_is_ordered(2 * v * dpr + 10000, (2 * 65535 * 80000 + 10000) as int, 20000);
        }
    }
    let cwd = ew + pl + pr;
    let chd = eh + pt + pb;
    if cwd > 65535 || chd > 65535 {
        return None;
    }
    proof {
        assert(cwd * chd <= 65535 * 65535) by (nonlinear_arith)
            requires
                0 <= cwd <= 65535,
                0 <= chd <= 65535,
        ;
    }
    if (cwd * chd) as u64 > max_px {
        return None;
    }
    Some(
        Plan2x {
            x0: x0 as u32,
            y0: y0 as u32,
            cw0,
            ch0,
            rw: p.rw,
            rh: p.rh,
            cx: cx as u32,
            cy: cy as u32,
            cw: p.cw,
            ch: p.ch,
            canvas_w: cwd as u32,
            canvas_h: chd as u32,
            ax: (ex + pl) as u32,
            ay: (ey + pt) as u32,
        },
    )
}

// ---------------------------------------------------------------------------
// Pixels
// ---------------------------------------------------------------------------

/// `embed`: `src` (`w` by `h`) at `(x, y)` on a `cw` by `ch` canvas of
/// `fill`.
#[verifier::rlimit(40)]
pub fn embed_rgba(src: &[u8], w: usize, h: usize, cw: usize, ch: usize, x: usize, y: usize, fill: [u8; 4]) -> (r: Vec<
    u8,
>)
    requires
        1 <= w,
        1 <= h,
        cw <= MAX_DIM,
        ch <= MAX_DIM,
        x + w <= cw,
        y + h <= ch,
        src@.len() == w * h * NC,
    ensures
        r@ == embed(src@, w as int, h as int, cw as int, ch as int, x as int, y as int, fill),
{
    let ghost want = embed(src@, w as int, h as int, cw as int, ch as int, x as int, y as int, fill);
    proof {
        assert(cw * ch * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                cw <= 65535,
                ch <= 65535,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(cw * ch * 4);
    let mut py: usize = 0;
    while py < ch
        invariant
            1 <= w,
            1 <= h,
            cw <= MAX_DIM,
            ch <= MAX_DIM,
            x + w <= cw,
            y + h <= ch,
            src@.len() == w * h * NC,
            want == embed(src@, w as int, h as int, cw as int, ch as int, x as int, y as int, fill),
            py <= ch,
            out@.len() == py * cw * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
        decreases ch - py,
    {
        let mut px: usize = 0;
        while px < cw
            invariant
                1 <= w,
                1 <= h,
                cw <= MAX_DIM,
                ch <= MAX_DIM,
                x + w <= cw,
                y + h <= ch,
                src@.len() == w * h * NC,
                want == embed(src@, w as int, h as int, cw as int, ch as int, x as int, y as int, fill),
                py < ch,
                px <= cw,
                out@.len() == (py * cw + px) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
            decreases cw - px,
        {
            let ghost before = out@;
            let ghost b = (py * cw + px) * NC;
            proof {
                lemma_idx(py as int, px as int, 0, cw as int, ch as int);
                lemma_idx(py as int, px as int, 3, cw as int, ch as int);
            }
            if x <= px && px < x + w && y <= py && py < y + h {
                proof {
                    assert(w * h <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            w <= 65535,
                            h <= 65535,
                    ;
                    lemma_idx((py - y) as int, (px - x) as int, 3, w as int, h as int);
                }
                let i = ((py - y) * w + (px - x)) * 4;
                out.push(src[i]);
                out.push(src[i + 1]);
                out.push(src[i + 2]);
                out.push(src[i + 3]);
            } else {
                out.push(fill[0]);
                out.push(fill[1]);
                out.push(fill[2]);
                out.push(fill[3]);
            }
            proof {
                assert((py * cw + px + 1) * NC == b + 4) by (nonlinear_arith)
                    requires
                        b == (py * cw + px) * NC,
                ;
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == want[j] by {
                    if j >= before.len() {
                        lemma_idx(py as int, px as int, j - b, cw as int, ch as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            px += 1;
        }
        proof {
            assert((py * cw + cw) * NC == (py + 1) * cw * NC) by (nonlinear_arith);
        }
        py += 1;
    }
    proof {
        assert(out@.len() == cw * ch * NC) by (nonlinear_arith)
            requires
                out@.len() == ch * cw * NC,
        ;
        assert(out@ =~= want);
    }
    out
}

/// `turn_src`, in machine integers.
fn turn_src_x(w: usize, h: usize, q: u32, fh: bool, fv: bool, px: usize, py: usize) -> (r: (usize, usize))
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        q < 4,
        px < (if q % 2 == 1 { h } else { w }),
        py < (if q % 2 == 1 { w } else { h }),
    ensures
        r.0 < w,
        r.1 < h,
        (r.0 as int, r.1 as int) == turn_src(w as int, h as int, q as int, fh, fv, px as int, py as int),
{
    let ow = if q % 2 == 1 { h } else { w };
    let oh = if q % 2 == 1 { w } else { h };
    let x = if fh { ow - 1 - px } else { px };
    let y = if fv { oh - 1 - py } else { py };
    if q == 1 {
        (y, h - 1 - x)
    } else if q == 2 {
        (w - 1 - x, h - 1 - y)
    } else if q == 3 {
        (w - 1 - y, x)
    } else {
        (x, y)
    }
}

/// `turn`: `src` (`w` by `h`) turned clockwise by `q` quarter turns, then
/// flipped.
#[verifier::rlimit(40)]
pub fn turn_rgba(src: &[u8], w: usize, h: usize, q: u32, fh: bool, fv: bool) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        q < 4,
        src@.len() == w * h * NC,
    ensures
        r@ == turn(src@, w as int, h as int, q as int, fh, fv),
{
    let ghost want = turn(src@, w as int, h as int, q as int, fh, fv);
    let ow = if q % 2 == 1 { h } else { w };
    let oh = if q % 2 == 1 { w } else { h };
    proof {
        assert(ow * oh == w * h) by (nonlinear_arith)
            requires
                (ow == w && oh == h) || (ow == h && oh == w),
        ;
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                w <= 65535,
                h <= 65535,
        ;
        assert(ow * oh * NC == w * h * NC) by (nonlinear_arith)
            requires
                ow * oh == w * h,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(w * h * 4);
    let mut py: usize = 0;
    while py < oh
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            q < 4,
            ow == (if q % 2 == 1 { h } else { w }),
            oh == (if q % 2 == 1 { w } else { h }),
            ow * oh * NC == w * h * NC,
            src@.len() == w * h * NC,
            want == turn(src@, w as int, h as int, q as int, fh, fv),
            py <= oh,
            out@.len() == py * ow * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
        decreases oh - py,
    {
        let mut px: usize = 0;
        while px < ow
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                q < 4,
                ow == (if q % 2 == 1 { h } else { w }),
                oh == (if q % 2 == 1 { w } else { h }),
                ow * oh * NC == w * h * NC,
                src@.len() == w * h * NC,
                want == turn(src@, w as int, h as int, q as int, fh, fv),
                py < oh,
                px <= ow,
                out@.len() == (py * ow + px) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
            decreases ow - px,
        {
            let ghost before = out@;
            let ghost b = (py * ow + px) * NC;
            let (sx, sy) = turn_src_x(w, h, q, fh, fv, px, py);
            proof {
                assert(w * h <= 65535 * 65535) by (nonlinear_arith)
                    requires
                        w <= 65535,
                        h <= 65535,
                ;
                lemma_idx(sy as int, sx as int, 3, w as int, h as int);
                lemma_idx(py as int, px as int, 3, ow as int, oh as int);
            }
            let i = (sy * w + sx) * 4;
            out.push(src[i]);
            out.push(src[i + 1]);
            out.push(src[i + 2]);
            out.push(src[i + 3]);
            proof {
                assert((py * ow + px + 1) * NC == b + 4) by (nonlinear_arith)
                    requires
                        b == (py * ow + px) * NC,
                ;
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == want[j] by {
                    if j >= before.len() {
                        lemma_idx(py as int, px as int, j - b, ow as int, oh as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            px += 1;
        }
        proof {
            assert((py * ow + ow) * NC == (py + 1) * ow * NC) by (nonlinear_arith);
        }
        py += 1;
    }
    proof {
        assert(out@.len() == w * h * NC) by (nonlinear_arith)
            requires
                out@.len() == oh * ow * NC,
                ow * oh * NC == w * h * NC,
        ;
        assert(out@ =~= want);
    }
    out
}

} // verus!
