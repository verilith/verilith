//! The specification of the geometry options (imgproxy's `gravity`,
//! `crop`, `extend`, `padding`, `dpr`, `rotate` and `flip`): where each
//! rectangle goes, and what rotating, flipping and placing an image on a
//! canvas return. Part of the trusted base with `spec.rs`.
//!
//! The steps, in order, on the decoded image: rotate (clockwise, by
//! quarter turns) and then flip; crop to `crop`'s rectangle; resize (the
//! requested size times `dpr`) as `fit::plan` says; crop to the requested
//! size at `gravity` (`fill`); place on a canvas of the requested size at
//! `extend`'s gravity (`extend`); add `padding` (times `dpr`). Fractional
//! values (`dpr`, focus points, fractional crops) are fixed point with 4
//! decimals (`F1` is 1.0).
#[cfg(verus_only)]
use crate::fit::plan;
use crate::fit::Mode;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Fixed-point 1.0 (4 decimals).
pub spec const F1: int = 10000;

/// imgproxy's gravity types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GKind {
    Ce,
    No,
    So,
    Ea,
    We,
    NoEa,
    NoWe,
    SoEa,
    SoWe,
    /// A focus point: `x` and `y` are fractions of the width and height.
    Fp,
    /// Smart (`spec_smart`): the pipeline finds the point and plans with
    /// it as a focus point; planned as it is, it is the centre.
    Sm,
}

/// A gravity: compass offsets in pixels (times `dpr` where the result's
/// pixels are meant), or, for `Fp`, the point in `F1` units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gravity {
    pub kind: GKind,
    pub x: i32,
    pub y: i32,
}

pub open spec fn centre() -> Gravity {
    Gravity { kind: GKind::Ce, x: 0, y: 0 }
}

/// Where along one axis a gravity puts things.
pub enum Side {
    Start,
    Centre,
    End,
    Focus,
}

pub open spec fn hside(k: GKind) -> Side {
    match k {
        GKind::We | GKind::NoWe | GKind::SoWe => Side::Start,
        GKind::Ea | GKind::NoEa | GKind::SoEa => Side::End,
        GKind::Fp => Side::Focus,
        _ => Side::Centre,
    }
}

pub open spec fn vside(k: GKind) -> Side {
    match k {
        GKind::No | GKind::NoEa | GKind::NoWe => Side::Start,
        GKind::So | GKind::SoEa | GKind::SoWe => Side::End,
        GKind::Fp => Side::Focus,
        _ => Side::Centre,
    }
}

/// `v * f`, rounded to nearest (halves up), for `f` in `F1` units.
pub open spec fn fmul(v: int, f: int) -> int {
    (2 * v * f + F1) / (2 * F1)
}

pub open spec fn clamp(v: int, lo: int, hi: int) -> int {
    if v < lo {
        lo
    } else if v > hi {
        hi
    } else {
        v
    }
}

/// Where a run `inner` long starts in one `outer` long (`inner <= outer`),
/// as imgproxy's `calcPosition` without overflow: the offset `off` is
/// scaled by `dpr` and moves away from the side the gravity names (from
/// the centre: right or down); a focus point centres on `off / F1` of
/// `outer`; the result stays inside.
pub open spec fn place(outer: int, inner: int, side: Side, off: int, dpr: int) -> int {
    let o = fmul(off, dpr);
    let p = match side {
        Side::Start => o,
        Side::Centre => (outer - inner + 1) / 2 + o,
        Side::End => outer - inner - o,
        Side::Focus => fmul(outer, off) - inner / 2,
    };
    clamp(p, 0, outer - inner)
}

/// A crop length: 0 is all of `s`, below `F1` a fraction of it (at least
/// one pixel), else whole pixels (at most `s`).
pub open spec fn cdim(v: int, s: int) -> int {
    if v == 0 {
        s
    } else if v < F1 {
        clamp(fmul(s, v), 1, s)
    } else {
        clamp(v / F1, 1, s)
    }
}

/// A requested length times `dpr`: 0 stays 0 ("not given").
pub open spec fn sdim(v: int, dpr: int) -> int {
    if v == 0 {
        0
    } else {
        clamp(fmul(v, dpr), 1, MAX_DIM)
    }
}

/// What the geometry options ask for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Geo {
    pub mode: Mode,
    pub w: u32,
    pub h: u32,
    pub enlarge: bool,
    pub gravity: Gravity,
    /// `crop`: width and height (`F1` units; 0 is the whole length), and
    /// its own gravity (`None`: `gravity`'s).
    pub crop_w: u32,
    pub crop_h: u32,
    pub crop_g: Option<Gravity>,
    /// `extend`, and its gravity (`None`: the centre).
    pub extend: bool,
    pub extend_g: Option<Gravity>,
    /// `padding`: top, right, bottom, left, in pixels before `dpr`.
    pub pad: [u32; 4],
    /// `F1` units, at least 1.
    pub dpr: u32,
}

/// The rectangles, in order: crop `(x0, y0, cw0, ch0)` of the source;
/// resize that to `rw` by `rh`; crop `(cx, cy, cw, ch)` of the result;
/// place that at `(ax, ay)` on a `canvas_w` by `canvas_h` canvas.
pub struct Plan2 {
    pub x0: int,
    pub y0: int,
    pub cw0: int,
    pub ch0: int,
    pub rw: int,
    pub rh: int,
    pub cx: int,
    pub cy: int,
    pub cw: int,
    pub ch: int,
    pub canvas_w: int,
    pub canvas_h: int,
    pub ax: int,
    pub ay: int,
}

/// The plan for a `sw` by `sh` (rotated, flipped) source.
pub open spec fn geom(sw: int, sh: int, g: Geo) -> Plan2 {
    let dpr = g.dpr as int;
    let g0 = match g.crop_g {
        Some(c) => c,
        None => g.gravity,
    };
    let cw0 = cdim(g.crop_w as int, sw);
    let ch0 = cdim(g.crop_h as int, sh);
    let x0 = place(sw, cw0, hside(g0.kind), g0.x as int, F1);
    let y0 = place(sh, ch0, vside(g0.kind), g0.y as int, F1);
    let w = sdim(g.w as int, dpr);
    let h = sdim(g.h as int, dpr);
    let p = plan(cw0, ch0, w, h, g.mode, g.enlarge);
    let (rw, rh, cw, ch) = (p.0, p.1, p.4, p.5);
    let cx = place(rw, cw, hside(g.gravity.kind), g.gravity.x as int, dpr);
    let cy = place(rh, ch, vside(g.gravity.kind), g.gravity.y as int, dpr);
    let ew = if g.extend && w > cw { w } else { cw };
    let eh = if g.extend && h > ch { h } else { ch };
    let ge = match g.extend_g {
        Some(e) => e,
        None => centre(),
    };
    let ex = place(ew, cw, hside(ge.kind), ge.x as int, dpr);
    let ey = place(eh, ch, vside(ge.kind), ge.y as int, dpr);
    let pt = fmul(g.pad[0] as int, dpr);
    let pr = fmul(g.pad[1] as int, dpr);
    let pb = fmul(g.pad[2] as int, dpr);
    let pl = fmul(g.pad[3] as int, dpr);
    Plan2 {
        x0,
        y0,
        cw0,
        ch0,
        rw,
        rh,
        cx,
        cy,
        cw,
        ch,
        canvas_w: ew + pl + pr,
        canvas_h: eh + pt + pb,
        ax: ex + pl,
        ay: ey + pt,
    }
}

// ---------------------------------------------------------------------------
// Pixels (RGBA, as in `spec.rs`)
// ---------------------------------------------------------------------------

/// `src` (`w` by `h`) on a `cw` by `ch` canvas filled with `fill`, its top
/// left pixel at `(x, y)`.
pub open spec fn embed(src: Seq<u8>, w: int, h: int, cw: int, ch: int, x: int, y: int, fill: [u8; 4]) -> Seq<u8> {
    Seq::new(
        (cw * ch * NC) as nat,
        |k: int|
            {
                let px = (k / NC) % cw;
                let py = (k / NC) / cw;
                if x <= px < x + w && y <= py < y + h {
                    src[((py - y) * w + (px - x)) * NC + k % NC]
                } else {
                    fill[k % NC]
                }
            },
    )
}

/// The source pixel output pixel `(px, py)` comes from when a `w` by `h`
/// image is turned clockwise by `q` quarter turns, then flipped
/// left-right (`fh`) and top-bottom (`fv`); the output is `h` by `w` for
/// odd `q`.
pub open spec fn turn_src(w: int, h: int, q: int, fh: bool, fv: bool, px: int, py: int) -> (int, int) {
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

/// `src` (`w` by `h`) turned and flipped as `turn_src` says.
pub open spec fn turn(src: Seq<u8>, w: int, h: int, q: int, fh: bool, fv: bool) -> Seq<u8> {
    let ow = if q % 2 == 1 { h } else { w };
    Seq::new(
        (w * h * NC) as nat,
        |k: int|
            {
                let s = turn_src(w, h, q, fh, fv, (k / NC) % ow, (k / NC) / ow);
                src[(s.1 * w + s.0) * NC + k % NC]
            },
    )
}

// ---------------------------------------------------------------------------
// Watermarks
// ---------------------------------------------------------------------------

/// Where a `ww` by `wh` watermark goes on a `w` by `h` image, at gravity
/// `g` (its offsets times `dpr`).
pub open spec fn wm_at(w: int, h: int, ww: int, wh: int, g: Gravity, dpr: int) -> (int, int) {
    (place(w, ww, hside(g.kind), g.x as int, dpr), place(h, wh, vside(g.kind), g.y as int, dpr))
}

/// One channel of a watermark pixel (value `sv`, alpha `sa`) laid over an
/// image pixel (value `dv`, alpha `da`) at opacity `op` (`F1` units):
/// Porter-Duff "over" with straight alpha, rounded to nearest. `alpha`
/// says the channel is the alpha channel.
pub open spec fn over_c(dv: int, da: int, sv: int, sa: int, op: int, alpha: bool) -> int {
    let a = (sa * op + F1 / 2) / F1;
    let oa = a * 255 + da * (255 - a);
    if oa == 0 {
        0
    } else if alpha {
        (oa + 127) / 255
    } else {
        (sv * a * 255 + dv * da * (255 - a) + oa / 2) / oa
    }
}

/// `dst` (`w` by `h`) with the watermark `wm` (`ww` by `wh`) laid over it
/// at opacity `op`: once with its top left at `(x, y)`, or (`tile`) every
/// `pw` pixels across and `ph` down from the top left.
pub open spec fn watermark(
    dst: Seq<u8>,
    w: int,
    h: int,
    wm: Seq<u8>,
    ww: int,
    wh: int,
    x: int,
    y: int,
    tile: bool,
    pw: int,
    ph: int,
    op: int,
) -> Seq<u8> {
    Seq::new(
        (w * h * NC) as nat,
        |k: int|
            {
                let px = (k / NC) % w;
                let py = (k / NC) / w;
                let c = k % NC;
                let sx = if tile { px % pw } else { px - x };
                let sy = if tile { py % ph } else { py - y };
                if 0 <= sx < ww && 0 <= sy < wh {
                    let ks = (sy * ww + sx) * NC;
                    over_c(dst[k] as int, dst[k - c + 3] as int, wm[ks + c] as int, wm[ks + 3] as int, op, c == 3) as u8
                } else {
                    dst[k]
                }
            },
    )
}

} // verus!
