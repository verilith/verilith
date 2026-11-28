//! The output size: from the source size and what the request asks for,
//! the size to resize to and the rectangle to keep, proven to match
//! `plan` and to stay within bounds (no zero-sized image, no crop outside
//! the resized image, nothing larger than `MAX_DIM` or than the caller's
//! pixel limit).
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// How the requested box is used (imgproxy's `resizing_type`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Keep the aspect ratio and fit inside the box.
    Fit,
    /// Keep the aspect ratio, cover the box, and crop to it (centred).
    Fill,
    /// Stretch to the box.
    Force,
}

/// The result: resize to `rw` by `rh`, then keep the `cw` by `ch`
/// rectangle at `(cx, cy)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Plan {
    pub rw: u32,
    pub rh: u32,
    pub cx: u32,
    pub cy: u32,
    pub cw: u32,
    pub ch: u32,
}

/// `v * n / d`, rounded to nearest, and at least 1.
pub open spec fn scaled(v: int, n: int, d: int) -> int {
    let r = (2 * v * n + d) / (2 * d);
    if r < 1 { 1 } else { r }
}

/// The scale factor, as `n / d`: the box's width over the source's, or its
/// height over the source's, whichever the mode picks (0 means "not
/// given": the other one is used, and with neither the scale is 1).
pub open spec fn ratio(sw: int, sh: int, w: int, h: int, mode: Mode) -> (int, int) {
    if w == 0 && h == 0 {
        (1, 1)
    } else if w == 0 {
        (h, sh)
    } else if h == 0 {
        (w, sw)
    } else {
        // w / sw <= h / sh
        let width_smaller = w * sh <= h * sw;
        let fill = match mode { Mode::Fill => true, _ => false };
            if fill != width_smaller { (w, sw) } else { (h, sh) }
    }
}

/// Without `enlarge`, a scale above 1 becomes 1.
pub open spec fn capped(r: (int, int), enlarge: bool) -> (int, int) {
    if !enlarge && r.0 > r.1 { (1, 1) } else { r }
}

/// The plan for a `sw` by `sh` source and a request for `w` by `h`.
pub open spec fn plan(sw: int, sh: int, w: int, h: int, mode: Mode, enlarge: bool) -> (int, int, int, int, int, int) {
    if mode == Mode::Force {
        let rw = if w == 0 { sw } else { w };
        let rh = if h == 0 { sh } else { h };
        (rw, rh, 0, 0, rw, rh)
    } else {
        let r = capped(ratio(sw, sh, w, h, mode), enlarge);
        let rw = scaled(sw, r.0, r.1);
        let rh = scaled(sh, r.0, r.1);
        if let Mode::Fill = mode {
            let cw = if w == 0 || w > rw { rw } else { w };
            let ch = if h == 0 || h > rh { rh } else { h };
            (rw, rh, (rw - cw) / 2, (rh - ch) / 2, cw, ch)
        } else {
            (rw, rh, 0, 0, rw, rh)
        }
    }
}

fn scaled_x(v: u64, n: u64, d: u64) -> (r: u64)
    requires
        1 <= v <= MAX_DIM,
        n <= MAX_DIM,
        1 <= d <= MAX_DIM,
    ensures
        r == scaled(v as int, n as int, d as int),
{
    proof {
        assert(2 * v * n <= 2 * 65535 * 65535) by (nonlinear_arith)
            requires
                v <= 65535,
                n <= 65535,
        ;
    }
    let r = (2 * v * n + d) / (2 * d);
    if r < 1 { 1 } else { r }
}

/// `plan`, when every dimension of the result is at most `MAX_DIM` and the
/// resized image has at most `max_px` pixels; `None` otherwise.
pub fn plan_x(sw: u32, sh: u32, w: u32, h: u32, mode: Mode, enlarge: bool, max_px: u64) -> (r: Option<Plan>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        w <= MAX_DIM,
        h <= MAX_DIM,
    ensures
        r matches Some(p) ==> {
            &&& plan(sw as int, sh as int, w as int, h as int, mode, enlarge) == (
                p.rw as int,
                p.rh as int,
                p.cx as int,
                p.cy as int,
                p.cw as int,
                p.ch as int,
            )
            &&& 1 <= p.rw <= MAX_DIM
            &&& 1 <= p.rh <= MAX_DIM
            &&& 1 <= p.cw
            &&& 1 <= p.ch
            &&& p.cx + p.cw <= p.rw
            &&& p.cy + p.ch <= p.rh
            &&& p.rw * p.rh <= max_px
        },
{
    let (rw, rh, cx, cy, cw, ch): (u64, u64, u64, u64, u64, u64) = if let Mode::Force = mode {
        let rw = if w == 0 { sw as u64 } else { w as u64 };
        let rh = if h == 0 { sh as u64 } else { h as u64 };
        (rw, rh, 0, 0, rw, rh)
    } else {
        let (sw6, sh6, w6, h6) = (sw as u64, sh as u64, w as u64, h as u64);
        let (n, d): (u64, u64) = if w == 0 && h == 0 {
            (1, 1)
        } else if w == 0 {
            (h6, sh6)
        } else if h == 0 {
            (w6, sw6)
        } else {
            proof {
                assert(w6 * sh6 <= 65535 * 65535 && h6 * sw6 <= 65535 * 65535) by (nonlinear_arith)
                    requires
                        w6 <= 65535,
                        sh6 <= 65535,
                        h6 <= 65535,
                        sw6 <= 65535,
                ;
            }
            let width_smaller = w6 * sh6 <= h6 * sw6;
            let fill = match mode { Mode::Fill => true, _ => false };
            if fill != width_smaller { (w6, sw6) } else { (h6, sh6) }
        };
        let (n, d) = if !enlarge && n > d { (1u64, 1u64) } else { (n, d) };
        let rw = scaled_x(sw6, n, d);
        let rh = scaled_x(sh6, n, d);
        if let Mode::Fill = mode {
            let cw = if w == 0 || w6 > rw { rw } else { w6 };
            let ch = if h == 0 || h6 > rh { rh } else { h6 };
            (rw, rh, (rw - cw) / 2, (rh - ch) / 2, cw, ch)
        } else {
            (rw, rh, 0, 0, rw, rh)
        }
    };
    if rw > 65535 || rh > 65535 || cw == 0 || ch == 0 {
        return None;
    }
    proof {
        assert(rw * rh <= 65535 * 65535) by (nonlinear_arith)
            requires
                rw <= 65535,
                rh <= 65535,
        ;
    }
    if rw * rh > max_px {
        return None;
    }
    Some(Plan { rw: rw as u32, rh: rh as u32, cx: cx as u32, cy: cy as u32, cw: cw as u32, ch: ch as u32 })
}

} // verus!
