//! Smart gravity, proven to compute `spec_smart::smart` for every image up
//! to 65535 by 65535 and every blur table `filter` takes.
use crate::filter::blur_rgba;
#[cfg(verus_only)]
use crate::filter::{gk_ok, gseq};
use crate::lanczos::kc_x;
#[cfg(verus_only)]
use crate::resize::lemma_idx;
use crate::spec::*;
use crate::spec_smart::*;
#[cfg(verus_only)]
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

fn lum_x(s: &[u8], k: usize) -> (r: i32)
    requires
        k + 3 <= s@.len(),
    ensures
        r == lum(s@, k as int),
        0 <= r <= 255,
{
    ((2126 * s[k] as u32 + 7152 * s[k + 1] as u32 + 722 * s[k + 2] as u32 + 5000) / 10000) as i32
}

fn lum_at_x(s: &[u8], w: usize, h: usize, x: i64, y: i64) -> (r: i32)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        s@.len() == w * h * NC,
    ensures
        r == lum_at(s@, w as int, h as int, x as int, y as int),
        0 <= r <= 255,
{
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                w <= 65535,
                h <= 65535,
        ;
    }
    let cx = kc_x(x, w);
    let cy = kc_x(y, h);
    proof {
        lemma_idx(cy as int, cx as int, 3, w as int, h as int);
    }
    lum_x(s, (cy * w + cx) * 4)
}

fn clamp255_x(v: i32) -> (r: i32)
    ensures
        r == clamp255(v as int),
{
    if v < 0 {
        0
    } else if v > 255 {
        255
    } else {
        v
    }
}

fn score_x(s: &[u8], w: usize, h: usize, x: usize, y: usize) -> (r: u8)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        s@.len() == w * h * NC,
        x < w,
        y < h,
    ensures
        r == score(s@, w as int, h as int, x as int, y as int) as u8,
{
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                w <= 65535,
                h <= 65535,
        ;
    }
    proof {
        lemma_idx(y as int, x as int, 3, w as int, h as int);
    }
    let (xi, yi) = (x as i64, y as i64);
    let l = 4 * lum_at_x(s, w, h, xi, yi) - lum_at_x(s, w, h, xi - 1, yi) - lum_at_x(s, w, h, xi + 1, yi) - lum_at_x(
        s,
        w,
        h,
        xi,
        yi - 1,
    ) - lum_at_x(s, w, h, xi, yi + 1);
    let e = clamp255_x(if l < 0 { -l } else { l });
    let k = (y * w + x) * 4;
    let (r, g, b, a) = (s[k] as i32, s[k + 1] as i32, s[k + 2] as i32, s[k + 3] as i32);
    let mn = if g < b { g } else { b };
    let sk = r > 95 && g > 40 && b > 20 && r > g && r > b && r - mn > 15 && r - g > 15;
    let mx3 = if r > g { if r > b { r } else { b } } else { if g > b { g } else { b } };
    let mn3 = if r < g { if r < b { r } else { b } } else { if g < b { g } else { b } };
    let st = if lum_x(s, k) > 32 { mx3 - mn3 } else { 0 };
    let v = clamp255_x(e + (if sk { 128 } else { 0 }) + st / 2);
    proof {
        assert(0 <= v * a <= 255 * 255) by (nonlinear_arith)
            requires
                0 <= v <= 255,
                0 <= a <= 255,
        ;
        vstd::arithmetic::div_mod::lemma_div_is_ordered((v * a) as int, (255 * 255) as int, 255);
    }
    (v * a / 255) as u8
}

/// `scores`.
pub fn scores_rgba(s: &[u8], w: usize, h: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        s@.len() == w * h * NC,
    ensures
        r@ == scores(s@, w as int, h as int),
{
    let ghost want = scores(s@, w as int, h as int);
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                w <= 65535,
                h <= 65535,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(w * h * 4);
    let mut y: usize = 0;
    while y < h
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            s@.len() == w * h * NC,
            w * h * NC <= 65535 * 65535 * 4,
            want == scores(s@, w as int, h as int),
            y <= h,
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
        decreases h - y,
    {
        let mut x: usize = 0;
        while x < w
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                s@.len() == w * h * NC,
                w * h * NC <= 65535 * 65535 * 4,
                want == scores(s@, w as int, h as int),
                y < h,
                x <= w,
                out@.len() == (y * w + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == want[j],
            decreases w - x,
        {
            let ghost before = out@;
            let ghost b = (y * w + x) * NC;
            let v = score_x(s, w, h, x, y);
            out.push(v);
            out.push(v);
            out.push(v);
            out.push(v);
            proof {
                lemma_idx(y as int, x as int, 3, w as int, h as int);
                assert((y * w + x + 1) * NC == b + 4) by (nonlinear_arith)
                    requires
                        b == (y * w + x) * NC,
                ;
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == want[j] by {
                    if j >= before.len() {
                        lemma_idx(y as int, x as int, j - b, w as int, h as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x += 1;
        }
        proof {
            assert((y * w + w) * NC == (y + 1) * w * NC) by (nonlinear_arith);
        }
        y += 1;
    }
    proof {
        assert(out@.len() == w * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * w * NC,
        ;
        assert(out@ =~= want);
    }
    out
}

/// `best(v, n)`.
pub fn best_x(v: &[u8], n: usize) -> (r: usize)
    requires
        1 <= n,
        n * NC <= v@.len(),
    ensures
        r == best(v@, n as int),
        r < n,
{
    let mut b: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            n * NC <= v@.len(),
            b == best(v@, i as int),
            b < i,
        decreases n - i,
    {
        if v[i * 4] > v[b * 4] {
            b = i;
        }
        i += 1;
    }
    b
}

pub proof fn lemma_divmod_lt(b: int, w: int, h: int)
    requires
        0 <= b < w * h,
        1 <= w,
    ensures
        0 <= b % w < w,
        0 <= b / w < h,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(b, w);
    if b / w >= h {
        assert(w * (b / w) >= w * h) by (nonlinear_arith)
            requires
                b / w >= h,
                w >= 1,
        ;
    }
}

/// `smart`: the point smart gravity centres on.
pub fn smart_x(g: &[u32], s: &[u8], w: usize, h: usize) -> (r: (usize, usize))
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        s@.len() == w * h * NC,
    ensures
        (r.0 as int, r.1 as int) == smart(gseq(g@), s@, w as int, h as int),
        r.0 < w,
        r.1 < h,
{
    let sc = scores_rgba(s, w, h);
    let bl = blur_rgba(g, &sc, w, h);
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                w <= 65535,
                h <= 65535,
        ;
        assert(bl@.len() == w * h * NC);
    }
    proof {
        assert(1 <= w * h) by (nonlinear_arith)
            requires
                1 <= w,
                1 <= h,
        ;
    }
    let b = best_x(&bl, w * h);
    proof {
        lemma_divmod_lt(b as int, w as int, h as int);
    }
    (b % w, b / w)
}

} // verus!

