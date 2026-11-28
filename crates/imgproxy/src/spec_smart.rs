//! The specification of smart gravity (`g:sm`), after libvips's
//! `vips_smartcrop` with its "attention" strategy: score each pixel of a
//! small copy of the image for edges (a Laplacian of the luminance),
//! skin-coloured pixels and saturated colour, blur the scores, and centre
//! the crop on the first pixel with the highest blurred score. Part of
//! the trusted base with `spec.rs`.
//!
//! The weights are this crate's own (libvips's are not reproduced
//! exactly); they decide only which part of the image is kept.
use crate::spec::*;
use crate::spec_filter::*;
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

/// The luminance (Rec. 709 weights) of the pixel at index `k`.
pub open spec fn lum(s: Seq<u8>, k: int) -> int {
    (2126 * s[k] + 7152 * s[k + 1] + 722 * s[k + 2] + 5000) / 10000
}

/// The luminance at `(x, y)` of a `w` by `h` image, edges repeated.
pub open spec fn lum_at(s: Seq<u8>, w: int, h: int, x: int, y: int) -> int {
    lum(s, (kc(y, h) * w + kc(x, w)) * NC)
}

pub open spec fn clamp255(v: int) -> int {
    if v < 0 {
        0
    } else if v > 255 {
        255
    } else {
        v
    }
}

/// Edges: the absolute Laplacian of the luminance.
pub open spec fn edge(s: Seq<u8>, w: int, h: int, x: int, y: int) -> int {
    let l = 4 * lum_at(s, w, h, x, y) - lum_at(s, w, h, x - 1, y) - lum_at(s, w, h, x + 1, y) - lum_at(s, w, h, x, y - 1)
        - lum_at(s, w, h, x, y + 1);
    clamp255(if l < 0 { -l } else { l })
}

/// Skin: the RGB rule of Kovač, Peer and Solina (daylight).
pub open spec fn skin(r: int, g: int, b: int) -> bool {
    let mn = if g < b { g } else { b };
    r > 95 && g > 40 && b > 20 && r > g && r > b && r - mn > 15 && r - g > 15
}

/// Saturation: the spread of the channels, in pixels that are not dark.
pub open spec fn sat(r: int, g: int, b: int, l: int) -> int {
    let mx = if r > g { if r > b { r } else { b } } else { if g > b { g } else { b } };
    let mn = if r < g { if r < b { r } else { b } } else { if g < b { g } else { b } };
    if l > 32 {
        mx - mn
    } else {
        0
    }
}

/// The score of pixel `(x, y)`: edges, plus 128 for skin, plus half the
/// saturation, at most 255, times the pixel's opacity.
pub open spec fn score(s: Seq<u8>, w: int, h: int, x: int, y: int) -> int {
    let k = (y * w + x) * NC;
    let (r, g, b, a) = (s[k] as int, s[k + 1] as int, s[k + 2] as int, s[k + 3] as int);
    let v = clamp255(edge(s, w, h, x, y) + (if skin(r, g, b) { 128int } else { 0 }) + sat(r, g, b, lum(s, k)) / 2);
    v * a / 255
}

/// The scores as a grey image (every channel the score).
pub open spec fn scores(s: Seq<u8>, w: int, h: int) -> Seq<u8> {
    Seq::new((w * h * NC) as nat, |k: int| score(s, w, h, (k / NC) % w, (k / NC) / w) as u8)
}

/// The first of the first `n` pixels of `v` with the highest first channel.
pub open spec fn best(v: Seq<u8>, n: int) -> int
    decreases n,
{
    if n <= 1 {
        0
    } else {
        let b = best(v, n - 1);
        if v[(n - 1) * NC] > v[b * NC] {
            n - 1
        } else {
            b
        }
    }
}

/// The point smart gravity centres on, in a `w` by `h` image: the best
/// pixel of the scores blurred with `g`.
pub open spec fn smart(g: Seq<int>, s: Seq<u8>, w: int, h: int) -> (int, int) {
    let b = best(blur(g, scores(s, w, h), w, h), w * h);
    (b % w, b / w)
}

} // verus!
