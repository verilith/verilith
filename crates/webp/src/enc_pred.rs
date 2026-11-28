//! The predictor transform (§4.1) for the encoder: each pixel is replaced
//! by its difference from what the decoder will predict for it, from the
//! pixels before it and the block's mode. `residuals` is proven to give
//! back exactly the image under `spec::unpredict`.
#[cfg(verus_only)]
use crate::enc_tok::lemma_argb_chans;
#[cfg(verus_only)]
use crate::pixels::lemma_argb;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Pixels
// ---------------------------------------------------------------------------
/// The channels of `c`, each below 256.
#[inline(always)]
pub fn chans(c: u32) -> (r: (u32, u32, u32, u32))
    ensures
        r.0 == alpha(c) && r.1 == red(c) && r.2 == green(c) && r.3 == blue(c),
        r.0 < 256 && r.1 < 256 && r.2 < 256 && r.3 < 256,
{
    proof {
        assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && (c >> 8u32) & 0xffu32 < 256 && c & 0xffu32 < 256)
            by (bit_vector);
    }
    (c >> 24u32, (c >> 16u32) & 0xffu32, (c >> 8u32) & 0xffu32, c & 0xffu32)
}

/// The pixel of channels `a`, `r`, `g`, `b`.
#[inline(always)]
pub fn pack(a: u32, r: u32, g: u32, b: u32) -> (c: u32)
    requires
        a < 256,
        r < 256,
        g < 256,
        b < 256,
    ensures
        c == argb(a as nat, r as nat, g as nat, b as nat),
        alpha(c) == a && red(c) == r && green(c) == g && blue(c) == b,
{
    let c = (a << 24u32) | (r << 16u32) | (g << 8u32) | b;
    proof {
        lemma_argb(a, r, g, b);
        assert(c >> 24u32 == a && (c >> 16u32) & 0xffu32 == r && (c >> 8u32) & 0xffu32 == g && c & 0xffu32 == b)
            by (bit_vector)
            requires
                a < 256,
                r < 256,
                g < 256,
                b < 256,
                c == (a << 24u32) | (r << 16u32) | (g << 8u32) | b,
        ;
    }
    c
}

/// `a - p` channel by channel, modulo 256: `add_px` undoes it.
pub fn sub_px(a: u32, p: u32) -> (r: u32)
    ensures
        add_px(r, p) == a,
{
    let (a0, a1, a2, a3) = chans(a);
    let (p0, p1, p2, p3) = chans(p);
    let r = pack((a0 + 256 - p0) % 256, (a1 + 256 - p1) % 256, (a2 + 256 - p2) % 256, (a3 + 256 - p3) % 256);
    proof {
        assert forall|x: int, y: int| 0 <= x < 256 && 0 <= y < 256 implies #[trigger] (((x + 256 - y) % 256 + y) % 256) == x by {
            assert(((x + 256 - y) % 256 + y) % 256 == x) by (nonlinear_arith)
                requires
                    0 <= x < 256,
                    0 <= y < 256,
            ;
        }
        assert((((a0 + 256 - p0) % 256 + p0) % 256) as int == a0);
        assert((((a1 + 256 - p1) % 256 + p1) % 256) as int == a1);
        assert((((a2 + 256 - p2) % 256 + p2) % 256) as int == a2);
        assert((((a3 + 256 - p3) % 256 + p3) % 256) as int == a3);
        lemma_argb_chans(a);
    }
    r
}

pub fn avg2_x(a: u32, b: u32) -> (r: u32)
    ensures
        r == avg2(a, b),
{
    let (a0, a1, a2, a3) = chans(a);
    let (b0, b1, b2, b3) = chans(b);
    pack((a0 + b0) / 2, (a1 + b1) / 2, (a2 + b2) / 2, (a3 + b3) / 2)
}

#[inline(always)]
fn absd(x: u32, y: u32) -> (r: u32)
    requires
        x < 256,
        y < 256,
    ensures
        r as int == abs(x - y),
        r < 256,
{
    if x >= y {
        x - y
    } else {
        y - x
    }
}

pub fn select_x(l: u32, t: u32, tl: u32) -> (r: u32)
    ensures
        r == select(l, t, tl),
{
    let (l0, l1, l2, l3) = chans(l);
    let (t0, t1, t2, t3) = chans(t);
    let (c0, c1, c2, c3) = chans(tl);
    let pl = absd(t0, c0) + absd(t1, c1) + absd(t2, c2) + absd(t3, c3);
    let pt = absd(l0, c0) + absd(l1, c1) + absd(l2, c2) + absd(l3, c3);
    if pl < pt {
        l
    } else {
        t
    }
}

#[inline(always)]
fn clamp_x(v: i32) -> (r: u32)
    requires
        -1024 <= v <= 1024,
    ensures
        r as int == clamp(v as int),
        r < 256,
{
    if v < 0 {
        0
    } else if v > 255 {
        255
    } else {
        v as u32
    }
}

pub fn clamp_full_x(a: u32, b: u32, c: u32) -> (r: u32)
    ensures
        r == clamp_add_sub_full(a, b, c),
{
    let (a0, a1, a2, a3) = chans(a);
    let (b0, b1, b2, b3) = chans(b);
    let (c0, c1, c2, c3) = chans(c);
    pack(
        clamp_x(a0 as i32 + b0 as i32 - c0 as i32),
        clamp_x(a1 as i32 + b1 as i32 - c1 as i32),
        clamp_x(a2 as i32 + b2 as i32 - c2 as i32),
        clamp_x(a3 as i32 + b3 as i32 - c3 as i32),
    )
}

#[inline(always)]
fn half_x(x: u32, y: u32) -> (r: u32)
    requires
        x < 256,
        y < 256,
    ensures
        r as int == clamp(x + half_c(x - y)),
        r < 256,
{
    let d = x as i32 - y as i32;
    let hd = if d >= 0 {
        d / 2
    } else {
        -((-d) / 2)
    };
    clamp_x(x as i32 + hd)
}

pub fn clamp_half_x(a: u32, b: u32) -> (r: u32)
    ensures
        r == clamp_add_sub_half(a, b),
{
    let (a0, a1, a2, a3) = chans(a);
    let (b0, b1, b2, b3) = chans(b);
    pack(half_x(a0, b0), half_x(a1, b1), half_x(a2, b2), half_x(a3, b3))
}

/// `predict_mode`.
pub fn predict_mode_x(m: u32, l: u32, t: u32, tr: u32, tl: u32) -> (r: u32)
    ensures
        r == predict_mode(m as nat, l, t, tr, tl),
{
    if m == 1 {
        l
    } else if m == 2 {
        t
    } else if m == 3 {
        tr
    } else if m == 4 {
        tl
    } else if m == 5 {
        avg2_x(avg2_x(l, tr), t)
    } else if m == 6 {
        avg2_x(l, tl)
    } else if m == 7 {
        avg2_x(l, t)
    } else if m == 8 {
        avg2_x(tl, t)
    } else if m == 9 {
        avg2_x(t, tr)
    } else if m == 10 {
        avg2_x(avg2_x(l, tl), avg2_x(t, tr))
    } else if m == 11 {
        select_x(l, t, tl)
    } else if m == 12 {
        clamp_full_x(l, t, tl)
    } else if m == 13 {
        clamp_half_x(avg2_x(l, t), tl)
    } else {
        0xff00_0000u32
    }
}

// ---------------------------------------------------------------------------
// The prediction of a pixel
// ---------------------------------------------------------------------------
/// `2^bits`.
pub fn pow2_x(bits: u32) -> (r: usize)
    requires
        bits <= 16,
    ensures
        r as nat == pow2(bits as nat),
        1 <= r <= 0x1_0000,
{
    let mut r: usize = 1;
    let mut k: u32 = 0;
    proof {
        lemma2_to64();
    }
    while k < bits
        invariant
            k <= bits <= 16,
            r as nat == pow2(k as nat),
            1 <= r <= pow2(k as nat),
            pow2(16) == 0x1_0000,
        decreases bits - k,
    {
        proof {
            lemma_pow2_unfold((k + 1) as nat);
            lemma_pow2_strictly_increases(k as nat, 16);
        }
        r = r * 2;
        k = k + 1;
    }
    proof {
        if bits < 16 {
            lemma_pow2_strictly_increases(bits as nat, 16);
        }
    }
    r
}

/// The block of pixel (`x`, `y`) is inside the mode image.
proof fn lemma_block(x: int, y: int, w: int, h: int, pb: int)
    requires
        0 <= x < w,
        0 <= y < h,
        pb >= 1,
    ensures
        0 <= (y / pb) * ((w + pb - 1) / pb) + x / pb < ((w + pb - 1) / pb) * ((h + pb - 1) / pb),
        (w + pb - 1) / pb >= 1,
{
    let sw = (w + pb - 1) / pb;
    let sh = (h + pb - 1) / pb;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, w - 1, pb);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, h - 1, pb);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, pb);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(y, pb);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(w - 1, w + pb - 1 - pb, pb);
    assert((w + pb - 1) / pb == (w - 1) / pb + 1) by {
        vstd::arithmetic::div_mod::lemma_div_plus_one(w - 1, pb);
    }
    assert((h + pb - 1) / pb == (h - 1) / pb + 1) by {
        vstd::arithmetic::div_mod::lemma_div_plus_one(h - 1, pb);
    }
    assert(0 <= (y / pb) * sw + x / pb < sw * sh) by (nonlinear_arith)
        requires
            0 <= x / pb <= (w - 1) / pb,
            0 <= y / pb <= (h - 1) / pb,
            sw == (w - 1) / pb + 1,
            sh == (h - 1) / pb + 1,
    ;
}

/// The mode image fits an image `w` by `h` in blocks of `2^bits`.
pub open spec fn modes_fit(data: Seq<u32>, w: nat, h: nat, bits: nat) -> bool {
    data.len() == subsample(w, bits) * subsample(h, bits)
}

/// `predict` on the pixels themselves: what the decoder predicts for pixel
/// `i` once it has decoded the pixels before it.
pub fn predict_x(px: &[u32], i: usize, w: usize, h: usize, bits: u32, data: &[u32]) -> (r: u32)
    requires
        1 <= w <= 0x4000,
        h <= 0x4000,
        px@.len() == w * h,
        i < px@.len(),
        bits <= 9,
        modes_fit(data@, w as nat, h as nat, bits as nat),
    ensures
        r == predict(px@, i as nat, w as nat, bits as nat, data@),
{
    let x = i % w;
    let y = i / w;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, w as int);
        assert(y < h) by (nonlinear_arith)
            requires
                i == w * y + x,
                0 <= x,
                i < w * h,
                w >= 1,
        ;
    }
    if i == 0 {
        0xff00_0000u32
    } else if y == 0 {
        px[i - 1]
    } else if x == 0 {
        proof {
            assert(i >= w) by (nonlinear_arith)
                requires
                    i == w * y + x,
                    y >= 1,
                    x == 0,
            ;
        }
        px[i - w]
    } else {
        let pb = pow2_x(bits);
        proof {
            lemma_block(x as int, y as int, w as int, h as int, pb as int);
            assert(i >= w + 1) by (nonlinear_arith)
                requires
                    i == w * y + x,
                    y >= 1,
                    x >= 1,
            ;
            assert(x < w) by {
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(i as int, w as int);
            }
        }
        let sw = (w + pb - 1) / pb;
        proof {
            assert(data@.len() == data.len());
            assert(sw as int == subsample(w as nat, bits as nat));
            assert(((y / pb) * sw + x / pb) < data.len()) by {
                lemma_block(x as int, y as int, w as int, h as int, pb as int);
            }
            assert((y / pb) * sw <= (y / pb) * sw + x / pb);
        }
        let t = (y / pb) * sw + x / pb;
        let m = (data[t] >> 8u32) & 0xffu32;
        proof {
            assert(m % 16 < 16);
        }
        predict_mode_x(m % 16, px[i - 1], px[i - w], px[i - w + 1], px[i - w - 1])
    }
}

// ---------------------------------------------------------------------------
// Residuals
// ---------------------------------------------------------------------------
/// `unpredict` reads only the first `n` residuals.
proof fn lemma_unpredict_prefix(r1: Seq<u32>, r2: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, n: nat)
    requires
        n <= r1.len(),
        n <= r2.len(),
        forall|j: int| 0 <= j < n ==> r1[j] == r2[j],
    ensures
        unpredict(r1, w, bits, data, n) == unpredict(r2, w, bits, data, n),
    decreases n,
{
    if n > 0 {
        lemma_unpredict_prefix(r1, r2, w, bits, data, (n - 1) as nat);
    }
}

/// `unpredict`'s output has `n` pixels.
proof fn lemma_unpredict_len(r: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, n: nat)
    ensures
        unpredict(r, w, bits, data, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_unpredict_len(r, w, bits, data, (n - 1) as nat);
    }
}

/// `predict` reads only the pixels before `i`.
proof fn lemma_predict_take(o: Seq<u32>, i: nat, w: nat, bits: nat, data: Seq<u32>)
    requires
        i < o.len(),
        w >= 1,
    ensures
        predict(o.take(i as int), i, w, bits, data) == predict(o, i, w, bits, data),
{
    let x = i % w;
    let y = i / w;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, w as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i as int, w as int);
    if i > 0 && y > 0 {
        assert(i >= w) by (nonlinear_arith)
            requires
                i == w * y + x,
                y >= 1,
        ;
        if x > 0 {
            assert(i >= w + 1) by (nonlinear_arith)
                requires
                    i == w * y + x,
                    y >= 1,
                    x >= 1,
            ;
        }
    }
}

/// The residuals of `px` under the modes `data`, which `unpredict` turns
/// back into `px`.
pub fn residuals(px: &[u32], w: usize, h: usize, bits: u32, data: &[u32]) -> (r: Vec<u32>)
    requires
        1 <= w <= 0x4000,
        h <= 0x4000,
        px@.len() == w * h,
        bits <= 9,
        modes_fit(data@, w as nat, h as nat, bits as nat),
    ensures
        r@.len() == px@.len(),
        unpredict(r@, w as nat, bits as nat, data@, px@.len()) == px@,
{
    let mut out: Vec<u32> = Vec::with_capacity(px.len());
    let mut i: usize = 0;
    proof {
        assert(px@.take(0) =~= Seq::<u32>::empty());
    }
    while i < px.len()
        invariant
            1 <= w <= 0x4000,
            h <= 0x4000,
            px@.len() == w * h,
            bits <= 9,
            modes_fit(data@, w as nat, h as nat, bits as nat),
            i <= px@.len(),
            out@.len() == i,
            unpredict(out@, w as nat, bits as nat, data@, i as nat) == px@.take(i as int),
        decreases px.len() - i,
    {
        let p = predict_x(px, i, w, h, bits, data);
        let ghost o = out@;
        out.push(sub_px(px[i], p));
        proof {
            lemma_unpredict_prefix(o, out@, w as nat, bits as nat, data@, i as nat);
            lemma_predict_take(px@, i as nat, w as nat, bits as nat, data@);
            assert(px@.take(i + 1) =~= px@.take(i as int).push(px@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(px@.take(px@.len() as int) =~= px@);
    }
    out
}


// ---------------------------------------------------------------------------
// Choosing the modes
// ---------------------------------------------------------------------------
/// The cost of residual channel `d` (mod 256): its distance from zero.
#[inline(always)]
fn ch_cost(a: u32, p: u32) -> (r: u64)
    requires
        a < 256,
        p < 256,
    ensures
        r <= 128,
{
    let d = (a + 256 - p) % 256;
    let m = if d <= 128 {
        d
    } else {
        256 - d
    };
    // Roughly the bits a residual of size `m` costs.
    if m == 0 {
        0
    } else if m < 2 {
        3
    } else if m < 4 {
        4
    } else if m < 8 {
        5
    } else if m < 16 {
        6
    } else if m < 32 {
        7
    } else if m < 64 {
        8
    } else {
        9
    }
}

/// The cost of predicting `a` by `p`.
#[inline(always)]
fn px_cost(a: u32, p: u32) -> (r: u64)
    ensures
        r <= 512,
{
    let (a0, a1, a2, a3) = chans(a);
    let (p0, p1, p2, p3) = chans(p);
    ch_cost(a0, p0) + ch_cost(a1, p1) + ch_cost(a2, p2) + ch_cost(a3, p3)
}

/// The mode (0 to 13) that predicts the block at `(x0, y0)` best.
fn best_mode(px: &[u32], w: usize, h: usize, x0: usize, y0: usize, pb: usize) -> (r: u32)
    requires
        1 <= w <= 0x4000,
        h <= 0x4000,
        px@.len() == w * h,
        1 <= pb <= 512,
        x0 <= 0x100_0000,
        y0 <= 0x100_0000,
    ensures
        r < 14,
{
    let mut costs: [u64; 14] = [0u64; 14];
    let xe = if x0 + pb < w { x0 + pb } else { w };
    let ye = if y0 + pb < h { y0 + pb } else { h };
    let xs = if x0 == 0 { 1 } else { x0 };
    let mut y = if y0 == 0 { 1 } else { y0 };
    while y < ye
        invariant
            1 <= w <= 0x4000,
            h <= 0x4000,
            px@.len() == w * h,
            ye <= h,
            xe <= w,
            1 <= y,
            1 <= xs,
        decreases ye - y,
    {
        proof {
            assert(y * w <= 0x4000 * 0x4000) by (nonlinear_arith)
                requires
                    y < h <= 0x4000,
                    w <= 0x4000,
            ;
        }
        let row = y * w;
        proof {
            assert(row + w <= w * h) by (nonlinear_arith)
                requires
                    row == y * w,
                    y < h,
            ;
            assert(row >= w) by (nonlinear_arith)
                requires
                    row == y * w,
                    y >= 1,
            ;
        }
        let mut x = xs;
        while x < xe
            invariant
                1 <= w <= 0x4000,
                px@.len() == w * h,
                xe <= w,
                row + w <= w * h,
                row >= w,
                1 <= x,
            decreases xe - x,
        {
            let i = row + x;
            let a = px[i];
            let l = px[i - 1];
            let t = px[i - w];
            let tr = px[i - w + 1];
            let tl = px[i - w - 1];
            let mut m: usize = 0;
            while m < 14
                invariant
                    m <= 14,
                decreases 14 - m,
            {
                let c = px_cost(a, predict_mode_x(m as u32, l, t, tr, tl));
                if costs[m] < 0x1_0000_0000_0000 {
                    costs[m] = costs[m] + c;
                }
                m = m + 1;
            }
            x = x + 1;
        }
        y = y + 1;
    }
    // Ties go to the simplest mode; mode 1 (left) when the block is empty.
    let mut best: u32 = 1;
    let mut m: usize = 0;
    while m < 14
        invariant
            m <= 14,
            best < 14,
        decreases 14 - m,
    {
        if costs[m] < costs[best as usize] {
            best = m as u32;
        }
        m = m + 1;
    }
    best
}

/// The modes, one per `2^bits` square block, in the green channel as the
/// predictor transform stores them.
pub fn choose_modes(px: &[u32], w: usize, h: usize, bits: u32) -> (r: Vec<u32>)
    requires
        1 <= w <= 0x4000,
        h <= 0x4000,
        px@.len() == w * h,
        bits <= 9,
    ensures
        modes_fit(r@, w as nat, h as nat, bits as nat),
{
    let pb = pow2_x(bits);
    proof {
        lemma2_to64();
        assert(pb <= 512) by {
            lemma_pow2_strictly_increases(bits as nat, 10);
        }
    }
    let sw = (w + pb - 1) / pb;
    let sh = (h + pb - 1) / pb;
    proof {
        assert(sw <= w + pb - 1 && sh <= h + pb - 1) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator((w + pb - 1) as int, 1, pb as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator((h + pb - 1) as int, 1, pb as int);
        }
    }
    let mut out: Vec<u32> = Vec::new();
    let mut by: usize = 0;
    while by < sh
        invariant
            1 <= w <= 0x4000,
            h <= 0x4000,
            px@.len() == w * h,
            1 <= pb <= 512,
            sw <= 0x4200,
            sh <= 0x4200,
            by <= sh,
            out@.len() == by * sw,
        decreases sh - by,
    {
        let mut bx: usize = 0;
        while bx < sw
            invariant
                1 <= w <= 0x4000,
                h <= 0x4000,
                px@.len() == w * h,
                1 <= pb <= 512,
                sw <= 0x4200,
                by < sh <= 0x4200,
                bx <= sw,
                out@.len() == by * sw + bx,
            decreases sw - bx,
        {
            proof {
                assert(bx * pb <= 0x4200 * 512 && by * pb <= 0x4200 * 512) by (nonlinear_arith)
                    requires
                        bx <= 0x4200,
                        by <= 0x4200,
                        pb <= 512,
                ;
            }
            let m = best_mode(px, w, h, bx * pb, by * pb, pb);
            out.push(0xff00_0000u32 | (m << 8u32));
            bx = bx + 1;
        }
        proof {
            assert(by * sw + sw == (by + 1) * sw) by (nonlinear_arith);
        }
        by = by + 1;
    }
    proof {
        assert(sw as int == subsample(w as nat, bits as nat));
        assert(sh as int == subsample(h as nat, bits as nat));
        assert(sh * sw == sw * sh) by (nonlinear_arith);
    }
    out
}

} // verus!
