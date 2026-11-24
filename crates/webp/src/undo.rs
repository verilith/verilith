//! Undoing the transforms (§4), proven to compute `spec::undo_all`.
use crate::pixels::*;
use verilith_core::prims::*;
use crate::pxops::*;
use crate::transform::*;
use crate::vx::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
#[cfg(verus_only)]
use verilith_simd::cpu::avx2;
use vstd::prelude::*;

verus! {

/// Blocks of `2^b` pixels: a pixel's block is within the subsampled size.
pub proof fn lemma_sub_bound(n: nat, b: nat, x: nat)
    requires
        x < n,
    ensures
        x / pow2(b) < subsample(n, b),
        subsample(n, b) <= n,
{
    let pp = pow2(b) as int;
    lemma_pow2_pos(b);
    lemma_fundamental_div_mod(x as int, pp);
    lemma_mod_bound(x as int, pp);
    let q = x as int / pp;
    assert((q + 1) * pp <= n + pp - 1) by (nonlinear_arith)
        requires
            x == pp * q + x as int % pp,
            x as int % pp >= 0,
            x < n,
    ;
    lemma_div_multiples_vanish(q + 1, pp);
    lemma_div_is_ordered(((q + 1) * pp) as int, (n + pp - 1) as int, pp);
    lemma_mul_is_commutative_int(q + 1, pp);
    assert(n + pp - 1 <= n * pp) by (nonlinear_arith)
        requires
            n >= 1,
            pp >= 1,
    ;
    lemma_div_is_ordered((n + pp - 1) as int, (n * pp) as int, pp);
    lemma_div_multiples_vanish(n as int, pp);
    lemma_mul_is_commutative_int(n as int, pp);
}

proof fn lemma_mul_is_commutative_int(a: int, b: int)
    ensures
        a * b == b * a,
{
}

/// The index of pixel `(x, y)`'s block in a block image.
pub proof fn lemma_block_index(x: nat, y: nat, w: nat, h: nat, b: nat)
    requires
        x < w,
        y < h,
    ensures
        (y / pow2(b)) * subsample(w, b) + x / pow2(b) < subsample(w, b) * subsample(h, b),
{
    lemma_sub_bound(w, b, x);
    lemma_sub_bound(h, b, y);
    let sw = subsample(w, b);
    let sh = subsample(h, b);
    let ty = y / pow2(b);
    let tx = x / pow2(b);
    assert(ty * sw + tx < sw * sh) by (nonlinear_arith)
        requires
            ty < sh,
            tx < sw,
    ;
}

/// Row and column of pixel `i` from `x == i % w`, `y == i / w`.
pub proof fn lemma_xy(i: nat, w: nat, h: nat, x: nat, y: nat)
    requires
        w >= 1,
        i < w * h,
        x == i % w,
        y == i / w,
    ensures
        x < w,
        y < h,
        i == y * w + x,
{
    lemma_mod_bound(i as int, w as int);
    lemma_fundamental_div_mod(i as int, w as int);
    lemma_multiply_divide_lt(i as int, w as int, h as int);
    lemma_mul_is_commutative_int(w as int, y as int);
}

/// `x >> b` is `x / 2^b`.
pub proof fn lemma_shr(x: usize, b: u32)
    requires
        b <= 9,
    ensures
        (x >> b) as nat == (x as nat) / pow2(b as nat),
{
    lemma_usize_shr_is_div(x, b as usize);
}

/// Undoes subtract green.
pub fn undo_sg(px: &mut Vec<u32>)
    ensures
        final(px)@ == undo(Transform::SubtractGreen, old(px)@, 0),
{
    let ghost src = px@;
    if has_avx2() {
        // The CPU has AVX2.
        undo_sg_avx2(px);
        assert(px@ =~= undo(Transform::SubtractGreen, src, 0));
        return;
    }
    let n = px.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == px@.len(),
            src.len() == n,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] px@[j] == add_green(src[j]),
            forall|j: int| i <= j < n ==> #[trigger] px@[j] == src[j],
        decreases n - i,
    {
        let c = add_green_exec(px[i]);
        px.set(i, c);
        i = i + 1;
    }
    assert(px@ =~= undo(Transform::SubtractGreen, src, 0));
}

/// Undoes the color transform.
pub fn undo_color(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        wf_t(Transform::Color { bits: bits as nat, w: w as nat, data: data@ }, w as nat, h as nat),
    ensures
        final(px)@ == undo(Transform::Color { bits: bits as nat, w: w as nat, data: data@ }, old(px)@, h as nat),
{
    let fast = has_avx2();
    let ghost src = px@;
    let ghost t = Transform::Color { bits: bits as nat, w: w as nat, data: data@ };
    let ghost spec = undo(t, src, h as nat);
    proof {
        assert(w * h <= 16384 * 16384) by (nonlinear_arith)
            requires
                w <= 16384,
                h <= 16384,
        ;
        lemma_pow2_pos(bits as nat);
        lemma_pow2_strictly_increases(bits as nat, 10);
        lemma2_to64();
        vstd::bits::lemma_u64_shl_is_mul(1, bits as u64);
    }
    let sw = subsample_exec(w, bits);
    let bw: usize = 1usize << bits;
    proof {
        assert(bw as nat == pow2(bits as nat)) by {
            vstd::bits::lemma_usize_shl_is_mul(1, bits as usize);
        }
        lemma_sub_bound(h as nat, bits as nat, 0);
        assert(data@.len() <= w * h) by (nonlinear_arith)
            requires
                data@.len() == sw * subsample(h as nat, bits as nat),
                sw <= w,
                subsample(h as nat, bits as nat) <= h,
        ;
    }
    assert(spec.len() == px@.len());
    let mut y: usize = 0;
    while y < h
        invariant
            fast ==> avx2(),
            1 <= w <= 16384,
            1 <= h <= 16384,
            2 <= bits <= 9,
            w * h == px@.len(),
            src.len() == px@.len(),
            sw == subsample(w as nat, bits as nat),
            bw as nat == pow2(bits as nat),
            1 <= bw <= 512,
            1 <= sw,
            forall|x: nat| x < w ==> #[trigger] (x / pow2(bits as nat)) < sw,
            w * h <= 16384 * 16384,
            data@.len() <= w * h,
            data@.len() == subsample(w as nat, bits as nat) * subsample(h as nat, bits as nat),
            spec == undo(t, src, h as nat),
            spec.len() == px@.len(),
            t == (Transform::Color { bits: bits as nat, w: w as nat, data: data@ }),
            y <= h,
            forall|j: int| 0 <= j < y * w ==> #[trigger] px@[j] == spec[j],
            forall|j: int| y * w <= j < px@.len() ==> #[trigger] px@[j] == src[j],
        decreases h - y,
    {
        proof {
            assert(y * w + w <= w * h) by (nonlinear_arith)
                requires
                    y < h,
            ;
            lemma_shr(y, bits);
            lemma_sub_bound(h as nat, bits as nat, y as nat);
        }
        let row = y * w;
        let by = y >> bits;
        proof {
            assert(by * sw + sw <= data@.len()) by (nonlinear_arith)
                requires
                    by < subsample(h as nat, bits as nat),
                    data@.len() == sw * subsample(h as nat, bits as nat),
            ;
        }
        let brow = by * sw;
        let mut x0: usize = 0;
        let mut bx: usize = 0;
        while x0 < w
            invariant
                fast ==> avx2(),
                1 <= w <= 16384,
                2 <= bits <= 9,
                w * h == px@.len(),
                src.len() == px@.len(),
                sw == subsample(w as nat, bits as nat),
                bw as nat == pow2(bits as nat),
                1 <= bw <= 512,
                row == y * w,
                row + w <= px@.len(),
                1 <= sw,
                forall|x: nat| x < w ==> #[trigger] (x / pow2(bits as nat)) < sw,
                w * h <= 16384 * 16384,
                data@.len() <= w * h,
                y < h,
                by as nat == y as nat / pow2(bits as nat),
                brow == by * sw,
                brow + sw <= data@.len(),
                spec == undo(t, src, h as nat),
                t == (Transform::Color { bits: bits as nat, w: w as nat, data: data@ }),
                x0 <= w,
                x0 < w ==> x0 == bx * bw,
                x0 < w ==> bx < sw,
                forall|j: int| 0 <= j < row + x0 ==> #[trigger] px@[j] == spec[j],
                forall|j: int| row + x0 <= j < px@.len() ==> #[trigger] px@[j] == src[j],
            decreases w - x0,
        {
            let x1 = if w - x0 > bw {
                x0 + bw
            } else {
                w
            };
            let e = data[brow + bx];
            let ghost before = px@;
            if fast {
                // The CPU has AVX2.
                uncolor_run_avx2(px, row + x0, row + x1, e);
            } else {
                uncolor_run_swar(px, row + x0, row + x1, e);
            }
            proof {
                assert forall|j: int| row + x0 <= j < row + x1 implies #[trigger] px@[j] == spec[j] by {
                    let x = j - row;
                    lemma_fundamental_div_mod_converse(j, w as int, y as int, x);
                    lemma_fundamental_div_mod_converse(x, bw as int, bx as int, x - bx * bw);
                    assert(px@[j] == uncolor(src[j], e));
                }
                // The next block starts where this one ended.
                if x1 < w {
                    assert(x1 == (bx + 1) * bw) by (nonlinear_arith)
                        requires
                            x1 == x0 + bw,
                            x0 == bx * bw,
                    ;
                    assert(bx + 1 < sw) by {
                        assert(x1 as nat / pow2(bits as nat) < sw);
                        lemma_fundamental_div_mod_converse(x1 as int, bw as int, (bx + 1) as int, 0);
                    }
                }
            }
            x0 = x1;
            bx = bx + 1;
            proof {
                if x0 < w {
                    assert(x0 == bx * bw) by (nonlinear_arith)
                        requires
                            x0 == (bx - 1) * bw + bw,
                    ;
                }
            }
        }
        y = y + 1;
        proof {
            assert(row + w == y * w) by (nonlinear_arith)
                requires
                    row == (y - 1) * w,
            ;
        }
    }
    assert(h * w == w * h) by (nonlinear_arith);
    assert(px@ =~= spec);
}

/// Undoes the color transform with element `e` on pixels `i0..i1`, one
/// pixel at a time (no AVX2).
fn uncolor_run_swar(px: &mut Vec<u32>, i0: usize, i1: usize, e: u32)
    requires
        i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == uncolor(old(px)@[j], e),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    let ghost src = px@;
    let mut j = i0;
    while j < i1
        invariant
            i0 <= j <= i1 <= src.len(),
            px@.len() == src.len(),
            forall|q: int| i0 <= q < j ==> #[trigger] px@[q] == uncolor(src[q], e),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let c = uncolor_exec(get32(px.as_slice(), j), e);
        set32(px.as_mut_slice(), j, c);
        j = j + 1;
    }
}

/// Undoes the predictor transform.
pub fn undo_predict(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        wf_t(Transform::Predictor { bits: bits as nat, w: w as nat, data: data@ }, w as nat, h as nat),
    ensures
        final(px)@ == undo(Transform::Predictor { bits: bits as nat, w: w as nat, data: data@ }, old(px)@, h as nat),
{
    if has_avx2() {
        // The CPU has AVX2.
        crate::vpred::unpredict_avx2(px, w, h, bits, data);
        return;
    }
    proof {
        assert(old(px)@.len() == w * h);
    }
    crate::vpred::unpredict_swar(px, w, h, bits, data);
}

/// Undoes color indexing: the image is `subsample(w, bits)` wide.
pub fn undo_index(px: &Vec<u32>, w: usize, h: usize, bits: u32, palette: &Vec<u32>) -> (r: Option<Vec<u32>>)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        px@.len() == subsample(w as nat, bits as nat) * h,
        wf_t(Transform::ColorIndexing { bits: bits as nat, w: w as nat, palette: palette@ }, w as nat, h as nat),
    ensures
        r matches Some(v) ==> v@ == undo(
            Transform::ColorIndexing { bits: bits as nat, w: w as nat, palette: palette@ },
            px@,
            h as nat,
        ),
{
    let ghost t = Transform::ColorIndexing { bits: bits as nat, w: w as nat, palette: palette@ };
    let ghost spec = undo(t, px@, h as nat);
    proof {
        assert(w * h <= 16384 * 16384) by (nonlinear_arith)
            requires
                w <= 16384,
                h <= 16384,
        ;
    }
    let n = w * h;
    let mut out = match alloc_u32(n) {
        Some(v) => v,
        None => return None,
    };
    let sw = subsample_exec(w, bits);
    let (bpp, xmask, imask): (u32, usize, u32) = if bits == 0 {
        (8, 0, 255)
    } else if bits == 1 {
        (4, 1, 15)
    } else if bits == 2 {
        (2, 3, 3)
    } else {
        (1, 7, 1)
    };
    proof {
        lemma2_to64();
        assert(pow2(0) == 1 && pow2(1) == 2 && pow2(2) == 4 && pow2(3) == 8 && pow2(4) == 16 && pow2(8) == 256);
        if bits == 0 {
            assert(pow2(bits as nat) == 1);
            assert(8nat / 1 == 8);
            assert(bpp == 8);
            assert(bpp * pow2(bits as nat) == 8) by (nonlinear_arith)
                requires
                    bpp == 8,
                    pow2(bits as nat) == 1,
            ;
        } else if bits == 1 {
            assert(pow2(bits as nat) == 2);
            assert(8nat / 2 == 4);
            assert(bpp == 4);
            assert(bpp * pow2(bits as nat) == 8) by (nonlinear_arith)
                requires
                    bpp == 4,
                    pow2(bits as nat) == 2,
            ;
        } else if bits == 2 {
            assert(pow2(bits as nat) == 4);
            assert(8nat / 4 == 2);
            assert(bpp == 2);
            assert(bpp * pow2(bits as nat) == 8) by (nonlinear_arith)
                requires
                    bpp == 2,
                    pow2(bits as nat) == 4,
            ;
        } else {
            assert(pow2(bits as nat) == 8);
            assert(8nat / 8 == 1);
            assert(bpp == 1);
            assert(bpp * pow2(bits as nat) == 8) by (nonlinear_arith)
                requires
                    bpp == 1,
                    pow2(bits as nat) == 8,
            ;
        }
        assert(bpp as nat == 8nat / pow2(bits as nat));
        assert(bpp * pow2(bits as nat) == 8);
        assert(xmask as nat + 1 == pow2(bits as nat));
        assert(imask as nat + 1 == pow2(bpp as nat));
        assert(palette@.len() == pow2(bpp as nat));
    }
    let mut i: usize = 0;
    let mut x: usize = 0;
    let mut y: usize = 0;
    while i < n
        invariant
            1 <= w <= 16384,
            1 <= h <= 16384,
            bits <= 3,
            n == w * h,
            out@.len() == n,
            sw == subsample(w as nat, bits as nat),
            px@.len() == sw * h,
            bpp as nat == 8nat / pow2(bits as nat),
            xmask as nat + 1 == pow2(bits as nat),
            imask as nat + 1 == pow2(bpp as nat),
            bpp * pow2(bits as nat) == 8,
            palette@.len() == pow2(bpp as nat),
            1 <= bpp <= 8,
            spec == undo(t, px@, h as nat),
            t == (Transform::ColorIndexing { bits: bits as nat, w: w as nat, palette: palette@ }),
            i <= n,
            x == (i as nat) % (w as nat),
            y == (i as nat) / (w as nat),
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == spec[j],
        decreases n - i,
    {
        proof {
            lemma_xy(i as nat, w as nat, h as nat, x as nat, y as nat);
            lemma_sub_bound(w as nat, bits as nat, x as nat);
            lemma_shr(x, bits);
            assert(y * sw + (x >> bits) < sw * h) by (nonlinear_arith)
                requires
                    y < h,
                    (x >> bits) < sw,
            ;
            assert(y * sw + (x >> bits) <= 16384 * 16384) by (nonlinear_arith)
                requires
                    y < 16384,
                    sw <= 16384,
                    (x >> bits) < 16384,
            ;
        }
        let packed = (px[y * sw + (x >> bits)] >> 8) & 0xff;
        let xr = x & xmask;
        proof {
            lemma_usize_low_bits_mask_is_mod(x, bits as nat);
            vstd::bits::lemma_low_bits_mask_values();
            assert(xmask == low_bits_mask(bits as nat) as usize);
            assert(xr == x as nat % pow2(bits as nat));
            lemma_mod_bound(x as int, pow2(bits as nat) as int);
            assert(xr < pow2(bits as nat));
            assert(xr * bpp < 8) by (nonlinear_arith)
                requires
                    xr < pow2(bits as nat),
                    bpp * pow2(bits as nat) == 8,
            ;
        }
        let sh = (xr as u32) * bpp;
        let idx = (packed >> sh) & imask;
        proof {
            lemma_u32_shr_is_div(packed, sh);
            lemma_u32_low_bits_mask_is_mod(packed >> sh, bpp as nat);
            vstd::bits::lemma_low_bits_mask_values();
            assert(imask == low_bits_mask(bpp as nat) as u32);
            assert(idx == (packed as nat / pow2(sh as nat)) % pow2(bpp as nat));
            lemma_mod_bound((packed as nat / pow2(sh as nat)) as int, pow2(bpp as nat) as int);
            assert(idx < palette@.len());
            assert(packed == green(px@[(y * sw + (x >> bits)) as int]));
            assert(spec[i as int] == palette@[idx as int]);
        }
        out.set(i, palette[idx as usize]);
        proof {
            lemma_xy_step(i as nat, w as nat, x as nat, y as nat);
        }
        i = i + 1;
        if x + 1 < w {
            x = x + 1;
        } else {
            x = 0;
            y = y + 1;
        }
    }
    assert(out@ =~= spec);
    Some(out)
}

} // verus!
