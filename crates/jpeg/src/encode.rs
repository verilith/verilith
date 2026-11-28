//! The JPEG encoder: baseline, YCbCr with 4:2:0 or 4:4:4 sampling, the
//! typical Huffman tables, libjpeg's quality scaling. Proven: the file it
//! returns decodes, under `spec::jpeg_coded`, to `enc_spec::enc_coded` of
//! its input, the coefficients libjpeg-turbo computes with its default
//! settings.
use crate::enc_bits::*;
use crate::enc_file::*;
use crate::enc_front::*;
use crate::enc_huff::*;
use crate::enc_scan::*;
use crate::enc_spec::*;
use crate::huff::*;
use crate::parse::std_tab;
use crate::spec::*;
use crate::types::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Planes
// ---------------------------------------------------------------------------
pub open spec fn im_ok(im: Rgb) -> bool {
    &&& 1 <= im.w <= 65500
    &&& 1 <= im.h <= 65500
    &&& im.bpp == 3 || im.bpp == 4
    &&& im.px.len() == im.w * im.h * im.bpp
}

/// `pl` is `ht` rows of `wd` samples, each `full` of component `c`.
pub open spec fn plane_full(pl: Seq<Vec<u8>>, im: Rgb, c: int, wd: int, ht: int) -> bool {
    &&& pl.len() == ht
    &&& forall|y: int| 0 <= y < ht ==> (#[trigger] pl[y])@.len() == wd
    &&& forall|y: int, x: int| 0 <= y < ht && 0 <= x < wd ==> (#[trigger] pl[y]@[x]) as int == full(im, c, y, x)
}

/// The same with each sample `samp`.
pub open spec fn plane_samp(pl: Seq<Vec<u8>>, im: Rgb, sub: bool, c: int, wd: int, ht: int) -> bool {
    &&& pl.len() == ht
    &&& forall|y: int| 0 <= y < ht ==> (#[trigger] pl[y])@.len() == wd
    &&& forall|y: int, x: int|
        0 <= y < ht && 0 <= x < wd ==> (#[trigger] pl[y]@[x]) as int == samp(im, sub, c, y, x)
}

proof fn lemma_pix(w: int, h: int, bpp: int, y: int, x: int)
    requires
        0 <= y < h,
        0 <= x < w,
        3 <= bpp,
    ensures
        0 <= y * w,
        y * w + x < w * h,
        w * h <= w * h * bpp,
        0 <= (y * w + x) * bpp,
        (y * w + x) * bpp + 2 < w * h * bpp,
{
    assert(0 <= (y * w + x) * bpp) by (nonlinear_arith)
        requires
            0 <= y,
            0 <= x,
            0 <= w,
            0 <= bpp,
    ;
    assert(0 <= y * w) by (nonlinear_arith)
        requires
            0 <= y,
            0 <= w,
    ;
    assert(w * h <= w * h * bpp) by (nonlinear_arith)
        requires
            0 <= w,
            0 <= h,
            1 <= bpp,
    ;
    assert(y * w + x + 1 <= w * h) by (nonlinear_arith)
        requires
            0 <= y < h,
            0 <= x < w,
    ;
    assert((y * w + x + 1) * bpp <= w * h * bpp) by (nonlinear_arith)
        requires
            y * w + x + 1 <= w * h,
            0 <= bpp,
    ;
    assert((y * w + x + 1) * bpp == (y * w + x) * bpp + bpp) by (nonlinear_arith);
}

/// Row `sy`'s first `8 * n` pixels, `bpp` bytes each, and 4 bytes more,
/// fit in the image (`n` as `full_planes` picks it, `m` at most `w`).
proof fn lemma_row_run(w: int, h: int, bpp: int, sy: int, m: int, n: int)
    requires
        0 <= sy < h,
        1 <= w,
        m <= w,
        3 <= bpp <= 4,
        1 <= n,
        sy + 1 < h ==> 8 * n <= m,
        sy + 1 >= h ==> 8 * n + 2 <= m,
    ensures
        0 <= sy * w * bpp,
        sy * w <= sy * w * bpp,
        sy * w * bpp + bpp * (8 * n) + 4 <= w * h * bpp,
        8 * n <= w,
{
    assert(0 <= sy * w && sy * w <= sy * w * bpp) by (nonlinear_arith)
        requires
            0 <= sy,
            1 <= w,
            3 <= bpp,
    ;
    if sy + 1 < h {
        assert(sy * w * bpp + bpp * (8 * n) + 4 <= w * h * bpp) by (nonlinear_arith)
            requires
                0 <= sy,
                sy + 2 <= h,
                1 <= w,
                3 <= bpp,
                0 <= 8 * n <= w,
        ;
    } else {
        assert(sy * w * bpp + bpp * (8 * n) + 4 <= w * h * bpp) by (nonlinear_arith)
            requires
                sy + 1 == h,
                1 <= w,
                3 <= bpp,
                0 <= 8 * n,
                8 * n + 2 <= w,
        ;
    }
}

/// Pixel (`sy`, `x`)'s bytes start at `sy * w * bpp + bpp * x`.
proof fn lemma_row_px(w: int, bpp: int, sy: int, x: int)
    ensures
        (sy * w + x) * bpp == sy * w * bpp + bpp * x,
{
    assert((sy * w + x) * bpp == sy * w * bpp + bpp * x) by (nonlinear_arith);
}

/// Y, Cb and Cr at full resolution, `ph` rows of `pw`, the image's edges
/// repeated.
fn full_planes(px: &[u8], w: usize, h: usize, bpp: usize, pw: usize, ph: usize, simd: bool) -> (r: (
    Vec<Vec<u8>>,
    Vec<Vec<u8>>,
    Vec<Vec<u8>>,
))
    requires
        simd ==> verilith_simd::cpu::avx2(),
        im_ok(Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }),
    ensures
        plane_full(r.0@, Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }, 0, pw as int, ph as int),
        plane_full(r.1@, Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }, 1, pw as int, ph as int),
        plane_full(r.2@, Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }, 2, pw as int, ph as int),
{
    let ghost im = Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ };
    let mut p0: Vec<Vec<u8>> = Vec::new();
    let mut p1: Vec<Vec<u8>> = Vec::new();
    let mut p2: Vec<Vec<u8>> = Vec::new();
    let mut y: usize = 0;
    while y < ph
        invariant
            simd ==> verilith_simd::cpu::avx2(),
            im == (Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }),
            im_ok(im),
            y <= ph,
            p0@.len() == y && p1@.len() == y && p2@.len() == y,
            forall|yy: int| 0 <= yy < y ==> (#[trigger] p0@[yy])@.len() == pw,
            forall|yy: int| 0 <= yy < y ==> (#[trigger] p1@[yy])@.len() == pw,
            forall|yy: int| 0 <= yy < y ==> (#[trigger] p2@[yy])@.len() == pw,
            forall|yy: int, x: int| 0 <= yy < y && 0 <= x < pw ==> (#[trigger] p0@[yy]@[x]) as int == full(im, 0, yy, x),
            forall|yy: int, x: int| 0 <= yy < y && 0 <= x < pw ==> (#[trigger] p1@[yy]@[x]) as int == full(im, 1, yy, x),
            forall|yy: int, x: int| 0 <= yy < y && 0 <= x < pw ==> (#[trigger] p2@[yy]@[x]) as int == full(im, 2, yy, x),
        decreases ph - y,
    {
        let sy = if y < h {
            y
        } else {
            h - 1
        };
        let mut r0: Vec<u8> = Vec::with_capacity(pw);
        let mut r1: Vec<u8> = Vec::with_capacity(pw);
        let mut r2: Vec<u8> = Vec::with_capacity(pw);
        let mut x: usize = 0;
        if simd && w >= 16 && pw >= 16 {
            let m = if w < pw {
                w
            } else {
                pw
            };
            // Each group reads 4 bytes past its pixels: past the row's end
            // into the next row, or on the last row short of its last two.
            let n = if sy + 1 < h {
                m / 8
            } else {
                (m - 2) / 8
            };
            proof {
                lemma_row_run(w as int, h as int, bpp as int, sy as int, m as int, n as int);
                assert(px@.len() == px.len());
            }
            let i = sy * w * bpp;
            // `ycc_run` enables AVX2, which makes it unsafe to call, on
            // x86-64; `simd` says the CPU has it.
            #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
            unsafe {
                crate::color_avx2::ycc_run(px, i, n, bpp, &mut r0, &mut r1, &mut r2)
            };
            x = 8 * n;
            proof {
                assert forall|xx: int| #![trigger r0@[xx]] #![trigger r1@[xx]] #![trigger r2@[xx]] 0 <= xx < x implies {
                    &&& (r0@[xx]) as int == full(im, 0, y as int, xx)
                    &&& (r1@[xx]) as int == full(im, 1, y as int, xx)
                    &&& (r2@[xx]) as int == full(im, 2, y as int, xx)
                } by {
                    lemma_row_px(w as int, bpp as int, sy as int, xx);
                    assert(r0@[0 + xx] == r0@[xx]);
                }
            }
        }
        while x < pw
            invariant
                simd ==> verilith_simd::cpu::avx2(),
                im == (Rgb { w: w as int, h: h as int, bpp: bpp as int, px: px@ }),
                im_ok(im),
                y < ph,
                sy as int == min(y as int, h - 1),
                x <= pw,
                r0@.len() == x && r1@.len() == x && r2@.len() == x,
                forall|xx: int| 0 <= xx < x ==> (#[trigger] r0@[xx]) as int == full(im, 0, y as int, xx),
                forall|xx: int| 0 <= xx < x ==> (#[trigger] r1@[xx]) as int == full(im, 1, y as int, xx),
                forall|xx: int| 0 <= xx < x ==> (#[trigger] r2@[xx]) as int == full(im, 2, y as int, xx),
            decreases pw - x,
        {
            let sx = if x < w {
                x
            } else {
                w - 1
            };
            proof {
                lemma_pix(w as int, h as int, bpp as int, sy as int, sx as int);
                assert(px@.len() == px.len());
            }
            let i = (sy * w + sx) * bpp;
            let (cy, cb, cr) = ycc_x(px[i], px[i + 1], px[i + 2]);
            r0.push(cy);
            r1.push(cb);
            r2.push(cr);
            x += 1;
        }
        p0.push(r0);
        p1.push(r1);
        p2.push(r2);
        y += 1;
    }
    (p0, p1, p2)
}

/// `h2v2_downsample`: chroma at half resolution, `ph2` rows of `pw2`.
fn down_plane(fp: &Vec<Vec<u8>>, pw2: usize, ph2: usize, hh: usize, Ghost(im): Ghost<Rgb>, Ghost(c): Ghost<int>) -> (r:
    Vec<Vec<u8>>)
    requires
        1 <= c < 3,
        im_ok(im),
        hh as int == (im.h + 1) / 2,
        2 * hh <= fp@.len(),
        pw2 < 0x4000_0000,
        plane_full(fp@, im, c, 2 * pw2, fp@.len() as int),
    ensures
        plane_samp(r@, im, true, c, pw2 as int, ph2 as int),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut y: usize = 0;
    while y < ph2
        invariant
            1 <= c < 3,
            im_ok(im),
            hh as int == (im.h + 1) / 2,
            2 * hh <= fp@.len(),
            pw2 < 0x4000_0000,
            plane_full(fp@, im, c, 2 * pw2, fp@.len() as int),
            y <= ph2,
            out@.len() == y,
            forall|yy: int| 0 <= yy < y ==> (#[trigger] out@[yy])@.len() == pw2,
            forall|yy: int, x: int|
                0 <= yy < y && 0 <= x < pw2 ==> (#[trigger] out@[yy]@[x]) as int == samp(im, true, c, yy, x),
        decreases ph2 - y,
    {
        let sy = if y < hh {
            y
        } else {
            hh - 1
        };
        let ra = &fp[2 * sy];
        let rb = &fp[2 * sy + 1];
        let mut row: Vec<u8> = Vec::with_capacity(pw2);
        let mut x: usize = 0;
        while x < pw2
            invariant
                1 <= c < 3,
                im_ok(im),
                hh as int == (im.h + 1) / 2,
                2 * hh <= fp@.len(),
                pw2 < 0x4000_0000,
                plane_full(fp@, im, c, 2 * pw2, fp@.len() as int),
                y < ph2,
                sy as int == min(y as int, hh - 1),
                *ra == fp@[2 * sy],
                *rb == fp@[2 * sy + 1],
                x <= pw2,
                row@.len() == x,
                forall|xx: int| 0 <= xx < x ==> (#[trigger] row@[xx]) as int == samp(im, true, c, y as int, xx),
            decreases pw2 - x,
        {
            let s = ra[2 * x] as u32 + ra[2 * x + 1] as u32 + rb[2 * x] as u32 + rb[2 * x + 1] as u32 + 1 + (x % 2) as u32;
            proof {
                let yy = sy as int;
                assert(ra@[2 * x] as int == full(im, c, 2 * yy, 2 * x));
                assert(ra@[2 * x + 1] as int == full(im, c, 2 * yy, 2 * x + 1));
                assert(rb@[2 * x] as int == full(im, c, 2 * yy + 1, 2 * x));
                assert(rb@[2 * x + 1] as int == full(im, c, 2 * yy + 1, 2 * x + 1));
            }
            row.push((s / 4) as u8);
            x += 1;
        }
        out.push(row);
        y += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------
/// The 64 samples of block (`bx`, `by`) of a plane, less 128.
pub open spec fn pblock(pl: Seq<Vec<u8>>, bx: int, by: int) -> Seq<int> {
    Seq::new(64, |i: int| pl[8 * by + i / 8]@[8 * bx + i % 8] as int - 128)
}

pub open spec fn qblock(s: Seq<int>, q: Seq<u8>) -> Seq<i16> {
    let t = fdct(s);
    Seq::new(64, |k: int| quant(t[k], q[k] as int, k) as i16)
}

/// The forward DCT of block (`bx`, `by`) of a plane.
fn fdct_plane(pl: &Vec<Vec<u8>>, bx: usize, by: usize) -> (t: [i64; 64])
    requires
        8 * by + 8 <= pl@.len(),
        forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
        bx < 0x1000_0000,
        by < 0x1000_0000,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] t[i] as int == fdct(pblock(pl@, bx as int, by as int))[i],
        forall|i: int| 0 <= i < 64 ==> -(1i64 << 20) <= #[trigger] t[i] <= (1i64 << 20),
{
    let mut s = [0i64; 64];
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            bx < 0x1000_0000,
            by < 0x1000_0000,
            8 * by + 8 <= pl@.len(),
            forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] s[j] as int == pblock(pl@, bx as int, by as int)[j],
            forall|j: int| 0 <= j < i ==> -128 <= #[trigger] s[j] <= 128,
        decreases 64 - i,
    {
        let row = &pl[8 * by + i / 8];
        s[i] = row[8 * bx + i % 8] as i64 - 128;
        i += 1;
    }
    proof {
        assert(s64(s) =~= pblock(pl@, bx as int, by as int));
    }
    fdct_x(&s)
}

/// A block's samples transformed and quantized.
fn real_block_x(pl: &Vec<Vec<u8>>, bx: usize, by: usize, q: &[u8; 64], rq: &[u64; 64], simd: bool) -> (r: [i16; 64])
    requires
        simd ==> verilith_simd::cpu::avx2(),
        forall|i: int| 0 <= i < 64 ==> #[trigger] rq[i] as int == (0x1_0000_0000 + 8 * q[i] - 1) / (8 * q[i] as int) && rq[i] <= 0x2000_0100,
        8 * by + 8 <= pl@.len(),
        forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
        forall|i: int| 0 <= i < 64 ==> #[trigger] q[i] >= 1,
        bx < 0x1000_0000,
        by < 0x1000_0000,
    ensures
        r@ == qblock(pblock(pl@, bx as int, by as int), q@),
{
    // `fdct_block` enables AVX2, which makes it unsafe to call, on x86-64;
    // `simd` says the CPU has it.
    let t = if simd {
        #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
        let t = unsafe { crate::fdct_avx2::fdct_block(pl, bx, by) };
        t
    } else {
        fdct_plane(pl, bx, by)
    };
    let mut r = [0i16; 64];
    let mut k: usize = 0;
    while k < 64
        invariant
            k <= 64,
            forall|i: int| 0 <= i < 64 ==> #[trigger] q[i] >= 1,
            forall|i: int| 0 <= i < 64 ==> #[trigger] rq[i] as int == (0x1_0000_0000 + 8 * q[i] - 1) / (8 * q[i] as int) && rq[i] <= 0x2000_0100,
            forall|i: int| 0 <= i < 64 ==> #[trigger] t[i] as int == fdct(pblock(pl@, bx as int, by as int))[i],
            forall|i: int| 0 <= i < 64 ==> -(1i64 << 20) <= #[trigger] t[i] <= (1i64 << 20),
            forall|j: int| 0 <= j < k ==> #[trigger] r[j] == qblock(pblock(pl@, bx as int, by as int), q@)[j],
        decreases 64 - k,
    {
        r[k] = quant_r(t[k], q[k], rq[k], k);
        k += 1;
    }
    proof {
        assert(r@ =~= qblock(pblock(pl@, bx as int, by as int), q@));
    }
    r
}

proof fn lemma_real(pl: Seq<Vec<u8>>, im: Rgb, sub: bool, quality: int, c: int, bx: int, by: int, wd: int, ht: int)
    requires
        plane_samp(pl, im, sub, c, wd, ht),
        0 <= bx,
        0 <= by,
        8 * bx + 8 <= wd,
        8 * by + 8 <= ht,
    ensures
        qblock(pblock(pl, bx, by), qtab_of(quality, c)) == real_block(im, sub, quality, c, bx, by),
{
    assert forall|i: int| 0 <= i < 64 implies pblock(pl, bx, by)[i] == block_samples(im, sub, c, bx, by)[i] by {
        assert(0 <= i / 8 < 8 && 0 <= i % 8 < 8);
        assert(pl[8 * by + i / 8]@[8 * bx + i % 8] as int == samp(im, sub, c, 8 * by + i / 8, 8 * bx + i % 8));
    }
    assert(pblock(pl, bx, by) =~= block_samples(im, sub, c, bx, by));
    assert(qblock(pblock(pl, bx, by), qtab_of(quality, c)) =~= real_block(im, sub, quality, c, bx, by));
}

proof fn lemma_quant_range(t: int, q: int, k: int)
    ensures
        -1024 <= quant(t, q, k) <= 1023,
        k != 0 ==> quant(t, q, k) != -1024,
{
}

proof fn lemma_block_range(im: Rgb, sub: bool, quality: int, c: int, bx: int, by: int, k: int)
    requires
        0 <= k < 64,
    ensures
        -1024 <= coef_block(im, sub, quality, c, bx, by)[k] <= 1023,
        k != 0 ==> coef_block(im, sub, quality, c, bx, by)[k] != -1024,
{
    let f = enc_frame_of(im, sub);
    let q = qtab_of(quality, c);
    if bx < wb(f, c) && by < hb(f, c) {
        let t = fdct(block_samples(im, sub, c, bx, by));
        lemma_quant_range(t[k], q[k] as int, k);
    } else {
        let h0 = f.comps[0].h as int;
        let (rx, ry) = if by < hb(f, c) {
            (wb(f, c) - 1, by)
        } else {
            (min(bx - bx % h0 + h0 - 1, wb(f, c) - 1), hb(f, c) - 1)
        };
        let t = fdct(block_samples(im, sub, c, rx, ry));
        lemma_quant_range(t[0], q[0] as int, 0);
    }
}

/// The block coded at (`bx`, `by`) of component `c`: the image's, or a
/// dummy past it (zero AC, the DC of the last real block before it).
fn coef_block_x(
    pl: &Vec<Vec<u8>>,
    bx: usize,
    by: usize,
    wbc: usize,
    hbc: usize,
    h0: usize,
    q: &[u8; 64],
    rq: &[u64; 64],
    simd: bool,
    Ghost(im): Ghost<Rgb>,
    Ghost(sub): Ghost<bool>,
    Ghost(quality): Ghost<int>,
    Ghost(c): Ghost<int>,
) -> (r: [i16; 64])
    requires
        simd ==> verilith_simd::cpu::avx2(),
        forall|i: int| 0 <= i < 64 ==> #[trigger] rq[i] as int == (0x1_0000_0000 + 8 * q[i] - 1) / (8 * q[i] as int) && rq[i] <= 0x2000_0100,
        0 <= c < 3,
        plane_samp(pl@, im, sub, c, 8 * cw(enc_frame_of(im, sub), c), 8 * ch(enc_frame_of(im, sub), c)),
        wbc as int == wb(enc_frame_of(im, sub), c),
        hbc as int == hb(enc_frame_of(im, sub), c),
        1 <= wbc <= cw(enc_frame_of(im, sub), c),
        1 <= hbc <= ch(enc_frame_of(im, sub), c),
        h0 as int == enc_frame_of(im, sub).comps[0].h,
        1 <= h0 <= 2,
        q@ == qtab_of(quality, c),
        forall|i: int| 0 <= i < 64 ==> #[trigger] q[i] >= 1,
        bx < 0x1000_0000,
        by < 0x1000_0000,
        wbc < 0x1000_0000,
        hbc < 0x1000_0000,
    ensures
        r@ == coef_block(im, sub, quality, c, bx as int, by as int),
{
    let ghost f = enc_frame_of(im, sub);
    if bx < wbc && by < hbc {
        proof {
            lemma_real(pl@, im, sub, quality, c, bx as int, by as int, 8 * cw(f, c), 8 * ch(f, c));
        }
        real_block_x(pl, bx, by, q, rq, simd)
    } else {
        let (rx, ry) = if by < hbc {
            (wbc - 1, by)
        } else {
            proof {
                lemma_mod_decreases(bx as nat, h0 as nat);
            }
            let e = bx - bx % h0 + h0 - 1;
            (if e < wbc - 1 {
                e
            } else {
                wbc - 1
            }, hbc - 1)
        };
        proof {
            lemma_real(pl@, im, sub, quality, c, rx as int, ry as int, 8 * cw(f, c), 8 * ch(f, c));
        }
        let rb = real_block_x(pl, rx, ry, q, rq, simd);
        let mut r = [0i16; 64];
        r[0] = rb[0];
        proof {
            assert(r@ =~= coef_block(im, sub, quality, c, bx as int, by as int));
        }
        r
    }
}

// ---------------------------------------------------------------------------
// Headers
// ---------------------------------------------------------------------------
fn push_slice(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost o = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == o + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        out.push(s[i]);
        i += 1;
        proof {
            assert(o + s@.subrange(0, i as int) =~= (o + s@.subrange(0, i - 1)).push(s@[i - 1]));
        }
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
}

/// The number of symbols of a table.
fn total_x(t: &HuffTab) -> (n: usize)
    requires
        huff_ok(t@),
    ensures
        n as int == total(t@),
        n <= 256,
{
    let mut n: usize = 0;
    let mut l: usize = 1;
    while l <= 16
        invariant
            1 <= l <= 17,
            n as int == hbase(t@, l as int),
            n <= 255 * (l - 1),
        decreases 17 - l,
    {
        n += t.counts[l - 1] as usize;
        l += 1;
    }
    n
}

/// The table can go in the file.
fn tab_ok_x(t: &HuffTab) -> (r: bool)
    ensures
        r ==> tab_ok(t@),
{
    if derive(t, false).is_none() {
        return false;
    }
    let n = total_x(t);
    let mut i = n;
    while i < 256
        invariant
            n <= i <= 256,
            n as int == total(t@),
            forall|j: int| n <= j < i ==> #[trigger] t.vals[j] == 0,
        decreases 256 - i,
    {
        if t.vals[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

fn write_dqt(out: &mut Vec<u8>, n: u8, q: &[u8; 64])
    ensures
        final(out)@ == old(out)@ + dqt_seg(n, q@),
{
    let ghost o = out@;
    push_slice(out, &[0xFF, 0xDB, 0, 67, n]);
    let ghost o2 = out@;
    proof {
        lemma_zz_perm();
    }
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            o2 == o + seq![0xFFu8, 0xDB, 0, 67, n],
            forall|j: int| 0 <= j < 64 ==> 0 <= zz(j) < 64 && #[trigger] zzi(zz(j)) == j,
            out@ == o2 + Seq::new(i as nat, |j: int| q@[zz(j)]),
        decreases 64 - i,
    {
        proof {
            assert(zzi(zz(i as int)) == i);
        }
        let z = ZZ[i] as usize;
        out.push(q[z]);
        i += 1;
        proof {
            assert(o2 + Seq::new(i as nat, |j: int| q@[zz(j)]) =~= (o2 + Seq::new((i - 1) as nat, |j: int| q@[zz(j)])).push(
                q@[zz(i - 1)],
            ));
        }
    }
    proof {
        assert(out@ =~= o + dqt_seg(n, q@));
    }
}

fn write_dht(out: &mut Vec<u8>, tc: u8, t: &HuffTab)
    requires
        tab_ok(t@),
    ensures
        final(out)@ == old(out)@ + dht_seg(tc, t@),
{
    let ghost o = out@;
    let n = total_x(t);
    let len = 19 + n;
    push_slice(out, &[0xFF, 0xC4, (len / 256) as u8, (len % 256) as u8, tc]);
    push_slice(out, &t.counts);
    push_slice(out, t.vals.split_at(n).0);
    proof {
        assert(out@ =~= o + dht_seg(tc, t@));
    }
}

fn write_headers(out: &mut Vec<u8>, w: usize, h: usize, hv: u8, q0: &[u8; 64], q1: &[u8; 64], ht: &[HuffTab; 4])
    requires
        old(out)@.len() == 0,
        w <= 65535,
        h <= 65535,
        forall|i: int| 0 <= i < 4 ==> tab_ok(#[trigger] ht[i]@),
    ensures
        final(out)@ == headers(w as int, h as int, hv, q0@, q1@, seq![ht[0]@, ht[1]@, ht[2]@, ht[3]@]),
{
    push_slice(out, &[0xFF, 0xD8]);
    push_slice(out, &[0xFF, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0]);
    write_dqt(out, 0, q0);
    write_dqt(out, 1, q1);
    push_slice(
        out,
        &[
            0xFF,
            0xC0,
            0,
            17,
            8,
            (h / 256) as u8,
            (h % 256) as u8,
            (w / 256) as u8,
            (w % 256) as u8,
            3,
            1,
            hv,
            0,
            2,
            0x11,
            1,
            3,
            0x11,
            1,
        ],
    );
    proof {
        assert(tab_ok(ht[0]@) && tab_ok(ht[1]@) && tab_ok(ht[2]@) && tab_ok(ht[3]@));
    }
    write_dht(out, 0x00, &ht[0]);
    write_dht(out, 0x10, &ht[1]);
    write_dht(out, 0x01, &ht[2]);
    write_dht(out, 0x11, &ht[3]);
    push_slice(out, &[0xFF, 0xDA, 0, 12, 3, 1, 0, 2, 0x11, 3, 0x11, 0, 63, 0]);
    proof {
        let ghost hts = seq![ht[0]@, ht[1]@, ht[2]@, ht[3]@];
        assert(out@ =~= headers(w as int, h as int, hv, q0@, q1@, hts));
    }
}

// ---------------------------------------------------------------------------
// Geometry
// ---------------------------------------------------------------------------
pub open spec fn h0_of(sub: bool) -> int {
    if sub {
        2
    } else {
        1
    }
}

/// The encoder's frame, and its sizes in the encoder's terms.
proof fn lemma_frame(im: Rgb, sub: bool)
    requires
        im_ok(im),
    ensures
        ({
            let f = enc_frame_of(im, sub);
            let h0 = h0_of(sub);
            &&& enc_frame(f)
            &&& f.comps[0].h == h0 && f.comps[0].v == h0
            &&& maxh(f) == h0 && maxv(f) == h0
            &&& mcux(f) == (im.w + 8 * h0 - 1) / (8 * h0)
            &&& mcuy(f) == (im.h + 8 * h0 - 1) / (8 * h0)
            &&& 1 <= mcux(f) <= 8200 && 1 <= mcuy(f) <= 8200
            &&& cw(f, 0) == mcux(f) * h0 && ch(f, 0) == mcuy(f) * h0
            &&& cw(f, 1) == mcux(f) && cw(f, 2) == mcux(f)
            &&& ch(f, 1) == mcuy(f) && ch(f, 2) == mcuy(f)
            &&& wb(f, 0) == (im.w * h0 + 8 * h0 - 1) / (8 * h0)
            &&& hb(f, 0) == (im.h * h0 + 8 * h0 - 1) / (8 * h0)
            &&& wb(f, 1) == mcux(f) && wb(f, 2) == mcux(f)
            &&& hb(f, 1) == mcuy(f) && hb(f, 2) == mcuy(f)
            &&& 1 <= wb(f, 0) <= cw(f, 0) && 1 <= hb(f, 0) <= ch(f, 0)
            &&& mcu_blocks(f, enc_scan_hdr()) == h0 * h0 + 2
            &&& n_mcus(f) == mcux(f) * mcuy(f)
            &&& 8 * mcuy(f) * h0 >= im.h
        }),
{
    let f = enc_frame_of(im, sub);
    let h0 = h0_of(sub);
    assert(enc_frame(f));
    lemma_geom(f);
    let d = 8 * h0;
    let mx = (im.w + d - 1) / d;
    let my = (im.h + d - 1) / d;
    lemma_fundamental_div_mod(im.w + d - 1, d);
    lemma_fundamental_div_mod(im.h + d - 1, d);
    lemma_mod_bound(im.w + d - 1, d);
    lemma_mod_bound(im.h + d - 1, d);
    lemma_mul_is_commutative(mx, d);
    lemma_mul_is_commutative(my, d);
    assert(mx * d >= im.w);
    assert(my * d >= im.h);
    assert(mx <= 8200 && my <= 8200) by {
        lemma_div_is_ordered(im.w + d - 1, 65515int, d);
        lemma_div_is_ordered(im.h + d - 1, 65515int, d);
        lemma_div_is_ordered_by_denominator(65515, 8, d);
    }
    if sub {
        let wb0 = (im.w * 2 + 15) / 16;
        lemma_fundamental_div_mod(im.w * 2 + 15, 16);
        lemma_mod_bound(im.w * 2 + 15, 16);
        assert(wb0 <= 2 * mx);
        assert(wb0 >= 1);
        let hb0 = (im.h * 2 + 15) / 16;
        lemma_fundamental_div_mod(im.h * 2 + 15, 16);
        lemma_mod_bound(im.h * 2 + 15, 16);
        assert(hb0 <= 2 * my);
        assert(hb0 >= 1);
    }
    assert(8 * mcuy(f) * h0 >= im.h) by (nonlinear_arith)
        requires
            mcuy(f) == my,
            my * d >= im.h,
            d == 8 * h0,
    ;
}

/// Block `b` of MCU (`mxi`, `myi`): component `c`'s block (`bx`, `by`).
#[verifier::rlimit(60)]
proof fn lemma_blk(im: Rgb, sub: bool, quality: int, mxi: int, myi: int, b: int, c: int, bx: int, by: int)
    requires
        im_ok(im),
        0 <= mxi < mcux(enc_frame_of(im, sub)),
        0 <= myi < mcuy(enc_frame_of(im, sub)),
        0 <= b < h0_of(sub) * h0_of(sub) + 2,
        c == (if b < h0_of(sub) * h0_of(sub) {
            0
        } else {
            b - h0_of(sub) * h0_of(sub) + 1
        }),
        bx == (if c == 0 {
            mxi * h0_of(sub) + b % h0_of(sub)
        } else {
            mxi
        }),
        by == (if c == 0 {
            myi * h0_of(sub) + b / h0_of(sub)
        } else {
            myi
        }),
    ensures
        ({
            let f = enc_frame_of(im, sub);
            let m = myi * mcux(f) + mxi;
            let idx = by * cw(f, c) + bx;
            &&& 0 <= m < n_mcus(f)
            &&& 0 <= bx < cw(f, c) && 0 <= by < ch(f, c)
            &&& blk_index(f, enc_scan_hdr(), m, b) == (c, idx)
            &&& blk(enc_coefs(im, sub, quality), c, idx) == coef_block(im, sub, quality, c, bx, by)
        }),
{
    let f = enc_frame_of(im, sub);
    let s = enc_scan_hdr();
    lemma_frame(im, sub);
    let h0 = h0_of(sub);
    let mx = mcux(f);
    let my = mcuy(f);
    let m = myi * mx + mxi;
    assert(0 <= m < mx * my) by (nonlinear_arith)
        requires
            0 <= mxi < mx,
            0 <= myi < my,
            m == myi * mx + mxi,
    ;
    lemma_fundamental_div_mod_converse(m, mx, myi, mxi);
    lemma_slot(f, b);
    assert(comp_of(f, b) == c);
    let off = if c == 0 {
        b
    } else {
        0
    };
    let h = f.comps[c].h as int;
    let v = f.comps[c].v as int;
    assert(h == v);
    let w = cw(f, c);
    assert(0 <= off < h * v);
    lemma_fundamental_div_mod(off, h);
    lemma_mod_bound(off, h);
    lemma_div_pos_is_pos(off, h);
    assert(off / h < v) by {
        lemma_multiply_divide_lt(off, h, v);
    }
    assert(bx == mxi * h + off % h);
    assert(by == myi * v + off / h);
    assert(w == mx * h);
    assert(ch(f, c) == my * v);
    assert(0 <= bx < w) by (nonlinear_arith)
        requires
            0 <= mxi < mx,
            0 <= off % h < h,
            w == mx * h,
            bx == mxi * h + off % h,
    ;
    assert(0 <= by < my * v) by (nonlinear_arith)
        requires
            0 <= myi < my,
            0 <= off / h < v,
            v >= 1,
            by == myi * v + off / h,
    ;
    let idx = by * w + bx;
    assert(blk_index(f, s, m, b) == (c, idx));
    assert(0 <= idx < w * ch(f, c)) by (nonlinear_arith)
        requires
            0 <= bx < w,
            0 <= by < ch(f, c),
            idx == by * w + bx,
    ;
    lemma_fundamental_div_mod_converse(idx, w, by, bx);
    let a = enc_coefs(im, sub, quality);
    assert(a[c].len() == 64 * w * ch(f, c));
    assert(64 * idx + 64 <= 64 * w * ch(f, c)) by (nonlinear_arith)
        requires
            idx < w * ch(f, c),
    ;
    assert forall|j: int| 0 <= j < 64 implies #[trigger] blk(a, c, idx)[j] == coef_block(im, sub, quality, c, bx, by)[j] by {
        lemma_fundamental_div_mod_converse(64 * idx + j, 64, idx, j);
        assert(a[c][64 * idx + j] == coef_block(im, sub, quality, c, idx % w, idx / w)[j]);
    }
    assert(blk(a, c, idx) =~= coef_block(im, sub, quality, c, bx, by));
}

/// The coefficients are ones the encoder can code.
proof fn lemma_coefs_ok(im: Rgb, sub: bool, quality: int)
    requires
        im_ok(im),
    ensures
        coefs_ok(enc_frame_of(im, sub), enc_coefs(im, sub, quality)),
{
    let f = enc_frame_of(im, sub);
    let a = enc_coefs(im, sub, quality);
    lemma_frame(im, sub);
    assert forall|c: int, j: int| 0 <= c < 3 && 0 <= j < a[c].len() implies -1024 <= #[trigger] a[c][j] <= 1023 && (j
        % 64 != 0 ==> a[c][j] != -1024) by {
        lemma_mod_bound(j, 64);
        lemma_block_range(im, sub, quality, c, (j / 64) % cw(f, c), (j / 64) / cw(f, c), j % 64);
    }
}

// ---------------------------------------------------------------------------
// The MCUs
// ---------------------------------------------------------------------------
/// What the MCU loop works from.
pub struct Enc {
    pub py: Vec<Vec<u8>>,
    pub pcb: Vec<Vec<u8>>,
    pub pcr: Vec<Vec<u8>>,
    /// DC and AC codes of luma, then of chroma.
    pub e: [ETab; 4],
    pub q0: [u8; 64],
    pub q1: [u8; 64],
    /// Their reciprocals, for `quant_r`.
    pub r0: [u64; 64],
    pub r1: [u64; 64],
    pub wbs: [usize; 3],
    pub hbs: [usize; 3],
    pub h0: usize,
    pub mx: usize,
    pub my: usize,
    /// The CPU has AVX2.
    pub simd: bool,
}

pub open spec fn rq_ok(q: [u8; 64], rq: [u64; 64]) -> bool {
    forall|i: int| 0 <= i < 64 ==> #[trigger] rq[i] as int == (0x1_0000_0000 + 8 * q[i] - 1) / (8 * q[i] as int) && rq[i] <= 0x2000_0100
}

fn recips(q: &[u8; 64]) -> (rq: [u64; 64])
    requires
        forall|i: int| 0 <= i < 64 ==> #[trigger] q[i] >= 1,
    ensures
        rq_ok(*q, rq),
{
    let mut rq = [0u64; 64];
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            forall|j: int| 0 <= j < 64 ==> #[trigger] q[j] >= 1,
            forall|j: int|
                0 <= j < i ==> #[trigger] rq[j] as int == (0x1_0000_0000 + 8 * q[j] - 1) / (8 * q[j] as int) && rq[j]
                    <= 0x2000_0100,
        decreases 64 - i,
    {
        rq[i] = recip(q[i]);
        i += 1;
    }
    rq
}

pub open spec fn pseq(p: [i32; 3]) -> Seq<int> {
    seq![p[0] as int, p[1] as int, p[2] as int]
}

pub open spec fn pr_ok(p: [i32; 3]) -> bool {
    forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] p[i] <= 1023
}

impl Enc {
    pub open spec fn codes(&self) -> Codes {
        Codes {
            dco: seq![self.e[0].co@, self.e[2].co@],
            dsi: seq![self.e[0].si@, self.e[2].si@],
            aco: seq![self.e[1].co@, self.e[3].co@],
            asi: seq![self.e[1].si@, self.e[3].si@],
        }
    }

    pub open spec fn pl(&self, c: int) -> Seq<Vec<u8>> {
        if c == 0 {
            self.py@
        } else if c == 1 {
            self.pcb@
        } else {
            self.pcr@
        }
    }

    pub open spec fn ok(&self, im: Rgb, sub: bool, quality: int, ht: Seq<HuffTable>) -> bool {
        let f = enc_frame_of(im, sub);
        &&& im_ok(im)
        &&& (self.simd ==> verilith_simd::cpu::avx2())
        &&& self.h0 as int == h0_of(sub)
        &&& self.mx as int == mcux(f)
        &&& self.my as int == mcuy(f)
        &&& forall|c: int| 0 <= c < 3 ==> plane_samp(#[trigger] self.pl(c), im, sub, c, 8 * cw(f, c), 8 * ch(f, c))
        &&& forall|c: int|
            0 <= c < 3 ==> #[trigger] self.wbs[c] as int == wb(f, c) && self.hbs[c] as int == hb(f, c)
        &&& self.q0@ == qtab(quality, 0)
        &&& self.q1@ == qtab(quality, 1)
        &&& forall|i: int| 0 <= i < 64 ==> #[trigger] self.q0[i] >= 1 && self.q1[i] >= 1
        &&& rq_ok(self.q0, self.r0) && rq_ok(self.q1, self.r1)
        &&& ht.len() == 4
        &&& dc_ready(ht[0], self.e[0].co@, self.e[0].si@) && self.e[0].has(ht[0])
        &&& ac_ready(ht[1], self.e[1].co@, self.e[1].si@) && self.e[1].has(ht[1])
        &&& dc_ready(ht[2], self.e[2].co@, self.e[2].si@) && self.e[2].has(ht[2])
        &&& ac_ready(ht[3], self.e[3].co@, self.e[3].si@) && self.e[3].has(ht[3])
    }
}

proof fn lemma_mcu_step(
    f: Frame,
    k: Codes,
    a: Seq<Seq<i16>>,
    m: int,
    b: int,
    pc: Seq<int>,
    c: int,
    idx: int,
    bl: Seq<i16>,
    bits: Seq<bool>,
    nbits: Seq<bool>,
)
    requires
        0 <= b < mcu_blocks(f, enc_scan_hdr()),
        blk_index(f, enc_scan_hdr(), m, b) == (c, idx),
        blk(a, c, idx) == bl,
        nbits == bits + block_bits(
            k.dco[enc_scan_hdr().td[c]],
            k.dsi[enc_scan_hdr().td[c]],
            k.aco[enc_scan_hdr().td[c]],
            k.asi[enc_scan_hdr().td[c]],
            bl,
            pc[c],
        ),
    ensures
        nbits + enc_mcu(f, k, a, m, b + 1, pc.update(c, bl[0] as int)).0 == bits + enc_mcu(f, k, a, m, b, pc).0,
        enc_mcu(f, k, a, m, b + 1, pc.update(c, bl[0] as int)).1 == enc_mcu(f, k, a, m, b, pc).1,
{
    let r = enc_mcu(f, k, a, m, b + 1, pc.update(c, bl[0] as int));
    let bb = nbits.subrange(bits.len() as int, nbits.len() as int);
    assert(enc_mcu(f, k, a, m, b, pc).0 == block_bits(
        k.dco[enc_scan_hdr().td[c]],
        k.dsi[enc_scan_hdr().td[c]],
        k.aco[enc_scan_hdr().td[c]],
        k.asi[enc_scan_hdr().td[c]],
        bl,
        pc[c],
    ) + r.0);
    assert(nbits + r.0 =~= bits + enc_mcu(f, k, a, m, b, pc).0);
}

/// Codes block `b` of MCU (`mxi`, `myi`).
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn block_x(
    e: &Enc,
    bw: &mut BitWriter,
    preds: &mut [i32; 3],
    mxi: usize,
    myi: usize,
    b: usize,
    Ghost(im): Ghost<Rgb>,
    Ghost(sub): Ghost<bool>,
    Ghost(quality): Ghost<int>,
    Ghost(ht): Ghost<Seq<HuffTable>>,
)
    requires
        e.ok(im, sub, quality, ht),
        mxi < e.mx,
        myi < e.my,
        b < e.h0 * e.h0 + 2,
        old(bw).wf(),
        pr_ok(*old(preds)),
    ensures
        final(bw).wf(),
        pr_ok(*final(preds)),
        final(bw).bits@ + enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            b + 1,
            pseq(*final(preds)),
        ).0 == old(bw).bits@ + enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            b as int,
            pseq(*old(preds)),
        ).0,
        enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            b + 1,
            pseq(*final(preds)),
        ).1 == enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            b as int,
            pseq(*old(preds)),
        ).1,
{
    hide(enc_mcu);
    hide(enc_coefs);
    hide(coef_block);
    hide(plane_samp);
    hide(dc_ready);
    hide(ac_ready);
    let ghost f = enc_frame_of(im, sub);
    let ghost k = e.codes();
    let ghost a = enc_coefs(im, sub, quality);
    let ghost m = myi * e.mx + mxi;
    proof {
        lemma_frame(im, sub);
    }
    let h0 = e.h0;
    proof {
        assert(mxi * h0 <= 8200 * 2 && myi * h0 <= 8200 * 2) by (nonlinear_arith)
            requires
                mxi <= 8200,
                myi <= 8200,
                h0 <= 2,
        ;
    }
    let n0 = h0 * h0;
    let c: usize;
    let bx: usize;
    let by: usize;
    if b < n0 {
        c = 0;
        bx = mxi * h0 + b % h0;
        by = myi * h0 + b / h0;
    } else {
        c = b - n0 + 1;
        bx = mxi;
        by = myi;
    }
    proof {
        lemma_blk(im, sub, quality, mxi as int, myi as int, b as int, c as int, bx as int, by as int);
        assert(plane_samp(e.pl(c as int), im, sub, c as int, 8 * cw(f, c as int), 8 * ch(f, c as int)));
        assert(e.wbs[c as int] as int == wb(f, c as int));
        assert(e.hbs[c as int] as int == hb(f, c as int));
    }
    let pl = if c == 0 {
        &e.py
    } else if c == 1 {
        &e.pcb
    } else {
        &e.pcr
    };
    let q = if c == 0 {
        &e.q0
    } else {
        &e.q1
    };
    let rq = if c == 0 {
        &e.r0
    } else {
        &e.r1
    };
    let bk = coef_block_x(
        pl,
        bx,
        by,
        e.wbs[c],
        e.hbs[c],
        h0,
        q,
        rq,
        e.simd,
        Ghost(im),
        Ghost(sub),
        Ghost(quality),
        Ghost(c as int),
    );
    proof {
        assert forall|i: int| 1 <= i < 64 implies -1024 < #[trigger] bk@[i] < 1024 by {
            lemma_block_range(im, sub, quality, c as int, bx as int, by as int, i);
        }
        lemma_block_range(im, sub, quality, c as int, bx as int, by as int, 0);
        assert(pr_ok(*preds) && -1024 <= preds[c as int] <= 1023);
    }
    let ghost pc = pseq(*preds);
    let ghost bits = bw.bits@;
    let pred = preds[c];
    if c == 0 {
        encode_block(bw, &bk, pred, &e.e[0], &e.e[1], Ghost(ht[0]), Ghost(ht[1]));
    } else {
        encode_block(bw, &bk, pred, &e.e[2], &e.e[3], Ghost(ht[2]), Ghost(ht[3]));
    }
    preds[c] = bk[0] as i32;
    proof {
        lemma_mcu_step(f, k, a, m, b as int, pc, c as int, by * cw(f, c as int) + bx, bk@, bits, bw.bits@);
        assert(pc.update(c as int, bk@[0] as int) =~= pseq(*preds));
    }
}

/// Codes MCU (`mxi`, `myi`).
fn mcu_x(
    e: &Enc,
    bw: &mut BitWriter,
    preds: &mut [i32; 3],
    mxi: usize,
    myi: usize,
    Ghost(im): Ghost<Rgb>,
    Ghost(sub): Ghost<bool>,
    Ghost(quality): Ghost<int>,
    Ghost(ht): Ghost<Seq<HuffTable>>,
)
    requires
        e.ok(im, sub, quality, ht),
        mxi < e.mx,
        myi < e.my,
        old(bw).wf(),
        pr_ok(*old(preds)),
    ensures
        final(bw).wf(),
        pr_ok(*final(preds)),
        final(bw).bits@ == old(bw).bits@ + enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            0,
            pseq(*old(preds)),
        ).0,
        pseq(*final(preds)) == enc_mcu(
            enc_frame_of(im, sub),
            e.codes(),
            enc_coefs(im, sub, quality),
            myi * e.mx + mxi,
            0,
            pseq(*old(preds)),
        ).1,
{
    hide(enc_mcu);
    hide(enc_coefs);
    let ghost f = enc_frame_of(im, sub);
    let ghost k = e.codes();
    let ghost a = enc_coefs(im, sub, quality);
    let ghost m = myi * e.mx + mxi;
    let ghost b0 = bw.bits@;
    let ghost p0 = pseq(*preds);
    let ghost all = enc_mcu(f, k, a, m, 0, p0);
    proof {
        lemma_frame(im, sub);
    }
    let h0 = e.h0;
    let nb = h0 * h0 + 2;
    let mut b: usize = 0;
    while b < nb
        invariant
            e.ok(im, sub, quality, ht),
            f == enc_frame_of(im, sub),
            k == e.codes(),
            a == enc_coefs(im, sub, quality),
            m == myi * e.mx + mxi,
            mxi < e.mx,
            myi < e.my,
            h0 == e.h0,
            nb == h0 * h0 + 2,
            mcu_blocks(f, enc_scan_hdr()) == nb,
            all == enc_mcu(f, k, a, m, 0, p0),
            b <= nb,
            bw.wf(),
            pr_ok(*preds),
            bw.bits@ + enc_mcu(f, k, a, m, b as int, pseq(*preds)).0 == b0 + all.0,
            enc_mcu(f, k, a, m, b as int, pseq(*preds)).1 == all.1,
        decreases nb - b,
    {
        block_x(e, bw, preds, mxi, myi, b, Ghost(im), Ghost(sub), Ghost(quality), Ghost(ht));
        b += 1;
    }
    proof {
        reveal_with_fuel(enc_mcu, 1);
        assert(enc_mcu(f, k, a, m, nb as int, pseq(*preds)).0 == Seq::<bool>::empty());
        assert(bw.bits@ =~= b0 + all.0);
    }
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------
pub open spec fn rgb(px: Seq<u8>, w: usize, h: usize, bpp: usize) -> Rgb {
    Rgb { w: w as int, h: h as int, bpp: bpp as int, px }
}

/// Codes all the MCUs.
fn scan_x(e: &Enc, Ghost(im): Ghost<Rgb>, Ghost(sub): Ghost<bool>, Ghost(quality): Ghost<int>, Ghost(ht): Ghost<Seq<HuffTable>>) -> (r: BitWriter)
    requires
        e.ok(im, sub, quality, ht),
    ensures
        r.wf(),
        r.bits@ == enc_upto(enc_frame_of(im, sub), e.codes(), enc_coefs(im, sub, quality), n_mcus(enc_frame_of(im, sub))).0,
{
    hide(enc_mcu);
    hide(enc_coefs);
    let ghost f = enc_frame_of(im, sub);
    let ghost k = e.codes();
    let ghost a = enc_coefs(im, sub, quality);
    proof {
        lemma_frame(im, sub);
    }
    let mut bw = BitWriter::new(Vec::new());
    let mut preds: [i32; 3] = [0, 0, 0];
    proof {
        assert(pseq(preds) =~= seq![0int, 0int, 0int]);
    }
    let mut myi: usize = 0;
    while myi < e.my
        invariant
            e.ok(im, sub, quality, ht),
            f == enc_frame_of(im, sub),
            k == e.codes(),
            a == enc_coefs(im, sub, quality),
            myi <= e.my,
            e.mx <= 8200 && e.my <= 8200,
            bw.wf(),
            pr_ok(preds),
            bw.bits@ == enc_upto(f, k, a, myi * e.mx).0,
            pseq(preds) == enc_upto(f, k, a, myi * e.mx).1,
        decreases e.my - myi,
    {
        let mut mxi: usize = 0;
        while mxi < e.mx
            invariant
                e.ok(im, sub, quality, ht),
                f == enc_frame_of(im, sub),
                k == e.codes(),
                a == enc_coefs(im, sub, quality),
                myi < e.my,
                mxi <= e.mx,
                e.mx <= 8200 && e.my <= 8200,
                bw.wf(),
                pr_ok(preds),
                bw.bits@ == enc_upto(f, k, a, myi * e.mx + mxi).0,
                pseq(preds) == enc_upto(f, k, a, myi * e.mx + mxi).1,
            decreases e.mx - mxi,
        {
            let ghost m = myi * e.mx + mxi;
            mcu_x(e, &mut bw, &mut preds, mxi, myi, Ghost(im), Ghost(sub), Ghost(quality), Ghost(ht));
            proof {
                assert(m + 1 == myi * e.mx + (mxi + 1));
                assert(enc_upto(f, k, a, m + 1) == (
                    enc_upto(f, k, a, m).0 + enc_mcu(f, k, a, m, 0, enc_upto(f, k, a, m).1).0,
                    enc_mcu(f, k, a, m, 0, enc_upto(f, k, a, m).1).1,
                ));
            }
            mxi += 1;
        }
        proof {
            assert(myi * e.mx + e.mx == (myi + 1) * e.mx) by (nonlinear_arith);
        }
        myi += 1;
    }
    proof {
        assert(e.my * e.mx == n_mcus(f)) by (nonlinear_arith)
            requires
                n_mcus(f) == mcux(f) * mcuy(f),
                e.mx == mcux(f),
                e.my == mcuy(f),
        ;
    }
    bw
}

pub open spec fn hseq(ht: [HuffTab; 4]) -> Seq<HuffTable> {
    seq![ht[0]@, ht[1]@, ht[2]@, ht[3]@]
}

pub open spec fn tabs_ok(ht: [HuffTab; 4], e: [ETab; 4]) -> bool {
    let hts = hseq(ht);
    &&& forall|i: int| 0 <= i < 4 ==> tab_ok(#[trigger] hts[i])
    &&& huff_dc_ok(hts[0]) && huff_dc_ok(hts[2])
    &&& dc_ready(hts[0], e[0].co@, e[0].si@) && e[0].has(hts[0])
    &&& ac_ready(hts[1], e[1].co@, e[1].si@) && e[1].has(hts[1])
    &&& dc_ready(hts[2], e[2].co@, e[2].si@) && e[2].has(hts[2])
    &&& ac_ready(hts[3], e[3].co@, e[3].si@) && e[3].has(hts[3])
}

proof fn lemma_dc_ready(t: HuffTable, e: ETab)
    requires
        huff_ok(t),
        e.has(t),
        forall|s: int| 0 <= s <= 11 ==> #[trigger] e.si[s] > 0,
    ensures
        dc_ready(t, e.co@, e.si@),
{
    assert forall|s: int| 0 <= s <= 11 implies #[trigger] code_ok(t, e.co@, e.si@, s) by {
        assert(e.si[s] > 0);
    }
}

proof fn lemma_ac_ready(t: HuffTable, e: ETab)
    requires
        huff_ok(t),
        e.has(t),
        forall|s: int| ac_sym(s) ==> #[trigger] e.si[s] > 0,
    ensures
        ac_ready(t, e.co@, e.si@),
{
    assert forall|s: int| ac_sym(s) implies #[trigger] code_ok(t, e.co@, e.si@, s) by {
        assert(e.si[s] > 0);
    }
}

/// The typical Huffman tables and their codes.
fn tables() -> (r: Option<([HuffTab; 4], [ETab; 4])>)
    ensures
        r matches Some((ht, e)) ==> tabs_ok(ht, e),
{
    hide(std_table);
    hide(code_ok);
    let ht = [std_tab(&STD_DC_L), std_tab(&STD_AC_L), std_tab(&STD_DC_C), std_tab(&STD_AC_C)];
    if !(tab_ok_x(&ht[0]) && tab_ok_x(&ht[1]) && tab_ok_x(&ht[2]) && tab_ok_x(&ht[3])) {
        return None;
    }
    if derive(&ht[0], true).is_none() || derive(&ht[2], true).is_none() {
        return None;
    }
    let e0 = etab(&ht[0]);
    let e1 = etab(&ht[1]);
    let e2 = etab(&ht[2]);
    let e3 = etab(&ht[3]);
    if !(dc_check(&e0) && ac_check(&e1) && dc_check(&e2) && ac_check(&e3)) {
        return None;
    }
    let ghost hts = hseq(ht);
    proof {
        lemma_dc_ready(ht[0]@, e0);
        lemma_dc_ready(ht[2]@, e2);
        lemma_ac_ready(ht[1]@, e1);
        lemma_ac_ready(ht[3]@, e3);
        assert(hts[0] == ht[0]@ && hts[1] == ht[1]@ && hts[2] == ht[2]@ && hts[3] == ht[3]@);
        assert forall|i: int| 0 <= i < 4 implies tab_ok(#[trigger] hts[i]) by {
        }
    }
    let e = [e0, e1, e2, e3];
    proof {
        assert(e[0] == e0 && e[1] == e1 && e[2] == e2 && e[3] == e3);
    }
    Some((ht, e))
}

/// The planes and the rest of what the MCU loop works from.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn build(px: &[u8], w: usize, h: usize, bpp: usize, quality: u8, sub: bool, ht: &[HuffTab; 4], et: [ETab; 4]) -> (e: Enc)
    requires
        im_ok(rgb(px@, w, h, bpp)),
        tabs_ok(*ht, et),
    ensures
        e.ok(rgb(px@, w, h, bpp), sub, quality as int, hseq(*ht)),
        e.e == et,
{
    let ghost im = rgb(px@, w, h, bpp);
    let ghost f = enc_frame_of(im, sub);
    let ghost qi = quality as int;
    proof {
        lemma_frame(im, sub);
    }
    let q0 = qtab_x(quality, 0);
    let q1 = qtab_x(quality, 1);
    let h0: usize = if sub {
        2
    } else {
        1
    };
    let d = 8 * h0;
    let mx = (w + d - 1) / d;
    let my = (h + d - 1) / d;
    let pw = 8 * mx * h0;
    let ph = 8 * my * h0;
    let simd = verilith_simd::cpu::has_avx2();
    let (py, fcb, fcr) = full_planes(px, w, h, bpp, pw, ph, simd);
    let pcb;
    let pcr;
    if sub {
        proof {
            assert(2 * ((h as int + 1) / 2) <= ph);
        }
        pcb = down_plane(&fcb, 8 * mx, 8 * my, (h + 1) / 2, Ghost(im), Ghost(1));
        pcr = down_plane(&fcr, 8 * mx, 8 * my, (h + 1) / 2, Ghost(im), Ghost(2));
    } else {
        pcb = fcb;
        pcr = fcr;
    }
    let wb0 = (w * h0 + d - 1) / d;
    let hb0 = (h * h0 + d - 1) / d;
    let r0 = recips(&q0);
    let r1 = recips(&q1);
    let e = Enc { py, pcb, pcr, e: et, q0, q1, r0, r1, wbs: [wb0, mx, mx], hbs: [hb0, my, my], h0, mx, my, simd };
    proof {
        assert(8 * cw(f, 0) == pw && 8 * ch(f, 0) == ph) by (nonlinear_arith)
            requires
                cw(f, 0) == mcux(f) * h0,
                ch(f, 0) == mcuy(f) * h0,
                mcux(f) == mx,
                mcuy(f) == my,
                pw == 8 * mx * h0,
                ph == 8 * my * h0,
        ;
        assert forall|c: int| 0 <= c < 3 implies plane_samp(#[trigger] e.pl(c), im, sub, c, 8 * cw(f, c), 8 * ch(f, c)) by {
            if c == 0 || !sub {
                assert forall|y: int, x: int| 0 <= y < 8 * ch(f, c) && 0 <= x < 8 * cw(f, c) implies (#[trigger] e.pl(
                    c,
                )[y]@[x]) as int == samp(im, sub, c, y, x) by {
                }
            }
        }
        assert forall|c: int| 0 <= c < 3 implies #[trigger] e.wbs[c] as int == wb(f, c) && e.hbs[c] as int == hb(
            f,
            c,
        ) by {
        }
    }
    e
}

/// Encodes an image of `h` rows of `w` pixels, `bpp` (3 or 4) bytes each,
/// R, G and B first, at `quality` (1 to 100), with 4:2:0 chroma if `sub`.
/// `None` for an image of no pixels, or one larger than 65500 by 65500.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub fn encode_rgb(px: &[u8], w: usize, h: usize, bpp: usize, quality: u8, sub: bool) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(o) ==> im_ok(rgb(px@, w, h, bpp)) && jpeg_coded(o@) == Some(
            enc_coded(rgb(px@, w, h, bpp), sub, quality as int),
        ),
{
    if !(1 <= w && w <= 65500 && 1 <= h && h <= 65500 && (bpp == 3 || bpp == 4)) {
        return None;
    }
    proof {
        assert((w as int) * (h as int) <= 65500 * 65500 && (w as int) * (h as int) * (bpp as int) <= 65500 * 65500 * 4) by (nonlinear_arith)
            requires
                w <= 65500,
                h <= 65500,
                bpp <= 4,
        ;
    }
    if (w as u64) * (h as u64) * (bpp as u64) != px.len() as u64 {
        return None;
    }
    let ghost im = rgb(px@, w, h, bpp);
    let ghost f = enc_frame_of(im, sub);
    let ghost qi = quality as int;
    let (ht, et) = match tables() {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let ghost hts = hseq(ht);
    let e = build(px, w, h, bpp, quality, sub, &ht, et);
    let bw = scan_x(&e, Ghost(im), Ghost(sub), Ghost(qi), Ghost(hts));
    let (data, Ghost(done)) = bw.finish();
    let hv: u8 = if sub {
        0x22
    } else {
        0x11
    };
    let mut out: Vec<u8> = Vec::new();
    proof {
        assert(tab_ok(hts[0]) && tab_ok(hts[1]) && tab_ok(hts[2]) && tab_ok(hts[3]));
    }
    write_headers(&mut out, w, h, hv, &e.q0, &e.q1, &ht);
    push_slice(&mut out, data.as_slice());
    out.push(0xFF);
    out.push(0xD9);
    proof {
        reveal(jfile);
        assert(out@ =~= jfile(w as int, h as int, hv, e.q0@, e.q1@, hts, done));
        lemma_coefs_ok(im, sub, qi);
        lemma_frame(im, sub);
        let k = e.codes();
        assert(frame_of(w as int, h as int, hv) == f);
        assert(file_pre(w as int, h as int, hv, e.q0@, e.q1@, hts, k, enc_coefs(im, sub, qi), done));
        lemma_file(w as int, h as int, hv, e.q0@, e.q1@, hts, k, enc_coefs(im, sub, qi), done);
    }
    Some(out)
}

} // verus!
