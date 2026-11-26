//! The order of the loop filter (RFC 6386, section 15).
//!
//! `vp8spec::frame_recon` filters each macroblock row right after it is
//! reconstructed, as the decoder does. Section 15 describes the filter as
//! a pass over the whole reconstructed frame, macroblock by macroblock in
//! raster order, and says prediction uses the unfiltered pixels. This file
//! states that second order (`frame_unfiltered`, then `lf_frame`) and
//! proves the two give the same planes (`lemma_vp8_frame_filter_order`).
//!
//! The argument: reconstructing row `y` writes only the planes' pixel rows
//! from `16 y` (luma) and `8 y` (chroma) on, and reads no plane at all;
//! filtering rows before `y` reads and writes only pixel rows before
//! those. So the two commute.
use crate::vp8spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The whole-frame order
// ---------------------------------------------------------------------
/// The first `rows` macroblock rows of a frame, reconstructed with no loop
/// filter: `frame_recon` without `lf_recon`.
pub open spec fn frame_unfiltered(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
    rows: nat,
) -> Recon
    decreases rows,
{
    if rows == 0 {
        recon_init(mb_w, mb_h)
    } else {
        let y = (rows - 1) as nat;
        let r = frame_unfiltered(file, pstart, first, gh, fh, mb_w, mb_h, y);
        let ms = mode_rows(first, gh, fh, mb_w, rows).mbs;
        let cos = frame_coeffs(file, pstart, first, gh, fh, mb_w, y);
        row_recon(Recon { ws: row_init(r.ws, y as int), ..r }, ms, cos, y as int, mb_w as int, mb_h as int, mb_w)
    }
}

/// The planes `p` after the loop filter of macroblock row `y`, if the
/// frame has one: `lf_recon` on the planes alone.
pub open spec fn lf_planes_row(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    cos: Seq<Seq<int>>,
    y: int,
    mb_w: nat,
) -> (Seq<u8>, Seq<u8>, Seq<u8>) {
    if fh.filter.level == 0 {
        p
    } else {
        lf_row(p, fh, ms, cos, y, mb_w as int, mb_w)
    }
}

/// The planes `p` after the loop filter of the first `rows` macroblock
/// rows of the frame, every macroblock in raster order.
pub open spec fn lf_frame(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    rows: nat,
) -> (Seq<u8>, Seq<u8>, Seq<u8>)
    decreases rows,
{
    if rows == 0 {
        p
    } else {
        let y = (rows - 1) as nat;
        lf_planes_row(
            lf_frame(p, file, pstart, first, gh, fh, mb_w, y),
            fh,
            mode_rows(first, gh, fh, mb_w, rows).mbs,
            frame_coeffs(file, pstart, first, gh, fh, mb_w, y),
            y as int,
            mb_w,
        )
    }
}

// ---------------------------------------------------------------------
// Which pixels each step reads and writes
// ---------------------------------------------------------------------
/// `a` and `b` have the same length and agree below `h`.
pub open spec fn agree_below(a: Seq<u8>, b: Seq<u8>, h: int) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < h && i < a.len() ==> #[trigger] a[i] == b[i]
}

/// `a` and `b` have the same length and agree from `h` on.
pub open spec fn agree_from(a: Seq<u8>, b: Seq<u8>, h: int) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i && h <= i < a.len() ==> #[trigger] a[i] == b[i]
}

/// `agree_below` for the three planes: `hy` in Y, `huv` in U and V.
pub open spec fn agree3_below(p: (Seq<u8>, Seq<u8>, Seq<u8>), q: (Seq<u8>, Seq<u8>, Seq<u8>), hy: int, huv: int) -> bool {
    &&& agree_below(p.0, q.0, hy)
    &&& agree_below(p.1, q.1, huv)
    &&& agree_below(p.2, q.2, huv)
}

/// `agree_from` for the three planes.
pub open spec fn agree3_from(p: (Seq<u8>, Seq<u8>, Seq<u8>), q: (Seq<u8>, Seq<u8>, Seq<u8>), hy: int, huv: int) -> bool {
    &&& agree_from(p.0, q.0, hy)
    &&& agree_from(p.1, q.1, huv)
    &&& agree_from(p.2, q.2, huv)
}

proof fn lemma_agree_eq(a: Seq<u8>, b: Seq<u8>, h: int)
    requires
        agree_below(a, b, h),
        agree_from(a, b, h),
    ensures
        a == b,
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        if i < h {
            assert(a[i] == b[i]);
        } else {
            assert(a[i] == b[i]);
        }
    }
    assert(a =~= b);
}

/// Filtering one edge position reads and writes pixels `p - 4 step` to
/// `p + 3 step` only.
proof fn lemma_filter_local(
    b: Seq<u8>,
    c: Seq<u8>,
    p: int,
    step: int,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    hh: int,
    h: int,
)
    requires
        step > 0,
        p - 4 * step >= 0,
        p + 3 * step < h <= b.len(),
        agree_below(b, c, h),
    ensures
        agree_below(lf_filter(b, p, step, simple, inner, e, i, hh), lf_filter(c, p, step, simple, inner, e, i, hh), h),
        agree_from(lf_filter(b, p, step, simple, inner, e, i, hh), b, h),
{
    assert(b[p - 4 * step] == c[p - 4 * step]);
    assert(b[p - 3 * step] == c[p - 3 * step]);
    assert(b[p - 2 * step] == c[p - 2 * step]);
    assert(b[p - step] == c[p - step]);
    assert(b[p] == c[p]);
    assert(b[p + step] == c[p + step]);
    assert(b[p + 2 * step] == c[p + 2 * step]);
    assert(b[p + 3 * step] == c[p + 3 * step]);
    assert(lf_lane(b, p, step) == lf_lane(c, p, step));
}

proof fn lemma_run_local(
    b: Seq<u8>,
    c: Seq<u8>,
    p: int,
    hs: int,
    vs: int,
    n: nat,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    hh: int,
    h: int,
)
    requires
        hs > 0,
        vs > 0,
        p - 4 * hs >= 0,
        n > 0 ==> p + (n - 1) * vs + 3 * hs < h,
        h <= b.len(),
        agree_below(b, c, h),
    ensures
        agree_below(lf_run(b, p, hs, vs, n, simple, inner, e, i, hh), lf_run(c, p, hs, vs, n, simple, inner, e, i, hh), h),
        agree_from(lf_run(b, p, hs, vs, n, simple, inner, e, i, hh), b, h),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        if n1 > 0 {
            assert((n1 - 1) * vs <= (n - 1) * vs) by (nonlinear_arith)
                requires
                    vs > 0,
                    n1 == n - 1,
            ;
        }
        lemma_run_local(b, c, p, hs, vs, n1, simple, inner, e, i, hh, h);
        let b1 = lf_run(b, p, hs, vs, n1, simple, inner, e, i, hh);
        let c1 = lf_run(c, p, hs, vs, n1, simple, inner, e, i, hh);
        assert((n - 1) * vs >= 0) by (nonlinear_arith)
            requires
                vs > 0,
                n > 0,
        ;
        lemma_filter_local(b1, c1, p + (n - 1) * vs, hs, simple, inner, e, i, hh, h);
    }
}

proof fn lemma_inner_local(
    b: Seq<u8>,
    c: Seq<u8>,
    d: int,
    gap: int,
    hs: int,
    vs: int,
    n: nat,
    size: nat,
    simple: bool,
    e: int,
    i: int,
    hh: int,
    h: int,
)
    requires
        gap == hs,
        hs > 0,
        vs > 0,
        d >= 0,
        size > 0,
        n > 0 ==> d + 4 * n * gap + (size - 1) * vs + 3 * hs < h,
        h <= b.len(),
        agree_below(b, c, h),
    ensures
        agree_below(
            lf_inner_edges(b, d, gap, hs, vs, n, size, simple, e, i, hh),
            lf_inner_edges(c, d, gap, hs, vs, n, size, simple, e, i, hh),
            h,
        ),
        agree_from(lf_inner_edges(b, d, gap, hs, vs, n, size, simple, e, i, hh), b, h),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        assert(4 * n1 * gap <= 4 * n * gap && 4 * n * gap - 4 * hs >= 0 && 4 * n * gap == 4 * n1 * gap + 4 * gap)
            by (nonlinear_arith)
            requires
                gap == hs,
                hs > 0,
                n > 0,
                n1 == n - 1,
        ;
        lemma_inner_local(b, c, d, gap, hs, vs, n1, size, simple, e, i, hh, h);
        let b1 = lf_inner_edges(b, d, gap, hs, vs, n1, size, simple, e, i, hh);
        let c1 = lf_inner_edges(c, d, gap, hs, vs, n1, size, simple, e, i, hh);
        lemma_run_local(b1, c1, d + 4 * n * gap, hs, vs, size, simple, true, e, i, hh, h);
    }
}

/// One plane of one macroblock, whose top left pixel is at row `row0`,
/// column `col0`: only pixel rows before `row0 + size` are read or
/// written.
proof fn lemma_plane_local(
    b: Seq<u8>,
    c: Seq<u8>,
    d: int,
    row0: int,
    col0: int,
    stride: int,
    size: nat,
    left: bool,
    top: bool,
    simple: bool,
    inner: bool,
    limit: int,
    i: int,
    hh: int,
    h: int,
)
    requires
        size == 8 || size == 16,
        d == row0 * stride + col0,
        0 <= col0,
        col0 + size <= stride,
        0 <= row0,
        left ==> col0 >= 4,
        top ==> row0 >= 4,
        (row0 + size) * stride <= h <= b.len(),
        agree_below(b, c, h),
    ensures
        agree_below(
            lf_mb_plane(b, d, stride, size, left, top, simple, inner, limit, i, hh),
            lf_mb_plane(c, d, stride, size, left, top, simple, inner, limit, i, hh),
            h,
        ),
        agree_from(lf_mb_plane(b, d, stride, size, left, top, simple, inner, limit, i, hh), b, h),
{
    let x = row0 * stride;
    assert((row0 + size) * stride == x + size * stride) by (nonlinear_arith)
        requires
            x == row0 * stride,
    ;
    assert(x >= 0) by (nonlinear_arith)
        requires
            x == row0 * stride,
            row0 >= 0,
            stride > 0,
    ;
    assert(top ==> x >= 4 * stride) by (nonlinear_arith)
        requires
            x == row0 * stride,
            top ==> row0 >= 4,
            stride > 0,
    ;
    assert((size - 1) * stride == size * stride - stride && (size - 4) * stride == size * stride - 4 * stride
        && size * stride >= 8 * stride) by (nonlinear_arith)
        requires
            size >= 8,
            stride > 0,
    ;
    let n = (size / 4 - 1) as nat;
    assert(4 * n == size - 4);
    assert(4 * n * stride == (size - 4) * stride) by (nonlinear_arith)
        requires
            4 * n == size - 4,
    ;
    let b1 = if left {
        lf_run(b, d, 1, stride, size, simple, false, limit + 4, i, hh)
    } else {
        b
    };
    let c1 = if left {
        lf_run(c, d, 1, stride, size, simple, false, limit + 4, i, hh)
    } else {
        c
    };
    if left {
        lemma_run_local(b, c, d, 1, stride, size, simple, false, limit + 4, i, hh, h);
    }
    let b2 = if inner {
        lf_inner_edges(b1, d, 1, 1, stride, n, size, simple, limit, i, hh)
    } else {
        b1
    };
    let c2 = if inner {
        lf_inner_edges(c1, d, 1, 1, stride, n, size, simple, limit, i, hh)
    } else {
        c1
    };
    if inner {
        lemma_inner_local(b1, c1, d, 1, 1, stride, n, size, simple, limit, i, hh, h);
    }
    let b3 = if top {
        lf_run(b2, d, stride, 1, size, simple, false, limit + 4, i, hh)
    } else {
        b2
    };
    let c3 = if top {
        lf_run(c2, d, stride, 1, size, simple, false, limit + 4, i, hh)
    } else {
        c2
    };
    if top {
        lemma_run_local(b2, c2, d, stride, 1, size, simple, false, limit + 4, i, hh, h);
    }
    if inner {
        lemma_inner_local(b3, c3, d, stride, stride, 1, n, size, simple, limit, i, hh, h);
    }
}

/// The loop filter of macroblock `(mb_x, mb_y)` reads and writes only
/// pixel rows before `16 (mb_y + 1)` in Y and `8 (mb_y + 1)` in U and V.
#[verifier::spinoff_prover]
proof fn lemma_mb_local(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    q: (Seq<u8>, Seq<u8>, Seq<u8>),
    mb_x: int,
    mb_y: int,
    mb_w: int,
    simple: bool,
    inner: bool,
    limit: int,
    i: int,
    hh: int,
    hy: int,
    huv: int,
)
    requires
        0 <= mb_x < mb_w,
        0 <= mb_y,
        (16 * mb_y + 16) * (16 * mb_w) <= hy <= p.0.len(),
        (8 * mb_y + 8) * (8 * mb_w) <= huv <= p.1.len(),
        huv <= p.2.len(),
        agree3_below(p, q, hy, huv),
    ensures
        agree3_below(
            lf_mb(p.0, p.1, p.2, mb_x, mb_y, mb_w, simple, inner, limit, i, hh),
            lf_mb(q.0, q.1, q.2, mb_x, mb_y, mb_w, simple, inner, limit, i, hh),
            hy,
            huv,
        ),
        agree3_from(lf_mb(p.0, p.1, p.2, mb_x, mb_y, mb_w, simple, inner, limit, i, hh), p, hy, huv),
{
    hide(lf_mb_plane);
    let yd = 16 * mb_y * (16 * mb_w) + 16 * mb_x;
    let uvd = 8 * mb_y * (8 * mb_w) + 8 * mb_x;
    if limit != 0 {
        if simple {
            lemma_plane_local(
                p.0, q.0, yd, 16 * mb_y, 16 * mb_x, 16 * mb_w, 16, mb_x > 0, mb_y > 0, true, inner, limit, 0, 0, hy);
        } else {
            lemma_plane_local(
                p.0, q.0, yd, 16 * mb_y, 16 * mb_x, 16 * mb_w, 16, mb_x > 0, mb_y > 0, false, inner, limit, i, hh, hy);
            lemma_plane_local(
                p.1, q.1, uvd, 8 * mb_y, 8 * mb_x, 8 * mb_w, 8, mb_x > 0, mb_y > 0, false, inner, limit, i, hh, huv);
            lemma_plane_local(
                p.2, q.2, uvd, 8 * mb_y, 8 * mb_x, 8 * mb_w, 8, mb_x > 0, mb_y > 0, false, inner, limit, i, hh, huv);
        }
    }
}

/// `lf_row`: the first `n` macroblocks of row `mb_y`.
proof fn lemma_row_local(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    q: (Seq<u8>, Seq<u8>, Seq<u8>),
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    cos: Seq<Seq<int>>,
    mb_y: int,
    mb_w: int,
    n: nat,
    hy: int,
    huv: int,
)
    requires
        n <= mb_w,
        0 <= mb_y,
        (16 * mb_y + 16) * (16 * mb_w) <= hy <= p.0.len(),
        (8 * mb_y + 8) * (8 * mb_w) <= huv <= p.1.len(),
        huv <= p.2.len(),
        agree3_below(p, q, hy, huv),
    ensures
        agree3_below(lf_row(p, fh, ms, cos, mb_y, mb_w, n), lf_row(q, fh, ms, cos, mb_y, mb_w, n), hy, huv),
        agree3_from(lf_row(p, fh, ms, cos, mb_y, mb_w, n), p, hy, huv),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_row_local(p, q, fh, ms, cos, mb_y, mb_w, n1, hy, huv);
        let a = lf_row(p, fh, ms, cos, mb_y, mb_w, n1);
        let b = lf_row(q, fh, ms, cos, mb_y, mb_w, n1);
        let m = ms[n1 as int];
        let co = cos[n1 as int];
        let lv = seg_filter_level(fh, m.segment, m.is_i4x4);
        if lv > 0 {
            let il = interior_limit(lv, fh.filter.sharpness);
            lemma_mb_local(
                a,
                b,
                n1 as int,
                mb_y,
                mb_w,
                fh.filter.simple,
                m.is_i4x4 || any_nz(co),
                2 * lv + il,
                il,
                hev_threshold(lv),
                hy,
                huv,
            );
        }
    }
}

/// `lf_frame`: the filter of the first `rows` rows reads and writes only
/// pixel rows before `16 rows` in Y and `8 rows` in U and V.
proof fn lemma_frame_local(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    q: (Seq<u8>, Seq<u8>, Seq<u8>),
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    rows: nat,
    hy: int,
    huv: int,
)
    requires
        16 * rows * (16 * mb_w) <= hy <= p.0.len(),
        8 * rows * (8 * mb_w) <= huv <= p.1.len(),
        huv <= p.2.len(),
        agree3_below(p, q, hy, huv),
    ensures
        agree3_below(
            lf_frame(p, file, pstart, first, gh, fh, mb_w, rows),
            lf_frame(q, file, pstart, first, gh, fh, mb_w, rows),
            hy,
            huv,
        ),
        agree3_from(lf_frame(p, file, pstart, first, gh, fh, mb_w, rows), p, hy, huv),
    decreases rows,
{
    if rows > 0 {
        let y = (rows - 1) as nat;
        assert(16 * y * (16 * mb_w) <= 16 * rows * (16 * mb_w) && 8 * y * (8 * mb_w) <= 8 * rows * (8 * mb_w))
            by (nonlinear_arith)
            requires
                y == rows - 1,
                mb_w >= 0,
        ;
        assert((16 * y + 16) * (16 * mb_w) == 16 * rows * (16 * mb_w) && (8 * y + 8) * (8 * mb_w) == 8 * rows * (8
            * mb_w)) by (nonlinear_arith)
            requires
                y == rows - 1,
        ;
        lemma_frame_local(p, q, file, pstart, first, gh, fh, mb_w, y, hy, huv);
        let a = lf_frame(p, file, pstart, first, gh, fh, mb_w, y);
        let b = lf_frame(q, file, pstart, first, gh, fh, mb_w, y);
        if fh.filter.level != 0 {
            lemma_row_local(
                a,
                b,
                fh,
                mode_rows(first, gh, fh, mb_w, rows).mbs,
                frame_coeffs(file, pstart, first, gh, fh, mb_w, y),
                y as int,
                mb_w as int,
                mb_w,
                hy,
                huv,
            );
        }
    }
}

/// `put_rows` writes only from pixel row `y0` on, with the same bytes
/// whatever the plane held.
proof fn lemma_put_rows(
    pl: Seq<u8>,
    pl2: Seq<u8>,
    x0: int,
    y0: int,
    stride: int,
    ws: Seq<u8>,
    d: int,
    n: int,
    k: int,
    h: int,
)
    requires
        x0 >= 0,
        y0 >= 0,
        stride >= 0,
        h <= y0 * stride,
    ensures
        agree_below(put_rows(pl, x0, y0, stride, ws, d, n, k), pl, h),
        agree_from(pl, pl2, h) ==> agree_from(
            put_rows(pl, x0, y0, stride, ws, d, n, k),
            put_rows(pl2, x0, y0, stride, ws, d, n, k),
            h,
        ),
    decreases k,
{
    if k > 0 {
        lemma_put_rows(pl, pl2, x0, y0, stride, ws, d, n, k - 1, h);
        lemma_put_rows(pl2, pl, x0, y0, stride, ws, d, n, k - 1, h);
        let dd = (y0 + (k - 1)) * stride + x0;
        assert((y0 + (k - 1)) * stride >= y0 * stride) by (nonlinear_arith)
            requires
                k > 0,
                stride >= 0,
        ;
        let a = put_rows(pl, x0, y0, stride, ws, d, n, k - 1);
        let b = put_rows(pl2, x0, y0, stride, ws, d, n, k - 1);
        let s = d + 32 * (k - 1);
        assert(put_rows(pl, x0, y0, stride, ws, d, n, k) == put_run(a, dd, ws, s, n));
        assert(put_rows(pl2, x0, y0, stride, ws, d, n, k) == put_run(b, dd, ws, s, n));
        if agree_from(pl, pl2, h) {
            assert forall|j: int| 0 <= j && h <= j < a.len() implies #[trigger] put_run(a, dd, ws, s, n)[j] == put_run(
                b,
                dd,
                ws,
                s,
                n,
            )[j] by {
                assert(a[j] == b[j]);
            }
        }
    }
}

/// The parts of `Recon` that are not the planes.
pub open spec fn recon_rest_eq(a: Recon, b: Recon) -> bool {
    a.ws == b.ws && a.ty == b.ty && a.tu == b.tu && a.tv == b.tv
}

/// Reconstructing macroblocks of row `mb_y` reads no plane, and writes
/// only from pixel row `16 mb_y` (Y) and `8 mb_y` (U, V) on, the same
/// bytes whatever the planes held.
proof fn lemma_row_recon_planes(
    st: Recon,
    st2: Recon,
    ms: Seq<MbModeSpec>,
    cos: Seq<Seq<int>>,
    mb_y: int,
    mb_w: int,
    mb_h: int,
    n: nat,
)
    requires
        0 <= mb_y,
        mb_w >= 0,
        recon_rest_eq(st, st2),
    ensures
        ({
            let a = row_recon(st, ms, cos, mb_y, mb_w, mb_h, n);
            let b = row_recon(st2, ms, cos, mb_y, mb_w, mb_h, n);
            let hy = 16 * mb_y * (16 * mb_w);
            let huv = 8 * mb_y * (8 * mb_w);
            &&& recon_rest_eq(a, b)
            &&& agree_below(a.y, st.y, hy)
            &&& agree_below(a.u, st.u, huv)
            &&& agree_below(a.v, st.v, huv)
            &&& agree_from(st.y, st2.y, hy) ==> agree_from(a.y, b.y, hy)
            &&& agree_from(st.u, st2.u, huv) ==> agree_from(a.u, b.u, huv)
            &&& agree_from(st.v, st2.v, huv) ==> agree_from(a.v, b.v, huv)
        }),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_row_recon_planes(st, st2, ms, cos, mb_y, mb_w, mb_h, n1);
        let a = row_recon(st, ms, cos, mb_y, mb_w, mb_h, n1);
        let b = row_recon(st2, ms, cos, mb_y, mb_w, mb_h, n1);
        let m = ms[n1 as int];
        let mb_x = n1 as int;
        let w = mb_recon(mb_setup(a.ws, a.ty, a.tu, a.tv, mb_x, mb_y, mb_w, m.is_i4x4), m, mb_x, mb_y, cos[n1 as int]);
        assert(w == mb_recon(mb_setup(b.ws, b.ty, b.tu, b.tv, mb_x, mb_y, mb_w, m.is_i4x4), m, mb_x, mb_y, cos[n1 as int]));
        let hy = 16 * mb_y * (16 * mb_w);
        let huv = 8 * mb_y * (8 * mb_w);
        lemma_put_rows(a.y, b.y, 16 * mb_x, 16 * mb_y, 16 * mb_w, w, s_y(), 16, 16, hy);
        lemma_put_rows(a.u, b.u, 8 * mb_x, 8 * mb_y, 8 * mb_w, w, s_u(), 8, 8, huv);
        lemma_put_rows(a.v, b.v, 8 * mb_x, 8 * mb_y, 8 * mb_w, w, s_v(), 8, 8, huv);
        let a2 = row_recon(st, ms, cos, mb_y, mb_w, mb_h, n);
        let b2 = row_recon(st2, ms, cos, mb_y, mb_w, mb_h, n);
        assert(a2 == mb_step(a, m, cos[n1 as int], mb_x, mb_y, mb_w, mb_h));
        assert(b2 == mb_step(b, m, cos[n1 as int], mb_x, mb_y, mb_w, mb_h));
    }
}

// ---------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------
/// The first `rows` rows of `frame_recon` (each row filtered right after
/// it is reconstructed) are the first `rows` rows reconstructed with no
/// filter, then filtered row by row: the same scratch state, and the same
/// planes.
#[verifier::spinoff_prover]
pub proof fn lemma_filter_order(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
    rows: nat,
)
    requires
        rows <= mb_h,
    ensures
        ({
            let f = frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, rows);
            let u = frame_unfiltered(file, pstart, first, gh, fh, mb_w, mb_h, rows);
            &&& recon_rest_eq(f, u)
            &&& (f.y, f.u, f.v) == lf_frame((u.y, u.u, u.v), file, pstart, first, gh, fh, mb_w, rows)
            &&& u.y.len() == 16 * mb_w * (16 * mb_h)
            &&& u.u.len() == 8 * mb_w * (8 * mb_h)
            &&& u.v.len() == 8 * mb_w * (8 * mb_h)
        }),
    decreases rows,
{
    hide(row_recon);
    hide(lf_row);
    hide(mode_rows);
    hide(frame_coeffs);
    hide(row_init);
    if rows > 0 {
        let y = (rows - 1) as nat;
        lemma_filter_order(file, pstart, first, gh, fh, mb_w, mb_h, y);
        let f0 = frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, y);
        let u0 = frame_unfiltered(file, pstart, first, gh, fh, mb_w, mb_h, y);
        let ms = mode_rows(first, gh, fh, mb_w, rows).mbs;
        let cos = frame_coeffs(file, pstart, first, gh, fh, mb_w, y);
        let sf = Recon { ws: row_init(f0.ws, y as int), ..f0 };
        let su = Recon { ws: row_init(u0.ws, y as int), ..u0 };
        let a = row_recon(sf, ms, cos, y as int, mb_w as int, mb_h as int, mb_w);
        let b = row_recon(su, ms, cos, y as int, mb_w as int, mb_h as int, mb_w);
        let hy: int = (16 * y * (16 * mb_w)) as int;
        let huv: int = (8 * y * (8 * mb_w)) as int;
        assert(hy <= 16 * mb_w * (16 * mb_h) && huv <= 8 * mb_w * (8 * mb_h)) by (nonlinear_arith)
            requires
                y < mb_h,
                hy == 16 * y * (16 * mb_w),
                huv == 8 * y * (8 * mb_w),
        ;
        lemma_row_recon_planes(sf, su, ms, cos, y as int, mb_w as int, mb_h as int, mb_w);
        lemma_row_recon_planes(su, sf, ms, cos, y as int, mb_w as int, mb_h as int, mb_w);
        // The planes of `b` agree with `u0`'s below row `y`, so filtering
        // the rows before `y` gives the same there; and that filter leaves
        // rows `y` on alone.
        let pu = (u0.y, u0.u, u0.v);
        let pb = (b.y, b.u, b.v);
        lemma_frame_local(pb, pu, file, pstart, first, gh, fh, mb_w, y, hy, huv);
        let l = lf_frame(pb, file, pstart, first, gh, fh, mb_w, y);
        let lu = lf_frame(pu, file, pstart, first, gh, fh, mb_w, y);
        assert(lu == (f0.y, f0.u, f0.v));
        // `f0`'s planes agree with `u0`'s from row `y` on.
        lemma_frame_local(pu, pu, file, pstart, first, gh, fh, mb_w, y, hy, huv);
        lemma_agree_eq(a.y, l.0, hy);
        lemma_agree_eq(a.u, l.1, huv);
        lemma_agree_eq(a.v, l.2, huv);
        assert((a.y, a.u, a.v) == l);
        assert(frame_unfiltered(file, pstart, first, gh, fh, mb_w, mb_h, rows) == b);
        assert(frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, rows) == lf_recon(a, fh, ms, cos, y as int, mb_w));
    }
}

/// Section 15's order for the decoded frame: `vp8_frame`'s planes are the
/// frame reconstructed with no loop filter, then filtered macroblock by
/// macroblock in raster order.
pub proof fn lemma_vp8_frame_filter_order(file: Seq<u8>, off: int)
    ensures
        ({
            let (end, pt, gh, fh, mb_w, mb_h) = vp8_parts(file, off);
            let f = vp8_frame(file, off);
            let u = frame_unfiltered(file, end, pt, gh, fh, mb_w, mb_h, mb_h);
            (f.y, f.u, f.v) == lf_frame((u.y, u.u, u.v), file, end, pt, gh, fh, mb_w, mb_h)
        }),
{
    let (end, pt, gh, fh, mb_w, mb_h) = vp8_parts(file, off);
    lemma_filter_order(file, end, pt, gh, fh, mb_w, mb_h, mb_h);
}

} // verus!
