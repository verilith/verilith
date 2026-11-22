//! Decoding a VP8 key frame to Y, U and V planes, macroblock row by row as
//! libwebp 1.6.0 does (`VP8Decode`, `ParseFrame`, `ReconstructRow`,
//! `FilterRow` in `src/dec/frame_dec.c`).
use crate::pixels::Error;
use crate::vp8bool::*;
use crate::vp8dsp::*;
use crate::vp8p4::pred4_fast;
use crate::vp8parse::*;
use crate::vp8spec::*;
use verilith_core::prims::*;
use vstd::prelude::*;

verus! {

/// The decoded planes, in whole macroblocks: `Y` is `16 * mb_w` by
/// `16 * mb_h`, `U` and `V` are `8 * mb_w` by `8 * mb_h`.
pub struct Planes {
    pub width: usize,
    pub height: usize,
    pub y: Vec<u8>,
    pub u: Vec<u8>,
    pub v: Vec<u8>,
    pub y_stride: usize,
    pub uv_stride: usize,
}

impl Planes {
    /// The shape `decode_frame` returns: a 14-bit size, and planes that
    /// cover it (chroma at half resolution, rounded up).
    pub open spec fn ok(&self) -> bool {
        &&& 1 <= self.width <= 16384
        &&& 1 <= self.height <= 16384
        &&& self.width <= self.y_stride <= 16384 + 16
        &&& (self.width + 1) / 2 <= self.uv_stride <= 8192 + 8
        &&& self.y@.len() >= self.y_stride * self.height
        &&& self.u@.len() >= self.uv_stride * ((self.height + 1) / 2)
        &&& self.v@.len() >= self.uv_stride * ((self.height + 1) / 2)
    }
}

impl Planes {
    /// Whole macroblocks: `mb_w` by `mb_h` of them, each 16x16 in Y and 8x8
    /// in U and V, covering the frame.
    pub open spec fn mb_shape(&self, mb_w: nat, mb_h: nat) -> bool {
        &&& 1 <= mb_w <= 1024
        &&& 1 <= mb_h <= 1024
        &&& self.y_stride == 16 * mb_w
        &&& self.uv_stride == 8 * mb_w
        &&& self.y@.len() == self.y_stride * (16 * mb_h)
        &&& self.u@.len() == self.uv_stride * (8 * mb_h)
        &&& self.v@.len() == self.uv_stride * (8 * mb_h)
        &&& 1 <= self.width <= 16 * mb_w
        &&& 1 <= self.height <= 16 * mb_h
        &&& self.width < 0x4000
        &&& self.height < 0x4000
        &&& mb_w == (self.width + 15) / 16
        &&& mb_h == (self.height + 15) / 16
    }
}

/// The edges `filter_mb` filters, in a plane of `n`-pixel macroblocks
/// (`n` 8 or 16) `mw` wide and `mh` high: from the macroblock at
/// `(mx, my)`, at offset `4 k` across (columns) and `4 k` rows down.
pub proof fn lemma_edges(mx: int, my: int, mw: int, mh: int, n: int, k: int)
    requires
        0 <= mx < mw <= 1024,
        0 <= my < mh <= 1024,
        n == 8 || n == 16,
        0 <= k < n / 4,
    ensures
        ({
            let s = n * mw;
            let d = n * my * s + n * mx;
            let len = s * (n * mh);
            &&& 8 <= s <= 16 * 1024
            &&& len <= 16 * 1024 * 16 * 1024
            &&& d + 4 * k + (n - 1) * s + 3 < len
            &&& d + 4 * k * s + (n - 1) + 3 * s < len
            &&& (mx >= 1 || k >= 1) ==> d + 4 * k >= 4
            &&& (my >= 1 || k >= 1) ==> d + 4 * k * s >= 4 * s
            &&& 0 <= n * my * s <= d
        }),
{
    let s = n * mw;
    let nm = n * mx;
    let x = n * my * s;
    let y = s * (n * mh);
    assert(nm + n <= s) by (nonlinear_arith)
        requires mx < mw, s == n * mw, nm == n * mx, n >= 0;
    assert(nm >= 0) by (nonlinear_arith) requires nm == n * mx, mx >= 0, n >= 0;
    assert(8 <= s <= 16 * 1024) by (nonlinear_arith) requires s == n * mw, 8 <= n <= 16, 1 <= mw <= 1024;
    assert(x + n * s <= y) by (nonlinear_arith)
        requires x == n * my * s, y == s * (n * mh), my < mh, s >= 0, n >= 0;
    assert((4 * k + 4) * s <= n * s) by (nonlinear_arith) requires 4 * k + 4 <= n, s >= 0;
    assert((4 * k + 4) * s == 4 * k * s + 4 * s) by (nonlinear_arith);
    assert((n - 1) * s + s == n * s) by (nonlinear_arith);
    assert(y <= 16 * 1024 * 16 * 1024) by (nonlinear_arith)
        requires y == s * (n * mh), 0 <= s <= 16 * 1024, 0 <= n <= 16, 0 <= mh <= 1024;
    assert(x >= 0) by (nonlinear_arith) requires x == n * my * s, my >= 0, n >= 0, s >= 0;
    if my >= 1 {
        assert(x >= 4 * s) by (nonlinear_arith) requires x == n * my * s, my >= 1, n >= 8, s >= 0;
    }
    if k >= 1 {
        assert(4 * k * s >= 4 * s) by (nonlinear_arith) requires k >= 1, s >= 0;
    }
    assert(4 * k * s >= 0) by (nonlinear_arith) requires k >= 0, s >= 0;
}

/// Offsets in the scratch block (`Y_OFF`, `U_OFF`, `V_OFF`).
pub const Y_OFF: usize = BPS + 8;
pub const U_OFF: usize = Y_OFF + BPS * 16 + BPS;
pub const V_OFF: usize = U_OFF + 16;
pub const YUV_SIZE: usize = BPS * 17 + BPS * 9;

/// `kScan`: where the sixteen 4x4 luma blocks start in the scratch block.
pub const SCAN: [usize; 16] = [
    0,
    4,
    8,
    12,
    4 * BPS,
    4 + 4 * BPS,
    8 + 4 * BPS,
    12 + 4 * BPS,
    8 * BPS,
    4 + 8 * BPS,
    8 + 8 * BPS,
    12 + 8 * BPS,
    12 * BPS,
    4 + 12 * BPS,
    8 + 12 * BPS,
    12 + 12 * BPS,
];

/// A zeroed byte vector, or `None` if the allocation fails.
#[verifier::external_body]
pub fn alloc_u8(n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u8),
{
    let mut v: Vec<u8> = Vec::new();
    if v.try_reserve_exact(n).is_err() {
        return None;
    }
    v.resize(n, 0);
    Some(v)
}

/// `CheckMode`: the DC mode variant for macroblocks on the top or left
/// edge.
#[inline(always)]
fn check_mode(mb_x: usize, mb_y: usize, mode: u8) -> (r: u8)
    requires
        mode < 4,
    ensures
        r < 7,
        r == edge_mode(mb_x as int, mb_y as int, mode as int),
{
    if mode == 0 {
        if mb_x == 0 {
            if mb_y == 0 {
                6
            } else {
                5
            }
        } else {
            if mb_y == 0 {
                4
            } else {
                0
            }
        }
    } else {
        mode
    }
}

/// Copies `n` bytes from `src[s..]` to `dst[d..]`.
#[inline(always)]
fn copy_n(dst: &mut [u8], d: usize, src: &[u8], s: usize, n: usize)
    requires
        s + n <= src@.len(),
        d + n <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@ == put_run(old(dst)@, d as int, src@, s as int, n as int),
{
    proof {assert(dst@.len() == dst.len()); assert(src@.len() == src.len());}
    copy_in(dst, d, src, s, n);
    assert(dst@ =~= put_run(old(dst)@, d as int, src@, s as int, n as int));
}

/// Fills `n` bytes of `dst` from `d` with `v`.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn fill_n(dst: &mut [u8], d: usize, n: usize, v: u8)
    requires
        d + n <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@ == fill_run(old(dst)@, d as int, n as int, v),
{
    proof {assert(dst@.len() == dst.len());}
    let mut i: usize = 0;
    while i < n
        invariant
            dst@.len() <= usize::MAX,
            i <= n,
            d + n <= dst@.len(),
            dst@.len() == old(dst)@.len(),
            dst@ =~= fill_run(old(dst)@, d as int, i as int, v),
        decreases n - i,
    {
        set(dst, d + i, v);
        i = i + 1;
    }
}

/// The selector bits and the coefficient buffer that `reconstruct_mb` is
/// given are sound for the macroblock's coefficients `co`.
pub open spec fn res_ok(ny: u32, nuv: u32, buf: Seq<i16>, co: Seq<int>) -> bool {
    &&& forall|n: int| 0 <= n < 16 ==> #[trigger] y_ok(ny, buf, co, n)
    &&& uv_ok(nuv, buf, co, 256)
    &&& uv_ok(nuv >> 8u32, buf, co, 320)
}

/// `bits_at` is a shift, and its top two bits are block `n`'s selector.
proof fn lemma_bits_at(b: u32, n: nat)
    requires
        n < 16,
    ensures
        bits_at(b, n) == b << ((2 * n) as u32),
        bits_at(b, n) >> 30u32 == ycode(b, 30, n as int),
    decreases n,
{
    if n > 0 {
        lemma_bits_at(b, (n - 1) as nat);
        let k = (2 * (n - 1)) as u32;
        let k2 = (2 * n) as u32;
        assert(k <= 28 && k2 == k + 2 ==> (b << k) << 2u32 == b << k2) by (bit_vector);
    } else {
        assert(b << 0u32 == b) by (bit_vector);
    }
    let k2 = (2 * n) as u32;
    let sh = (30 - 2 * n) as u32;
    assert(k2 <= 30 && sh == 30 - k2 ==> (b << k2) >> 30u32 == (b >> sh) & 3) by (bit_vector);
}

/// Sound selectors for a chroma block's four subblocks, with tame
/// coefficients, are what `do_uv_transform` needs.
proof fn lemma_uv_res_ok(bits: u32, buf: Seq<i16>, co: Seq<int>, i: int)
    requires
        buf.len() == 384,
        c16(buf) == co,
        i == 256 || i == 320,
        sel_ok(bits & 0xff, 6, 4, buf, i),
        mb_tame(co),
    ensures
        uv_ok(bits, buf, co, i),
{
    let b8 = bits & 0xff;
    assert(bits & 0xff == 0 ==> ((bits & 0xff) >> 6u32) & 3 == 0 && ((bits & 0xff) >> 4u32) & 3 == 0 && ((bits & 0xff)
        >> 2u32) & 3 == 0 && ((bits & 0xff) >> 0u32) & 3 == 0) by (bit_vector);
    assert(bits & 0xaa == 0 ==> ((bits & 0xff) >> 6u32) & 3 <= 1 && ((bits & 0xff) >> 4u32) & 3 <= 1 && ((bits & 0xff)
        >> 2u32) & 3 <= 1 && ((bits & 0xff) >> 0u32) & 3 <= 1) by (bit_vector);
    assert forall|n: int| 0 <= n < 4 implies {
        let cb = blk(co, i + 16 * n);
        &&& #[trigger] cblk(buf, i + 16 * n) == cb
        &&& ksound(ycode(b8, 6, n), cb)
        &&& idct_tame(cb)
        &&& bits & 0xff == 0 ==> ycode(b8, 6, n) == 0
        &&& bits & 0xaa == 0 ==> ycode(b8, 6, n) <= 1
    } by {
        assert(ksound(ycode(b8, 6, n), blk16(buf, i + 16 * n)));
        assert(blk16(buf, i + 16 * n) =~= blk(co, i + 16 * n));
        assert(cblk(buf, i + 16 * n) =~= blk(co, i + 16 * n));
        assert(idct_tame(mblk(co, i / 16 + n)));
        assert(16 * (i / 16 + n) == i + 16 * n);
        assert((6 - 2 * n) as u32 == 6 || (6 - 2 * n) as u32 == 4 || (6 - 2 * n) as u32 == 2 || (6 - 2 * n) as u32 == 0);
    }
    if bits & 0xff == 0 {
        assert forall|n: int| 0 <= n < 4 implies zero_blk(#[trigger] blk(co, i + 16 * n)) by {
            assert(cblk(buf, i + 16 * n) == blk(co, i + 16 * n));
        }
    } else {
        assert forall|n: int| 0 <= n < 4 implies {
            let cb = #[trigger] cblk(buf, i + 16 * n);
            &&& bits & 0xff == 0 ==> only_dc(cb) && cb[0] == 0
            &&& bits & 0xaa == 0 ==> only_dc(cb)
            &&& bits & 0xaa != 0 ==> idct_tame(cb)
        } by {}
    }
}

/// The parser's selectors, sound for a buffer that holds the macroblock's
/// coefficients, are what `reconstruct_mb` needs when the coefficients
/// are tame.
proof fn lemma_res_ok(res: Residuals, buf: Seq<i16>, co: Seq<int>)
    requires
        buf.len() == 384,
        c16(buf) == co,
        sels_ok(res, buf),
        mb_tame(co),
    ensures
        res_ok(res.non_zero_y, res.non_zero_uv, buf, co),
{
    let ny = res.non_zero_y;
    assert forall|n: int| 0 <= n < 16 implies #[trigger] y_ok(ny, buf, co, n) by {
        lemma_bits_at(ny, n as nat);
        assert(ksound(ycode(ny, 30, n), blk16(buf, 0 + 16 * n)));
        assert(blk16(buf, 0 + 16 * n) =~= blk(co, 16 * n));
        assert(cblk(buf, 16 * n) =~= blk(co, 16 * n));
        assert(idct_tame(mblk(co, n)));
        let x = bits_at(ny, n as nat);
        assert((x >> 30u32) <= 3) by (bit_vector);
    }
    lemma_uv_res_ok(res.non_zero_uv, buf, co, 256);
    let v = res.non_zero_uv >> 8u32;
    lemma_uv_res_ok(v, buf, co, 320);
}

/// A macroblock with no coefficients and no selector set.
proof fn lemma_res_ok_zero(buf: Seq<i16>, co: Seq<int>)
    requires
        co == Seq::new(384, |i: int| 0int),
    ensures
        res_ok(0, 0, buf, co),
{
    assert(0u32 >> 30u32 == 0 && 0u32 & 0xff == 0 && 0u32 >> 8u32 == 0) by (bit_vector);
    assert forall|n: int| 0 <= n < 16 implies #[trigger] y_ok(0, buf, co, n) by {
        lemma_bits_zero(n as nat);
    }
}

/// What `mb_coeffs` establishes is what `reconstruct_mb` needs, for a
/// macroblock whose coefficients are tame.
proof fn lemma_mb_res_ok(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    m: MbModeSpec,
    top: Seq<bool>,
    left: Seq<bool>,
    res: Residuals,
    buf: Seq<i16>,
)
    requires
        buf.len() == 384,
        ({
            let e = mb_tokens(data, s, fh, m, top, left);
            &&& !(fh.mb_no_coeff_skip && m.skip) ==> c16(buf) == e.coeffs && sels_ok(res, buf)
            &&& fh.mb_no_coeff_skip && m.skip ==> res.non_zero_y == 0 && res.non_zero_uv == 0
            &&& mb_tame(e.coeffs)
        }),
    ensures
        res_ok(res.non_zero_y, res.non_zero_uv, buf, mb_tokens(data, s, fh, m, top, left).coeffs),
{
    let e = mb_tokens(data, s, fh, m, top, left);
    if fh.mb_no_coeff_skip && m.skip {
        lemma_res_ok_zero(buf, e.coeffs);
    } else {
        lemma_res_ok(res, buf, e.coeffs);
    }
}

proof fn lemma_scan(n: int)
    requires
        0 <= n < 16,
    ensures
        SCAN[n] == scan(n),
        scan(n) + 3 * 32 + 8 <= 500,
        n % 2 == 0 ==> scan(n + 1) == scan(n) + 4,
{
    assert(SCAN[0] == 0 && SCAN[1] == 4 && SCAN[2] == 8 && SCAN[3] == 12);
    assert(SCAN[4] == 128 && SCAN[5] == 132 && SCAN[6] == 136 && SCAN[7] == 140);
    assert(SCAN[8] == 256 && SCAN[9] == 260 && SCAN[10] == 264 && SCAN[11] == 268);
    assert(SCAN[12] == 384 && SCAN[13] == 388 && SCAN[14] == 392 && SCAN[15] == 396);
}

/// Moves the last four columns of the scratch block's luma and chroma
/// blocks (and of the rows above them) to the left of the blocks.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn rotate_left(ws: &mut [u8])
    requires
        old(ws)@.len() == YUV_SIZE,
    ensures
        final(ws)@.len() == YUV_SIZE,
        final(ws)@ == rot3(old(ws)@, 17, 9, 9),
{
    proof { assert(ws@.len() == ws.len()); }
    let ghost w0 = ws@;
    assert(ws@ =~= rot3(w0, 0, 0, 0));
    let mut j: usize = 0;
    while j < 17
        invariant
            j <= 17,
            ws@.len() == YUV_SIZE,
            ws@ == rot3(w0, j as int, 0, 0),
        decreases 17 - j,
    {
        let r = Y_OFF - BPS + j * BPS;
        copy_within(ws, r + 12, r - 4, 4);
        assert(ws@ =~= rot3(w0, j + 1, 0, 0));
        j = j + 1;
    }
    let mut j: usize = 0;
    while j < 9
        invariant
            j <= 9,
            ws@.len() == YUV_SIZE,
            ws@ == rot3(w0, 17, j as int, j as int),
        decreases 9 - j,
    {
        let ru = U_OFF - BPS + j * BPS;
        let rv = V_OFF - BPS + j * BPS;
        copy_within(ws, ru + 4, ru - 4, 4);
        assert(ws@ =~= rot3(w0, 17, j + 1, j as int));
        copy_within(ws, rv + 4, rv - 4, 4);
        assert(ws@ =~= rot3(w0, 17, j + 1, j + 1));
        j = j + 1;
    }
}

/// Sets up the pixels above and to the right of a `B_PRED` macroblock.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn top_right(ws: &mut [u8], top_y: &Vec<u8>, mb_x: usize, mb_y: usize, mb_w: usize)
    requires
        old(ws)@.len() == YUV_SIZE,
        mb_x < mb_w,
        top_y@.len() == 16 * mb_w,
    ensures
        final(ws)@.len() == YUV_SIZE,
        final(ws)@ == set_tr(old(ws)@, top_y@, mb_x as int, mb_y as int, mb_w as int),
{
    proof { assert(ws@.len() == ws.len()); assert(top_y@.len() == top_y.len()); }
    let tr = Y_OFF - BPS + 16;
    if mb_y > 0 {
        if mb_x >= mb_w - 1 {
            let v = top_y[16 * mb_x + 15];
            fill_n(ws, tr, 4, v);
        } else {
            copy_n(ws, tr, top_y.as_slice(), 16 * mb_x + 16, 4);
        }
    }
    // The top-right samples of the right column's lower blocks repeat
    // the macroblock's.
    let ghost w1 = ws@;
    assert(ws@ =~= tr_rep(w1, 1));
    let mut k: usize = 1;
    while k < 4
        invariant
            1 <= k <= 4,
            ws@.len() == YUV_SIZE,
            ws@ == tr_rep(w1, k as int),
        decreases 4 - k,
    {
        copy_within(ws, tr, tr + 4 * k * BPS, 4);
        assert(ws@ =~= tr_rep(w1, k + 1));
        k = k + 1;
    }
}

/// The sixteen subblocks of a `B_PRED` macroblock.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn do_luma4(ws: &mut [u8], m: &MbModes, bits0: u32, coeffs: &[i16], Ghost(bm): Ghost<Seq<int>>, Ghost(co): Ghost<Seq<int>>)
    requires
        old(ws)@.len() == YUV_SIZE,
        coeffs@.len() == 384,
        forall|i: int| 0 <= i < 16 ==> m.imodes@[i] < 10,
    ensures
        final(ws)@.len() == YUV_SIZE,
        (forall|i: int| 0 <= i < 16 ==> #[trigger] m.imodes@[i] == bm[i]) && (forall|n: int|
            0 <= n < 16 ==> #[trigger] y_ok(bits0, coeffs@, co, n)) ==> final(ws)@ == rec_luma4(old(ws)@, bm, co, 16),
{
    hide(add_res);
    hide(paint4);
    proof { assert(ws@.len() == ws.len()); assert(coeffs@.len() == coeffs.len()); }
    let ghost w0 = ws@;
    let ghost g = (forall|i: int| 0 <= i < 16 ==> #[trigger] m.imodes@[i] == bm[i]) && (forall|n: int|
        0 <= n < 16 ==> #[trigger] y_ok(bits0, coeffs@, co, n));
    let mut bits = bits0;
    let mut n: usize = 0;
    while n < 16
        invariant
            n <= 16,
            ws@.len() == YUV_SIZE,
            bits == bits_at(bits0, n as nat),
            g ==> ws@ == rec_luma4(w0, bm, co, n as int),
        decreases 16 - n,
    {
        proof { lemma_scan(n as int); }
        let d = Y_OFF + SCAN[n];
        pred4_fast(ws, d, m.imodes[n]);
        let ghost w2 = ws@;
        do_transform(bits, coeffs, 16 * n, ws, d);
        proof {
            if g {
                assert(y_ok(bits0, coeffs@, co, n as int));
                let cb = blk(co, 16 * n);
                if bits >> 30u32 == 0 {
                    lemma_add_zero(w2, d as int, cb);
                }
                assert(ws@ == add_res(w2, d as int, idct(cb)));
                assert(m.imodes@[n as int] == bm[n as int]);
                assert(d == s_y() + scan(n as int));
                assert(ws@ == rec_luma4(w0, bm, co, n + 1));
            }
            assert(bits_at(bits0, (n + 1) as nat) == bits_at(bits0, n as nat) << 2u32);
        }
        bits = bits << 2u32;
        n = n + 1;
    }
}

/// A 16x16 predicted macroblock: prediction `mode`, then the residuals.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn do_luma16(ws: &mut [u8], mode: u8, bits0: u32, coeffs: &[i16], Ghost(co): Ghost<Seq<int>>)
    requires
        old(ws)@.len() == YUV_SIZE,
        coeffs@.len() == 384,
        mode < 7,
    ensures
        final(ws)@.len() == YUV_SIZE,
        (forall|n: int| 0 <= n < 16 ==> #[trigger] y_ok(bits0, coeffs@, co, n)) ==> final(ws)@ == rec_res16(
            paint_big(old(ws)@, s_y(), 16, mode as int),
            co,
            16,
        ),
{
    hide(add_res);
    hide(paint_big);
    proof { assert(ws@.len() == ws.len()); assert(coeffs@.len() == coeffs.len()); }
    let ghost g = forall|n: int| 0 <= n < 16 ==> #[trigger] y_ok(bits0, coeffs@, co, n);
    pred_block(ws, Y_OFF, 16, mode);
    let ghost w1 = ws@;
    let mut bits = bits0;
    if bits != 0 {
        let mut n: usize = 0;
        while n < 16
            invariant
                n <= 16,
                ws@.len() == YUV_SIZE,
                bits == bits_at(bits0, n as nat),
                g ==> ws@ == rec_res16(w1, co, n as int),
            decreases 16 - n,
        {
            proof {
                lemma_scan(n as int);
                assert(bits_at(bits0, (n + 1) as nat) == bits_at(bits0, n as nat) << 2u32);
            }
            let ghost w2 = ws@;
            if n % 2 == 0 && bits >> 28u32 == 0xf {
                // Two full transforms side by side, done together.
                proof {
                    lemma_scan(n + 1);
                    assert(bits_at(bits0, (n + 2) as nat) == bits_at(bits0, (n + 1) as nat) << 2u32);
                    assert(bits >> 28u32 == 0xf ==> bits >> 30u32 == 3 && (bits << 2u32) >> 30u32 == 3 && bits << 4u32 == (bits
                        << 2u32) << 2u32) by (bit_vector);
                }
                transform_two(coeffs, 16 * n, ws, Y_OFF + SCAN[n]);
                proof {
                    if g {
                        assert(y_ok(bits0, coeffs@, co, n as int));
                        assert(y_ok(bits0, coeffs@, co, n + 1));
                        let ca = blk(co, 16 * n);
                        let cb = blk(co, 16 * (n + 1));
                        assert(cblk(coeffs@, 16 * n) == ca);
                        assert(cblk(coeffs@, 16 * n + 16) == cb);
                        let w3 = add_res(w2, s_y() + scan(n as int), idct(ca));
                        assert(w3 == rec_res16(w1, co, n + 1));
                        assert(ws@ == add_res(w3, s_y() + scan(n + 1), idct(cb)));
                        assert(ws@ == rec_res16(w1, co, n + 2));
                    }
                }
                bits = bits << 4u32;
                n = n + 2;
            } else {
                do_transform(bits, coeffs, 16 * n, ws, Y_OFF + SCAN[n]);
                proof {
                    if g {
                        assert(y_ok(bits0, coeffs@, co, n as int));
                        let cb = blk(co, 16 * n);
                        if bits >> 30u32 == 0 {
                            lemma_add_zero(w2, s_y() + scan(n as int), cb);
                        }
                        assert(ws@ == add_res(w2, s_y() + scan(n as int), idct(cb)));
                        assert(ws@ == rec_res16(w1, co, n + 1));
                    }
                }
                bits = bits << 2u32;
                n = n + 1;
            }
        }
    } else {
        proof {
            if g {
                assert forall|n: int| 0 <= n < 16 implies zero_blk(#[trigger] blk(co, 16 * n)) by {
                    assert(y_ok(bits0, coeffs@, co, n));
                    lemma_bits_zero(n as nat);
                    assert(0u32 >> 30u32 == 0) by (bit_vector);
                }
                lemma_res16_zero(w1, co, 16);
            }
        }
    }
}

/// Reconstructs one macroblock in the scratch block `ws` (`ReconstructRow`
/// for one `mb_x`): prediction from the samples around it, plus the
/// inverse transforms of `coeffs`. With selector bits that are sound for
/// the macroblock's coefficients `co`, the result is the specification's
/// `mb_recon` of the scratch block as `mb_setup` prepares it.
fn reconstruct_mb(
    ws: &mut [u8],
    top_y: &Vec<u8>,
    top_u: &Vec<u8>,
    top_v: &Vec<u8>,
    mb_x: usize,
    mb_y: usize,
    mb_w: usize,
    m: &MbModes,
    res: &Residuals,
    coeffs: &[i16],
    Ghost(ms): Ghost<MbModeSpec>,
    Ghost(co): Ghost<Seq<int>>,
)
    requires
        old(ws)@.len() == YUV_SIZE,
        mb_x < mb_w,
        top_y@.len() == 16 * mb_w,
        top_u@.len() == 8 * mb_w,
        top_v@.len() == 8 * mb_w,
        coeffs@.len() == 384,
        m.uvmode < 4,
        forall|i: int| 0 <= i < 16 ==> m.imodes@[i] < 10,
        !m.is_i4x4 ==> m.imodes@[0] < 4,
    ensures
        final(ws)@.len() == YUV_SIZE,
        m.matches(ms) && res_ok(res.non_zero_y, res.non_zero_uv, coeffs@, co) ==> final(ws)@ == mb_recon(
            mb_setup(old(ws)@, top_y@, top_u@, top_v@, mb_x as int, mb_y as int, mb_w as int, m.is_i4x4),
            ms,
            mb_x as int,
            mb_y as int,
            co,
        ),
{
    hide(add_res);
    hide(paint_big);
    hide(paint4);
    hide(rot3);
    hide(set_tr);
    hide(put_run);
    proof {
        assert(ws@.len() == ws.len());
        assert(coeffs@.len() == coeffs.len());
        assert(top_y@.len() == top_y.len());
    }
    let ghost g = m.matches(ms) && res_ok(res.non_zero_y, res.non_zero_uv, coeffs@, co);
    // Rotate the left samples in from the previous macroblock.
    if mb_x > 0 {
        rotate_left(ws);
    }
    if mb_y > 0 {
        copy_n(ws, Y_OFF - BPS, top_y.as_slice(), 16 * mb_x, 16);
        copy_n(ws, U_OFF - BPS, top_u.as_slice(), 8 * mb_x, 8);
        copy_n(ws, V_OFF - BPS, top_v.as_slice(), 8 * mb_x, 8);
    }
    if m.is_i4x4 {
        top_right(ws, top_y, mb_x, mb_y, mb_w);
        assert(ws@ == mb_setup(old(ws)@, top_y@, top_u@, top_v@, mb_x as int, mb_y as int, mb_w as int, true));
        do_luma4(ws, m, res.non_zero_y, coeffs, Ghost(ms.bmodes), Ghost(co));
    } else {
        assert(ws@ == mb_setup(old(ws)@, top_y@, top_u@, top_v@, mb_x as int, mb_y as int, mb_w as int, false));
        let mode = check_mode(mb_x, mb_y, m.imodes[0]);
        do_luma16(ws, mode, res.non_zero_y, coeffs, Ghost(co));
    }
    let ghost wy = ws@;
    let uvmode = check_mode(mb_x, mb_y, m.uvmode);
    pred_block(ws, U_OFF, 8, uvmode);
    pred_block(ws, V_OFF, 8, uvmode);
    let ghost wp = ws@;
    do_uv_transform(res.non_zero_uv, coeffs, 256, ws, U_OFF);
    let ghost wu = ws@;
    do_uv_transform(res.non_zero_uv >> 8u32, coeffs, 320, ws, V_OFF);
    proof {
        if g {
            lemma_uv_ok(res.non_zero_uv, coeffs@, co, 256, wp, wu, s_u());
            lemma_uv_ok(res.non_zero_uv >> 8u32, coeffs@, co, 320, wu, ws@, s_v());
        }
    }
}

/// The reconstruction state the row loop holds.
pub open spec fn recon_of(ws: Seq<u8>, ty: Seq<u8>, tu: Seq<u8>, tv: Seq<u8>, pl: Planes) -> Recon {
    Recon { ws, ty, tu, tv, y: pl.y@, u: pl.u@, v: pl.v@ }
}

/// Writes the macroblock in the scratch block to the planes, and keeps
/// its unfiltered bottom rows for the next row's prediction.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn emit_mb(
    ws: &[u8],
    top_y: &mut Vec<u8>,
    top_u: &mut Vec<u8>,
    top_v: &mut Vec<u8>,
    pl: &mut Planes,
    mb_x: usize,
    mb_y: usize,
    mb_w: usize,
    mb_h: usize,
)
    requires
        ws@.len() == YUV_SIZE,
        mb_x < mb_w,
        mb_y < mb_h,
        old(pl).mb_shape(mb_w as nat, mb_h as nat),
        old(top_y)@.len() == 16 * mb_w,
        old(top_u)@.len() == 8 * mb_w,
        old(top_v)@.len() == 8 * mb_w,
    ensures
        final(pl).mb_shape(mb_w as nat, mb_h as nat),
        final(pl).width == old(pl).width,
        final(pl).height == old(pl).height,
        final(top_y)@.len() == 16 * mb_w,
        final(top_u)@.len() == 8 * mb_w,
        final(top_v)@.len() == 8 * mb_w,
        final(top_y)@ == (if mb_y < mb_h - 1 {
            put_run(old(top_y)@, 16 * mb_x, ws@, 520, 16)
        } else {
            old(top_y)@
        }),
        final(top_u)@ == (if mb_y < mb_h - 1 {
            put_run(old(top_u)@, 8 * mb_x, ws@, 808, 8)
        } else {
            old(top_u)@
        }),
        final(top_v)@ == (if mb_y < mb_h - 1 {
            put_run(old(top_v)@, 8 * mb_x, ws@, 824, 8)
        } else {
            old(top_v)@
        }),
        final(pl).y@ == put_rows(old(pl).y@, 16 * mb_x, 16 * mb_y, 16 * mb_w, ws@, s_y(), 16, 16),
        final(pl).u@ == put_rows(old(pl).u@, 8 * mb_x, 8 * mb_y, 8 * mb_w, ws@, s_u(), 8, 8),
        final(pl).v@ == put_rows(old(pl).v@, 8 * mb_x, 8 * mb_y, 8 * mb_w, ws@, s_v(), 8, 8),
{
    hide(put_run);
    let y_stride = 16 * mb_w;
    let uv_stride = 8 * mb_w;
    if mb_y < mb_h - 1 {
        copy_n(top_y.as_mut_slice(), 16 * mb_x, ws, Y_OFF + 15 * BPS, 16);
        copy_n(top_u.as_mut_slice(), 8 * mb_x, ws, U_OFF + 7 * BPS, 8);
        copy_n(top_v.as_mut_slice(), 8 * mb_x, ws, V_OFF + 7 * BPS, 8);
    }
    let ghost y0 = pl.y@;
    let ghost u0 = pl.u@;
    let ghost v0 = pl.v@;
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            pl.mb_shape(mb_w as nat, mb_h as nat),
            pl.width == old(pl).width,
            pl.height == old(pl).height,
            pl.y@ == put_rows(y0, 16 * mb_x, 16 * mb_y, 16 * mb_w, ws@, s_y(), 16, j as int),
            pl.u@ == u0,
            pl.v@ == v0,
        decreases 16 - j,
    {
        proof { lemma_row(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, j as int); }
        copy_n(pl.y.as_mut_slice(), (16 * mb_y + j) * y_stride + 16 * mb_x, ws, Y_OFF + j * BPS, 16);
        j = j + 1;
    }
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            pl.mb_shape(mb_w as nat, mb_h as nat),
            pl.width == old(pl).width,
            pl.height == old(pl).height,
            pl.y@ == put_rows(y0, 16 * mb_x, 16 * mb_y, 16 * mb_w, ws@, s_y(), 16, 16),
            pl.u@ == put_rows(u0, 8 * mb_x, 8 * mb_y, 8 * mb_w, ws@, s_u(), 8, j as int),
            pl.v@ == put_rows(v0, 8 * mb_x, 8 * mb_y, 8 * mb_w, ws@, s_v(), 8, j as int),
        decreases 8 - j,
    {
        proof { lemma_row(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 8, j as int); }
        copy_n(pl.u.as_mut_slice(), (8 * mb_y + j) * uv_stride + 8 * mb_x, ws, U_OFF + j * BPS, 8);
        copy_n(pl.v.as_mut_slice(), (8 * mb_y + j) * uv_stride + 8 * mb_x, ws, V_OFF + j * BPS, 8);
        j = j + 1;
    }
}

/// Sets the scratch block's borders for macroblock row `mb_y`.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn init_row(wsl: &mut [u8], mb_y: usize)
    requires
        old(wsl)@.len() == YUV_SIZE,
    ensures
        final(wsl)@.len() == YUV_SIZE,
        final(wsl)@ == row_init(old(wsl)@, mb_y as int),
{
    proof { assert(wsl@.len() == wsl.len()); }
    let ghost w0 = wsl@;
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            wsl@.len() == YUV_SIZE,
            forall|i: int| 0 <= i < YUV_SIZE ==> #[trigger] wsl@[i] == if 39 <= i && (i - 39) % 32 == 0 && (i - 39) / 32 < j {
                129u8
            } else {
                w0[i]
            },
        decreases 16 - j,
    {
        set(wsl, Y_OFF + j * BPS - 1, 129);
        j = j + 1;
    }
    let ghost w1 = wsl@;
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            wsl@.len() == YUV_SIZE,
            forall|i: int| 0 <= i < YUV_SIZE ==> #[trigger] wsl@[i] == if (583 <= i && (i - 583) % 32 == 0 && (i - 583) / 32 < j)
                || (599 <= i && (i - 599) % 32 == 0 && (i - 599) / 32 < j) {
                129u8
            } else {
                w1[i]
            },
        decreases 8 - j,
    {
        set(wsl, U_OFF + j * BPS - 1, 129);
        set(wsl, V_OFF + j * BPS - 1, 129);
        j = j + 1;
    }
    if mb_y > 0 {
        set(wsl, Y_OFF - 1 - BPS, 129);
        set(wsl, U_OFF - 1 - BPS, 129);
        set(wsl, V_OFF - 1 - BPS, 129);
    } else {
        fill_n(wsl, Y_OFF - BPS - 1, 16 + 4 + 1, 127);
        fill_n(wsl, U_OFF - BPS - 1, 8 + 1, 127);
        fill_n(wsl, V_OFF - BPS - 1, 8 + 1, 127);
    }
    assert(wsl@ =~= row_init(w0, mb_y as int));
}

/// Every inner-edge count starts from the plane itself.
proof fn lemma_inner_base(b: Seq<u8>, d: int, s1: int, s2: int)
    ensures
        forall|size: nat, simple: bool, e: int, i: int, h: int|
            #![trigger lf_inner_edges(b, d, 1, 1, s2, 0, size, simple, e, i, h)]
            lf_inner_edges(b, d, 1, 1, s2, 0, size, simple, e, i, h) == b,
        forall|size: nat, simple: bool, e: int, i: int, h: int|
            #![trigger lf_inner_edges(b, d, s2, s2, 1, 0, size, simple, e, i, h)]
            lf_inner_edges(b, d, s2, s2, 1, 0, size, simple, e, i, h) == b,
{
}

/// The `n`th inner edge is a run on the plane with the first `n - 1` done.
proof fn lemma_inner_step(
    b: Seq<u8>,
    d: int,
    gap: int,
    hs: int,
    vs: int,
    n: nat,
    size: nat,
    simple: bool,
    e: int,
    i: int,
    h: int,
)
    requires
        n >= 1,
    ensures
        lf_inner_edges(b, d, gap, hs, vs, n, size, simple, e, i, h) == lf_run(
            lf_inner_edges(b, d, gap, hs, vs, (n - 1) as nat, size, simple, e, i, h),
            d + 4 * n * gap,
            hs,
            vs,
            size,
            simple,
            true,
            e,
            i,
            h,
        ),
{
}

/// The lanes `filter_mb` filters do not overlap.
proof fn lemma_apart_mb(s: int)
    requires
        s >= 8,
    ensures
        lanes_apart(1, s, 16),
        lanes_apart(1, s, 8),
        lanes_apart(s, 1, 8),
        s >= 16 ==> lanes_apart(s, 1, 16),
{
}

/// `DoFilter`: the loop filter of macroblock `(mb_x, mb_y)` in the planes.
#[verifier::loop_isolation(false)]
fn filter_mb(pl: &mut Planes, mb_x: usize, mb_y: usize, mb_w: usize, mb_h: usize, f: FInfo, filter_type: u32)
    requires
        old(pl).mb_shape(mb_w as nat, mb_h as nat),
        mb_x < mb_w,
        mb_y < mb_h,
        finfo_ok(f),
    ensures
        final(pl).mb_shape(mb_w as nat, mb_h as nat),
        final(pl).width == old(pl).width,
        final(pl).height == old(pl).height,
        (final(pl).y@, final(pl).u@, final(pl).v@) == lf_mb(
            old(pl).y@,
            old(pl).u@,
            old(pl).v@,
            mb_x as int,
            mb_y as int,
            mb_w as int,
            filter_type == 1,
            f.inner,
            f.limit as int,
            f.ilevel as int,
            f.hev_thresh as int,
        ),
{
    hide(lf_run);
    hide(lf_inner_edges);
    hide(lf_mb_plane);
    hide(lanes_apart);
    let limit = f.limit;
    if limit == 0 {
        return;
    }
    let ys = pl.y_stride;
    proof {
        lemma_apart_mb(pl.y_stride as int);
        lemma_apart_mb(pl.uv_stride as int);
    }
    let ghost y0 = pl.y@;
    let ghost u0 = pl.u@;
    let ghost v0 = pl.v@;
    let ghost e = limit as int;
    proof {
        lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, 0);
        lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 8, 0);
    }
    let yd = 16 * mb_y * ys + 16 * mb_x;
    if filter_type == 1 {
        if mb_x > 0 {
            simple_filter(pl.y.as_mut_slice(), yd, 1, ys, 16, limit + 4);
        }
        let ghost y1 = pl.y@;
        if f.inner {
            proof { lemma_inner_base(pl.y@, yd as int, 1, ys as int); }
            let mut k: usize = 1;
            while k < 4
                invariant
                    1 <= k <= 4,
                    pl.mb_shape(mb_w as nat, mb_h as nat),
                    pl.width == old(pl).width,
                    pl.height == old(pl).height,
                    ys == pl.y_stride,
                    pl.y@ == lf_inner_edges(y1, yd as int, 1, 1, ys as int, (k - 1) as nat, 16, true, e, 0, 0),
                    pl.u@ == u0,
                    pl.v@ == v0,
                decreases 4 - k,
            {
                proof { lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, k as int); }
                proof {
                    lemma_inner_step(y1, yd as int, 1, 1, ys as int, k as nat, 16, true, e, 0, 0);
                    lemma_run_simple(pl.y@, yd + 4 * k, 1, ys as int, 16, e, true, 0, 0);
                }
                simple_filter(pl.y.as_mut_slice(), yd + 4 * k, 1, ys, 16, limit);
                k = k + 1;
            }
        }
        let ghost y2 = pl.y@;
        if mb_y > 0 {
            simple_filter(pl.y.as_mut_slice(), yd, ys, 1, 16, limit + 4);
        }
        let ghost y3 = pl.y@;
        if f.inner {
            proof { lemma_inner_base(pl.y@, yd as int, 1, ys as int); }
            let mut k: usize = 1;
            while k < 4
                invariant
                    1 <= k <= 4,
                    pl.mb_shape(mb_w as nat, mb_h as nat),
                    pl.width == old(pl).width,
                    pl.height == old(pl).height,
                    ys == pl.y_stride,
                    pl.y@ == lf_inner_edges(y3, yd as int, ys as int, ys as int, 1, (k - 1) as nat, 16, true, e, 0, 0),
                    pl.u@ == u0,
                    pl.v@ == v0,
                decreases 4 - k,
            {
                proof { lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, k as int); }
                proof {
                    lemma_inner_step(y3, yd as int, ys as int, ys as int, 1, k as nat, 16, true, e, 0, 0);
                    lemma_run_simple(pl.y@, yd + 4 * k * ys, ys as int, 1, 16, e, true, 0, 0);
                }
                simple_filter(pl.y.as_mut_slice(), yd + 4 * k * ys, ys, 1, 16, limit);
                k = k + 1;
            }
        }
        proof {
            reveal(lf_mb_plane);
            assert(pl.y@ == lf_mb_plane(y0, yd as int, ys as int, 16, mb_x > 0, mb_y > 0, true, f.inner, e, 0, 0));
        }
    } else {
        let uvs = pl.uv_stride;
        let uvd = 8 * mb_y * uvs + 8 * mb_x;
        let il = f.ilevel;
        let ht = f.hev_thresh;
        proof { lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 8, 1); }
        let ghost gi = il as int;
        let ghost gh = ht as int;
        if mb_x > 0 {
            filter_loop(pl.y.as_mut_slice(), yd, 1, ys, 16, limit + 4, il, ht, false);
            filter_loop_uv(pl.u.as_mut_slice(), pl.v.as_mut_slice(), uvd, 1, uvs, limit + 4, il, ht, false);
        }
        let ghost y1 = pl.y@;
        let ghost u1 = pl.u@;
        let ghost v1 = pl.v@;
        if f.inner {
            proof { lemma_inner_base(pl.y@, yd as int, 1, ys as int); }
            let mut k: usize = 1;
            while k < 4
                invariant
                    1 <= k <= 4,
                    pl.mb_shape(mb_w as nat, mb_h as nat),
                    pl.width == old(pl).width,
                    pl.height == old(pl).height,
                    ys == pl.y_stride,
                    uvs == pl.uv_stride,
                    pl.y@ == lf_inner_edges(y1, yd as int, 1, 1, ys as int, (k - 1) as nat, 16, false, e, gi, gh),
                    pl.u@ == u1,
                    pl.v@ == v1,
                decreases 4 - k,
            {
                proof { lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, k as int); }
                proof { lemma_inner_step(y1, yd as int, 1, 1, ys as int, k as nat, 16, false, e, gi, gh); }
                filter_loop(pl.y.as_mut_slice(), yd + 4 * k, 1, ys, 16, limit, il, ht, true);
                k = k + 1;
            }
            filter_loop_uv(pl.u.as_mut_slice(), pl.v.as_mut_slice(), uvd + 4, 1, uvs, limit, il, ht, true);
            proof {
                lemma_inner_base(u1, uvd as int, 1, uvs as int);
                lemma_inner_base(v1, uvd as int, 1, uvs as int);
                lemma_inner_step(u1, uvd as int, 1, 1, uvs as int, 1, 8, false, e, gi, gh);
                lemma_inner_step(v1, uvd as int, 1, 1, uvs as int, 1, 8, false, e, gi, gh);
                assert(pl.u@ == lf_inner_edges(u1, uvd as int, 1, 1, uvs as int, 1, 8, false, e, gi, gh));
                assert(pl.v@ == lf_inner_edges(v1, uvd as int, 1, 1, uvs as int, 1, 8, false, e, gi, gh));
            }
        }
        let ghost y2 = pl.y@;
        let ghost u2 = pl.u@;
        let ghost v2 = pl.v@;
        if mb_y > 0 {
            filter_loop(pl.y.as_mut_slice(), yd, ys, 1, 16, limit + 4, il, ht, false);
            filter_loop_uv(pl.u.as_mut_slice(), pl.v.as_mut_slice(), uvd, uvs, 1, limit + 4, il, ht, false);
        }
        let ghost y3 = pl.y@;
        let ghost u3 = pl.u@;
        let ghost v3 = pl.v@;
        if f.inner {
            proof { lemma_inner_base(pl.y@, yd as int, 1, ys as int); }
            let mut k: usize = 1;
            while k < 4
                invariant
                    1 <= k <= 4,
                    pl.mb_shape(mb_w as nat, mb_h as nat),
                    pl.width == old(pl).width,
                    pl.height == old(pl).height,
                    ys == pl.y_stride,
                    uvs == pl.uv_stride,
                    pl.y@ == lf_inner_edges(y3, yd as int, ys as int, ys as int, 1, (k - 1) as nat, 16, false, e, gi, gh),
                    pl.u@ == u3,
                    pl.v@ == v3,
                decreases 4 - k,
            {
                proof { lemma_edges(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, k as int); }
                proof { lemma_inner_step(y3, yd as int, ys as int, ys as int, 1, k as nat, 16, false, e, gi, gh); }
                filter_loop(pl.y.as_mut_slice(), yd + 4 * k * ys, ys, 1, 16, limit, il, ht, true);
                k = k + 1;
            }
            filter_loop_uv(pl.u.as_mut_slice(), pl.v.as_mut_slice(), uvd + 4 * uvs, uvs, 1, limit, il, ht, true);
            proof {
                lemma_inner_base(u3, uvd as int, 1, uvs as int);
                lemma_inner_base(v3, uvd as int, 1, uvs as int);
                lemma_inner_step(u3, uvd as int, uvs as int, uvs as int, 1, 1, 8, false, e, gi, gh);
                lemma_inner_step(v3, uvd as int, uvs as int, uvs as int, 1, 1, 8, false, e, gi, gh);
                assert(pl.u@ == lf_inner_edges(u3, uvd as int, uvs as int, uvs as int, 1, 1, 8, false, e, gi, gh));
                assert(pl.v@ == lf_inner_edges(v3, uvd as int, uvs as int, uvs as int, 1, 1, 8, false, e, gi, gh));
            }
        }
        proof {
            reveal(lf_mb_plane);
            assert(pl.y@ == lf_mb_plane(y0, yd as int, ys as int, 16, mb_x > 0, mb_y > 0, false, f.inner, e, gi, gh));
            assert(pl.u@ == lf_mb_plane(u0, uvd as int, uvs as int, 8, mb_x > 0, mb_y > 0, false, f.inner, e, gi, gh));
            assert(pl.v@ == lf_mb_plane(v0, uvd as int, uvs as int, 8, mb_x > 0, mb_y > 0, false, f.inner, e, gi, gh));
        }
    }
}

/// One row of macroblocks: their coefficients from the row's token
/// partition, then reconstruction into the frame.
///
/// The partition's reader and the nonzero contexts end where
/// `vp8spec::row_tokens` has them, for the row's modes `rm`.
#[verifier::loop_isolation(false)]
fn decode_mb_row(
    tok: &mut BoolReader,
    data: &[u8],
    hdr: &Header,
    modes: &Vec<MbModes>,
    nz_top: &mut Vec<Nz>,
    finfo: &mut Vec<FInfo>,
    top_y: &mut Vec<u8>,
    top_u: &mut Vec<u8>,
    top_v: &mut Vec<u8>,
    ws: &mut Vec<u8>,
    coeffs: &mut Vec<i16>,
    pl: &mut Planes,
    mb_y: usize,
    Ghost(ps): Ghost<int>,
    Ghost(s0): Ghost<BoolState>,
    Ghost(fh): Ghost<FrameHeader>,
    Ghost(rm): Ghost<Seq<MbModeSpec>>,
    Ghost(tops): Ghost<Seq<Seq<bool>>>,
) -> (r: Result<(), Error>)
    requires
        hdr.ok(data@.len()),
        old(tok).inv(data@.len()),
        mb_y < hdr.mb_h,
        old(pl).mb_shape(hdr.mb_w as nat, hdr.mb_h as nat),
        modes@.len() == hdr.mb_w,
        forall|j: int| 0 <= j < hdr.mb_w ==> #[trigger] modes_ok(modes@[j]),
        old(nz_top)@.len() == hdr.mb_w,
        old(top_y)@.len() == 16 * hdr.mb_w,
        old(top_u)@.len() == 8 * hdr.mb_w,
        old(top_v)@.len() == 8 * hdr.mb_w,
        old(ws)@.len() == YUV_SIZE,
        old(coeffs)@.len() == 384,
        tops.len() == hdr.mb_w,
    ensures
        final(tok).inv(data@.len()),
        final(tok).end == old(tok).end,
        old(tok).eof ==> final(tok).eof,
        final(pl).mb_shape(hdr.mb_w as nat, hdr.mb_h as nat),
        final(pl).width == old(pl).width,
        final(pl).height == old(pl).height,
        final(nz_top)@.len() == hdr.mb_w,
        final(top_y)@.len() == 16 * hdr.mb_w,
        final(top_u)@.len() == 8 * hdr.mb_w,
        final(top_v)@.len() == 8 * hdr.mb_w,
        final(ws)@.len() == YUV_SIZE,
        final(coeffs)@.len() == 384,
        r is Ok ==> final(finfo)@.len() == (if hdr.filter_type > 0 {
            hdr.mb_w as int
        } else {
            0
        }),
        forall|j: int| 0 <= j < final(finfo)@.len() ==> #[trigger] finfo_ok(final(finfo)@[j]),
        r is Ok ==> !final(tok).eof,
        r is Ok && hdr.tok_matches(fh) && (forall|j: int| 0 <= j < hdr.mb_w ==> (#[trigger] modes@[j]).matches(rm[j]))
            && old(tok).rel(data@, ps, s0) && (forall|j: int|
            0 <= j < hdr.mb_w ==> (#[trigger] old(nz_top)@[j]).is(tops[j])) ==> {
            let o = row_tokens(part(data@, ps, old(tok).end as int), s0, fh, rm, tops, hdr.mb_w as nat);
            &&& final(tok).rel(data@, ps, o.s)
            &&& forall|j: int| 0 <= j < hdr.mb_w ==> (#[trigger] final(nz_top)@[j]).is(o.tops[j])
            &&& row_solid(part(data@, ps, old(tok).end as int), s0, fh, rm, tops, hdr.mb_w as nat) && hdr.lf_matches(fh)
                && hdr.filter_type > 0 ==> forall|j: int|
                0 <= j < hdr.mb_w ==> fi_is(#[trigger] final(finfo)@[j], fh, rm[j], o.mbs[j])
            &&& row_tame(o.mbs) ==> recon_of(final(ws)@, final(top_y)@, final(top_u)@, final(top_v)@, *final(pl))
                == row_recon(
                recon_of(old(ws)@, old(top_y)@, old(top_u)@, old(top_v)@, *old(pl)),
                rm,
                o.mbs,
                mb_y as int,
                hdr.mb_w as int,
                hdr.mb_h as int,
                hdr.mb_w as nat,
            )
        },
{
    hide(row_tokens);
    hide(mb_tokens);
    hide(Header::tok_matches);
    hide(Nz::is);
    hide(fi_is);
    hide(Header::lf_matches);
    hide(tok_solid);
    let ghost len = data@.len();
    let mb_w = hdr.mb_w;
    let mb_h = hdr.mb_h;
    let y_stride = 16 * mb_w;
    let uv_stride = 8 * mb_w;
    let ghost tpd = part(data@, ps, tok.end as int);
    let ghost gg = hdr.tok_matches(fh) && (forall|j: int| 0 <= j < mb_w ==> (#[trigger] modes@[j]).matches(rm[j]))
        && tok.rel(data@, ps, s0) && (forall|j: int| 0 <= j < mb_w ==> (#[trigger] nz_top@[j]).is(tops[j]));
    let mut left_nz = Nz { nz: 0, nz_dc: 0 };
    let ghost full = row_tokens(tpd, s0, fh, rm, tops, mb_w as nat);
    let ghost tame = row_tame(full.mbs);
    let ghost sol = row_solid(tpd, s0, fh, rm, tops, mb_w as nat) && hdr.lf_matches(fh) && hdr.filter_type > 0;
    let ghost st0 = recon_of(ws@, top_y@, top_u@, top_v@, *pl);
    proof {
        lemma_nz_zero();
        lemma_row_tokens_zero(tpd, s0, fh, rm, tops);
        lemma_row_tokens_len(tpd, s0, fh, rm, tops, mb_w as nat);
    }
    finfo.clear();
    let mut mb_x: usize = 0;
    while mb_x < mb_w
        invariant
            mb_x <= mb_w,
            mb_y < mb_h,
                    tok.inv(len),
            1 <= mb_w,
            mb_x > 0 ==> !tok.eof,
            old(tok).eof ==> tok.eof,
                    tok.end == old(tok).end,
            // The partition's reader and the contexts are where the
            // specification has them after `mb_x` macroblocks of the row.
            gg && !tok.eof ==> {
                let r = row_tokens(tpd, s0, fh, rm, tops, mb_x as nat);
                &&& tok.rel(data@, ps, r.s)
                &&& left_nz.is(r.left)
                &&& forall|j: int| 0 <= j < mb_w ==> (#[trigger] nz_top@[j]).is(r.tops[j])
            },
            gg && sol && !tok.eof ==> forall|j: int|
                0 <= j < mb_x ==> fi_is(#[trigger] finfo@[j], fh, rm[j], full.mbs[j]),
            gg && tame && !tok.eof ==> recon_of(ws@, top_y@, top_u@, top_v@, *pl) == row_recon(
                st0,
                rm,
                full.mbs,
                mb_y as int,
                mb_w as int,
                mb_h as int,
                mb_x as nat,
            ),
            pl.mb_shape(mb_w as nat, mb_h as nat),
            pl.width == old(pl).width,
            pl.height == old(pl).height,
            modes@.len() == mb_w,
            forall|j: int| 0 <= j < mb_w ==> #[trigger] modes_ok(modes@[j]),
            finfo@.len() == (if hdr.filter_type > 0 { mb_x as int } else { 0 }),
            forall|j: int| 0 <= j < finfo@.len() ==> #[trigger] finfo_ok(finfo@[j]),
            top_y@.len() == 16 * mb_w,
            top_u@.len() == 8 * mb_w,
            top_v@.len() == 8 * mb_w,
            nz_top@.len() == mb_w,
            ws@.len() == YUV_SIZE,
            coeffs@.len() == 384,
        decreases mb_w - mb_x,
    {
        let m = &modes[mb_x];
        proof { assert(modes_ok(modes@[mb_x as int])); }
        let mut tnz = nz_top[mb_x];
        let ghost rr = row_tokens(tpd, s0, fh, rm, tops, mb_x as nat);
        proof {
            lemma_row_tokens_shape(tpd, s0, fh, rm, tops, mb_x as nat);
        }
        let (res, skip) = mb_coeffs(
            tok,
            data,
            hdr,
            m,
            &mut tnz,
            &mut left_nz,
            coeffs.as_mut_slice(),
            Ghost(ps),
            Ghost(rr.s),
            Ghost(fh),
            Ghost(rm[mb_x as int]),
            Ghost(rr.tops[mb_x as int]),
            Ghost(rr.left),
        );
        nz_top.set(mb_x, tnz);
        if hdr.filter_type > 0 {
            let fi = 2 * m.segment + if m.is_i4x4 { 1 } else { 0 };
            let mut f = hdr.fstrengths[fi];
            proof { assert(finfo_ok(hdr.fstrengths@[fi as int])); }
            f.inner = f.inner || !skip;
            finfo.push(f);
        }
        if tok.eof {
            return Err(Error::Bitstream);
        }
        proof {
            lemma_row_tokens_step(tpd, s0, fh, rm, tops, mb_x as nat);
            if gg {
                let r2 = row_tokens(tpd, s0, fh, rm, tops, (mb_x + 1) as nat);
                let o = mb_tokens(tpd, rr.s, fh, rm[mb_x as int], rr.tops[mb_x as int], rr.left);
                assert(r2.tops == rr.tops.update(mb_x as int, o.top));
                assert(r2.s == o.s && r2.left == o.left);
                assert forall|j: int| 0 <= j < mb_w implies (#[trigger] nz_top@[j]).is(r2.tops[j]) by {
                    if j != mb_x {
                        assert(nz_top@[j].is(rr.tops[j]));
                    }
                }
            }
        }
        let ghost co = mb_tokens(tpd, rr.s, fh, rm[mb_x as int], rr.tops[mb_x as int], rr.left).coeffs;
        let ghost ws0 = ws@;
        proof {
            lemma_row_tokens_mbs(tpd, s0, fh, rm, tops, mb_w as nat, mb_x as int);
            if gg && sol {
                assert(m.matches(rm[mb_x as int]));
                assert(tok_solid_at(tpd, s0, fh, rm, tops, mb_x as int));
                assert(skip == !any_nz(co));
                lemma_fi(*hdr, fh, *m, rm[mb_x as int], finfo@[mb_x as int], skip, co);
            }
            if gg && tame {
                assert(mb_tame(full.mbs[mb_x as int]));
                lemma_mb_res_ok(tpd, rr.s, fh, rm[mb_x as int], rr.tops[mb_x as int], rr.left, res, coeffs@);
            }
        }
        reconstruct_mb(
            ws.as_mut_slice(),
            &top_y,
            &top_u,
            &top_v,
            mb_x,
            mb_y,
            mb_w,
            m,
            &res,
            coeffs.as_slice(),
            Ghost(rm[mb_x as int]),
            Ghost(co),
        );
        assert(gg && tame ==> ws@ == mb_recon(
            mb_setup(ws0, top_y@, top_u@, top_v@, mb_x as int, mb_y as int, mb_w as int, m.is_i4x4),
            rm[mb_x as int],
            mb_x as int,
            mb_y as int,
            co,
        ));
        let ghost st1 = recon_of(ws0, top_y@, top_u@, top_v@, *pl);
        emit_mb(ws.as_slice(), top_y, top_u, top_v, pl, mb_x, mb_y, mb_w, mb_h);
        proof {
            if gg && tame {
                assert(recon_of(ws@, top_y@, top_u@, top_v@, *pl) == mb_step(
                    st1,
                    rm[mb_x as int],
                    co,
                    mb_x as int,
                    mb_y as int,
                    mb_w as int,
                    mb_h as int,
                ));
            }
        }
        mb_x = mb_x + 1;
    }
    Ok(())
}

/// Storing a row's reader back keeps every partition's reader where the
/// specification has it.
proof fn lemma_row_end(
    parts0: Seq<BoolReader>,
    parts1: Seq<BoolReader>,
    tok: BoolReader,
    tp: int,
    np: int,
    buf: Seq<u8>,
    starts: Seq<usize>,
    t0: TokRows,
    t1: TokRows,
    os: BoolState,
)
    requires
        0 <= tp < np,
        parts0.len() == np,
        parts1 == parts0.update(tp, tok),
        t0.parts.len() == np,
        t1.parts == t0.parts.update(tp, os),
        forall|p: int| 0 <= p < np && !(#[trigger] parts0[p]).eof ==> parts0[p].rel(buf, starts[p] as int, t0.parts[p]),
        tok.rel(buf, starts[tp] as int, os),
    ensures
        forall|p: int| 0 <= p < np && !(#[trigger] parts1[p]).eof ==> parts1[p].rel(buf, starts[p] as int, t1.parts[p]),
{
    assert forall|p: int| 0 <= p < np && !(#[trigger] parts1[p]).eof implies parts1[p].rel(
        buf,
        starts[p] as int,
        t1.parts[p],
    ) by {
        if p != tp {
            assert(parts1[p] == parts0[p]);
        }
    }
}

/// The filter entry `decode_mb_row` builds for a macroblock is the
/// specification's.
proof fn lemma_fi(hdr: Header, fh: FrameHeader, m: MbModes, ms: MbModeSpec, f: FInfo, skip: bool, co: Seq<int>)
    requires
        hdr.lf_matches(fh),
        hdr.filter_type > 0,
        m.matches(ms),
        m.segment < 4,
        skip == !any_nz(co),
        ({
            let g = hdr.fstrengths@[2 * m.segment + if m.is_i4x4 { 1int } else { 0int }];
            f == FInfo { inner: g.inner || !skip, ..g }
        }),
    ensures
        fi_is(f, fh, ms, co),
{
    let fi = 2 * m.segment + if m.is_i4x4 { 1int } else { 0int };
    assert(finfo_matches(hdr.fstrengths@[fi], fh, fi / 2, fi % 2 == 1));
}

/// The loop filter of macroblock row `mb_y`.
#[verifier::loop_isolation(false)]
fn filter_row(
    pl: &mut Planes,
    finfo: &Vec<FInfo>,
    mb_y: usize,
    mb_w: usize,
    mb_h: usize,
    filter_type: u32,
    Ghost(fh): Ghost<FrameHeader>,
    Ghost(ms): Ghost<Seq<MbModeSpec>>,
    Ghost(cos): Ghost<Seq<Seq<int>>>,
)
    requires
        old(pl).mb_shape(mb_w as nat, mb_h as nat),
        mb_y < mb_h,
        finfo@.len() == mb_w,
        forall|j: int| 0 <= j < finfo@.len() ==> #[trigger] finfo_ok(finfo@[j]),
    ensures
        final(pl).mb_shape(mb_w as nat, mb_h as nat),
        final(pl).width == old(pl).width,
        final(pl).height == old(pl).height,
        (filter_type == 1) == fh.filter.simple && (forall|j: int|
            0 <= j < mb_w ==> fi_is(#[trigger] finfo@[j], fh, ms[j], cos[j])) ==> (final(pl).y@, final(pl).u@, final(pl).v@)
            == lf_row((old(pl).y@, old(pl).u@, old(pl).v@), fh, ms, cos, mb_y as int, mb_w as int, mb_w as nat),
{
    hide(lf_mb_plane);
    let ghost p0 = (pl.y@, pl.u@, pl.v@);
    let ghost good = (filter_type == 1) == fh.filter.simple && (forall|j: int|
        0 <= j < mb_w ==> fi_is(#[trigger] finfo@[j], fh, ms[j], cos[j]));
    let mut mb_x: usize = 0;
    while mb_x < mb_w
        invariant
            mb_x <= mb_w,
            pl.mb_shape(mb_w as nat, mb_h as nat),
            pl.width == old(pl).width,
            pl.height == old(pl).height,
            good ==> (pl.y@, pl.u@, pl.v@) == lf_row(p0, fh, ms, cos, mb_y as int, mb_w as int, mb_x as nat),
        decreases mb_w - mb_x,
    {
        proof {
            assert(finfo_ok(finfo@[mb_x as int]));
            if good {
                assert(fi_is(finfo@[mb_x as int], fh, ms[mb_x as int], cos[mb_x as int]));
            }
            assert((mb_x + 1 - 1) as nat == mb_x as nat);
        }
        let ghost pb = (pl.y@, pl.u@, pl.v@);
        filter_mb(pl, mb_x, mb_y, mb_w, mb_h, finfo[mb_x], filter_type);
        proof {
            if good {
                assert((pl.y@, pl.u@, pl.v@) == lf_mb_at(
                    pb,
                    fh,
                    ms[mb_x as int],
                    cos[mb_x as int],
                    mb_x as int,
                    mb_y as int,
                    mb_w as int,
                ));
            }
        }
        mb_x = mb_x + 1;
    }
}

/// Decodes the VP8 frame whose frame tag is at `data[off]`.
#[verifier::loop_isolation(false)]
#[verifier::rlimit(800)]
pub fn decode_frame(data: &[u8], off: usize) -> (r: Result<Planes, Error>)
    requires
        off <= data@.len(),
    ensures
        r matches Ok(pl) ==> pl.ok(),
        // The planes are the specification's, for a frame it covers.
        r matches Ok(pl) ==> vp8_plain(data@, off as int) ==> {
            let f = vp8_frame(data@, off as int);
            pl.y@ == f.y && pl.u@ == f.u && pl.v@ == f.v
        },
        // Their size is the frame header's, in rows of whole macroblocks.
        r matches Ok(pl) ==> {
            &&& off + 10 <= data@.len()
            &&& pl.width == frame_width(data@, off as int)
            &&& pl.height == frame_height(data@, off as int)
            &&& pl.y_stride == 16 * ((pl.width + 15) / 16)
            &&& pl.uv_stride == 8 * ((pl.width + 15) / 16)
        },
{
    hide(tok_rows);
    hide(row_recon);
    hide(row_init);
    hide(frame_tame);
    hide(frame_coeffs);
    hide(lf_row);
    hide(row_tokens);
    hide(mb_tokens);
    hide(Header::tok_matches);
    hide(Nz::is);
    proof {assert(data@.len() == data.len());}
    let (hdr, mut br) = match parse_header(data, off) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let ghost len = data@.len();
    // The specification's view of the first partition: its header, and
    // the decoder state after it.
    let ghost gp = off + 10;
    let ghost pt = part(data@, gp, br.end as int);
    let ghost wf = bool_wf(bool_init(pt));
    let ghost fh = frame_header(pt, bool_init(pt)).1;
    let ghost gh = frame_header(pt, bool_init(pt)).0;
    let ghost hm = hdr.mode_matches(fh);
    let ghost end0 = br.end;
    let ghost e0 = br.eof;
    let ghost hl = hdr.lf_matches(fh);
    proof {
        assert(wf && !br.eof ==> hl);
        assert(hdr.ok(len));
        assert(br.inv(len));
        assert(wf && !br.eof ==> hm && br.rel(data@, gp, gh));
    }
    // The token partitions: the header describes them as the specification
    // does, and each begins as a boolean decoder can.
    let ghost np = hdr.num_parts as int;
    let ghost hx = hdr.tok_matches(fh) && num_parts(fh) == np && forall|p: int|
        0 <= p < np ==> part(data@, #[trigger] hdr.part_start@[p] as int, hdr.part_end@[p] as int) == tok_part(
            data@,
            end0 as int,
            np - 1,
            p,
        );
    let ghost wft = forall|p: int| 0 <= p < np ==> bool_wf(bool_init(#[trigger] tok_part(data@, end0 as int, np - 1, p)));
    let ghost gg = wf && wft && hx;
    let ghost ft = frame_tame(data@, end0 as int, pt, gh, fh, hdr.mb_w as nat, hdr.mb_h as nat) && hl && (fh.filter.level
        != 0 ==> frame_solid(data@, end0 as int, pt, gh, fh, hdr.mb_w as nat, hdr.mb_h as nat));
    proof {
        if wf && !br.eof {
            lemma_header_parts(hdr, data@, end0 as int, fh);
            assert(hx);
        }
        assert(1 <= hdr.mb_w);
    }
    let mb_w = hdr.mb_w;
    let mb_h = hdr.mb_h;
    let y_stride = 16 * mb_w;
    let uv_stride = 8 * mb_w;
    proof {
        assert(y_stride * (16 * mb_h) <= 16 * 1024 * 16 * 1024) by (nonlinear_arith)
            requires y_stride <= 16 * 1024, mb_h <= 1024;
        assert(uv_stride * (8 * mb_h) <= 8 * 1024 * 8 * 1024) by (nonlinear_arith)
            requires uv_stride <= 8 * 1024, mb_h <= 1024;
    }
    let y = match alloc_u8(y_stride * (16 * mb_h)) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let u = match alloc_u8(uv_stride * (8 * mb_h)) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let v = match alloc_u8(uv_stride * (8 * mb_h)) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut pl = Planes { width: hdr.width, height: hdr.height, y, u, v, y_stride, uv_stride };
    let mut top_y = match alloc_u8(16 * mb_w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut top_u = match alloc_u8(8 * mb_w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut top_v = match alloc_u8(8 * mb_w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut intra_t = match alloc_u8(4 * mb_w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let nz0 = Nz { nz: 0, nz_dc: 0 };
    let mut nz_top: Vec<Nz> = Vec::new();
    let mut i: usize = 0;
    while i < mb_w
        invariant
            i <= mb_w,
            nz_top@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] nz_top@[j] == nz0,
        decreases mb_w - i,
    {
        nz_top.push(nz0);
        i = i + 1;
    }
    let mut parts: Vec<BoolReader> = Vec::new();
    let mut p: usize = 0;
    while p < hdr.num_parts
        invariant
            p <= hdr.num_parts,
            parts@.len() == p,
            forall|j: int| 0 <= j < p ==> #[trigger] parts@[j].inv(len),
            forall|j: int| 0 <= j < p ==> (#[trigger] parts@[j]).end == hdr.part_end@[j],
            forall|j: int|
                0 <= j < p ==> !(#[trigger] parts@[j]).eof && bool_wf(
                    bool_init(part(data@, hdr.part_start@[j] as int, hdr.part_end@[j] as int)),
                ) ==> parts@[j].rel(
                    data@,
                    hdr.part_start@[j] as int,
                    bool_init(part(data@, hdr.part_start@[j] as int, hdr.part_end@[j] as int)),
                ),
            hdr.ok(len),
            len == data@.len(),
        decreases hdr.num_parts - p,
    {
        proof {
            assert(p < hdr.num_parts);
            assert(hdr.ok(len));
            let pi = p as int;
            assert(0 <= pi < hdr.num_parts);
            assert(hdr.part_start@[pi] <= hdr.part_end@[pi]);
            assert(hdr.part_end@[pi] <= len);
        }
        parts.push(BoolReader::new(data, hdr.part_start[p], hdr.part_end[p]));
        p = p + 1;
    }
    let mut ws: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < YUV_SIZE
        invariant
            i <= YUV_SIZE,
            ws@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] ws@[j] == 0,
        decreases YUV_SIZE - i,
    {
        ws.push(0);
        i = i + 1;
    }
    let mut coeffs: Vec<i16> = Vec::new();
    let mut i: usize = 0;
    while i < 384
        invariant
            i <= 384,
            coeffs@.len() == i,
        decreases 384 - i,
    {
        coeffs.push(0);
        i = i + 1;
    }
    let mut modes: Vec<MbModes> = Vec::new();
    let mut finfo: Vec<FInfo> = Vec::new();
    proof {
        assert(pl.mb_shape(mb_w as nat, mb_h as nat));
        assert(16 * (mb_w as nat) * (16 * (mb_h as nat)) == y_stride * (16 * mb_h)) by (nonlinear_arith)
            requires y_stride == 16 * mb_w;
        assert(8 * (mb_w as nat) * (8 * (mb_h as nat)) == uv_stride * (8 * mb_h)) by (nonlinear_arith)
            requires uv_stride == 8 * mb_w;
        assert(all_zero(ws@, 832));
        assert(all_zero(top_y@, 16 * mb_w));
        assert(all_zero(top_u@, 8 * mb_w));
        assert(all_zero(top_v@, 8 * mb_w));
        assert(all_zero(pl.y@, y_stride * (16 * mb_h)));
        assert(all_zero(pl.u@, uv_stride * (8 * mb_h)));
        assert(all_zero(pl.v@, uv_stride * (8 * mb_h)));
        lemma_recon_init(recon_of(ws@, top_y@, top_u@, top_v@, pl), mb_w as nat, mb_h as nat);
        assert(forall|j: int| 0 <= j < intra_t@.len() ==> intra_t@[j] < 10);
        lemma_tok_rows_shape(data@, end0 as int, pt, gh, fh, mb_w as nat, 0);
        lemma_tok_rows_zero(data@, end0 as int, pt, gh, fh, mb_w as nat);
        lemma_nz_zero();
        if gg {
            let t0 = tok_rows(data@, end0 as int, pt, gh, fh, mb_w as nat, 0);
            assert forall|p: int| 0 <= p < np && !(#[trigger] parts@[p]).eof implies parts@[p].rel(
                data@,
                hdr.part_start@[p] as int,
                t0.parts[p],
            ) by {
                let tp = tok_part(data@, end0 as int, np - 1, p);
                assert(bool_wf(bool_init(tp)));
                assert(part(data@, hdr.part_start@[p] as int, hdr.part_end@[p] as int) == tp);
            }
            assert forall|j: int| 0 <= j < mb_w implies (#[trigger] nz_top@[j]).is(t0.tops[j]) by {
                assert(nz_top@[j] == nz0);
            }
        }
    }
    let mut mb_y: usize = 0;
    while mb_y < mb_h
        invariant
            mb_y <= mb_h,
            pl.mb_shape(mb_w as nat, mb_h as nat),
            pl.width == hdr.width,
            pl.height == hdr.height,
            br.inv(len),
            br.end == end0,
            wf && !br.eof ==> hm,
            // The first partition's reader and the mode context are where
            // the specification has them after `mb_y` rows of modes.
            wf && !br.eof ==> br.rel(data@, gp, mode_rows(pt, gh, fh, mb_w as nat, mb_y as nat).s),
            wf && !br.eof ==> ctxn(intra_t@) == mode_rows(pt, gh, fh, mb_w as nat, mb_y as nat).top,
            top_y@.len() == 16 * mb_w,
            top_u@.len() == 8 * mb_w,
            top_v@.len() == 8 * mb_w,
            intra_t@.len() == 4 * mb_w,
            forall|j: int| 0 <= j < intra_t@.len() ==> intra_t@[j] < 10,
            nz_top@.len() == mb_w,
            parts@.len() == hdr.num_parts,
            forall|j: int| 0 <= j < hdr.num_parts ==> #[trigger] parts@[j].inv(len),
            1 <= mb_w,
            forall|j: int| 0 <= j < np ==> (#[trigger] parts@[j]).end == hdr.part_end@[j],
            // The token partitions' readers and the nonzero contexts are
            // where the specification has them after `mb_y` rows.
            gg ==> forall|p: int|
                0 <= p < np && !(#[trigger] parts@[p]).eof ==> parts@[p].rel(
                    data@,
                    hdr.part_start@[p] as int,
                    tok_rows(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat).parts[p],
                ),
            gg ==> forall|j: int|
                0 <= j < mb_w ==> (#[trigger] nz_top@[j]).is(
                    tok_rows(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat).tops[j],
                ),
            ws@.len() == YUV_SIZE,
            coeffs@.len() == 384,
            mb_y > 0 ==> !br.eof,
            !br.eof ==> !e0,
            gg && ft && !br.eof ==> recon_of(ws@, top_y@, top_u@, top_v@, pl) == frame_recon(
                data@,
                end0 as int,
                pt,
                gh,
                fh,
                mb_w as nat,
                mb_h as nat,
                mb_y as nat,
            ),
        decreases mb_h - mb_y,
    {
        // Intra modes of the whole row, from the first partition.
        let ghost r0 = mode_rows(pt, gh, fh, mb_w as nat, mb_y as nat);
        proof {
            lemma_mode_rows_shape(pt, gh, fh, mb_w as nat, mb_y as nat);
            if wf && !br.eof {
                assert(ctxn(intra_t@) =~= r0.top);
            }
        }
        parse_mode_row(&mut br, data, &hdr, &mut intra_t, &mut modes, mb_w, Ghost(gp), Ghost(r0.s), Ghost(fh));
        proof {
            assert((mb_y + 1 - 1) as nat == mb_y as nat);
            assert(mode_rows(pt, gh, fh, mb_w as nat, (mb_y + 1) as nat) == row_modes(
                pt,
                r0.s,
                fh,
                r0.top,
                mb_w as nat,
            ));
        }
        if br.eof {
            return Err(Error::Bitstream);
        }
        let ghost rm = mode_rows(pt, gh, fh, mb_w as nat, (mb_y + 1) as nat).mbs;
        let ghost t0 = tok_rows(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat);
        proof {
            assert(wf ==> forall|j: int| 0 <= j < mb_w ==> (#[trigger] modes@[j]).matches(rm[j]));
            lemma_tok_rows_shape(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat);
        }
        // The scratch block's borders for this row.
        let ghost f0 = recon_of(ws@, top_y@, top_u@, top_v@, pl);
        init_row(ws.as_mut_slice(), mb_y);
        let ghost f1 = recon_of(ws@, top_y@, top_u@, top_v@, pl);
        // `num_parts` is a power of two: this is `mb_y & (num_parts - 1)`.
        let tp = mb_y % hdr.num_parts;
        let mut tok = parts[tp];
        let ghost tpd = tok_part(data@, end0 as int, np - 1, tp as int);
        let ghost ps = hdr.part_start@[tp as int] as int;
        let ghost s0 = t0.parts[tp as int];
        proof {
            assert(tok == parts@[tp as int]);
            if gg {
                assert(part(data@, hdr.part_start@[tp as int] as int, hdr.part_end@[tp as int] as int) == tpd);
                assert(part(data@, ps, tok.end as int) == tpd);
            }
        }
        match decode_mb_row(
            &mut tok,
            data,
            &hdr,
            &modes,
            &mut nz_top,
            &mut finfo,
            &mut top_y,
            &mut top_u,
            &mut top_v,
            &mut ws,
            &mut coeffs,
            &mut pl,
            mb_y,
            Ghost(ps),
            Ghost(s0),
            Ghost(fh),
            Ghost(rm),
            Ghost(t0.tops),
        ) {
            Ok(()) => {},
            Err(e) => return Err(e),
        }
        let ghost parts0 = parts@;
        parts.set(tp, tok);
        proof {
            lemma_tok_rows_step(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat);
            if gg {
                let t1 = tok_rows(data@, end0 as int, pt, gh, fh, mb_w as nat, (mb_y + 1) as nat);
                let o = row_tokens(tpd, s0, fh, rm, t0.tops, mb_w as nat);
                assert(mb_y as int % num_parts(fh) == tp);
                assert(t1.tops == o.tops);
                assert(tok.rel(data@, ps, o.s));
                assert(t1.parts == t0.parts.update(tp as int, o.s));
                lemma_row_end(parts0, parts@, tok, tp as int, np, data@, hdr.part_start@, t0, t1, o.s);
            }
        }
        let ghost f2 = recon_of(ws@, top_y@, top_u@, top_v@, pl);
        let ghost o = row_tokens(tpd, s0, fh, rm, t0.tops, mb_w as nat);
        if hdr.filter_type > 0 {
            filter_row(&mut pl, &finfo, mb_y, mb_w, mb_h, hdr.filter_type, Ghost(fh), Ghost(rm), Ghost(o.mbs));
        }
        proof {
            if gg && ft {
                assert(frame_row_solid(data@, end0 as int, pt, gh, fh, mb_w as nat, mb_y as nat) || fh.filter.level == 0);
                lemma_frame_step(
                    data@,
                    end0 as int,
                    pt,
                    gh,
                    fh,
                    mb_w as nat,
                    mb_h as nat,
                    mb_y as nat,
                    f0,
                    o.mbs,
                    f2,
                    recon_of(ws@, top_y@, top_u@, top_v@, pl),
                );
            }
        }
        mb_y = mb_y + 1;
    }
    proof {
        assert(pl.width <= pl.y_stride);
        assert(pl.y_stride * pl.height <= pl.y_stride * (16 * mb_h)) by (nonlinear_arith)
            requires pl.height <= 16 * mb_h;
        assert((pl.width + 1) / 2 <= pl.uv_stride);
        assert(pl.uv_stride * ((pl.height + 1) / 2) <= pl.uv_stride * (8 * mb_h)) by (nonlinear_arith)
            requires (pl.height + 1) / 2 <= 8 * mb_h;
        if vp8_plain(data@, off as int) {
            assert(vp8_parts(data@, off as int) == (end0 as int, pt, gh, fh, mb_w as nat, mb_h as nat));
            assert(gg && ft);
        }
    }
    Ok(pl)
}

/// Row `j` of macroblock `(mx, my)` in a plane of `n`-pixel macroblocks:
/// its `n` bytes are inside the plane.
pub proof fn lemma_row(mx: int, my: int, mw: int, mh: int, n: int, j: int)
    requires
        0 <= mx < mw <= 1024,
        0 <= my < mh <= 1024,
        n == 8 || n == 16,
        0 <= j < n,
    ensures
        0 <= (n * my + j) * (n * mw) + n * mx,
        (n * my + j) * (n * mw) + n * mx + n <= (n * mw) * (n * mh),
        (n * mw) * (n * mh) <= 16 * 1024 * 16 * 1024,
{
    let s = n * mw;
    assert(n * mx + n <= s) by (nonlinear_arith) requires mx < mw, s == n * mw, n >= 0;
    assert((n * my + j) * s + s <= (n * mh) * s) by (nonlinear_arith)
        requires n * my + j + 1 <= n * mh, s >= 0;
    assert(s * (n * mh) == (n * mh) * s) by (nonlinear_arith);
    assert(0 <= (n * my + j) * s) by (nonlinear_arith) requires n * my + j >= 0, s >= 0;
    assert(0 <= n * mx) by (nonlinear_arith) requires mx >= 0, n >= 0;
    assert(n * my + j + 1 <= n * mh) by (nonlinear_arith) requires my + 1 <= mh, j < n, n >= 0;
    assert(s <= 16 * 1024) by (nonlinear_arith) requires s == n * mw, 0 <= n <= 16, 0 <= mw <= 1024;
    assert(s * (n * mh) <= 16 * 1024 * 16 * 1024) by (nonlinear_arith)
        requires 0 <= s <= 16 * 1024, 0 <= n <= 16, 0 <= mh <= 1024;
}

} // verus!
