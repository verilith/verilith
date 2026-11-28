//! The residual tokens of macroblocks and rows (RFC 6386 section 13) as
//! the lossy encoder writes them, proven to read back under
//! `vp8spec::mb_tokens` and `vp8spec::row_tokens`.
//!
//! A macroblock's levels are 25 blocks of sixteen, each in zigzag order:
//! luma 0 to 15, U 16 to 19, V 20 to 23 and Y2 at 24. The writer keeps the
//! same "has nonzero coefficients" contexts the reader does.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
use vstd::prelude::*;

verus! {

/// What reading a macroblock's tokens leaves, apart from the bool state.
pub struct EncRes {
    pub coeffs: Seq<int>,
    pub top: Seq<bool>,
    pub left: Seq<bool>,
}

pub open spec fn as_res(s: BoolState, c: EncRes) -> ResState {
    ResState { s, coeffs: c.coeffs, top: c.top, left: c.left }
}

pub open spec fn res_ok(c: EncRes) -> bool {
    &&& c.coeffs.len() == 384
    &&& c.top.len() == 9
    &&& c.left.len() == 9
}

pub open spec fn lvs_ok(lvs: Seq<Seq<int>>) -> bool {
    &&& lvs.len() == 25
    &&& forall|i: int| 0 <= i < 25 ==> lv_ok(#[trigger] lvs[i])
}

pub open spec fn pb_ctx(c: EncRes, off: int, w: int, k: int) -> int {
    b2i(c.left[off + k / w]) + b2i(c.top[off + k % w])
}

/// Block `k` of a plane, after `plane_block`.
pub open spec fn pb_next(
    c: EncRes,
    lk: Seq<int>,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    k: int,
) -> EncRes {
    let at = 16 * (base + k);
    let f = tok_end(lk, first, true) > first;
    EncRes {
        coeffs: splice16(c.coeffs, at, tok_out(c.coeffs.subrange(at, at + 16), lk, first, true, dq_dc, dq_ac)),
        top: c.top.update(off + k % w, f),
        left: c.left.update(off + k / w, f),
    }
}

/// The first `n` blocks of a plane: what they leave and their tokens.
pub open spec fn pb(
    probs: Seq<int>,
    c: EncRes,
    lvs: Seq<Seq<int>>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    n: nat,
) -> (EncRes, Seq<(int, bool)>)
    decreases n,
{
    if n == 0 {
        (c, Seq::empty())
    } else {
        let k = n - 1;
        let r = pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let lk = lvs[base + k];
        (
            pb_next(r.0, lk, first, dq_dc, dq_ac, base, off, w, k),
            r.1 + tok_ws(probs, t, first, pb_ctx(r.0, off, w, k), true, lk),
        )
    }
}

pub open spec fn plane_ok(t: int, first: int, base: int, off: int, w: int, n: nat) -> bool {
    &&& 0 <= t < 4
    &&& 0 <= first <= 1
    &&& (w == 4 && off == 0 && base == 0 && n <= 16) || (w == 2 && (off == 4 || off == 6) && (base == 16
        || base == 20) && n <= 4)
}

pub proof fn lemma_pb(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    c: EncRes,
    lvs: Seq<Seq<int>>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    n: nat,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        res_ok(c),
        lvs_ok(lvs),
        plane_ok(t, first, base, off, w, n),
        good(data, e, pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).1 + rest),
    ensures
        ({
            let r = pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n);
            &&& plane_blocks(data, as_res(dst(data, e), c), probs, t, first, dq_dc, dq_ac, base, off, w, n)
                == as_res(dst(data, enc_run(e, r.1)), r.0)
            &&& res_ok(r.0)
        }),
        good(data, enc_run(e, pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).1), rest),
    decreases n,
{
    hide(block_tokens);
    hide(tok_ws);
    hide(tok_out);
    hide(tok_end);
    if n == 0 {
        assert(Seq::<(int, bool)>::empty() + rest =~= rest);
    } else {
        let k = (n - 1) as int;
        let r = pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let lk = lvs[base + k];
        let ctx = pb_ctx(r.0, off, w, k);
        let tw = tok_ws(probs, t, first, ctx, true, lk);
        assert(pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).1 + rest =~= r.1 + (tw + rest));
        lemma_pb(data, e, probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat, tw + rest);
        let e1 = enc_run(e, r.1);
        let at = 16 * (base + k);
        assert(0 <= k / w < w && 0 <= k % w < w) by {
            assert(0 <= k < w * w);
        }
        assert(lv_ok(lk));
        lemma_tok(data, e1, probs, t, first, ctx, true, lk, dq_dc, dq_ac, r.0.coeffs.subrange(at, at + 16), rest);
        lemma_run_concat(e, r.1, tw);
    }
}

/// The Y2 block, after `y2_block`.
pub open spec fn y2(probs: Seq<int>, c: EncRes, lk: Seq<int>, dq_dc: int, dq_ac: int) -> (EncRes, Seq<(int, bool)>) {
    let ctx = b2i(c.left[8]) + b2i(c.top[8]);
    let dc = iwht(tok_out(Seq::new(16, |i: int| 0int), lk, 0, true, dq_dc, dq_ac));
    let f = tok_end(lk, 0, true) > 0;
    (
        EncRes {
            coeffs: Seq::new(
                c.coeffs.len(),
                |i: int|
                    if 0 <= i < 256 && i % 16 == 0 {
                        dc[i / 16]
                    } else {
                        c.coeffs[i]
                    },
            ),
            top: c.top.update(8, f),
            left: c.left.update(8, f),
        },
        tok_ws(probs, 1, 0, ctx, true, lk),
    )
}

pub proof fn lemma_y2(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    c: EncRes,
    lk: Seq<int>,
    dq_dc: int,
    dq_ac: int,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        res_ok(c),
        lv_ok(lk),
        good(data, e, y2(probs, c, lk, dq_dc, dq_ac).1 + rest),
    ensures
        y2_block(data, as_res(dst(data, e), c), probs, dq_dc, dq_ac) == as_res(
            dst(data, enc_run(e, y2(probs, c, lk, dq_dc, dq_ac).1)),
            y2(probs, c, lk, dq_dc, dq_ac).0,
        ),
        res_ok(y2(probs, c, lk, dq_dc, dq_ac).0),
        good(data, enc_run(e, y2(probs, c, lk, dq_dc, dq_ac).1), rest),
{
    hide(block_tokens);
    hide(tok_ws);
    hide(tok_out);
    hide(tok_end);
    hide(iwht);
    let ctx = b2i(c.left[8]) + b2i(c.top[8]);
    lemma_tok(data, e, probs, 1, 0, ctx, true, lk, dq_dc, dq_ac, Seq::new(16, |i: int| 0int), rest);
}

/// A macroblock's residuals, after `mb_residuals`: Y2 (unless `B_PRED`),
/// then luma, U and V.
pub open spec fn mb_res(
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    is_i4x4: bool,
    top: Seq<bool>,
    left: Seq<bool>,
    lvs: Seq<Seq<int>>,
) -> (EncRes, Seq<(int, bool)>) {
    let c0 = EncRes { coeffs: Seq::new(384, |i: int| 0int), top, left };
    let r1 = if is_i4x4 {
        (c0, Seq::empty())
    } else {
        y2(probs, c0, lvs[24], q.2, q.3)
    };
    let (t, first) = if is_i4x4 {
        (3int, 0int)
    } else {
        (0int, 1int)
    };
    let ry = pb(probs, r1.0, lvs, t, first, q.0, q.1, 0, 0, 4, 16);
    let ru = pb(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    let rv = pb(probs, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
    (rv.0, r1.1 + (ry.1 + (ru.1 + rv.1)))
}

#[verifier::spinoff_prover]
pub proof fn lemma_mb_res(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    is_i4x4: bool,
    top: Seq<bool>,
    left: Seq<bool>,
    lvs: Seq<Seq<int>>,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        top.len() == 9,
        left.len() == 9,
        lvs_ok(lvs),
        good(data, e, mb_res(probs, q, is_i4x4, top, left, lvs).1 + rest),
    ensures
        mb_residuals(data, dst(data, e), probs, q, is_i4x4, top, left) == as_res(
            dst(data, enc_run(e, mb_res(probs, q, is_i4x4, top, left, lvs).1)),
            mb_res(probs, q, is_i4x4, top, left, lvs).0,
        ),
        res_ok(mb_res(probs, q, is_i4x4, top, left, lvs).0),
        good(data, enc_run(e, mb_res(probs, q, is_i4x4, top, left, lvs).1), rest),
{
    hide(pb);
    hide(y2);
    hide(plane_blocks);
    hide(y2_block);
    let c0 = EncRes { coeffs: Seq::new(384, |i: int| 0int), top, left };
    let r1 = if is_i4x4 {
        (c0, Seq::<(int, bool)>::empty())
    } else {
        y2(probs, c0, lvs[24], q.2, q.3)
    };
    let (t, first) = if is_i4x4 {
        (3int, 0int)
    } else {
        (0int, 1int)
    };
    let ry = pb(probs, r1.0, lvs, t, first, q.0, q.1, 0, 0, 4, 16);
    let ru = pb(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    let rv = pb(probs, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
    assert(mb_res(probs, q, is_i4x4, top, left, lvs).1 + rest =~= r1.1 + (ry.1 + (ru.1 + (rv.1 + rest))));
    assert(as_res(dst(data, e), c0) == (ResState { s: dst(data, e), coeffs: Seq::new(384, |i: int| 0int), top, left }));
    if is_i4x4 {
        assert(r1.1 + (ry.1 + (ru.1 + (rv.1 + rest))) =~= ry.1 + (ru.1 + (rv.1 + rest)));
    } else {
        assert(lv_ok(lvs[24]));
        lemma_y2(data, e, probs, c0, lvs[24], q.2, q.3, ry.1 + (ru.1 + (rv.1 + rest)));
    }
    let e1 = enc_run(e, r1.1);
    lemma_pb(data, e1, probs, r1.0, lvs, t, first, q.0, q.1, 0, 0, 4, 16, ru.1 + (rv.1 + rest));
    let e2 = enc_run(e1, ry.1);
    lemma_pb(data, e2, probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4, rv.1 + rest);
    let e3 = enc_run(e2, ru.1);
    lemma_pb(data, e3, probs, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4, rest);
    lemma_run_concat(e2, ru.1, rv.1);
    lemma_run_concat(e1, ry.1, ru.1 + rv.1);
    lemma_run_concat(e, r1.1, ry.1 + (ru.1 + rv.1));
}

/// A macroblock's tokens, after `mb_tokens`: none when it is skipped.
pub open spec fn mb_tok(fh: FrameHeader, m: MbModeSpec, top: Seq<bool>, left: Seq<bool>, lvs: Seq<Seq<int>>) -> (
    EncRes,
    Seq<(int, bool)>,
) {
    if fh.mb_no_coeff_skip && m.skip {
        (
            EncRes {
                coeffs: Seq::new(384, |i: int| 0int),
                top: Seq::new(9, |i: int| i == 8 && m.is_i4x4 && top[8]),
                left: Seq::new(9, |i: int| i == 8 && m.is_i4x4 && left[8]),
            },
            Seq::empty(),
        )
    } else {
        mb_res(fh.probs, seg_quant(fh, m.segment), m.is_i4x4, top, left, lvs)
    }
}

pub proof fn lemma_mb_tok(
    data: Seq<u8>,
    e: EncState,
    fh: FrameHeader,
    m: MbModeSpec,
    top: Seq<bool>,
    left: Seq<bool>,
    lvs: Seq<Seq<int>>,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(fh.probs),
        top.len() == 9,
        left.len() == 9,
        lvs_ok(lvs),
        good(data, e, mb_tok(fh, m, top, left, lvs).1 + rest),
    ensures
        mb_tokens(data, dst(data, e), fh, m, top, left) == as_res(
            dst(data, enc_run(e, mb_tok(fh, m, top, left, lvs).1)),
            mb_tok(fh, m, top, left, lvs).0,
        ),
        res_ok(mb_tok(fh, m, top, left, lvs).0),
        good(data, enc_run(e, mb_tok(fh, m, top, left, lvs).1), rest),
{
    hide(mb_res);
    hide(mb_residuals);
    if fh.mb_no_coeff_skip && m.skip {
        assert(Seq::<(int, bool)>::empty() + rest =~= rest);
    } else {
        lemma_mb_res(data, e, fh.probs, seg_quant(fh, m.segment), m.is_i4x4, top, left, lvs, rest);
    }
}

/// The first `n` macroblocks of a row: the contexts, the coefficients and
/// the tokens.
pub struct EncRow {
    pub tops: Seq<Seq<bool>>,
    pub left: Seq<bool>,
    pub mbs: Seq<Seq<int>>,
}

pub open spec fn row_tok(
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    lvss: Seq<Seq<Seq<int>>>,
    tops: Seq<Seq<bool>>,
    n: nat,
) -> (EncRow, Seq<(int, bool)>)
    decreases n,
{
    if n == 0 {
        (EncRow { tops, left: Seq::new(9, |i: int| false), mbs: Seq::empty() }, Seq::empty())
    } else {
        let k = n - 1;
        let r = row_tok(fh, modes, lvss, tops, (n - 1) as nat);
        let o = mb_tok(fh, modes[k], r.0.tops[k], r.0.left, lvss[k]);
        (EncRow { tops: r.0.tops.update(k, o.0.top), left: o.0.left, mbs: r.0.mbs.push(o.0.coeffs) }, r.1 + o.1)
    }
}

pub open spec fn tops_ok(tops: Seq<Seq<bool>>) -> bool {
    forall|j: int| 0 <= j < tops.len() ==> (#[trigger] tops[j]).len() == 9
}

pub proof fn lemma_row_tok(
    data: Seq<u8>,
    e: EncState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    lvss: Seq<Seq<Seq<int>>>,
    tops: Seq<Seq<bool>>,
    n: nat,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(fh.probs),
        tops_ok(tops),
        n <= tops.len(),
        n <= lvss.len(),
        forall|j: int| 0 <= j < n ==> lvs_ok(#[trigger] lvss[j]),
        good(data, e, row_tok(fh, modes, lvss, tops, n).1 + rest),
    ensures
        ({
            let r = row_tok(fh, modes, lvss, tops, n);
            &&& row_tokens(data, dst(data, e), fh, modes, tops, n) == (RowTokens {
                s: dst(data, enc_run(e, r.1)),
                tops: r.0.tops,
                left: r.0.left,
                mbs: r.0.mbs,
            })
            &&& tops_ok(r.0.tops)
            &&& r.0.tops.len() == tops.len()
            &&& r.0.left.len() == 9
        }),
        good(data, enc_run(e, row_tok(fh, modes, lvss, tops, n).1), rest),
    decreases n,
{
    hide(mb_tok);
    hide(mb_tokens);
    if n == 0 {
        assert(Seq::<(int, bool)>::empty() + rest =~= rest);
        lemma_row_tokens_zero(data, dst(data, e), fh, modes, tops);
    } else {
        let k = (n - 1) as int;
        let r = row_tok(fh, modes, lvss, tops, (n - 1) as nat);
        let o = mb_tok(fh, modes[k], r.0.tops[k], r.0.left, lvss[k]);
        assert(row_tok(fh, modes, lvss, tops, n).1 + rest =~= r.1 + (o.1 + rest));
        lemma_row_tok(data, e, fh, modes, lvss, tops, (n - 1) as nat, o.1 + rest);
        let e1 = enc_run(e, r.1);
        assert(lvs_ok(lvss[k]));
        lemma_mb_tok(data, e1, fh, modes[k], r.0.tops[k], r.0.left, lvss[k], rest);
        lemma_run_concat(e, r.1, o.1);
        let t2 = r.0.tops.update(k, o.0.top);
        assert forall|j: int| 0 <= j < t2.len() implies (#[trigger] t2[j]).len() == 9 by {
            if j != k {
                assert(t2[j] == r.0.tops[j]);
            }
        }
    }
}

} // verus!
