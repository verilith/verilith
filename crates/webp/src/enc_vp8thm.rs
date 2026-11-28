//! The lossy encoder's frames are plain (`vp8spec::vp8_plain`): both
//! partitions begin as a boolean decoder can, and every coefficient the
//! decoder reads is tame, so the pixel theorem applies to them.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::enc_vp8::*;
#[cfg(verus_only)]
use crate::enc_vp8frm::*;
#[cfg(verus_only)]
use crate::enc_vp8hdr::*;
#[cfg(verus_only)]
use crate::enc_vp8mb::*;
#[cfg(verus_only)]
use crate::enc_vp8modes::*;
#[cfg(verus_only)]
use crate::enc_vp8res::*;
#[cfg(verus_only)]
use crate::enc_vp8tame::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
#[cfg(verus_only)]
use crate::enc_vp8w::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// A zero byte after the end reads as the zeros past the end do.
pub proof fn lemma_pad_bits(d: Seq<u8>, a: nat, n: nat)
    ensures
        stream_bits(d.push(0u8), a, n) == stream_bits(d, a, n),
    decreases n,
{
    if n > 0 {
        lemma_pad_bits(d, a, (n - 1) as nat);
        let i = a + (n - 1) as nat;
        if i / 8 < d.len() {
            assert(d.push(0u8)[(i / 8) as int] == d[(i / 8) as int]);
        } else if i / 8 == d.len() {
            lemma_pow2_pos((7 - i % 8) as nat);
            assert(d.push(0u8)[(i / 8) as int] == 0u8);
            assert(0nat / pow2((7 - i % 8) as nat) == 0);
        }
    }
}

pub proof fn lemma_good_pad(d: Seq<u8>, e: EncState, ws: Seq<(int, bool)>)
    requires
        good(d, e, ws),
    ensures
        good(d.push(0u8), e, ws),
{
    lemma_pad_bits(d, 0, enc_run(e, ws).pos);
}

/// A partition the encoder wrote begins as a boolean decoder can.
pub proof fn lemma_init_wf(d: Seq<u8>, ws: Seq<(int, bool)>)
    requires
        good(d, enc_init(), ws),
    ensures
        bool_wf(bool_init(d)),
        bool_init(d) == dst(d, enc_init()),
{
    lemma_covers_take(d, enc_init(), ws, 0);
    assert(ws.take(0) =~= Seq::<(int, bool)>::empty());
    assert(enc_run(enc_init(), Seq::<(int, bool)>::empty()) == enc_init());
}

/// The contexts and coefficients `mb_res` gives have the shape of a
/// macroblock's.
pub proof fn lemma_mb_res_ok(
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    top: Seq<bool>,
    left: Seq<bool>,
    lvs: Seq<Seq<int>>,
)
    requires
        top.len() == 9,
        left.len() == 9,
    ensures
        res_ok(mb_res(probs, q, false, top, left, lvs).0),
{
    hide(pb);
    let c0 = EncRes { coeffs: Seq::new(384, |i: int| 0int), top, left };
    let r1 = y2(probs, c0, lvs[24], q.2, q.3);
    assert(res_ok(r1.0));
    lemma_pb_ok(probs, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    let ry = pb(probs, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    lemma_pb_ok(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    let ru = pb(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    lemma_pb_ok(probs, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
}

/// A row of macroblocks the encoder can write has tame coefficients.
pub proof fn lemma_row_tame(
    fh: FrameHeader,
    msy: Seq<MbModeSpec>,
    lvy: Seq<Seq<Seq<int>>>,
    tops: Seq<Seq<bool>>,
    n: nat,
)
    requires
        tops_ok(tops),
        n <= tops.len(),
        n <= lvy.len(),
        n <= msy.len(),
        forall|j: int| 0 <= j < n ==> mb_lv_ok(#[trigger] lvy[j], seg_quant(fh, 0)),
        forall|j: int| 0 <= j < n ==> mb_ok(fh, #[trigger] msy[j]),
    ensures
        ({
            let r = row_tok(fh, msy, lvy, tops, n);
            &&& row_tame(r.0.mbs)
            &&& r.0.mbs.len() == n
            &&& tops_ok(r.0.tops)
            &&& r.0.tops.len() == tops.len()
            &&& r.0.left.len() == 9
        }),
    decreases n,
{
    hide(mb_res);
    if n > 0 {
        let k = n - 1;
        lemma_row_tame(fh, msy, lvy, tops, (n - 1) as nat);
        let r = row_tok(fh, msy, lvy, tops, (n - 1) as nat);
        let m = msy[k];
        assert(mb_ok(fh, m));
        let o = mb_tok(fh, m, r.0.tops[k], r.0.left, lvy[k]);
        if fh.mb_no_coeff_skip && m.skip {
            assert(within(o.0.coeffs, 2047));
        } else {
            assert(mb_lv_ok(lvy[k], seg_quant(fh, 0)));
            lemma_mb_res_within(fh.probs, seg_quant(fh, 0), r.0.tops[k], r.0.left, lvy[k]);
            lemma_mb_res_ok(fh.probs, seg_quant(fh, 0), r.0.tops[k], r.0.left, lvy[k]);
        }
        lemma_tame(o.0.coeffs);
        let r1 = row_tok(fh, msy, lvy, tops, n);
        assert(r1.0.mbs == r.0.mbs.push(o.0.coeffs));
        assert forall|j: int| 0 <= j < r1.0.mbs.len() implies mb_tame(#[trigger] r1.0.mbs[j]) by {
            if j < k {
                assert(r1.0.mbs[j] == r.0.mbs[j]);
            }
        }
        assert forall|j: int| 0 <= j < r1.0.tops.len() implies (#[trigger] r1.0.tops[j]).len() == 9 by {
            if j != k {
                assert(r1.0.tops[j] == r.0.tops[j]);
            }
        }
    }
}

/// The rows the encoder writes have the shape of a frame's.
pub proof fn lemma_frame_shape(fh: FrameHeader, ms: Seq<MbModeSpec>, lv: Seq<Seq<Seq<int>>>, mb_w: nat, mb_h: nat, rows: nat)
    requires
        rows <= mb_h,
        ms.len() == mb_w * mb_h,
        lv.len() == mb_w * mb_h,
        forall|i: int| 0 <= i < lv.len() ==> mb_lv_ok(#[trigger] lv[i], seg_quant(fh, 0)),
        all_ok(fh, ms),
    ensures
        tops_ok(frame_tok(fh, ms, lv, mb_w, rows).0),
        frame_tok(fh, ms, lv, mb_w, rows).0.len() == mb_w,
        forall|y: int|
            0 <= y < rows ==> row_tame(
                #[trigger] row_tok(fh, row_of(ms, mb_w, y), row_of(lv, mb_w, y), frame_tok(fh, ms, lv, mb_w, y as nat).0, mb_w).0.mbs,
            ),
    decreases rows,
{
    hide(row_tok);
    if rows > 0 {
        let y = (rows - 1) as int;
        lemma_frame_shape(fh, ms, lv, mb_w, mb_h, (rows - 1) as nat);
        let t = frame_tok(fh, ms, lv, mb_w, y as nat).0;
        let msy = row_of(ms, mb_w, y);
        let lvy = row_of(lv, mb_w, y);
        assert((y + 1) * mb_w <= mb_h * mb_w) by (nonlinear_arith)
            requires
                y < mb_h,
        ;
        assert((y + 1) * mb_w == y * mb_w + mb_w) by (nonlinear_arith);
        assert(0 <= y * mb_w) by (nonlinear_arith)
            requires
                0 <= y,
        ;
        assert forall|j: int| 0 <= j < mb_w implies mb_lv_ok(#[trigger] lvy[j], seg_quant(fh, 0)) by {
            assert(lvy[j] == lv[y * mb_w + j]);
        }
        assert forall|j: int| 0 <= j < mb_w implies mb_ok(fh, #[trigger] msy[j]) by {
            assert(msy[j] == ms[y * mb_w + j]);
        }
        lemma_row_tame(fh, msy, lvy, t, mb_w);
        assert(frame_tok(fh, ms, lv, mb_w, rows).0 == row_tok(fh, msy, lvy, t, mb_w).0.tops);
    }
}

/// The modes the encoder writes for its choices are ones it can write.
pub proof fn lemma_ms_ok(mbs: Seq<MbChoice>, p: HdrParams, q: (int, int, int, int, int, int))
    requires
        forall|i: int| 0 <= i < mbs.len() ==> choice_ok(&#[trigger] mbs[i], q),
    ensures
        all_ok(fh_of(p), ms_of(mbs, p.skip)),
        lv_all_ok(lv_of(mbs)),
        forall|i: int| 0 <= i < lv_of(mbs).len() ==> mb_lv_ok(#[trigger] lv_of(mbs)[i], q),
{
    let ms = ms_of(mbs, p.skip);
    assert forall|i: int| 0 <= i < ms.len() implies mb_ok(fh_of(p), #[trigger] ms[i]) by {
        assert(choice_ok(&mbs[i], q));
    }
    assert forall|i: int| 0 <= i < lv_of(mbs).len() implies lvs_ok(#[trigger] lv_of(mbs)[i]) && mb_lv_ok(lv_of(mbs)[i], q) by {
        assert(choice_ok(&mbs[i], q));
        lemma_mb_lvs(mbs[i].lv@);
    }
}

/// The file is plain when it holds the encoder's partitions after a frame
/// tag at 20 that gives the first's size and the frame's size.
pub proof fn lemma_lossy_plain(file: Seq<u8>, p1: Seq<u8>, p2: Seq<u8>, p: HdrParams, mbs: Seq<MbChoice>, mb_w: nat, mb_h: nat)
    requires
        parts_ok(p1, p2, p, mbs, mb_w, mb_h),
        forall|i: int| 0 <= i < mbs.len() ==> choice_ok(&#[trigger] mbs[i], sq(p.q as int)),
        mbs.len() == mb_w * mb_h,
        first_part_size(file, 20) == p1.len(),
        30 + p1.len() as int <= file.len(),
        file.subrange(30, 30 + p1.len() as int) == p1,
        file.subrange(30 + p1.len() as int, file.len() as int) == p2 || file.subrange(30 + p1.len() as int, file.len() as int) == p2.push(0u8),
        (frame_width(file, 20) + 15) / 16 == mb_w,
        (frame_height(file, 20) + 15) / 16 == mb_h,
    ensures
        vp8_plain(file, 20),
        vp8_parts(file, 20).3 == fh_of(p),
        modes_read(p1, vp8_parts(file, 20).2, fh_of(p), ms_of(mbs, p.skip), mb_w, mb_h),
{
    hide(frame_coeffs);
    hide(row_tok);
    hide(frame_tok);
    hide(modes_ws);
    hide(fh_ws);
    hide(tok_rows);
    let fh = fh_of(p);
    let ms = ms_of(mbs, p.skip);
    let lv = lv_of(mbs);
    let end: int = 30 + p1.len() as int;
    let wt = frame_tok(fh, ms, lv, mb_w, mb_h).1;
    let wm = modes_ws(fh, ms, mb_w, mb_h);
    // The first partition: the header, then the modes.
    lemma_init_wf(p1, fh_ws(p) + wm);
    lemma_fh(p1, enc_init(), p, wm);
    let e1 = enc_run(enc_init(), fh_ws(p));
    let gh = dst(p1, e1);
    let vp = vp8_parts(file, 20);
    assert(vp.0 == end && vp.1 =~= p1);
    assert(vp.2 == gh && vp.3 == fh && vp.4 == mb_w && vp.5 == mb_h);
    lemma_sq(p);
    lemma_ms_ok(mbs, p, sq(p.q as int));
    lemma_modes_read(p1, e1, fh, ms, mb_w, mb_h);
    // The token partition.
    let tp = tok_part(file, end, 0, 0);
    assert(tp == file.subrange(end, file.len() as int));
    assert(good(tp, enc_init(), wt)) by {
        if tp != p2 {
            lemma_good_pad(p2, enc_init(), wt);
        }
    }
    lemma_init_wf(tp, wt);
    assert(num_parts(fh) == 1);
    assert forall|q: int| 0 <= q < 1 implies bool_wf(bool_init(#[trigger] tok_part(file, end, 0, q))) by {}
    assert(probs_in(fh.probs));
    lemma_frame_shape(fh, ms, lv, mb_w, mb_h, mb_h);
    assert forall|y: nat| y < mb_h implies row_tame(#[trigger] frame_coeffs(file, end, p1, gh, fh, mb_w, y)) by {
        lemma_frame_coeffs(file, end, p1, gh, fh, ms, lv, mb_w, mb_h, y);
        assert(row_tame(row_tok(fh, row_of(ms, mb_w, y as int), row_of(lv, mb_w, y as int), frame_tok(fh, ms, lv, mb_w, y).0, mb_w).0.mbs));
    }
}

} // verus!
