//! A whole VP8 key frame as the lossy encoder lays it out: the first
//! partition (frame header and modes) and one token partition, proven to
//! read back as the header, modes and coefficients the encoder chose.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::enc_vp8modes::*;
#[cfg(verus_only)]
use crate::enc_vp8res::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn row_of<A>(s: Seq<A>, mb_w: nat, y: int) -> Seq<A> {
    s.subrange(y * mb_w, (y + 1) * mb_w)
}

/// The tokens of the first `rows` rows, all in one partition, and the
/// contexts above the next row.
pub open spec fn frame_tok(fh: FrameHeader, ms: Seq<MbModeSpec>, lv: Seq<Seq<Seq<int>>>, mb_w: nat, rows: nat) -> (
    Seq<Seq<bool>>,
    Seq<(int, bool)>,
)
    decreases rows,
{
    if rows == 0 {
        (Seq::new(mb_w, |j: int| Seq::new(9, |i: int| false)), Seq::empty())
    } else {
        let y = rows - 1;
        let r = frame_tok(fh, ms, lv, mb_w, (rows - 1) as nat);
        let o = row_tok(fh, row_of(ms, mb_w, y), row_of(lv, mb_w, y), r.0, mb_w);
        (o.0.tops, r.1 + o.1)
    }
}

/// The first rows' tokens begin those of more rows.
pub proof fn lemma_frame_tok_prefix(fh: FrameHeader, ms: Seq<MbModeSpec>, lv: Seq<Seq<Seq<int>>>, mb_w: nat, a: nat, b: nat)
    requires
        a <= b,
    ensures
        ({
            let wa = frame_tok(fh, ms, lv, mb_w, a).1;
            let wb = frame_tok(fh, ms, lv, mb_w, b).1;
            &&& wa.len() <= wb.len()
            &&& wb =~= wa + wb.subrange(wa.len() as int, wb.len() as int)
        }),
    decreases b,
{
    if a < b {
        lemma_frame_tok_prefix(fh, ms, lv, mb_w, a, (b - 1) as nat);
    }
}

pub proof fn lemma_modes_prefix(fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, a: nat, b: nat)
    requires
        a <= b,
    ensures
        ({
            let wa = modes_ws(fh, ms, mb_w, a);
            let wb = modes_ws(fh, ms, mb_w, b);
            &&& wa.len() <= wb.len()
            &&& wb =~= wa + wb.subrange(wa.len() as int, wb.len() as int)
        }),
    decreases b,
{
    if a < b {
        lemma_modes_prefix(fh, ms, mb_w, a, (b - 1) as nat);
    }
}

/// `good` for a prefix.
pub proof fn lemma_good_prefix(data: Seq<u8>, e: EncState, wa: Seq<(int, bool)>, wb: Seq<(int, bool)>)
    requires
        good(data, e, wb),
        wa.len() <= wb.len(),
        wb =~= wa + wb.subrange(wa.len() as int, wb.len() as int),
    ensures
        good(data, e, wa),
{
    lemma_good_split(data, e, wa, wb.subrange(wa.len() as int, wb.len() as int));
}

/// The modes the first partition gives each row: those the encoder wrote,
/// when the frame header's state is `gh`.
pub open spec fn modes_read(first: Seq<u8>, gh: BoolState, fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, mb_h: nat) -> bool {
    forall|y: nat| y < mb_h ==> #[trigger] mode_rows(first, gh, fh, mb_w, y + 1).mbs == row_of(ms, mb_w, y as int)
}

proof fn lemma_modes_read_row(first: Seq<u8>, e: EncState, fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, mb_h: nat, y: nat)
    requires
        fh_mode_ok(fh),
        all_ok(fh, ms),
        ms.len() == mb_w * mb_h,
        y < mb_h,
        good(first, e, modes_ws(fh, ms, mb_w, mb_h)),
    ensures
        mode_rows(first, dst(first, e), fh, mb_w, y + 1).mbs == row_of(ms, mb_w, y as int),
{
    hide(modes_ws);
    hide(mode_rows);
    lemma_modes_prefix(fh, ms, mb_w, y + 1, mb_h);
    let w = modes_ws(fh, ms, mb_w, y + 1);
    lemma_good_prefix(first, e, w, modes_ws(fh, ms, mb_w, mb_h));
    assert((y + 1) * mb_w <= mb_w * mb_h) by (nonlinear_arith)
        requires
            y < mb_h,
    ;
    assert(w + Seq::empty() =~= w);
    lemma_modes(first, e, fh, ms, mb_w, y + 1, Seq::empty());
    assert(((y + 1) - 1) as nat == y);
}

pub proof fn lemma_modes_read(first: Seq<u8>, e: EncState, fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, mb_h: nat)
    requires
        fh_mode_ok(fh),
        all_ok(fh, ms),
        ms.len() == mb_w * mb_h,
        good(first, e, modes_ws(fh, ms, mb_w, mb_h)),
    ensures
        modes_read(first, dst(first, e), fh, ms, mb_w, mb_h),
{
    hide(mode_rows);
    assert forall|y: nat| y < mb_h implies #[trigger] mode_rows(first, dst(first, e), fh, mb_w, y + 1).mbs == row_of(
        ms,
        mb_w,
        y as int,
    ) by {
        lemma_modes_read_row(first, e, fh, ms, mb_w, mb_h, y);
    }
}

pub open spec fn lv_all_ok(lv: Seq<Seq<Seq<int>>>) -> bool {
    forall|j: int| 0 <= j < lv.len() ==> lvs_ok(#[trigger] lv[j])
}

proof fn lemma_row_of_ok(lv: Seq<Seq<Seq<int>>>, mb_w: nat, mb_h: nat, y: int)
    requires
        lv_all_ok(lv),
        lv.len() == mb_w * mb_h,
        0 <= y < mb_h,
    ensures
        row_of(lv, mb_w, y).len() == mb_w,
        forall|j: int| 0 <= j < mb_w ==> lvs_ok(#[trigger] row_of(lv, mb_w, y)[j]),
{
    assert((y + 1) * mb_w <= mb_h * mb_w) by (nonlinear_arith)
        requires
            y < mb_h,
    ;
    assert((y + 1) * mb_w == y * mb_w + mb_w) by (nonlinear_arith);
    assert(0 <= y * mb_w) by (nonlinear_arith)
        requires
            0 <= y,
    ;
    assert forall|j: int| 0 <= j < mb_w implies lvs_ok(#[trigger] row_of(lv, mb_w, y)[j]) by {
        assert(row_of(lv, mb_w, y)[j] == lv[y * mb_w + j]);
    }
}

/// The token partition of a frame with one partition (`log2_parts` 0),
/// read: every row's tokens are the encoder's.
pub proof fn lemma_frame_tok(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    lv: Seq<Seq<Seq<int>>>,
    mb_w: nat,
    mb_h: nat,
    rows: nat,
    rest: Seq<(int, bool)>,
)
    requires
        fh.log2_parts == 0,
        probs_in(fh.probs),
        modes_read(first, gh, fh, ms, mb_w, mb_h),
        lv_all_ok(lv),
        lv.len() == mb_w * mb_h,
        rows <= mb_h,
        good(tok_part(file, pstart, 0, 0), enc_init(), frame_tok(fh, ms, lv, mb_w, rows).1 + rest),
    ensures
        ({
            let tp = tok_part(file, pstart, 0, 0);
            let w = frame_tok(fh, ms, lv, mb_w, rows);
            let r = tok_rows(file, pstart, first, gh, fh, mb_w, rows);
            &&& r.parts.len() == 1
            &&& r.parts[0] == dst(tp, enc_run(enc_init(), w.1))
            &&& r.tops == w.0
            &&& tops_ok(w.0)
            &&& w.0.len() == mb_w
        }),
        good(tok_part(file, pstart, 0, 0), enc_run(enc_init(), frame_tok(fh, ms, lv, mb_w, rows).1), rest),
    decreases rows,
{
    hide(row_tok);
    hide(row_tokens);
    hide(tok_part);
    let tp = tok_part(file, pstart, 0, 0);
    if rows == 0 {
        assert(Seq::<(int, bool)>::empty() + rest =~= rest);
        assert(frame_tok(fh, ms, lv, mb_w, 0).1 =~= Seq::<(int, bool)>::empty());
    } else {
        let y = (rows - 1) as nat;
        let r = frame_tok(fh, ms, lv, mb_w, y);
        let msy = row_of(ms, mb_w, y as int);
        let lvy = row_of(lv, mb_w, y as int);
        let o = row_tok(fh, msy, lvy, r.0, mb_w);
        assert(frame_tok(fh, ms, lv, mb_w, rows).1 + rest =~= r.1 + (o.1 + rest));
        lemma_frame_tok(file, pstart, first, gh, fh, ms, lv, mb_w, mb_h, y, o.1 + rest);
        lemma_row_of_ok(lv, mb_w, mb_h, y as int);
        assert(y + 1 == rows);
        assert(mode_rows(first, gh, fh, mb_w, rows).mbs == msy);
        lemma_row_tok(tp, enc_run(enc_init(), r.1), fh, msy, lvy, r.0, mb_w, rest);
        lemma_run_concat(enc_init(), r.1, o.1);
        assert(y as int % 1 == 0);
    }
}

/// The coefficients of row `y` are those the encoder's tokens give.
pub proof fn lemma_frame_coeffs(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    lv: Seq<Seq<Seq<int>>>,
    mb_w: nat,
    mb_h: nat,
    y: nat,
)
    requires
        fh.log2_parts == 0,
        probs_in(fh.probs),
        modes_read(first, gh, fh, ms, mb_w, mb_h),
        lv_all_ok(lv),
        lv.len() == mb_w * mb_h,
        y < mb_h,
        good(tok_part(file, pstart, 0, 0), enc_init(), frame_tok(fh, ms, lv, mb_w, mb_h).1),
    ensures
        frame_coeffs(file, pstart, first, gh, fh, mb_w, y) == row_tok(
            fh,
            row_of(ms, mb_w, y as int),
            row_of(lv, mb_w, y as int),
            frame_tok(fh, ms, lv, mb_w, y).0,
            mb_w,
        ).0.mbs,
{
    hide(row_tok);
    hide(row_tokens);
    hide(tok_part);
    hide(tok_rows);
    hide(frame_tok);
    let tp = tok_part(file, pstart, 0, 0);
    lemma_frame_tok_prefix(fh, ms, lv, mb_w, y + 1, mb_h);
    let w1 = frame_tok(fh, ms, lv, mb_w, y + 1).1;
    lemma_good_prefix(tp, enc_init(), w1, frame_tok(fh, ms, lv, mb_w, mb_h).1);
    let r = frame_tok(fh, ms, lv, mb_w, y);
    let msy = row_of(ms, mb_w, y as int);
    let lvy = row_of(lv, mb_w, y as int);
    let o = row_tok(fh, msy, lvy, r.0, mb_w);
    assert(w1 == r.1 + o.1) by {
        reveal(frame_tok);
    }
    lemma_frame_tok(file, pstart, first, gh, fh, ms, lv, mb_w, mb_h, y, o.1);
    lemma_row_of_ok(lv, mb_w, mb_h, y as int);
    assert(o.1 + Seq::empty() =~= o.1);
    lemma_row_tok(tp, enc_run(enc_init(), r.1), fh, msy, lvy, r.0, mb_w, Seq::empty());
    assert(y as int % 1 == 0);
    assert(num_parts(fh) == 1);
}

} // verus!
