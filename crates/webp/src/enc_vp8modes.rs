//! The macroblock modes of the first partition (RFC 6386 section 19.3) as
//! the lossy encoder writes them, proven to read back under
//! `vp8spec::mode_rows`. Every macroblock is predicted as a whole
//! (`DC_PRED`, `TM_PRED`, `V_PRED` or `H_PRED` for luma, the same four
//! for chroma), so no mode depends on its neighbours'.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
use vstd::prelude::*;

verus! {

/// The luma mode in `kf_ymode_tree` (libwebp's numbering).
pub open spec fn ymode_ws(m: int) -> Seq<(int, bool)> {
    if m == 0 {
        seq![(156int, false), (163int, false)]
    } else if m == 2 {
        seq![(156int, false), (163int, true)]
    } else if m == 1 {
        seq![(156int, true), (128int, true)]
    } else {
        seq![(156int, true), (128int, false)]
    }
}

/// The chroma mode in `uv_mode_tree`.
pub open spec fn uv_ws(m: int) -> Seq<(int, bool)> {
    if m == 0 {
        seq![(142int, false)]
    } else if m == 2 {
        seq![(142int, true), (114int, false)]
    } else if m == 1 {
        seq![(142int, true), (114int, true), (183int, true)]
    } else {
        seq![(142int, true), (114int, true), (183int, false)]
    }
}

/// A macroblock the encoder can write.
pub open spec fn mb_ok(fh: FrameHeader, m: MbModeSpec) -> bool {
    &&& m.segment == 0
    &&& !m.is_i4x4
    &&& m.bmodes == Seq::<int>::empty()
    &&& 0 <= m.ymode < 4
    &&& 0 <= m.uvmode < 4
    &&& !fh.mb_no_coeff_skip ==> !m.skip
}

pub open spec fn fh_mode_ok(fh: FrameHeader) -> bool {
    &&& !fh.seg.update_map
    &&& 0 <= fh.prob_skip_false < 256
}

pub open spec fn mbm_ws(fh: FrameHeader, m: MbModeSpec) -> Seq<(int, bool)> {
    (if fh.mb_no_coeff_skip {
        seq![(fh.prob_skip_false, m.skip)]
    } else {
        Seq::empty()
    }) + (seq![(145int, true)] + (ymode_ws(m.ymode) + uv_ws(m.uvmode)))
}

proof fn lemma_two(data: Seq<u8>, e: EncState, a: (int, bool), b: (int, bool), rest: Seq<(int, bool)>) -> (e2: EncState)
    requires
        good(data, e, seq![a, b] + rest),
    ensures
        e2 == enc_run(e, seq![a, b]),
        bool_bit(dst(data, e), a.0) == a.1,
        bool_bit(dst(data, enc_put(e, a.0, a.1)), b.0) == b.1,
        bool_next(data, dst(data, e), a.0) == dst(data, enc_put(e, a.0, a.1)),
        bool_next(data, dst(data, enc_put(e, a.0, a.1)), b.0) == dst(data, e2),
        good(data, e2, rest),
{
    assert(seq![a, b] + rest =~= seq![a] + (seq![b] + rest));
    lemma_bit(data, e, a.0, a.1, seq![b] + rest);
    let e1 = enc_put(e, a.0, a.1);
    lemma_bit(data, e1, b.0, b.1, rest);
    lemma_run_concat(e, seq![a], seq![b]);
    assert(seq![a] + seq![b] =~= seq![a, b]);
    enc_run(e, seq![a, b])
}

proof fn lemma_ymode(data: Seq<u8>, e: EncState, m: int, rest: Seq<(int, bool)>)
    requires
        0 <= m < 4,
        good(data, e, ymode_ws(m) + rest),
    ensures
        kf_ymode(data, dst(data, e)) == (dst(data, enc_run(e, ymode_ws(m))), m),
        good(data, enc_run(e, ymode_ws(m)), rest),
{
    let w = ymode_ws(m);
    lemma_two(data, e, w[0], w[1], rest);
    assert(w =~= seq![w[0], w[1]]);
}

proof fn lemma_uv(data: Seq<u8>, e: EncState, m: int, rest: Seq<(int, bool)>)
    requires
        0 <= m < 4,
        good(data, e, uv_ws(m) + rest),
    ensures
        uv_mode(data, dst(data, e)) == (dst(data, enc_run(e, uv_ws(m))), m),
        good(data, enc_run(e, uv_ws(m)), rest),
{
    let w = uv_ws(m);
    if m == 0 {
        lemma_bit(data, e, 142, false, rest);
    } else if m == 2 {
        lemma_two(data, e, w[0], w[1], rest);
        assert(w =~= seq![w[0], w[1]]);
    } else {
        assert(w + rest =~= seq![w[0], w[1]] + (seq![w[2]] + rest));
        let e2 = lemma_two(data, e, w[0], w[1], seq![w[2]] + rest);
        lemma_bit(data, e2, 183, m == 1, rest);
        lemma_run_concat(e, seq![w[0], w[1]], seq![w[2]]);
        assert(seq![w[0], w[1]] + seq![w[2]] =~= w);
    }
}

pub proof fn lemma_mbm(data: Seq<u8>, e: EncState, fh: FrameHeader, m: MbModeSpec, top: Seq<int>, left: Seq<int>, rest: Seq<(int, bool)>)
    requires
        fh_mode_ok(fh),
        mb_ok(fh, m),
        good(data, e, mbm_ws(fh, m) + rest),
    ensures
        mb_modes(data, dst(data, e), fh, top, left).s == dst(data, enc_run(e, mbm_ws(fh, m))),
        mb_modes(data, dst(data, e), fh, top, left).m == m,
        good(data, enc_run(e, mbm_ws(fh, m)), rest),
{
    let sk = if fh.mb_no_coeff_skip {
        seq![(fh.prob_skip_false, m.skip)]
    } else {
        Seq::empty()
    };
    let nb = seq![(145int, true)];
    let yw = ymode_ws(m.ymode);
    let uw = uv_ws(m.uvmode);
    assert(mbm_ws(fh, m) + rest =~= sk + (nb + (yw + (uw + rest))));
    let e1 = if fh.mb_no_coeff_skip {
        lemma_bit(data, e, fh.prob_skip_false, m.skip, nb + (yw + (uw + rest)));
        enc_put(e, fh.prob_skip_false, m.skip)
    } else {
        assert(sk + (nb + (yw + (uw + rest))) =~= nb + (yw + (uw + rest)));
        e
    };
    assert(e1 == enc_run(e, sk)) by {
        if !fh.mb_no_coeff_skip {
            assert(sk =~= Seq::<(int, bool)>::empty());
        }
    }
    assert(mb_skip(data, dst(data, e), fh) == (dst(data, e1), m.skip));
    lemma_bit(data, e1, 145, true, yw + (uw + rest));
    let e2 = enc_put(e1, 145, true);
    lemma_ymode(data, e2, m.ymode, uw + rest);
    let e3 = enc_run(e2, yw);
    lemma_uv(data, e3, m.uvmode, rest);
    let e4 = enc_run(e3, uw);
    lemma_run_concat(e2, yw, uw);
    lemma_run_concat(e1, nb, yw + uw);
    lemma_run_concat(e, sk, nb + (yw + uw));
    assert(mb_modes(data, dst(data, e), fh, top, left).m == MbModeSpec {
        segment: 0,
        skip: m.skip,
        is_i4x4: false,
        ymode: m.ymode,
        bmodes: Seq::empty(),
        uvmode: m.uvmode,
    });
}

/// Macroblocks `base` to `base + n` of `ms`.
pub open spec fn row_ws(fh: FrameHeader, ms: Seq<MbModeSpec>, base: int, n: nat) -> Seq<(int, bool)>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        row_ws(fh, ms, base, (n - 1) as nat) + mbm_ws(fh, ms[base + n - 1])
    }
}

pub open spec fn all_ok(fh: FrameHeader, ms: Seq<MbModeSpec>) -> bool {
    forall|i: int| 0 <= i < ms.len() ==> mb_ok(fh, #[trigger] ms[i])
}

pub proof fn lemma_row(
    data: Seq<u8>,
    e: EncState,
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    base: int,
    top: Seq<int>,
    n: nat,
    rest: Seq<(int, bool)>,
)
    requires
        fh_mode_ok(fh),
        all_ok(fh, ms),
        0 <= base,
        base + n <= ms.len(),
        top.len() >= 4 * n,
        good(data, e, row_ws(fh, ms, base, n) + rest),
    ensures
        ({
            let r = row_modes(data, dst(data, e), fh, top, n);
            &&& r.s == dst(data, enc_run(e, row_ws(fh, ms, base, n)))
            &&& r.mbs == ms.subrange(base, base + n)
            &&& r.top.len() == top.len()
        }),
        good(data, enc_run(e, row_ws(fh, ms, base, n)), rest),
    decreases n,
{
    if n == 0 {
        assert(row_ws(fh, ms, base, 0) + rest =~= rest);
        assert(ms.subrange(base, base) =~= Seq::<MbModeSpec>::empty());
    } else {
        let k = (n - 1) as nat;
        let w0 = row_ws(fh, ms, base, k);
        let m = ms[base + k];
        let w1 = mbm_ws(fh, m);
        assert(row_ws(fh, ms, base, n) + rest =~= w0 + (w1 + rest));
        lemma_row(data, e, fh, ms, base, top, k, w1 + rest);
        let r = row_modes(data, dst(data, e), fh, top, k);
        let e1 = enc_run(e, w0);
        assert(mb_ok(fh, m));
        lemma_mbm(data, e1, fh, m, r.top.subrange(4 * k as int, (4 * k + 4) as int), r.left, rest);
        lemma_run_concat(e, w0, w1);
        assert(ms.subrange(base, base + n) =~= ms.subrange(base, base + k).push(m));
    }
}

/// The first `rows` rows of `mb_w` macroblocks.
pub open spec fn modes_ws(fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, rows: nat) -> Seq<(int, bool)>
    decreases rows,
{
    if rows == 0 {
        Seq::empty()
    } else {
        modes_ws(fh, ms, mb_w, (rows - 1) as nat) + row_ws(fh, ms, (rows - 1) * mb_w, mb_w)
    }
}

pub proof fn lemma_modes(data: Seq<u8>, e: EncState, fh: FrameHeader, ms: Seq<MbModeSpec>, mb_w: nat, rows: nat, rest: Seq<(int, bool)>)
    requires
        fh_mode_ok(fh),
        all_ok(fh, ms),
        rows * mb_w <= ms.len(),
        good(data, e, modes_ws(fh, ms, mb_w, rows) + rest),
    ensures
        ({
            let r = mode_rows(data, dst(data, e), fh, mb_w, rows);
            &&& r.s == dst(data, enc_run(e, modes_ws(fh, ms, mb_w, rows)))
            &&& rows > 0 ==> r.mbs == ms.subrange((rows - 1) * mb_w, (rows * mb_w) as int)
            &&& r.top.len() == 4 * mb_w
        }),
        good(data, enc_run(e, modes_ws(fh, ms, mb_w, rows)), rest),
    decreases rows,
{
    if rows == 0 {
        assert(modes_ws(fh, ms, mb_w, 0) + rest =~= rest);
    } else {
        let k = (rows - 1) as nat;
        let w0 = modes_ws(fh, ms, mb_w, k);
        let w1 = row_ws(fh, ms, (k * mb_w) as int, mb_w);
        assert(modes_ws(fh, ms, mb_w, rows) + rest =~= w0 + (w1 + rest));
        assert(k * mb_w <= rows * mb_w) by (nonlinear_arith)
            requires
                k <= rows,
        ;
        lemma_modes(data, e, fh, ms, mb_w, k, w1 + rest);
        let r = mode_rows(data, dst(data, e), fh, mb_w, k);
        assert(k * mb_w + mb_w == rows * mb_w) by (nonlinear_arith)
            requires
                k + 1 == rows,
        ;
        lemma_row(data, enc_run(e, w0), fh, ms, (k * mb_w) as int, r.top, mb_w, rest);
        lemma_run_concat(e, w0, w1);
    }
}

} // verus!
