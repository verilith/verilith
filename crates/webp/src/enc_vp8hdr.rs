//! The key frame header (RFC 6386 section 19.2) as the lossy encoder
//! writes it, proven to read back under `vp8spec::frame_header`.
//!
//! The encoder always writes the same shape: no segmentation, the normal
//! loop filter at `level` with sharpness 0 and no deltas, one token
//! partition, one quantizer index for every plane, new token
//! probabilities where they differ from the defaults, and skip flags if
//! `skip`.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
#[cfg(verus_only)]
use crate::vp8tables::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// What the header carries.
pub struct HdrParams {
    pub level: nat,
    pub q: nat,
    pub probs: Seq<int>,
    pub skip: bool,
    pub pskip: nat,
}

pub open spec fn hdr_ok(p: HdrParams) -> bool {
    &&& p.level < 64
    &&& p.q < 128
    &&& p.pskip < 256
    &&& p.probs.len() == 1056
    &&& forall|k: int| 0 <= k < 1056 ==> 0 <= #[trigger] p.probs[k] < 256
}

/// The token probability updates for the first `count` entries.
pub open spec fn tp_ws(probs: Seq<int>, count: nat) -> Seq<(int, bool)>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let k = (count - 1) as int;
        let up = spec_coeffs_update_proba(k) as int;
        tp_ws(probs, (count - 1) as nat) + if probs[k] == spec_coeffs_proba0(k) as int {
            seq![(up, false)]
        } else {
            seq![(up, true)] + lit_ws(probs[k] as nat, 8)
        }
    }
}

pub proof fn lemma_tp(data: Seq<u8>, e: EncState, probs: Seq<int>, count: nat, rest: Seq<(int, bool)>)
    requires
        count <= probs.len(),
        forall|k: int| 0 <= k < count ==> 0 <= #[trigger] probs[k] < 256,
        good(data, e, tp_ws(probs, count) + rest),
    ensures
        token_probs(data, dst(data, e), count) == (dst(data, enc_run(e, tp_ws(probs, count))), probs.take(count as int)),
        good(data, enc_run(e, tp_ws(probs, count)), rest),
    decreases count,
{
    if count == 0 {
        assert(tp_ws(probs, 0) + rest =~= rest);
        assert(probs.take(0) =~= Seq::<int>::empty());
    } else {
        let k = (count - 1) as int;
        let up = spec_coeffs_update_proba(k) as int;
        let t0 = tp_ws(probs, (count - 1) as nat);
        let piece = if probs[k] == spec_coeffs_proba0(k) as int {
            seq![(up, false)]
        } else {
            seq![(up, true)] + lit_ws(probs[k] as nat, 8)
        };
        assert(tp_ws(probs, count) + rest =~= t0 + (piece + rest));
        lemma_tp(data, e, probs, (count - 1) as nat, piece + rest);
        let e1 = enc_run(e, t0);
        lemma_run_concat(e, t0, piece);
        assert(probs.take(count as int) =~= probs.take(k).push(probs[k]));
        if probs[k] == spec_coeffs_proba0(k) as int {
            lemma_bit(data, e1, up, false, rest);
        } else {
            let l = lit_ws(probs[k] as nat, 8);
            assert(piece + rest =~= seq![(up, true)] + (l + rest));
            lemma_bit(data, e1, up, true, l + rest);
            let e2 = enc_put(e1, up, true);
            lemma2_to64();
            lemma_lit(data, e2, probs[k] as nat, 8, rest);
            lemma_run_concat(e1, seq![(up, true)], l);
        }
    }
}

/// The four quantizer deltas after the index, all zero.
pub open spec fn zero_deltas() -> Seq<(int, bool)> {
    flag_ws(false) + (flag_ws(false) + (flag_ws(false) + (flag_ws(false) + flag_ws(false))))
}

/// `color_space`, `clamping_type`, no segmentation, the loop filter.
pub open spec fn fh_a_ws(p: HdrParams) -> Seq<(int, bool)> {
    flag_ws(false) + (flag_ws(false) + (flag_ws(false) + (flag_ws(false) + (lit_ws(p.level, 6) + (lit_ws(0, 3)
        + flag_ws(false))))))
}

/// One partition, and the quantizer index with no deltas.
pub open spec fn fh_b_ws(p: HdrParams) -> Seq<(int, bool)> {
    lit_ws(0, 2) + (lit_ws(p.q, 7) + zero_deltas())
}

/// `refresh_entropy_probs`, the token probabilities, the skip flags.
pub open spec fn fh_c_ws(p: HdrParams) -> Seq<(int, bool)> {
    flag_ws(false) + (tp_ws(p.probs, 1056) + (flag_ws(p.skip) + if p.skip {
        lit_ws(p.pskip, 8)
    } else {
        Seq::empty()
    }))
}

pub open spec fn fh_ws(p: HdrParams) -> Seq<(int, bool)> {
    fh_a_ws(p) + (fh_b_ws(p) + fh_c_ws(p))
}

pub open spec fn fh_of(p: HdrParams) -> FrameHeader {
    FrameHeader {
        color_space: false,
        clamping_type: false,
        seg: SegHeader {
            enabled: false,
            update_map: false,
            update_data: false,
            absolute: true,
            quant: zeros4(),
            lf: zeros4(),
            probs: seq![255int, 255int, 255int],
        },
        filter: FilterHeader {
            simple: false,
            level: p.level as int,
            sharpness: 0,
            adj_enable: false,
            delta_update: false,
            ref_delta: zeros4(),
            mode_delta: zeros4(),
        },
        log2_parts: 0,
        quant: QuantHeader { y_ac_qi: p.q as int, y_dc_delta: 0, y2_dc_delta: 0, y2_ac_delta: 0, uv_dc_delta: 0, uv_ac_delta: 0 },
        refresh_entropy_probs: false,
        probs: p.probs,
        mb_no_coeff_skip: p.skip,
        prob_skip_false: if p.skip {
            p.pskip as int
        } else {
            0
        },
    }
}

/// One flag read, and the state moved past it.
proof fn lemma_fl(data: Seq<u8>, e: EncState, b: bool, rest: Seq<(int, bool)>) -> (e1: EncState)
    requires
        good(data, e, flag_ws(b) + rest),
    ensures
        e1 == enc_run(e, flag_ws(b)),
        rd_flag(data, dst(data, e)) == (dst(data, e1), b),
        bool_bit(dst(data, e), 128) == b,
        bool_next(data, dst(data, e), 128) == dst(data, e1),
        good(data, e1, rest),
{
    lemma_flag(data, e, b, rest);
    lemma_bit(data, e, 128, b, rest);
    enc_run(e, flag_ws(b))
}

/// A literal read, and the state moved past it.
proof fn lemma_li(data: Seq<u8>, e: EncState, v: nat, n: nat, rest: Seq<(int, bool)>) -> (e1: EncState)
    requires
        v < pow2(n),
        good(data, e, lit_ws(v, n) + rest),
    ensures
        e1 == enc_run(e, lit_ws(v, n)),
        bool_literal(data, dst(data, e), n) == (dst(data, e1), v as int),
        good(data, e1, rest),
{
    lemma_lit(data, e, v, n, rest);
    enc_run(e, lit_ws(v, n))
}

proof fn lemma_fh_a(data: Seq<u8>, e: EncState, p: HdrParams, rest: Seq<(int, bool)>) -> (e7: EncState)
    requires
        hdr_ok(p),
        good(data, e, fh_a_ws(p) + rest),
    ensures
        e7 == enc_run(e, fh_a_ws(p)),
        good(data, e7, rest),
        ({
            let (s1, cs) = rd_flag(data, dst(data, e));
            let (s2, ct) = rd_flag(data, s1);
            let (s3, seg) = seg_header(data, s2);
            let (s4, fl) = filter_header(data, s3);
            &&& !cs && !ct
            &&& seg == fh_of(p).seg
            &&& fl == fh_of(p).filter
            &&& s4 == dst(data, e7)
        }),
{
    hide(lit_ws);
    hide(flag_ws);
    hide(bool_literal);
    lemma2_to64();
    let f = flag_ws(false);
    let w6 = f;
    let w5 = lit_ws(0, 3) + w6;
    let w4 = lit_ws(p.level, 6) + w5;
    let w3 = f + w4;
    let w2 = f + w3;
    let w1 = f + w2;
    assert(fh_a_ws(p) == f + w1);
    assert((f + w1) + rest =~= f + (w1 + rest));
    let e1 = lemma_fl(data, e, false, w1 + rest);
    assert(w1 + rest =~= f + (w2 + rest));
    let e2 = lemma_fl(data, e1, false, w2 + rest);
    assert(w2 + rest =~= f + (w3 + rest));
    let e3 = lemma_fl(data, e2, false, w3 + rest);
    assert(w3 + rest =~= f + (w4 + rest));
    let e4 = lemma_fl(data, e3, false, w4 + rest);
    assert(w4 + rest =~= lit_ws(p.level, 6) + (w5 + rest));
    let e5 = lemma_li(data, e4, p.level, 6, w5 + rest);
    assert(w5 + rest =~= lit_ws(0, 3) + (w6 + rest));
    let e6 = lemma_li(data, e5, 0, 3, w6 + rest);
    let e7 = lemma_fl(data, e6, false, rest);
    lemma_run_concat(e5, lit_ws(0, 3), w6);
    lemma_run_concat(e4, lit_ws(p.level, 6), w5);
    lemma_run_concat(e3, f, w4);
    lemma_run_concat(e2, f, w3);
    lemma_run_concat(e1, f, w2);
    lemma_run_concat(e, f, w1);
    e7
}

proof fn lemma_fh_b(data: Seq<u8>, e: EncState, p: HdrParams, rest: Seq<(int, bool)>) -> (e3: EncState)
    requires
        hdr_ok(p),
        good(data, e, fh_b_ws(p) + rest),
    ensures
        e3 == enc_run(e, fh_b_ws(p)),
        good(data, e3, rest),
        ({
            let (s1, lp) = bool_literal(data, dst(data, e), 2);
            let (s2, q) = quant_header(data, s1);
            &&& lp == 0
            &&& q == fh_of(p).quant
            &&& s2 == dst(data, e3)
        }),
{
    hide(lit_ws);
    hide(flag_ws);
    hide(bool_literal);
    hide(rd_flag);
    lemma2_to64();
    let f = flag_ws(false);
    let w2 = zero_deltas();
    let w1 = lit_ws(p.q, 7) + w2;
    assert(fh_b_ws(p) + rest =~= lit_ws(0, 2) + (w1 + rest));
    let e1 = lemma_li(data, e, 0, 2, w1 + rest);
    assert(w1 + rest =~= lit_ws(p.q, 7) + (w2 + rest));
    let e2 = lemma_li(data, e1, p.q, 7, w2 + rest);
    let f4 = f + (f + (f + f));
    assert(w2 + rest =~= f + (f + (f + (f + (f + rest)))));
    let d1 = lemma_fl(data, e2, false, f + (f + (f + (f + rest))));
    let d2 = lemma_fl(data, d1, false, f + (f + (f + rest)));
    let d3 = lemma_fl(data, d2, false, f + (f + rest));
    let d4 = lemma_fl(data, d3, false, f + rest);
    let d5 = lemma_fl(data, d4, false, rest);
    lemma_run_concat(d3, f, f);
    lemma_run_concat(d2, f, f + f);
    lemma_run_concat(d1, f, f + (f + f));
    lemma_run_concat(e2, f, f + (f + (f + f)));
    lemma_run_concat(e1, lit_ws(p.q, 7), w2);
    lemma_run_concat(e, lit_ws(0, 2), w1);
    reveal(rd_flag);
    assert(rd_opt_signed(data, dst(data, e2), 4) == (dst(data, d1), 0int));
    assert(rd_opt_signed(data, dst(data, d1), 4) == (dst(data, d2), 0int));
    assert(rd_opt_signed(data, dst(data, d2), 4) == (dst(data, d3), 0int));
    assert(rd_opt_signed(data, dst(data, d3), 4) == (dst(data, d4), 0int));
    assert(rd_opt_signed(data, dst(data, d4), 4) == (dst(data, d5), 0int));
    d5
}

proof fn lemma_fh_c(data: Seq<u8>, e: EncState, p: HdrParams, rest: Seq<(int, bool)>) -> (e3: EncState)
    requires
        hdr_ok(p),
        good(data, e, fh_c_ws(p) + rest),
    ensures
        e3 == enc_run(e, fh_c_ws(p)),
        good(data, e3, rest),
        ({
            let (s1, re) = rd_flag(data, dst(data, e));
            let (s2, probs) = token_probs(data, s1, 1056);
            let (s3, sk) = rd_flag(data, s2);
            let (s4, ps) = if sk {
                bool_literal(data, s3, 8)
            } else {
                (s3, 0)
            };
            &&& !re
            &&& probs == p.probs
            &&& sk == p.skip
            &&& ps == fh_of(p).prob_skip_false
            &&& s4 == dst(data, e3)
        }),
{
    hide(lit_ws);
    hide(flag_ws);
    hide(bool_literal);
    hide(tp_ws);
    hide(token_probs);
    lemma2_to64();
    let f = flag_ws(false);
    let sk = if p.skip {
        lit_ws(p.pskip, 8)
    } else {
        Seq::empty()
    };
    let w2 = flag_ws(p.skip) + sk;
    let w1 = tp_ws(p.probs, 1056) + w2;
    assert(fh_c_ws(p) + rest =~= f + (w1 + rest));
    let e1 = lemma_fl(data, e, false, w1 + rest);
    assert(w1 + rest =~= tp_ws(p.probs, 1056) + (w2 + rest));
    lemma_tp(data, e1, p.probs, 1056, w2 + rest);
    let e2 = enc_run(e1, tp_ws(p.probs, 1056));
    assert(p.probs.take(1056) =~= p.probs);
    assert(w2 + rest =~= flag_ws(p.skip) + (sk + rest));
    let e3 = lemma_fl(data, e2, p.skip, sk + rest);
    let e4 = if p.skip {
        lemma_li(data, e3, p.pskip, 8, rest)
    } else {
        assert(sk + rest =~= rest);
        e3
    };
    assert(e4 == enc_run(e3, sk)) by {
        if !p.skip {
            assert(sk =~= Seq::<(int, bool)>::empty());
        }
    }
    lemma_run_concat(e2, flag_ws(p.skip), sk);
    lemma_run_concat(e1, tp_ws(p.probs, 1056), w2);
    lemma_run_concat(e, f, w1);
    e4
}

pub proof fn lemma_fh(data: Seq<u8>, e: EncState, p: HdrParams, rest: Seq<(int, bool)>)
    requires
        hdr_ok(p),
        good(data, e, fh_ws(p) + rest),
    ensures
        frame_header(data, dst(data, e)) == (dst(data, enc_run(e, fh_ws(p))), fh_of(p)),
        good(data, enc_run(e, fh_ws(p)), rest),
{
    hide(fh_a_ws);
    hide(fh_b_ws);
    hide(fh_c_ws);
    hide(seg_header);
    hide(filter_header);
    hide(quant_header);
    hide(token_probs);
    hide(rd_flag);
    hide(bool_literal);
    let a = fh_a_ws(p);
    let b = fh_b_ws(p);
    let c = fh_c_ws(p);
    assert(fh_ws(p) + rest =~= a + (b + (c + rest)));
    let e1 = lemma_fh_a(data, e, p, b + (c + rest));
    let e2 = lemma_fh_b(data, e1, p, c + rest);
    let e3 = lemma_fh_c(data, e2, p, rest);
    lemma_run_concat(e1, b, c);
    lemma_run_concat(e, a, b + c);
}

} // verus!
