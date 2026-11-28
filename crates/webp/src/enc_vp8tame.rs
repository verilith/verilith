//! The coefficients the lossy encoder's tokens give are tame
//! (`vp8spec::mb_tame`): its levels dequantize within 2047, and so does
//! every luma DC the inverse WHT of its Y2 block gives.
#[cfg(verus_only)]
use crate::enc_vp8res::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn dq_at(k: int, dc: int, ac: int) -> int {
    if k > 0 {
        ac
    } else {
        dc
    }
}

/// Levels `first` to 15 dequantize within `b`.
pub open spec fn lv_dq(l: Seq<int>, first: int, dc: int, ac: int, b: int) -> bool {
    forall|k: int| first <= k < 16 ==> -b <= #[trigger] l[k] * dq_at(k, dc, ac) <= b
}

/// Every coefficient is within `b`.
pub open spec fn within(c: Seq<int>, b: int) -> bool {
    forall|i: int| 0 <= i < c.len() ==> -b <= #[trigger] c[i] <= b
}

/// The luma DCs of a Y2 block with levels `l`.
pub open spec fn y2_dcs(l: Seq<int>, dc: int, ac: int) -> Seq<int> {
    iwht(tok_out(Seq::new(16, |i: int| 0int), l, 0, true, dc, ac))
}

/// A macroblock's levels, for the dequantization factors `q`, give tame
/// coefficients.
pub open spec fn mb_lv_ok(lvs: Seq<Seq<int>>, q: (int, int, int, int, int, int)) -> bool {
    &&& forall|b: int| 0 <= b < 16 ==> lv_dq(#[trigger] lvs[b], 1, q.0, q.1, 2047)
    &&& forall|b: int| 16 <= b < 24 ==> lv_dq(#[trigger] lvs[b], 0, q.4, q.5, 2047)
    &&& within(y2_dcs(lvs[24], q.2, q.3), 2047)
}

pub proof fn lemma_wrap_id(x: int)
    requires
        -0x8000 <= x <= 0x7fff,
    ensures
        wrap16s(x) == x,
{
    if x < 0 {
        assert((x + 0x1_0000) % 0x1_0000 == x + 0x1_0000);
        assert(x % 0x1_0000 == (x + 0x1_0000) % 0x1_0000) by {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(x, 0x1_0000);
        }
    }
}

pub proof fn lemma_zz(n: int)
    requires
        0 <= n < 16,
    ensures
        0 <= zigzag(n) < 16,
{
    let z = seq![0int, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15];
    assert(forall|k: int| 0 <= k < 16 ==> 0 <= #[trigger] z[k] < 16);
}

pub proof fn lemma_tok_out_len(out: Seq<int>, lv: Seq<int>, n: int, ce: bool, dc: int, ac: int)
    requires
        out.len() == 16,
    ensures
        tok_out(out, lv, n, ce, dc, ac).len() == 16,
    decreases 16 - n,
{
    if !(n >= 16 || (ce && rest_zero(lv, n))) {
        let d = dq_at(n, dc, ac);
        let o1 = if lv[n] == 0 {
            out
        } else {
            out.update(zigzag(n), wrap16s(lv[n] * d))
        };
        lemma_tok_out_len(o1, lv, n + 1, lv[n] != 0, dc, ac);
    }
}

pub proof fn lemma_tok_out_within(out: Seq<int>, lv: Seq<int>, n: int, ce: bool, dc: int, ac: int, b: int)
    requires
        out.len() == 16,
        0 <= n,
        b <= 0x7fff,
        within(out, b),
        lv_dq(lv, n, dc, ac, b),
    ensures
        within(tok_out(out, lv, n, ce, dc, ac), b),
    decreases 16 - n,
{
    if !(n >= 16 || (ce && rest_zero(lv, n))) {
        let d = dq_at(n, dc, ac);
        assert(d == (if n > 0 {
            ac
        } else {
            dc
        }));
        assert(-b <= lv[n] * d <= b);
        lemma_wrap_id(lv[n] * d);
        let o1 = if lv[n] == 0 {
            out
        } else {
            out.update(zigzag(n), wrap16s(lv[n] * d))
        };
        lemma_zz(n);
        assert(within(o1, b));
        assert(lv_dq(lv, n + 1, dc, ac, b));
        lemma_tok_out_within(o1, lv, n + 1, lv[n] != 0, dc, ac, b);
    }
}

proof fn lemma_splice_within(c: Seq<int>, at: int, blk: Seq<int>, b: int)
    requires
        within(c, b),
        within(blk, b),
        blk.len() == 16,
    ensures
        within(splice16(c, at, blk), b),
        splice16(c, at, blk).len() == c.len(),
{
    let s = splice16(c, at, blk);
    assert forall|i: int| 0 <= i < s.len() implies -b <= #[trigger] s[i] <= b by {
        if at <= i < at + 16 {
            assert(s[i] == blk[i - at]);
        } else {
            assert(s[i] == c[i]);
        }
    }
}

pub proof fn lemma_pb_within(
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
)
    requires
        res_ok(c),
        plane_ok(t, first, base, off, w, n),
        within(c.coeffs, 2047),
        forall|k: int| base <= k < base + n ==> lv_dq(#[trigger] lvs[k], first, dq_dc, dq_ac, 2047),
    ensures
        within(pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).0.coeffs, 2047),
        pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).0.coeffs.len() == 384,
    decreases n,
{
    if n > 0 {
        let k = n - 1;
        lemma_pb_within(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let r = pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let at = 16 * (base + k);
        let sub = r.0.coeffs.subrange(at, at + 16);
        assert(within(sub, 2047));
        assert(lv_dq(lvs[base + k], first, dq_dc, dq_ac, 2047));
        lemma_tok_out_within(sub, lvs[base + k], first, true, dq_dc, dq_ac, 2047);
        lemma_tok_out_len(sub, lvs[base + k], first, true, dq_dc, dq_ac);
        lemma_splice_within(r.0.coeffs, at, tok_out(sub, lvs[base + k], first, true, dq_dc, dq_ac), 2047);
    }
}

pub proof fn lemma_mb_res_within(
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    top: Seq<bool>,
    left: Seq<bool>,
    lvs: Seq<Seq<int>>,
)
    requires
        top.len() == 9,
        left.len() == 9,
        mb_lv_ok(lvs, q),
    ensures
        within(mb_res(probs, q, false, top, left, lvs).0.coeffs, 2047),
        mb_res(probs, q, false, top, left, lvs).0.coeffs.len() == 384,
{
    hide(pb);
    let c0 = EncRes { coeffs: Seq::new(384, |i: int| 0int), top, left };
    let r1 = y2(probs, c0, lvs[24], q.2, q.3);
    let dcs = y2_dcs(lvs[24], q.2, q.3);
    assert(within(r1.0.coeffs, 2047)) by {
        assert forall|i: int| 0 <= i < 384 implies -2047 <= #[trigger] r1.0.coeffs[i] <= 2047 by {
            if 0 <= i < 256 && i % 16 == 0 {
                assert(r1.0.coeffs[i] == dcs[i / 16]);
            }
        }
    }
    assert(res_ok(r1.0));
    lemma_pb_within(probs, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    let ry = pb(probs, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    crate::enc_vp8w::lemma_pb_ok(probs, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    lemma_pb_within(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    let ru = pb(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    crate::enc_vp8w::lemma_pb_ok(probs, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    lemma_pb_within(probs, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
}

/// Coefficients within 2047 are tame.
pub proof fn lemma_tame(co: Seq<int>)
    requires
        co.len() == 384,
        within(co, 2047),
    ensures
        mb_tame(co),
{
    assert forall|i: int| 0 <= i < 24 implies idct_tame(#[trigger] mblk(co, i)) by {
        let b = mblk(co, i);
        assert forall|k: int| 0 <= k < 16 implies -2047 <= #[trigger] b[k] <= 2047 by {
            assert(b[k] == co[16 * i + k]);
        }
        lemma_idct_small(b);
    }
}

} // verus!
