//! The coefficient tokens of one block (RFC 6386 section 13) as the lossy
//! encoder writes them, proven to read back under `vp8spec::block_tokens`.
//!
//! A block is given as its sixteen quantized levels in stream (zigzag)
//! order. The tokens run up to the last nonzero level and end with
//! `dct_eob` unless that level is the sixteenth.
#[cfg(verus_only)]
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub open spec fn iabs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// Levels `n` to 15 are all zero.
pub open spec fn rest_zero(lv: Seq<int>, n: int) -> bool {
    forall|k: int| n <= k < 16 ==> #[trigger] lv[k] == 0
}

/// The extra bits of a `dct_cat` token, the most significant first.
pub open spec fn ext_ws(tab: Seq<u8>, v: nat, n: nat) -> Seq<(int, bool)>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        ext_ws(tab, v / 2, (n - 1) as nat).push((tab[n - 1] as int, v % 2 == 1))
    }
}

pub proof fn lemma_ext(data: Seq<u8>, e: EncState, tab: Seq<u8>, v: nat, n: nat, rest: Seq<(int, bool)>)
    requires
        n <= tab.len(),
        v < pow2(n),
        good(data, e, ext_ws(tab, v, n) + rest),
    ensures
        rd_extra(data, dst(data, e), tab, n) == (dst(data, enc_run(e, ext_ws(tab, v, n))), v as int),
        good(data, enc_run(e, ext_ws(tab, v, n)), rest),
    decreases n,
{
    lemma2_to64();
    if n == 0 {
        assert(ext_ws(tab, v, n) + rest =~= rest);
    } else {
        let n1 = (n - 1) as nat;
        let b = v % 2 == 1;
        let w1 = ext_ws(tab, v / 2, n1);
        let p = tab[n - 1] as int;
        lemma_pow2_unfold(n);
        assert(ext_ws(tab, v, n) + rest =~= w1 + (seq![(p, b)] + rest));
        lemma_ext(data, e, tab, v / 2, n1, seq![(p, b)] + rest);
        let e1 = enc_run(e, w1);
        lemma_bit(data, e1, p, b, rest);
        assert(ext_ws(tab, v, n).drop_last() =~= w1);
        assert(ext_ws(tab, v, n).last() == (p, b));
    }
}

/// The tree path of a magnitude from 2 (`DCT_2` and up), without the
/// extra bits, with the probabilities at `p`.
pub open spec fn large_head(probs: Seq<int>, p: int, v: int) -> Seq<(int, bool)> {
    if v == 2 {
        seq![(probs[p + 3], false), (probs[p + 4], false)]
    } else if v <= 4 {
        seq![(probs[p + 3], false), (probs[p + 4], true), (probs[p + 5], v == 4)]
    } else if v <= 6 {
        seq![(probs[p + 3], true), (probs[p + 6], false), (probs[p + 7], false), (159int, v == 6)]
    } else if v <= 10 {
        seq![(probs[p + 3], true), (probs[p + 6], false), (probs[p + 7], true), (165int, v - 7 >= 2), (145int, (v - 7) % 2 == 1)]
    } else if v <= 18 {
        seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], false), (probs[p + 9], false)]
    } else if v <= 34 {
        seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], false), (probs[p + 9], true)]
    } else if v <= 66 {
        seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], true), (probs[p + 10], false)]
    } else {
        seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], true), (probs[p + 10], true)]
    }
}

/// The extra bits of a magnitude from 11.
pub open spec fn large_tail(v: int) -> Seq<(int, bool)> {
    if v <= 10 {
        Seq::empty()
    } else if v <= 18 {
        ext_ws(pcat3(), (v - 11) as nat, 3)
    } else if v <= 34 {
        ext_ws(pcat4(), (v - 19) as nat, 4)
    } else if v <= 66 {
        ext_ws(pcat5(), (v - 35) as nat, 5)
    } else {
        ext_ws(pcat6(), (v - 67) as nat, 11)
    }
}

pub open spec fn large_ws(probs: Seq<int>, p: int, v: int) -> Seq<(int, bool)> {
    large_head(probs, p, v) + large_tail(v)
}

pub open spec fn probs_in(probs: Seq<int>) -> bool {
    &&& probs.len() == 1056
    &&& forall|k: int| 0 <= k < 1056 ==> 0 <= #[trigger] probs[k] < 256
}

proof fn lemma_large_small(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, v: int, rest: Seq<(int, bool)>)
    requires
        probs_in(probs),
        0 <= p,
        p + 10 < 1056,
        2 <= v <= 10,
        good(data, e, large_ws(probs, p, v) + rest),
    ensures
        large_value(data, dst(data, e), probs, p) == (dst(data, enc_run(e, large_ws(probs, p, v))), v),
        good(data, enc_run(e, large_ws(probs, p, v)), rest),
{
    let h = large_head(probs, p, v);
    assert(large_tail(v) =~= Seq::<(int, bool)>::empty());
    assert(large_ws(probs, p, v) =~= h);
    if v == 2 {
        lemma_chain2(data, e, h[0], h[1], rest);
        assert(h =~= seq![h[0], h[1]]);
    } else if v <= 4 {
        lemma_chain3(data, e, h[0], h[1], h[2], rest);
        assert(h =~= seq![h[0], h[1], h[2]]);
    } else if v <= 6 {
        lemma_chain4(data, e, h[0], h[1], h[2], h[3], rest);
        assert(h =~= seq![h[0], h[1], h[2], h[3]]);
    } else {
        lemma_chain5(data, e, h[0], h[1], h[2], h[3], h[4], rest);
        assert(h =~= seq![h[0], h[1], h[2], h[3], h[4]]);
    }
}

proof fn lemma_cat(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    p: int,
    v: int,
    tab: Seq<u8>,
    base: int,
    nb: nat,
    b8: bool,
    b9: bool,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        0 <= p,
        p + 10 < 1056,
        nb == tab.len(),
        0 <= v - base < pow2(nb),
        large_head(probs, p, v) == seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], b8), (probs[p + 9 + b2i(b8)], b9)],
        large_tail(v) == ext_ws(tab, (v - base) as nat, nb),
        ({
            let s4 = dst(data, enc_run(e, large_head(probs, p, v)));
            let (sx, x) = rd_extra(data, s4, tab, nb);
            large_value(data, dst(data, e), probs, p) == (sx, x + base)
        }),
        good(data, e, large_ws(probs, p, v) + rest),
    ensures
        large_value(data, dst(data, e), probs, p) == (dst(data, enc_run(e, large_ws(probs, p, v))), v),
        good(data, enc_run(e, large_ws(probs, p, v)), rest),
{
    hide(ext_ws);
    hide(rd_extra);
    hide(large_value);
    let h = large_head(probs, p, v);
    let t = large_tail(v);
    assert(large_ws(probs, p, v) + rest =~= h + (t + rest));
    lemma_good_split(data, e, h, t + rest);
    let eh = enc_run(e, h);
    lemma_run_concat(e, h, t);
    lemma_ext(data, eh, tab, (v - base) as nat, nb, rest);
}

/// The first four bits of a `dct_cat` token, read: what is left is
/// `rd_extra` with the category's table.
proof fn lemma_cat_head(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, b8: bool, b9: bool, rest: Seq<(int, bool)>)
    requires
        good(data, e, seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], b8), (probs[p + 9 + b2i(b8)], b9)] + rest),
    ensures
        ({
            let h = seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], b8), (probs[p + 9 + b2i(b8)], b9)];
            let s4 = dst(data, enc_run(e, h));
            let tab = if !b8 && !b9 {
                pcat3()
            } else if !b8 {
                pcat4()
            } else if !b9 {
                pcat5()
            } else {
                pcat6()
            };
            let nb: nat = if !b8 && !b9 {
                3
            } else if !b8 {
                4
            } else if !b9 {
                5
            } else {
                11
            };
            let base = if !b8 && !b9 {
                11int
            } else if !b8 {
                19
            } else if !b9 {
                35
            } else {
                67
            };
            let (sx, x) = rd_extra(data, s4, tab, nb);
            large_value(data, dst(data, e), probs, p) == (sx, x + base)
        }),
{
    hide(rd_extra);
    let h = seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], b8), (probs[p + 9 + b2i(b8)], b9)];
    lemma_chain4(data, e, h[0], h[1], h[2], h[3], rest);
    assert(h =~= seq![h[0], h[1], h[2], h[3]]);
}

proof fn lemma_large_cat(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, v: int, rest: Seq<(int, bool)>)
    requires
        probs_in(probs),
        0 <= p,
        p + 10 < 1056,
        11 <= v <= 2114,
        good(data, e, large_ws(probs, p, v) + rest),
    ensures
        large_value(data, dst(data, e), probs, p) == (dst(data, enc_run(e, large_ws(probs, p, v))), v),
        good(data, enc_run(e, large_ws(probs, p, v)), rest),
{
    hide(ext_ws);
    hide(rd_extra);
    hide(large_value);
    hide(large_ws);
    lemma2_to64();
    let b8 = v > 34;
    let b9 = if v <= 34 {
        v > 18
    } else {
        v > 66
    };
    let h = seq![(probs[p + 3], true), (probs[p + 6], true), (probs[p + 8], b8), (probs[p + 9 + b2i(b8)], b9)];
    assert(large_head(probs, p, v) == h);
    let t = large_tail(v);
    assert(large_ws(probs, p, v) + rest =~= h + (t + rest)) by {
        reveal(large_ws);
    }
    lemma_good_split(data, e, h, t + rest);
    assert(good(data, e, h + Seq::<(int, bool)>::empty())) by {
        assert(h + Seq::<(int, bool)>::empty() =~= h);
    }
    lemma_cat_head(data, e, probs, p, b8, b9, Seq::empty());
    if v <= 18 {
        lemma_cat(data, e, probs, p, v, pcat3(), 11, 3, b8, b9, rest);
    } else if v <= 34 {
        lemma_cat(data, e, probs, p, v, pcat4(), 19, 4, b8, b9, rest);
    } else if v <= 66 {
        lemma_cat(data, e, probs, p, v, pcat5(), 35, 5, b8, b9, rest);
    } else {
        lemma_cat(data, e, probs, p, v, pcat6(), 67, 11, b8, b9, rest);
    }
}

proof fn lemma_large(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, v: int, rest: Seq<(int, bool)>)
    requires
        probs_in(probs),
        0 <= p,
        p + 10 < 1056,
        2 <= v <= 2114,
        good(data, e, large_ws(probs, p, v) + rest),
    ensures
        large_value(data, dst(data, e), probs, p) == (dst(data, enc_run(e, large_ws(probs, p, v))), v),
        good(data, enc_run(e, large_ws(probs, p, v)), rest),
{
    if v <= 10 {
        lemma_large_small(data, e, probs, p, v, rest);
    } else {
        lemma_large_cat(data, e, probs, p, v, rest);
    }
}

/// The context the next token is read in.
pub open spec fn nctx(x: int) -> int {
    if x == 0 {
        0
    } else if iabs(x) > 1 {
        2
    } else {
        1
    }
}

/// The token at position `n` (not `dct_eob`).
pub open spec fn step_ws(probs: Seq<int>, t: int, n: int, ctx: int, ce: bool, lv: Seq<int>) -> Seq<(int, bool)> {
    let p = token_pidx(t, n, ctx);
    let v = iabs(lv[n]);
    (if ce {
        seq![(probs[p], true)]
    } else {
        Seq::empty()
    }) + if lv[n] == 0 {
        seq![(probs[p + 1], false)]
    } else {
        seq![(probs[p + 1], true)] + ((if v == 1 {
            seq![(probs[p + 2], false)]
        } else {
            seq![(probs[p + 2], true)] + large_ws(probs, p, v)
        }) + seq![(128int, lv[n] < 0)])
    }
}

/// The tokens of a block from position `n`, as `block_tokens` reads them.
pub open spec fn tok_ws(probs: Seq<int>, t: int, n: int, ctx: int, ce: bool, lv: Seq<int>) -> Seq<(int, bool)>
    decreases 16 - n,
{
    if n >= 16 {
        Seq::empty()
    } else if ce && rest_zero(lv, n) {
        seq![(probs[token_pidx(t, n, ctx)], false)]
    } else {
        step_ws(probs, t, n, ctx, ce, lv) + tok_ws(probs, t, n + 1, nctx(lv[n]), lv[n] != 0, lv)
    }
}

/// The block the tokens leave in `out`.
pub open spec fn tok_out(out: Seq<int>, lv: Seq<int>, n: int, ce: bool, dq_dc: int, dq_ac: int) -> Seq<int>
    decreases 16 - n,
{
    if n >= 16 || (ce && rest_zero(lv, n)) {
        out
    } else {
        let d = if n > 0 {
            dq_ac
        } else {
            dq_dc
        };
        tok_out(
            if lv[n] == 0 {
                out
            } else {
                out.update(zigzag(n), wrap16s(lv[n] * d))
            },
            lv,
            n + 1,
            lv[n] != 0,
            dq_dc,
            dq_ac,
        )
    }
}

/// Where the tokens end: the position of `dct_eob`, or 16.
pub open spec fn tok_end(lv: Seq<int>, n: int, ce: bool) -> int
    decreases 16 - n,
{
    if n >= 16 {
        16
    } else if ce && rest_zero(lv, n) {
        n
    } else {
        tok_end(lv, n + 1, lv[n] != 0)
    }
}

pub open spec fn lv_ok(lv: Seq<int>) -> bool {
    &&& lv.len() == 16
    &&& forall|k: int| 0 <= k < 16 ==> -2114 <= #[trigger] lv[k] <= 2114
}

/// Past the end-of-block branch: the token's first bit, if `ce`.
proof fn lemma_step_eob(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, ce: bool, rest: Seq<(int, bool)>) -> (e1: EncState)
    requires
        0 <= p < 1056,
        good(data, e, (if ce {
            seq![(probs[p], true)]
        } else {
            Seq::empty()
        }) + rest),
    ensures
        e1 == enc_run(e, if ce {
            seq![(probs[p], true)]
        } else {
            Seq::empty()
        }),
        ce ==> bool_bit(dst(data, e), probs[p]) && bool_next(data, dst(data, e), probs[p]) == dst(data, e1),
        !ce ==> e1 == e,
        good(data, e1, rest),
{
    let head = if ce {
        seq![(probs[p], true)]
    } else {
        Seq::empty()
    };
    if ce {
        lemma_bit(data, e, probs[p], true, rest);
        enc_put(e, probs[p], true)
    } else {
        assert(head + rest =~= rest);
        assert(head =~= Seq::<(int, bool)>::empty());
        e
    }
}

/// The bits of a nonzero token after its first: "not zero", "more than
/// one", the magnitude, the sign.
pub open spec fn val_ws(probs: Seq<int>, p: int, x: int) -> Seq<(int, bool)> {
    let v = iabs(x);
    seq![(probs[p + 1], true)] + ((if v == 1 {
        seq![(probs[p + 2], false)]
    } else {
        seq![(probs[p + 2], true)] + large_ws(probs, p, v)
    }) + seq![(128int, x < 0)])
}

proof fn lemma_val(data: Seq<u8>, e: EncState, probs: Seq<int>, p: int, x: int, rest: Seq<(int, bool)>)
    requires
        probs_in(probs),
        0 <= p,
        p + 10 < 1056,
        x != 0,
        -2114 <= x <= 2114,
        good(data, e, val_ws(probs, p, x) + rest),
    ensures
        ({
            let v = iabs(x);
            let (s2, nonzero) = rd_bool(data, dst(data, e), probs[p + 1]);
            let (s3, big) = rd_bool(data, s2, probs[p + 2]);
            let (s4, val) = if big {
                large_value(data, s3, probs, p)
            } else {
                (s3, 1)
            };
            let (s5, neg) = rd_bool(data, s4, 128);
            &&& nonzero
            &&& big == (v > 1)
            &&& val == v
            &&& neg == (x < 0)
            &&& s5 == dst(data, enc_run(e, val_ws(probs, p, x)))
        }),
        good(data, enc_run(e, val_ws(probs, p, x)), rest),
{
    hide(large_ws);
    hide(large_value);
    let v = iabs(x);
    let mw = if v == 1 {
        seq![(probs[p + 2], false)]
    } else {
        seq![(probs[p + 2], true)] + large_ws(probs, p, v)
    };
    let sg = seq![(128int, x < 0)];
    assert(val_ws(probs, p, x) + rest =~= seq![(probs[p + 1], true)] + (mw + (sg + rest)));
    lemma_bit(data, e, probs[p + 1], true, mw + (sg + rest));
    let e2 = enc_put(e, probs[p + 1], true);
    let e3 = if v == 1 {
        lemma_bit(data, e2, probs[p + 2], false, sg + rest);
        enc_put(e2, probs[p + 2], false)
    } else {
        let lw = large_ws(probs, p, v);
        assert(mw + (sg + rest) =~= seq![(probs[p + 2], true)] + (lw + (sg + rest)));
        lemma_bit(data, e2, probs[p + 2], true, lw + (sg + rest));
        let e2b = enc_put(e2, probs[p + 2], true);
        lemma_large(data, e2b, probs, p, v, sg + rest);
        lemma_run_concat(e2, seq![(probs[p + 2], true)], lw);
        enc_run(e2b, lw)
    };
    assert(e3 == enc_run(e2, mw));
    lemma_bit(data, e3, 128, x < 0, rest);
    lemma_run_concat(e2, mw, sg);
    lemma_run_concat(e, seq![(probs[p + 1], true)], mw + sg);
    assert(seq![(probs[p + 1], true)] + (mw + sg) =~= val_ws(probs, p, x));
}

/// One token that is not `dct_eob`, read: `block_tokens` goes on from
/// the next position.
#[verifier::spinoff_prover]
proof fn lemma_step(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    t: int,
    n: int,
    ctx: int,
    ce: bool,
    lv: Seq<int>,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        0 <= t < 4,
        0 <= n < 16,
        0 <= ctx < 3,
        lv_ok(lv),
        out.len() == 16,
        !(ce && rest_zero(lv, n)),
        good(data, e, step_ws(probs, t, n, ctx, ce, lv) + rest),
    ensures
        ({
            let d = if n > 0 {
                dq_ac
            } else {
                dq_dc
            };
            let out1 = if lv[n] == 0 {
                out
            } else {
                out.update(zigzag(n), wrap16s(lv[n] * d))
            };
            block_tokens(data, dst(data, e), probs, t, n, ctx, ce, dq_dc, dq_ac, out) == block_tokens(
                data,
                dst(data, enc_run(e, step_ws(probs, t, n, ctx, ce, lv))),
                probs,
                t,
                n + 1,
                nctx(lv[n]),
                lv[n] != 0,
                dq_dc,
                dq_ac,
                out1,
            )
        }),
        good(data, enc_run(e, step_ws(probs, t, n, ctx, ce, lv)), rest),
{
    hide(large_ws);
    hide(large_value);
    hide(block_tokens);
    hide(val_ws);
    hide(wrap16s);
    lemma_block_tokens_unfold(data, dst(data, e), probs, t, n, ctx, ce, dq_dc, dq_ac, out);
    let p = token_pidx(t, n, ctx);
    assert(0 <= p && p + 10 < 1056) by {
        assert(0 <= coeff_band(n) < 8);
    }
    let head = if ce {
        seq![(probs[p], true)]
    } else {
        Seq::empty()
    };
    let rem = if lv[n] == 0 {
        seq![(probs[p + 1], false)]
    } else {
        val_ws(probs, p, lv[n])
    };
    assert(step_ws(probs, t, n, ctx, ce, lv) == head + rem) by {
        reveal(val_ws);
    }
    assert(step_ws(probs, t, n, ctx, ce, lv) + rest =~= head + (rem + rest));
    let e1 = lemma_step_eob(data, e, probs, p, ce, rem + rest);
    lemma_run_concat(e, head, rem);
    if lv[n] == 0 {
        lemma_bit(data, e1, probs[p + 1], false, rest);
    } else {
        lemma_val(data, e1, probs, p, lv[n], rest);
        let v = iabs(lv[n]);
        let d = if n > 0 {
            dq_ac
        } else {
            dq_dc
        };
        assert(lv[n] * d == (if lv[n] < 0 {
            -v
        } else {
            v
        }) * d) by {
            if lv[n] < 0 {
                assert(lv[n] * d == (-v) * d) by (nonlinear_arith)
                    requires
                        v == -lv[n],
                ;
            }
        }
    }
}

pub proof fn lemma_tok(
    data: Seq<u8>,
    e: EncState,
    probs: Seq<int>,
    t: int,
    n: int,
    ctx: int,
    ce: bool,
    lv: Seq<int>,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
    rest: Seq<(int, bool)>,
)
    requires
        probs_in(probs),
        0 <= t < 4,
        0 <= n <= 16,
        0 <= ctx < 3,
        lv_ok(lv),
        out.len() == 16,
        good(data, e, tok_ws(probs, t, n, ctx, ce, lv) + rest),
    ensures
        block_tokens(data, dst(data, e), probs, t, n, ctx, ce, dq_dc, dq_ac, out) == (
            dst(data, enc_run(e, tok_ws(probs, t, n, ctx, ce, lv))),
            tok_out(out, lv, n, ce, dq_dc, dq_ac),
            tok_end(lv, n, ce),
        ),
        good(data, enc_run(e, tok_ws(probs, t, n, ctx, ce, lv)), rest),
    decreases 16 - n,
{
    hide(step_ws);
    hide(block_tokens);
    lemma_block_tokens_unfold(data, dst(data, e), probs, t, n, ctx, ce, dq_dc, dq_ac, out);
    let w = tok_ws(probs, t, n, ctx, ce, lv);
    if n >= 16 {
        assert(w + rest =~= rest);
        assert(w =~= Seq::<(int, bool)>::empty());
    } else if ce && rest_zero(lv, n) {
        let p = token_pidx(t, n, ctx);
        lemma_bit(data, e, probs[p], false, rest);
    } else {
        let sw = step_ws(probs, t, n, ctx, ce, lv);
        let tw = tok_ws(probs, t, n + 1, nctx(lv[n]), lv[n] != 0, lv);
        assert(w + rest =~= sw + (tw + rest));
        lemma_step(data, e, probs, t, n, ctx, ce, lv, dq_dc, dq_ac, out, tw + rest);
        let e1 = enc_run(e, sw);
        let d = if n > 0 {
            dq_ac
        } else {
            dq_dc
        };
        let out1 = if lv[n] == 0 {
            out
        } else {
            out.update(zigzag(n), wrap16s(lv[n] * d))
        };
        lemma_tok(data, e1, probs, t, n + 1, nctx(lv[n]), lv[n] != 0, lv, dq_dc, dq_ac, out1, rest);
        lemma_run_concat(e, sw, tw);
    }
}

} // verus!
