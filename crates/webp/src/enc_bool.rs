//! The boolean entropy encoder of VP8 (RFC 6386 section 7), proven
//! against the decoder of `vp8spec`: a partition it writes reads back, bit
//! for bit, as the bits it was given.
//!
//! The proof follows the encoder's interval. After the writes `ws` the
//! encoder holds `[low, low + range)` at a precision of `pos` bits
//! (`enc_run`), and the decoder state reading the same partition is
//! `dst(data, e)`: the same range and position, and the value the first
//! `pos` bits of the partition take above `low`. The partition the encoder
//! leaves has its first `pos` bits inside the final interval (`covers`),
//! and every earlier interval contains every later one.
#[cfg(verus_only)]
use crate::vp8spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The encoder, as a specification
// ---------------------------------------------------------------------------
/// The encoder's interval `[low, low + range)`, in units of `2^-pos`.
pub struct EncState {
    pub low: int,
    pub range: int,
    pub pos: nat,
}

pub open spec fn enc_init() -> EncState {
    EncState { low: 0, range: 255, pos: 8 }
}

/// Writing `bit` at probability `prob`, up to the renormalization.
pub open spec fn enc_take(e: EncState, prob: int, bit: bool) -> EncState {
    let split = bool_split(e.range, prob);
    if bit {
        EncState { low: e.low + split, range: e.range - split, pos: e.pos }
    } else {
        EncState { low: e.low, range: split, pos: e.pos }
    }
}

/// Doubling until the range is back in `[128, 255]`.
pub open spec fn enc_norm(e: EncState) -> EncState
    decreases
            (if 0 < e.range < 128 {
                128 - e.range
            } else {
                0
            }),
{
    if e.range >= 128 || e.range <= 0 {
        e
    } else {
        enc_norm(EncState { low: 2 * e.low, range: 2 * e.range, pos: e.pos + 1 })
    }
}

pub open spec fn enc_put(e: EncState, prob: int, bit: bool) -> EncState {
    enc_norm(enc_take(e, prob, bit))
}

/// The writes `ws`, each a probability and a bit, from state `e`.
pub open spec fn enc_run(e: EncState, ws: Seq<(int, bool)>) -> EncState
    decreases ws.len(),
{
    if ws.len() == 0 {
        e
    } else {
        enc_put(enc_run(e, ws.drop_last()), ws.last().0, ws.last().1)
    }
}

pub open spec fn enc_wf(e: EncState) -> bool {
    &&& 128 <= e.range <= 255
    &&& 0 <= e.low
    &&& e.low + e.range <= pow2(e.pos)
}

pub open spec fn probs_ok(ws: Seq<(int, bool)>) -> bool {
    forall|k: int| 0 <= k < ws.len() ==> 0 <= (#[trigger] ws[k]).0 <= 255
}

/// The first `e.pos` bits of `data` lie in `e`'s interval.
pub open spec fn covers(data: Seq<u8>, e: EncState) -> bool {
    e.low <= stream_bits(data, 0, e.pos) < e.low + e.range
}

/// The decoder state that goes with encoder state `e`.
pub open spec fn dst(data: Seq<u8>, e: EncState) -> BoolState {
    BoolState { range: e.range, value: stream_bits(data, 0, e.pos) - e.low, pos: e.pos }
}

/// The number of doublings that bring `r` to 128 or more.
pub open spec fn norm_n(r: int) -> nat
    decreases
            (if 0 < r < 128 {
                128 - r
            } else {
                0
            }),
{
    if r >= 128 || r <= 0 {
        0
    } else {
        1 + norm_n(2 * r)
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------
proof fn lemma_norm_n(r: int)
    requires
        1 <= r <= 255,
    ensures
        128 <= r * pow2(norm_n(r)) <= 255,
    decreases 256 - r,
{
    lemma2_to64();
    if r < 128 {
        lemma_norm_n(2 * r);
        let n1 = norm_n(2 * r);
        lemma_pow2_unfold(n1 + 1);
        assert(norm_n(r) == n1 + 1);
        assert(r * (2 * pow2(n1)) == (2 * r) * pow2(n1)) by (nonlinear_arith);
    } else {
        assert(r * 1 == r);
    }
}

/// The renormalization in closed form.
proof fn lemma_enc_norm(e: EncState, n: nat)
    requires
        1 <= e.range,
        128 <= e.range * pow2(n) <= 255,
    ensures
        enc_norm(e) == (EncState { low: e.low * pow2(n), range: e.range * pow2(n), pos: e.pos + n }),
    decreases n,
{
    lemma2_to64();
    if n == 0 {
        assert(e.range * 1 == e.range && e.low * 1 == e.low);
    } else {
        let n1 = (n - 1) as nat;
        lemma_pow2_unfold(n);
        let p = pow2(n1) as int;
        lemma_pow2_pos(n1);
        let r = e.range;
        assert(r * (2 * p) >= 2 * r) by (nonlinear_arith)
            requires
                p >= 1,
                r >= 1,
        ;
        let e1 = EncState { low: 2 * e.low, range: 2 * r, pos: e.pos + 1 };
        assert((2 * r) * p == r * (2 * p)) by (nonlinear_arith);
        assert((2 * e.low) * p == e.low * (2 * p)) by (nonlinear_arith);
        lemma_enc_norm(e1, n1);
        assert(e.pos + 1 + n1 == e.pos + n);
    }
}

/// One write read back: the decoder sees the bit and moves to the state
/// that goes with the encoder's next state.
pub proof fn lemma_step(data: Seq<u8>, e: EncState, prob: int, bit: bool)
    requires
        enc_wf(e),
        0 <= prob <= 255,
        covers(data, enc_put(e, prob, bit)),
    ensures
        bool_bit(dst(data, e), prob) == bit,
        bool_next(data, dst(data, e), prob) == dst(data, enc_put(e, prob, bit)),
        covers(data, e),
        enc_wf(enc_put(e, prob, bit)),
{
    lemma2_to64();
    lemma_split(e.range, prob);
    let t = enc_take(e, prob, bit);
    let n = norm_n(t.range);
    lemma_norm_n(t.range);
    lemma_enc_norm(t, n);
    let q = pow2(n) as int;
    lemma_pow2_pos(n);
    let s = stream_bits(data, 0, e.pos) as int;
    lemma_bits_split(data, 0, e.pos, n);
    let r = stream_bits(data, e.pos, n) as int;
    lemma_bits_bound(data, e.pos, n);
    assert(stream_bits(data, 0, e.pos + n) == s * q + r);
    assert(enc_put(e, prob, bit) == EncState { low: t.low * q, range: t.range * q, pos: e.pos + n });
    assert(t.low * q + t.range * q == (t.low + t.range) * q) by (nonlinear_arith);
    // The interval before the doublings holds the first `pos` bits.
    assert(t.low <= s < t.low + t.range) by (nonlinear_arith)
        requires
            t.low * q <= s * q + r < (t.low + t.range) * q,
            0 <= r < q,
    ;
    let ds = dst(data, e);
    let tk = bool_take(ds, prob);
    assert(tk == BoolState { range: t.range, value: s - t.low, pos: e.pos });
    lemma_norm(data, tk, n);
    assert((s - t.low) * q + r == s * q + r - t.low * q) by (nonlinear_arith);
    lemma_pow2_adds(e.pos, n);
    assert((t.low + t.range) * q <= pow2(e.pos) * q) by (nonlinear_arith)
        requires
            t.low + t.range <= pow2(e.pos),
            q >= 1,
    ;
    assert(t.low * q >= 0) by (nonlinear_arith)
        requires
            t.low >= 0,
            q >= 1,
    ;
    assert(t.low * q + t.range * q == (t.low + t.range) * q) by (nonlinear_arith);
}

pub proof fn lemma_run_wf(e: EncState, ws: Seq<(int, bool)>)
    requires
        enc_wf(e),
        probs_ok(ws),
    ensures
        enc_wf(enc_run(e, ws)),
    decreases ws.len(),
{
    if ws.len() > 0 {
        let w0 = ws.drop_last();
        assert(probs_ok(w0)) by {
            assert forall|k: int| 0 <= k < w0.len() implies 0 <= (#[trigger] w0[k]).0 <= 255 by {
                assert(w0[k] == ws[k]);
            }
        }
        lemma_run_wf(e, w0);
        let e0 = enc_run(e, w0);
        assert(ws.last() == ws[ws.len() - 1]);
        let t = enc_take(e0, ws.last().0, ws.last().1);
        lemma2_to64();
        lemma_split(e0.range, ws.last().0);
        let n = norm_n(t.range);
        lemma_norm_n(t.range);
        lemma_enc_norm(t, n);
        let q = pow2(n) as int;
        lemma_pow2_pos(n);
        lemma_pow2_adds(e0.pos, n);
        assert((t.low + t.range) * q <= pow2(e0.pos) * q) by (nonlinear_arith)
            requires
                t.low + t.range <= pow2(e0.pos),
                q >= 1,
        ;
        assert(t.low * q >= 0) by (nonlinear_arith)
            requires
                t.low >= 0,
                q >= 1,
        ;
        assert(t.low * q + t.range * q == (t.low + t.range) * q) by (nonlinear_arith);
    }
}

pub proof fn lemma_run_concat(e: EncState, a: Seq<(int, bool)>, b: Seq<(int, bool)>)
    ensures
        enc_run(e, a + b) == enc_run(enc_run(e, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_run_concat(e, a, b.drop_last());
    }
}

/// Every interval holds the next ones: covering the end covers each
/// prefix.
pub proof fn lemma_covers_take(data: Seq<u8>, e: EncState, ws: Seq<(int, bool)>, j: int)
    requires
        enc_wf(e),
        probs_ok(ws),
        0 <= j <= ws.len(),
        covers(data, enc_run(e, ws)),
    ensures
        covers(data, enc_run(e, ws.take(j))),
    decreases ws.len() - j,
{
    if j < ws.len() {
        assert(probs_ok(ws.take(j + 1))) by {
            assert forall|k: int| 0 <= k < ws.take(j + 1).len() implies 0 <= (#[trigger] ws.take(j + 1)[k]).0 <= 255 by {
                assert(ws.take(j + 1)[k] == ws[k]);
            }
        }
        lemma_covers_take(data, e, ws, j + 1);
        let w1 = ws.take(j + 1);
        assert(w1.drop_last() =~= ws.take(j));
        assert(w1.last() == ws[j]);
        assert(probs_ok(ws.take(j))) by {
            assert forall|k: int| 0 <= k < ws.take(j).len() implies 0 <= (#[trigger] ws.take(j)[k]).0 <= 255 by {
                assert(ws.take(j)[k] == ws[k]);
            }
        }
        lemma_run_wf(e, ws.take(j));
        lemma_step(data, enc_run(e, ws.take(j)), ws[j].0, ws[j].1);
    } else {
        assert(ws.take(j) =~= ws);
    }
}

/// Write `k` of `ws` read back.
pub proof fn lemma_read(data: Seq<u8>, e: EncState, ws: Seq<(int, bool)>, k: int)
    requires
        enc_wf(e),
        probs_ok(ws),
        0 <= k < ws.len(),
        covers(data, enc_run(e, ws)),
    ensures
        bool_bit(dst(data, enc_run(e, ws.take(k))), ws[k].0) == ws[k].1,
        bool_next(data, dst(data, enc_run(e, ws.take(k))), ws[k].0) == dst(data, enc_run(e, ws.take(k + 1))),
        enc_wf(enc_run(e, ws.take(k))),
{
    lemma_covers_take(data, e, ws, k + 1);
    let w1 = ws.take(k + 1);
    assert(w1.drop_last() =~= ws.take(k));
    assert(w1.last() == ws[k]);
    assert(probs_ok(ws.take(k))) by {
        assert forall|j: int| 0 <= j < ws.take(k).len() implies 0 <= (#[trigger] ws.take(k)[j]).0 <= 255 by {
            assert(ws.take(k)[j] == ws[j]);
        }
    }
    lemma_run_wf(e, ws.take(k));
    lemma_step(data, enc_run(e, ws.take(k)), ws[k].0, ws[k].1);
}



// ---------------------------------------------------------------------------
// Reading back what was written
// ---------------------------------------------------------------------------
/// The writes `ws` from encoder state `e` read back from `data`.
pub open spec fn good(data: Seq<u8>, e: EncState, ws: Seq<(int, bool)>) -> bool {
    &&& enc_wf(e)
    &&& probs_ok(ws)
    &&& covers(data, enc_run(e, ws))
}

pub proof fn lemma_good_split(data: Seq<u8>, e: EncState, a: Seq<(int, bool)>, b: Seq<(int, bool)>)
    requires
        good(data, e, a + b),
    ensures
        good(data, e, a),
        good(data, enc_run(e, a), b),
{
    let ab = a + b;
    assert(probs_ok(a)) by {
        assert forall|k: int| 0 <= k < a.len() implies 0 <= (#[trigger] a[k]).0 <= 255 by {
            assert(ab[k] == a[k]);
        }
    }
    assert(probs_ok(b)) by {
        assert forall|k: int| 0 <= k < b.len() implies 0 <= (#[trigger] b[k]).0 <= 255 by {
            assert(ab[k + a.len()] == b[k]);
        }
    }
    lemma_covers_take(data, e, ab, a.len() as int);
    assert(ab.take(a.len() as int) =~= a);
    lemma_run_wf(e, a);
    lemma_run_concat(e, a, b);
}

pub proof fn lemma_good_join(data: Seq<u8>, e: EncState, a: Seq<(int, bool)>, b: Seq<(int, bool)>)
    requires
        good(data, e, a),
        good(data, enc_run(e, a), b),
    ensures
        good(data, e, a + b),
{
    let ab = a + b;
    assert(probs_ok(ab)) by {
        assert forall|k: int| 0 <= k < ab.len() implies 0 <= (#[trigger] ab[k]).0 <= 255 by {
            if k < a.len() {
                assert(ab[k] == a[k]);
            } else {
                assert(ab[k] == b[k - a.len()]);
            }
        }
    }
    lemma_run_concat(e, a, b);
}

/// One write read back.
pub proof fn lemma_bit(data: Seq<u8>, e: EncState, p: int, b: bool, rest: Seq<(int, bool)>)
    requires
        good(data, e, seq![(p, b)] + rest),
    ensures
        bool_bit(dst(data, e), p) == b,
        bool_next(data, dst(data, e), p) == dst(data, enc_put(e, p, b)),
        good(data, enc_put(e, p, b), rest),
        enc_run(e, seq![(p, b)]) == enc_put(e, p, b),
{
    lemma_good_split(data, e, seq![(p, b)], rest);
    let w = seq![(p, b)];
    assert(w.drop_last() =~= Seq::<(int, bool)>::empty());
    assert(w.last() == (p, b));
    assert(enc_run(e, Seq::<(int, bool)>::empty()) == e);
    assert(enc_run(e, w) == enc_put(enc_run(e, w.drop_last()), w.last().0, w.last().1));
    assert(enc_run(e, w) == enc_put(e, p, b));
    assert(w[0] == (p, b));
    lemma_step(data, e, p, b);
}

/// `n` bits of `v` at probability 128, the most significant first: what
/// `bool_literal` reads.
pub open spec fn lit_ws(v: nat, n: nat) -> Seq<(int, bool)>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        lit_ws(v / 2, (n - 1) as nat).push((128int, v % 2 == 1))
    }
}

pub proof fn lemma_lit(data: Seq<u8>, e: EncState, v: nat, n: nat, rest: Seq<(int, bool)>)
    requires
        v < pow2(n),
        good(data, e, lit_ws(v, n) + rest),
    ensures
        bool_literal(data, dst(data, e), n) == (dst(data, enc_run(e, lit_ws(v, n))), v as int),
        good(data, enc_run(e, lit_ws(v, n)), rest),
    decreases n,
{
    lemma2_to64();
    if n == 0 {
        assert(lit_ws(v, n) + rest =~= rest);
    } else {
        let n1 = (n - 1) as nat;
        let b = v % 2 == 1;
        let l1 = lit_ws(v / 2, n1);
        lemma_pow2_unfold(n);
        assert(lit_ws(v, n) + rest =~= l1 + (seq![(128int, b)] + rest));
        lemma_lit(data, e, v / 2, n1, seq![(128int, b)] + rest);
        let e1 = enc_run(e, l1);
        lemma_bit(data, e1, 128, b, rest);
        assert(lit_ws(v, n).drop_last() =~= l1);
        assert(lit_ws(v, n).last() == (128int, b));
    }
}

/// A flag: one bit at probability 128.
pub open spec fn flag_ws(b: bool) -> Seq<(int, bool)> {
    seq![(128int, b)]
}

pub proof fn lemma_flag(data: Seq<u8>, e: EncState, b: bool, rest: Seq<(int, bool)>)
    requires
        good(data, e, flag_ws(b) + rest),
    ensures
        rd_flag(data, dst(data, e)) == (dst(data, enc_run(e, flag_ws(b))), b),
        good(data, enc_run(e, flag_ws(b)), rest),
{
    lemma_bit(data, e, 128, b, rest);
}

/// A magnitude in `n` bits and its sign: what `rd_signed` reads.
pub open spec fn signed_ws(x: int, n: nat) -> Seq<(int, bool)> {
    lit_ws((if x < 0 {
        -x
    } else {
        x
    }) as nat, n).push((128int, x < 0))
}

pub proof fn lemma_signed(data: Seq<u8>, e: EncState, x: int, n: nat, rest: Seq<(int, bool)>)
    requires
        -pow2(n) < x < pow2(n),
        good(data, e, signed_ws(x, n) + rest),
    ensures
        rd_signed(data, dst(data, e), n) == (dst(data, enc_run(e, signed_ws(x, n))), x),
        good(data, enc_run(e, signed_ws(x, n)), rest),
{
    let m = (if x < 0 {
        -x
    } else {
        x
    }) as nat;
    let l = lit_ws(m, n);
    assert(signed_ws(x, n) + rest =~= l + (seq![(128int, x < 0)] + rest));
    lemma_lit(data, e, m, n, seq![(128int, x < 0)] + rest);
    lemma_bit(data, enc_run(e, l), 128, x < 0, rest);
    assert(signed_ws(x, n).drop_last() =~= l);
}

/// A flag, then the value if it is not zero: what `rd_opt_signed` reads.
pub open spec fn opt_signed_ws(x: int, n: nat) -> Seq<(int, bool)> {
    if x == 0 {
        flag_ws(false)
    } else {
        flag_ws(true) + signed_ws(x, n)
    }
}

pub proof fn lemma_opt_signed(data: Seq<u8>, e: EncState, x: int, n: nat, rest: Seq<(int, bool)>)
    requires
        -pow2(n) < x < pow2(n),
        good(data, e, opt_signed_ws(x, n) + rest),
    ensures
        rd_opt_signed(data, dst(data, e), n) == (dst(data, enc_run(e, opt_signed_ws(x, n))), x),
        good(data, enc_run(e, opt_signed_ws(x, n)), rest),
{
    if x == 0 {
        lemma_bit(data, e, 128, false, rest);
    } else {
        let f = flag_ws(true);
        let sw = signed_ws(x, n);
        assert(opt_signed_ws(x, n) + rest =~= f + (sw + rest));
        lemma_bit(data, e, 128, true, sw + rest);
        let e1 = enc_put(e, 128, true);
        lemma_signed(data, e1, x, n, rest);
        lemma_run_concat(e, f, sw);
    }
}


/// Write `k` of a piece `w` read back, in the middle of a stream.
pub proof fn lemma_bits(data: Seq<u8>, e: EncState, w: Seq<(int, bool)>, rest: Seq<(int, bool)>, k: int)
    requires
        good(data, e, w + rest),
        0 <= k < w.len(),
    ensures
        bool_bit(dst(data, enc_run(e, w.take(k))), w[k].0) == w[k].1,
        bool_next(data, dst(data, enc_run(e, w.take(k))), w[k].0) == dst(data, enc_run(e, w.take(k + 1))),
        good(data, enc_run(e, w), rest),
        w.take(w.len() as int) == w,
{
    lemma_good_split(data, e, w, rest);
    lemma_read(data, e, w, k);
    assert(w.take(w.len() as int) =~= w);
}

/// The same for a whole piece of up to five writes, unrolled.
pub proof fn lemma_bits_all(data: Seq<u8>, e: EncState, w: Seq<(int, bool)>, rest: Seq<(int, bool)>)
    requires
        good(data, e, w + rest),
        w.len() <= 5,
    ensures
        forall|k: int|
            0 <= k < w.len() ==> bool_bit(dst(data, enc_run(e, #[trigger] w.take(k))), w[k].0) == w[k].1
                && bool_next(data, dst(data, enc_run(e, w.take(k))), w[k].0) == dst(data, enc_run(e, w.take(k + 1))),
        good(data, enc_run(e, w), rest),
        w.take(w.len() as int) == w,
        w.take(0) == Seq::<(int, bool)>::empty(),
        enc_run(e, Seq::<(int, bool)>::empty()) == e,
{
    assert forall|k: int| 0 <= k < w.len() implies bool_bit(dst(data, enc_run(e, #[trigger] w.take(k))), w[k].0) == w[k].1
        && bool_next(data, dst(data, enc_run(e, w.take(k))), w[k].0) == dst(data, enc_run(e, w.take(k + 1))) by {
        lemma_bits(data, e, w, rest, k);
    }
    lemma_good_split(data, e, w, rest);
    assert(w.take(w.len() as int) =~= w);
    assert(w.take(0) =~= Seq::<(int, bool)>::empty());
}


/// Short pieces of writes read back one by one.
pub proof fn lemma_chain2(data: Seq<u8>, e: EncState, a: (int, bool), b: (int, bool), rest: Seq<(int, bool)>)
    requires
        good(data, e, seq![a, b] + rest),
    ensures
        ({
            let e1 = enc_put(e, a.0, a.1);
            let e2 = enc_put(e1, b.0, b.1);
            &&& bool_bit(dst(data, e), a.0) == a.1 && bool_next(data, dst(data, e), a.0) == dst(data, e1)
            &&& bool_bit(dst(data, e1), b.0) == b.1 && bool_next(data, dst(data, e1), b.0) == dst(data, e2)
            &&& e2 == enc_run(e, seq![a, b])
            &&& good(data, e2, rest)
        }),
{
    assert(seq![a, b] + rest =~= seq![a] + (seq![b] + rest));
    lemma_bit(data, e, a.0, a.1, seq![b] + rest);
    let e1 = enc_put(e, a.0, a.1);
    lemma_bit(data, e1, b.0, b.1, rest);
    lemma_run_concat(e, seq![a], seq![b]);
    assert(seq![a] + seq![b] =~= seq![a, b]);
}

pub proof fn lemma_chain3(data: Seq<u8>, e: EncState, a: (int, bool), b: (int, bool), c: (int, bool), rest: Seq<(int, bool)>)
    requires
        good(data, e, seq![a, b, c] + rest),
    ensures
        ({
            let e1 = enc_put(e, a.0, a.1);
            let e2 = enc_put(e1, b.0, b.1);
            let e3 = enc_put(e2, c.0, c.1);
            &&& bool_bit(dst(data, e), a.0) == a.1 && bool_next(data, dst(data, e), a.0) == dst(data, e1)
            &&& bool_bit(dst(data, e1), b.0) == b.1 && bool_next(data, dst(data, e1), b.0) == dst(data, e2)
            &&& bool_bit(dst(data, e2), c.0) == c.1 && bool_next(data, dst(data, e2), c.0) == dst(data, e3)
            &&& e3 == enc_run(e, seq![a, b, c])
            &&& good(data, e3, rest)
        }),
{
    assert(seq![a, b, c] + rest =~= seq![a, b] + (seq![c] + rest));
    lemma_chain2(data, e, a, b, seq![c] + rest);
    let e2 = enc_run(e, seq![a, b]);
    lemma_bit(data, e2, c.0, c.1, rest);
    lemma_run_concat(e, seq![a, b], seq![c]);
    assert(seq![a, b] + seq![c] =~= seq![a, b, c]);
}

pub proof fn lemma_chain4(
    data: Seq<u8>,
    e: EncState,
    a: (int, bool),
    b: (int, bool),
    c: (int, bool),
    d: (int, bool),
    rest: Seq<(int, bool)>,
)
    requires
        good(data, e, seq![a, b, c, d] + rest),
    ensures
        ({
            let e1 = enc_put(e, a.0, a.1);
            let e2 = enc_put(e1, b.0, b.1);
            let e3 = enc_put(e2, c.0, c.1);
            let e4 = enc_put(e3, d.0, d.1);
            &&& bool_bit(dst(data, e), a.0) == a.1 && bool_next(data, dst(data, e), a.0) == dst(data, e1)
            &&& bool_bit(dst(data, e1), b.0) == b.1 && bool_next(data, dst(data, e1), b.0) == dst(data, e2)
            &&& bool_bit(dst(data, e2), c.0) == c.1 && bool_next(data, dst(data, e2), c.0) == dst(data, e3)
            &&& bool_bit(dst(data, e3), d.0) == d.1 && bool_next(data, dst(data, e3), d.0) == dst(data, e4)
            &&& e4 == enc_run(e, seq![a, b, c, d])
            &&& good(data, e4, rest)
        }),
{
    assert(seq![a, b, c, d] + rest =~= seq![a, b, c] + (seq![d] + rest));
    lemma_chain3(data, e, a, b, c, seq![d] + rest);
    let e3 = enc_run(e, seq![a, b, c]);
    lemma_bit(data, e3, d.0, d.1, rest);
    lemma_run_concat(e, seq![a, b, c], seq![d]);
    assert(seq![a, b, c] + seq![d] =~= seq![a, b, c, d]);
}

pub proof fn lemma_chain5(
    data: Seq<u8>,
    e: EncState,
    a: (int, bool),
    b: (int, bool),
    c: (int, bool),
    d: (int, bool),
    f: (int, bool),
    rest: Seq<(int, bool)>,
)
    requires
        good(data, e, seq![a, b, c, d, f] + rest),
    ensures
        ({
            let e1 = enc_put(e, a.0, a.1);
            let e2 = enc_put(e1, b.0, b.1);
            let e3 = enc_put(e2, c.0, c.1);
            let e4 = enc_put(e3, d.0, d.1);
            let e5 = enc_put(e4, f.0, f.1);
            &&& bool_bit(dst(data, e), a.0) == a.1 && bool_next(data, dst(data, e), a.0) == dst(data, e1)
            &&& bool_bit(dst(data, e1), b.0) == b.1 && bool_next(data, dst(data, e1), b.0) == dst(data, e2)
            &&& bool_bit(dst(data, e2), c.0) == c.1 && bool_next(data, dst(data, e2), c.0) == dst(data, e3)
            &&& bool_bit(dst(data, e3), d.0) == d.1 && bool_next(data, dst(data, e3), d.0) == dst(data, e4)
            &&& bool_bit(dst(data, e4), f.0) == f.1 && bool_next(data, dst(data, e4), f.0) == dst(data, e5)
            &&& e5 == enc_run(e, seq![a, b, c, d, f])
            &&& good(data, e5, rest)
        }),
{
    assert(seq![a, b, c, d, f] + rest =~= seq![a, b, c, d] + (seq![f] + rest));
    lemma_chain4(data, e, a, b, c, d, seq![f] + rest);
    let e4 = enc_run(e, seq![a, b, c, d]);
    lemma_bit(data, e4, f.0, f.1, rest);
    lemma_run_concat(e, seq![a, b, c, d], seq![f]);
    assert(seq![a, b, c, d] + seq![f] =~= seq![a, b, c, d, f]);
}

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------
pub open spec fn be(s: Seq<u8>) -> nat {
    be_bytes(s, 0, s.len())
}

proof fn lemma_be_frame(s1: Seq<u8>, s2: Seq<u8>, n: nat)
    requires
        n <= s1.len(),
        n <= s2.len(),
        forall|k: int| 0 <= k < n ==> s1[k] == s2[k],
    ensures
        be_bytes(s1, 0, n) == be_bytes(s2, 0, n),
    decreases n,
{
    if n > 0 {
        lemma_be_frame(s1, s2, (n - 1) as nat);
    }
}

/// Bytes from `i` to `n` all `c`, 0 or 255.
proof fn lemma_be_fill(s: Seq<u8>, i: nat, n: nat, c: u8)
    requires
        i <= n <= s.len(),
        c == 0 || c == 255,
        forall|k: int| i <= k < n ==> s[k] == c,
    ensures
        be_bytes(s, 0, n) == be_bytes(s, 0, i) * pow2((8 * (n - i)) as nat) + if c == 0 {
            0int
        } else {
            pow2((8 * (n - i)) as nat) - 1
        },
    decreases n,
{
    lemma2_to64();
    if n == i {
        assert(be_bytes(s, 0, i) * 1 == be_bytes(s, 0, i));
    } else {
        let n1 = (n - 1) as nat;
        lemma_be_fill(s, i, n1, c);
        let m = (8 * (n1 - i)) as nat;
        lemma_pow2_adds(m, 8);
        assert(m + 8 == 8 * (n - i));
        let p = pow2(m) as int;
        let x = be_bytes(s, 0, i) as int;
        assert(s[n1 as int] == c);
        if c == 0 {
            assert(256 * (x * p) == x * (p * 256)) by (nonlinear_arith);
        } else {
            assert(256 * (x * p + p - 1) + 255 == x * (p * 256) + p * 256 - 1) by (nonlinear_arith);
        }
    }
}

/// Adds one to the big-endian number the bytes spell.
fn carry(out: &mut Vec<u8>)
    requires
        be(old(out)@) + 1 < pow2((8 * old(out)@.len()) as nat),
    ensures
        final(out)@.len() == old(out)@.len(),
        be(final(out)@) == be(old(out)@) + 1,
{
    let ghost o = out@;
    let n = out.len();
    let mut i = n;
    while i > 0
        invariant
            n == out@.len(),
            n == o.len(),
            o == old(out)@,
            i <= n,
            be(o) + 1 < pow2((8 * o.len()) as nat),
            forall|k: int| 0 <= k < i ==> #[trigger] out@[k] == o[k],
            forall|k: int| i <= k < n ==> #[trigger] out@[k] == 0,
            forall|k: int| i <= k < n ==> #[trigger] o[k] == 255,
        decreases i,
    {
        let x = out[i - 1];
        if x != 255 {
            let ghost pre = out@;
            out.set(i - 1, x + 1);
            proof {
                assert forall|k: int| i <= k < n implies out@[k] == 0 by {
                    assert(out@[k] == pre[k]);
                    assert(pre[k] == 0 && o[k] == 255);
                }
                assert forall|k: int| 0 <= k < i - 1 implies out@[k] == o[k] by {
                    assert(out@[k] == pre[k]);
                }
                let ghost m = (8 * (n - i)) as nat;
                lemma_be_fill(out@, i as nat, n as nat, 0);
                lemma_be_fill(o, i as nat, n as nat, 255);
                lemma_be_frame(out@, o, (i - 1) as nat);
                assert(be_bytes(out@, 0, i as nat) == 256 * be_bytes(o, 0, (i - 1) as nat) + x + 1);
                assert(be_bytes(o, 0, i as nat) == 256 * be_bytes(o, 0, (i - 1) as nat) + x);
                let p = pow2(m) as int;
                let y = be_bytes(o, 0, i as nat) as int;
                assert((y + 1) * p == y * p + p - 1 + 1) by (nonlinear_arith);
            }
            return;
        }
        let ghost pre = out@;
        out.set(i - 1, 0);
        proof {
            assert(o[i - 1] == pre[i - 1]);
            assert forall|k: int| i - 1 <= k < n implies out@[k] == 0 && o[k] == 255 by {
                if k >= i {
                    assert(out@[k] == pre[k]);
                    assert(pre[k] == 0 && o[k] == 255);
                }
            }
            assert forall|k: int| 0 <= k < i - 1 implies out@[k] == o[k] by {
                assert(out@[k] == pre[k]);
                assert(pre[k] == o[k]);
            }
        }
        i = i - 1;
    }
    proof {
        lemma_be_fill(o, 0, n as nat, 255);
        assert(be_bytes(o, 0, 0) == 0);
        assert(0 * pow2((8 * n) as nat) == 0);
        assert(false);
    }
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------
/// The boolean encoder: finished bytes `out`, then `nacc` more bits of
/// `low` in `acc`. A carry out of `acc` goes into `out`.
pub struct BoolWriter {
    pub out: Vec<u8>,
    pub acc: u64,
    pub nacc: u32,
    pub range: u32,
    /// The writes so far.
    pub ws: Ghost<Seq<(int, bool)>>,
}

impl BoolWriter {
    pub open spec fn st(&self) -> EncState {
        EncState {
            low: be(self.out@) * pow2(self.nacc as nat) + self.acc,
            range: self.range as int,
            pos: (8 * self.out@.len() + self.nacc) as nat,
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& 128 <= self.range <= 255
        &&& 8 <= self.nacc <= 15
        &&& self.acc < pow2(self.nacc as nat)
        &&& probs_ok(self.ws@)
        &&& self.st() == enc_run(enc_init(), self.ws@)
        &&& self.out@.len() <= 0x1000_0000
    }

    pub fn new() -> (r: BoolWriter)
        ensures
            r.wf(),
            r.ws@ == Seq::<(int, bool)>::empty(),
    {
        let r = BoolWriter { out: Vec::new(), acc: 0, nacc: 8, range: 255, ws: Ghost(Seq::empty()) };
        proof {
            lemma2_to64();
            assert(be(r.out@) == 0);
        }
        r
    }

    /// The number of bytes so far.
    pub fn len(&self) -> (n: usize)
        requires
            self.wf(),
        ensures
            n <= 0x1000_0000,
            n == self.out@.len(),
    {
        self.out.len()
    }

    /// Writes `bit` at probability `prob` (of a zero, out of 256).
    #[verifier::spinoff_prover]
    pub fn put(&mut self, prob: u8, bit: bool)
        requires
            old(self).wf(),
            old(self).out@.len() < 0x1000_0000,
        ensures
            final(self).wf(),
            final(self).ws@ == old(self).ws@.push((prob as int, bit)),
    {
        let ghost e0 = self.st();
        let ghost ws1 = self.ws@.push((prob as int, bit));
        proof {
            lemma2_to64();
            lemma_split(self.range as int, prob as int);
            lemma_run_wf(enc_init(), self.ws@);
            assert(ws1.drop_last() =~= self.ws@);
            assert(probs_ok(ws1)) by {
                assert forall|k: int| 0 <= k < ws1.len() implies 0 <= (#[trigger] ws1[k]).0 <= 255 by {
                    if k < self.ws@.len() {
                        assert(ws1[k] == self.ws@[k]);
                    }
                }
            }
        }
        let x = (self.range - 1) * (prob as u32);
        proof {
            assert(x <= 255 * 255) by (nonlinear_arith)
                requires
                    x == (self.range - 1) * (prob as u32),
                    self.range <= 255,
            ;
            assert(x >> 8u32 == x / 256) by (bit_vector);
        }
        let split = 1 + (x >> 8u32);
        let ghost t = enc_take(e0, prob as int, bit);
        if bit {
            self.range = self.range - split;
            self.acc = self.acc + split as u64;
            proof {
                lemma_u64_shl_is_mul(1, self.nacc as u64);
                lemma_pow2_strictly_increases(self.nacc as nat, 16);
            }
            let top = 1u64 << self.nacc;
            if self.acc >= top {
                self.acc = self.acc - top;
                proof {
                    let ghost b0 = be(self.out@) as int;
                    let ghost q = pow2(self.nacc as nat) as int;
                    let ghost m = pow2((8 * self.out@.len()) as nat) as int;
                    lemma_pow2_adds((8 * self.out@.len()) as nat, self.nacc as nat);
                    // The new low stays below 2^pos.
                    assert(t.low + t.range <= m * q);
                    assert(t.low == (b0 + 1) * q + self.acc) by (nonlinear_arith)
                        requires
                            t.low == b0 * q + self.acc + q,
                    ;
                    assert(b0 + 1 < m) by (nonlinear_arith)
                        requires
                            (b0 + 1) * q + self.acc + t.range <= m * q,
                            self.acc >= 0,
                            t.range >= 1,
                            q >= 1,
                    ;
                }
                let ghost b0 = be(self.out@) as int;
                carry(&mut self.out);
                proof {
                    let ghost q = pow2(self.nacc as nat) as int;
                    assert((b0 + 1) * q == b0 * q + q) by (nonlinear_arith);
                }
            }
        } else {
            self.range = split;
        }
        proof {
            assert(self.st() == t);
        }
        let ghost n0 = self.nacc;
        while self.range < 128
            invariant
                1 <= self.range <= 255,
                n0 <= self.nacc,
                self.range >= pow2((self.nacc - n0) as nat),
                8 <= n0 <= 15,
                self.acc < pow2(self.nacc as nat),
                enc_norm(self.st()) == enc_norm(t),
                self.out@.len() <= 0x1000_0000,
            decreases 256 - self.range,
        {
            proof {
                lemma2_to64();
                if self.nacc - n0 > 7 {
                    lemma_pow2_strictly_increases(7, (self.nacc - n0) as nat);
                }
                assert(self.nacc <= 21);
                assert(self.acc < pow2(23));
                lemma_pow2_unfold((self.nacc + 1) as nat);
                lemma_pow2_unfold((self.nacc + 1 - n0) as nat);
                lemma_pow2_strictly_increases(self.nacc as nat, 23);
                lemma_u64_shl_is_mul(self.acc, 1);
            }
            let ghost s0 = self.st();
            self.range = self.range << 1u32;
            self.acc = self.acc << 1u64;
            self.nacc = self.nacc + 1;
            proof {
                assert(self.range == 2 * s0.range) by {
                    let r = s0.range as u32;
                    assert(r < 128 ==> (r << 1u32) == 2 * r) by (bit_vector);
                }
                let ghost b0 = be(self.out@) as int;
                let ghost q = pow2((self.nacc - 1) as nat) as int;
                assert(b0 * (2 * q) == 2 * (b0 * q)) by (nonlinear_arith);
                assert(self.st() == EncState { low: 2 * s0.low, range: 2 * s0.range, pos: s0.pos + 1 });
            }
        }
        proof {
            assert(enc_norm(t) == enc_put(e0, prob as int, bit));
            assert(enc_run(enc_init(), ws1) == enc_put(e0, prob as int, bit));
            assert(self.nacc <= 22) by {
                lemma2_to64();
                if self.nacc - n0 > 8 {
                    lemma_pow2_strictly_increases(8, (self.nacc - n0) as nat);
                }
            }
        }
        if self.nacc >= 16 {
            let sh = self.nacc - 8;
            proof {
                lemma_u64_shr_is_div(self.acc, sh as u64);
                lemma_pow2_adds(sh as nat, 8);
                assert(self.acc as nat / pow2(sh as nat) < 256) by {
                    let q = pow2(sh as nat) as int;
                    lemma_pow2_pos(sh as nat);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self.acc as int, q);
                    vstd::arithmetic::div_mod::lemma_mod_pos_bound(self.acc as int, q);
                    let d = self.acc as int / q;
                    assert(d < 256) by (nonlinear_arith)
                        requires
                            self.acc as int == q * d + (self.acc as int % q),
                            0 <= self.acc as int % q,
                            (self.acc as int) < q * 256,
                            q >= 1,
                    ;
                }
            }
            let byte = (self.acc >> (sh as u64)) as u8;
            proof {
                lemma_pow2_strictly_increases(sh as nat, 16);
                assert((byte as u64) * pow2(sh as nat) <= self.acc) by {
                    let q = pow2(sh as nat) as int;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self.acc as int, q);
                    lemma_pow2_pos(sh as nat);
                    vstd::arithmetic::div_mod::lemma_mod_pos_bound(self.acc as int, q);
                    let d = self.acc as int / q;
                    assert(byte as int == d);
                    assert(d * q <= self.acc as int) by (nonlinear_arith)
                        requires
                            self.acc as int == q * d + (self.acc as int % q),
                            0 <= self.acc as int % q,
                    ;
                }
                lemma_u64_shl_is_mul(byte as u64, sh as u64);
            }
            let ghost o = self.out@;
            let ghost a0 = self.acc;
            self.acc = self.acc - ((byte as u64) << (sh as u64));
            self.out.push(byte);
            self.nacc = sh;
            proof {
                let q = pow2(sh as nat) as int;
                lemma_pow2_pos(sh as nat);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a0 as int, q);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(a0 as int, q);
                lemma_be_frame(self.out@, o, o.len());
                assert(be(self.out@) == 256 * be(o) + byte);
                let b0 = be(o) as int;
                assert(b0 * (q * 256) + byte * q + self.acc == (256 * b0 + byte) * q + self.acc) by (nonlinear_arith);
                assert(8 * self.out@.len() + sh == 8 * o.len() + sh + 8);
                assert(self.acc == a0 as int % q) by (nonlinear_arith)
                    requires
                        self.acc == a0 - byte * q,
                        byte as int == a0 as int / q,
                        a0 as int == q * (a0 as int / q) + (a0 as int % q),
                ;
                assert(self.acc < pow2(self.nacc as nat));
            }
        }
        proof {
            self.ws = Ghost(ws1);
            assert(128 <= self.range <= 255);
            assert(8 <= self.nacc <= 15);
            assert(self.acc < pow2(self.nacc as nat));
            assert(probs_ok(self.ws@));
            assert(self.st() == enc_run(enc_init(), self.ws@));
            assert(self.out@.len() <= 0x1000_0000);
        }
    }

    /// The partition: what is written so far, padded to whole bytes.
    pub fn finish(self) -> (r: Vec<u8>)
        requires
            self.wf(),
        ensures
            covers(r@, enc_run(enc_init(), self.ws@)),
            r@.len() == self.out@.len() + 2,
    {
        let ghost e = self.st();
        let z = 16 - self.nacc;
        proof {
            lemma2_to64();
            lemma_pow2_adds(self.nacc as nat, z as nat);
            lemma_pow2_strictly_increases(16, 32);
            lemma_pow2_pos(z as nat);
            assert(self.acc * pow2(z as nat) < pow2(16)) by (nonlinear_arith)
                requires
                    self.acc < pow2(self.nacc as nat),
                    pow2(self.nacc as nat) * pow2(z as nat) == pow2(16),
                    pow2(z as nat) > 0,
            ;
            lemma_u64_shl_is_mul(self.acc, z as u64);
        }
        let a2 = self.acc << (z as u64);
        proof {
            assert(a2 < 65536);
            assert(a2 < 65536 ==> (a2 >> 8u64) < 256 && (a2 & 0xff) < 256 && a2 == 256 * (a2 >> 8u64) + (a2 & 0xff))
                by (bit_vector);
        }
        let b1 = (a2 >> 8u64) as u8;
        let b2 = (a2 & 0xff) as u8;
        let mut out = self.out;
        let ghost o = out@;
        out.push(b1);
        out.push(b2);
        proof {
            let d = out@;
            let n = o.len();
            lemma_be_frame(d, o, n);
            assert(be_bytes(d, 0, (n + 1) as nat) == 256 * be(o) + b1);
            assert(be_bytes(d, 0, (n + 2) as nat) == 256 * (256 * be(o) + b1) + b2);
            lemma_bytes(d, 0, (n + 2) as nat);
            assert(8 * (n + 2) == e.pos + z);
            lemma_bits_split(d, 0, e.pos, z as nat);
            lemma_bits_bound(d, e.pos, z as nat);
            let q = pow2(z as nat) as int;
            lemma_pow2_pos(z as nat);
            let bo = be(o) as int;
            let p = pow2(self.nacc as nat) as int;
            assert(256 * (256 * bo + b1) + b2 == bo * 65536 + a2);
            assert(bo * 65536 + a2 == (bo * p + self.acc) * q) by (nonlinear_arith)
                requires
                    p * q == 65536,
                    a2 == self.acc * q,
            ;
            let sb = stream_bits(d, 0, e.pos) as int;
            let r = stream_bits(d, e.pos, z as nat) as int;
            assert(sb == e.low) by (nonlinear_arith)
                requires
                    sb * q + r == e.low * q,
                    0 <= r < q,
            ;
        }
        out
    }
}

} // verus!
