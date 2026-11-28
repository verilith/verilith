//! The lossy encoder's bit writers: each appends exactly the writes its
//! specification twin (`fh_ws`, `mbm_ws`, `tok_ws`, `mb_res`) names, so the
//! read-back lemmas apply to the bytes it produces.
use crate::enc_bool::*;
#[cfg(verus_only)]
use crate::enc_vp8hdr::*;
#[cfg(verus_only)]
use crate::enc_vp8modes::*;
#[cfg(verus_only)]
use crate::enc_vp8res::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
use crate::vp8tables::*;
#[cfg(verus_only)]
use crate::vp8spec::*;
use crate::enc_vp8res::EncRes;
use crate::vp8spec::FrameHeader;
use vstd::prelude::*;

verus! {

/// A bool writer that stops writing once its output would grow past what
/// `BoolWriter` holds, and remembers that it did (`ok` false). While `ok`,
/// it has written `want`.
pub struct EncW {
    pub bw: BoolWriter,
    pub ok: bool,
    pub want: Ghost<Seq<(int, bool)>>,
}

impl EncW {
    pub open spec fn inv(&self) -> bool {
        &&& self.bw.wf()
        &&& self.ok ==> self.bw.ws@ == self.want@
    }

    pub fn new() -> (r: EncW)
        ensures
            r.inv(),
            r.want@ == Seq::<(int, bool)>::empty(),
    {
        EncW { bw: BoolWriter::new(), ok: true, want: Ghost(Seq::empty()) }
    }

    pub fn put(&mut self, prob: u8, bit: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).want@ == old(self).want@.push((prob as int, bit)),
    {
        let ghost w1 = self.want@.push((prob as int, bit));
        if self.ok && self.bw.len() < 0x0fff_ffff {
            self.bw.put(prob, bit);
        } else {
            self.ok = false;
        }
        self.want = Ghost(w1);
    }
}

/// The probabilities as the specification holds them.
pub open spec fn pr(probs: Seq<u8>) -> Seq<int> {
    Seq::new(probs.len(), |i: int| probs[i] as int)
}

pub fn put_lit(w: &mut EncW, v: u32, n: u32)
    requires
        old(w).inv(),
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + lit_ws(v as nat, n as nat),
    decreases n,
{
    if n > 0 {
        put_lit(w, v / 2, n - 1);
        w.put(128, v % 2 == 1);
        proof {
            assert(old(w).want@ + lit_ws(v as nat, n as nat) =~= (old(w).want@ + lit_ws((v / 2) as nat, (n - 1) as nat)).push(
                (128int, v % 2 == 1),
            ));
        }
    } else {
        proof {
            assert(old(w).want@ + lit_ws(v as nat, 0) =~= old(w).want@);
        }
    }
}

pub fn put_ext(w: &mut EncW, tab: &[u8], v: u32, n: usize)
    requires
        old(w).inv(),
        n <= tab@.len(),
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + ext_ws(tab@, v as nat, n as nat),
    decreases n,
{
    if n > 0 {
        put_ext(w, tab, v / 2, n - 1);
        w.put(tab[n - 1], v % 2 == 1);
        proof {
            assert(old(w).want@ + ext_ws(tab@, v as nat, n as nat) =~= (old(w).want@ + ext_ws(
                tab@,
                (v / 2) as nat,
                (n - 1) as nat,
            )).push((tab@[n - 1] as int, v % 2 == 1)));
        }
    } else {
        proof {
            assert(old(w).want@ + ext_ws(tab@, v as nat, 0) =~= old(w).want@);
        }
    }
}

/// The token probability updates.
pub fn put_tp(w: &mut EncW, probs: &[u8])
    requires
        old(w).inv(),
        probs@.len() == 1056,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + tp_ws(pr(probs@), 1056),
{
    let ghost w0 = w.want@;
    let mut k: usize = 0;
    while k < 1056
        invariant
            k <= 1056,
            probs@.len() == 1056,
            w.inv(),
            w.want@ == w0 + tp_ws(pr(probs@), k as nat),
        decreases 1056 - k,
    {
        let ghost a = w.want@;
        let up = coeffs_update_proba(k);
        let pk = probs[k];
        if pk == coeffs_proba0(k) {
            w.put(up, false);
            proof {
                assert(w0 + tp_ws(pr(probs@), (k + 1) as nat) =~= a.push((up as int, false)));
            }
        } else {
            w.put(up, true);
            let ghost b = w.want@;
            put_lit(w, pk as u32, 8);
            proof {
                assert(pr(probs@)[k as int] == pk as int);
                assert(w0 + tp_ws(pr(probs@), (k + 1) as nat) =~= b + lit_ws(pk as nat, 8));
            }
        }
        k = k + 1;
    }
}

pub open spec fn hparams(level: u32, q: u32, probs: Seq<u8>, skip: bool, pskip: u32) -> HdrParams {
    HdrParams { level: level as nat, q: q as nat, probs: pr(probs), skip, pskip: pskip as nat }
}

fn put_fha(w: &mut EncW, level: u32, q: u32, probs: &[u8], skip: bool, pskip: u32)
    requires
        old(w).inv(),
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + fh_a_ws(hparams(level, q, probs@, skip, pskip)),
{
    hide(lit_ws);
    let ghost w0 = w.want@;
    w.put(128, false);
    w.put(128, false);
    w.put(128, false);
    w.put(128, false);
    put_lit(w, level, 6);
    put_lit(w, 0, 3);
    w.put(128, false);
    proof {
        assert(w.want@ =~= w0 + fh_a_ws(hparams(level, q, probs@, skip, pskip)));
    }
}

fn put_fhb(w: &mut EncW, level: u32, q: u32, probs: &[u8], skip: bool, pskip: u32)
    requires
        old(w).inv(),
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + fh_b_ws(hparams(level, q, probs@, skip, pskip)),
{
    hide(lit_ws);
    let ghost w0 = w.want@;
    put_lit(w, 0, 2);
    put_lit(w, q, 7);
    w.put(128, false);
    w.put(128, false);
    w.put(128, false);
    w.put(128, false);
    w.put(128, false);
    proof {
        assert(w.want@ =~= w0 + fh_b_ws(hparams(level, q, probs@, skip, pskip)));
    }
}

fn put_fhc(w: &mut EncW, level: u32, q: u32, probs: &[u8], skip: bool, pskip: u32)
    requires
        old(w).inv(),
        probs@.len() == 1056,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + fh_c_ws(hparams(level, q, probs@, skip, pskip)),
{
    hide(lit_ws);
    hide(tp_ws);
    let ghost w0 = w.want@;
    w.put(128, false);
    put_tp(w, probs);
    w.put(128, skip);
    let ghost c = w.want@;
    if skip {
        put_lit(w, pskip, 8);
    } else {
        proof {
            assert(c + Seq::<(int, bool)>::empty() =~= c);
        }
    }
    proof {
        assert(w.want@ =~= w0 + fh_c_ws(hparams(level, q, probs@, skip, pskip)));
    }
}

/// The frame header after the frame tag (`fh_ws`).
pub fn put_hdr(w: &mut EncW, level: u32, q: u32, probs: &[u8], skip: bool, pskip: u32)
    requires
        old(w).inv(),
        probs@.len() == 1056,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + fh_ws(hparams(level, q, probs@, skip, pskip)),
{
    hide(fh_a_ws);
    hide(fh_b_ws);
    hide(fh_c_ws);
    let ghost w0 = w.want@;
    put_fha(w, level, q, probs, skip, pskip);
    put_fhb(w, level, q, probs, skip, pskip);
    put_fhc(w, level, q, probs, skip, pskip);
    proof {
        assert(w.want@ =~= w0 + fh_ws(hparams(level, q, probs@, skip, pskip)));
    }
}

pub open spec fn mbspec(skip: bool, ymode: u8, uvmode: u8) -> MbModeSpec {
    MbModeSpec { segment: 0, skip, is_i4x4: false, ymode: ymode as int, bmodes: Seq::empty(), uvmode: uvmode as int }
}

/// A macroblock's modes (`mbm_ws`).
pub fn put_mbm(w: &mut EncW, skip_on: bool, pskip: u8, skip: bool, ymode: u8, uvmode: u8, Ghost(fh): Ghost<FrameHeader>)
    requires
        old(w).inv(),
        fh.mb_no_coeff_skip == skip_on,
        fh.prob_skip_false == pskip as int,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + mbm_ws(fh, mbspec(skip, ymode, uvmode)),
{
    let ghost w0 = w.want@;
    if skip_on {
        w.put(pskip, skip);
    }
    let ghost a = w.want@;
    w.put(145, true);
    let ghost b = w.want@;
    if ymode == 0 {
        w.put(156, false);
        w.put(163, false);
    } else if ymode == 2 {
        w.put(156, false);
        w.put(163, true);
    } else if ymode == 1 {
        w.put(156, true);
        w.put(128, true);
    } else {
        w.put(156, true);
        w.put(128, false);
    }
    let ghost c = w.want@;
    if uvmode == 0 {
        w.put(142, false);
    } else if uvmode == 2 {
        w.put(142, true);
        w.put(114, false);
    } else if uvmode == 1 {
        w.put(142, true);
        w.put(114, true);
        w.put(183, true);
    } else {
        w.put(142, true);
        w.put(114, true);
        w.put(183, false);
    }
    proof {
        let m = mbspec(skip, ymode, uvmode);
        assert(c =~= b + ymode_ws(m.ymode));
        assert(w.want@ =~= c + uv_ws(m.uvmode));
        assert(w.want@ =~= w0 + mbm_ws(fh, m));
    }
}

/// The levels of block `b` of a macroblock's 400 (25 blocks of 16).
pub open spec fn blk_lv(lv: Seq<i16>, b: int) -> Seq<int> {
    Seq::new(16, |i: int| lv[16 * b + i] as int)
}

pub open spec fn mb_lvs(lv: Seq<i16>) -> Seq<Seq<int>> {
    Seq::new(25, |b: int| blk_lv(lv, b))
}

pub open spec fn lv_in(lv: Seq<i16>) -> bool {
    &&& lv.len() == 400
    &&& forall|i: int| 0 <= i < 400 ==> -2047 <= #[trigger] lv[i] <= 2047
}

pub proof fn lemma_mb_lvs(lv: Seq<i16>)
    requires
        lv_in(lv),
    ensures
        lvs_ok(mb_lvs(lv)),
{
    assert forall|b: int| 0 <= b < 25 implies lv_ok(#[trigger] mb_lvs(lv)[b]) by {
        assert forall|k: int| 0 <= k < 16 implies -2114 <= #[trigger] mb_lvs(lv)[b][k] <= 2114 by {
            assert(mb_lvs(lv)[b][k] == lv[16 * b + k] as int);
        }
    }
}

fn token_pidx_x(t: usize, n: usize, ctx: usize) -> (r: usize)
    requires
        t < 4,
        n <= 16,
        ctx < 3,
    ensures
        r == token_pidx(t as int, n as int, ctx as int),
        r + 10 < 1056,
{
    proof {
        assert(BANDS@[n as int] == coeff_band(n as int));
    }
    let b = BANDS[n] as usize;
    ((t * 8 + b) * 3 + ctx) * 11
}

fn put_head(w: &mut EncW, probs: &[u8], p: usize, v: u32)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        p + 10 < 1056,
        2 <= v,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + large_head(pr(probs@), p as int, v as int),
{
    let ghost w0 = w.want@;
    let ghost pp = pr(probs@);
    proof {
        assert forall|i: int| 0 <= i < 1056 implies #[trigger] pp[i] == probs@[i] as int by {}
    }
    if v == 2 {
        w.put(probs[p + 3], false);
        w.put(probs[p + 4], false);
    } else if v <= 4 {
        w.put(probs[p + 3], false);
        w.put(probs[p + 4], true);
        w.put(probs[p + 5], v == 4);
    } else if v <= 6 {
        w.put(probs[p + 3], true);
        w.put(probs[p + 6], false);
        w.put(probs[p + 7], false);
        w.put(159, v == 6);
    } else if v <= 10 {
        w.put(probs[p + 3], true);
        w.put(probs[p + 6], false);
        w.put(probs[p + 7], true);
        w.put(165, v - 7 >= 2);
        w.put(145, (v - 7) % 2 == 1);
    } else {
        w.put(probs[p + 3], true);
        w.put(probs[p + 6], true);
        if v <= 18 {
            w.put(probs[p + 8], false);
            w.put(probs[p + 9], false);
        } else if v <= 34 {
            w.put(probs[p + 8], false);
            w.put(probs[p + 9], true);
        } else if v <= 66 {
            w.put(probs[p + 8], true);
            w.put(probs[p + 10], false);
        } else {
            w.put(probs[p + 8], true);
            w.put(probs[p + 10], true);
        }
    }
    proof {
        assert(w.want@ =~= w0 + large_head(pp, p as int, v as int));
    }
}

fn put_tail(w: &mut EncW, v: u32)
    requires
        old(w).inv(),
        2 <= v <= 2114,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + large_tail(v as int),
{
    hide(ext_ws);
    let ghost w0 = w.want@;
    if v <= 10 {
        proof {
            assert(w0 + Seq::<(int, bool)>::empty() =~= w0);
        }
    } else if v <= 18 {
        put_ext(w, &CAT3, v - 11, 3);
        proof {
            assert(CAT3@ =~= pcat3());
        }
    } else if v <= 34 {
        put_ext(w, &CAT4, v - 19, 4);
        proof {
            assert(CAT4@ =~= pcat4());
        }
    } else if v <= 66 {
        put_ext(w, &CAT5, v - 35, 5);
        proof {
            assert(CAT5@ =~= pcat5());
        }
    } else {
        put_ext(w, &CAT6, v - 67, 11);
        proof {
            assert(CAT6@ =~= pcat6());
        }
    }
}

/// The tree path and extra bits of a magnitude from 2.
fn put_large(w: &mut EncW, probs: &[u8], p: usize, v: u32)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        p + 10 < 1056,
        2 <= v <= 2114,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + large_ws(pr(probs@), p as int, v as int),
{
    hide(large_head);
    hide(large_tail);
    let ghost w0 = w.want@;
    put_head(w, probs, p, v);
    put_tail(w, v);
    proof {
        assert(w.want@ =~= w0 + large_ws(pr(probs@), p as int, v as int));
    }
}

/// One token that is not `dct_eob` (`step_ws`).
fn put_step(w: &mut EncW, probs: &[u8], t: usize, n: usize, ctx: usize, ce: bool, v: i16, Ghost(lv): Ghost<Seq<int>>)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        t < 4,
        n < 16,
        ctx < 3,
        lv.len() == 16,
        lv[n as int] == v as int,
        -2047 <= v <= 2047,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + step_ws(pr(probs@), t as int, n as int, ctx as int, ce, lv),
{
    let ghost w0 = w.want@;
    let ghost pp = pr(probs@);
    let p = token_pidx_x(t, n, ctx);
    if ce {
        w.put(probs[p], true);
    }
    let ghost a = w.want@;
    if v == 0 {
        w.put(probs[p + 1], false);
        proof {
            assert(w.want@ =~= w0 + step_ws(pp, t as int, n as int, ctx as int, ce, lv));
        }
    } else {
        w.put(probs[p + 1], true);
        let ghost b = w.want@;
        let a16: u32 = if v < 0 {
            (-(v as i32)) as u32
        } else {
            v as u32
        };
        if a16 == 1 {
            w.put(probs[p + 2], false);
        } else {
            w.put(probs[p + 2], true);
            put_large(w, probs, p, a16);
        }
        let ghost c = w.want@;
        w.put(128, v < 0);
        proof {
            assert(a16 as int == iabs(v as int));
            assert(w.want@ =~= w0 + step_ws(pp, t as int, n as int, ctx as int, ce, lv));
        }
    }
}

proof fn lemma_tok_unfold(pp: Seq<int>, t: int, n: int, c: int, ce: bool, l: Seq<int>)
    requires
        0 <= n < 16,
    ensures
        ce && rest_zero(l, n) ==> tok_ws(pp, t, n, c, ce, l) == seq![(pp[token_pidx(t, n, c)], false)],
        ce && rest_zero(l, n) ==> tok_end(l, n, ce) == n,
        !(ce && rest_zero(l, n)) ==> tok_ws(pp, t, n, c, ce, l) == step_ws(pp, t, n, c, ce, l) + tok_ws(
            pp,
            t,
            n + 1,
            nctx(l[n]),
            l[n] != 0,
            l,
        ),
        !(ce && rest_zero(l, n)) ==> tok_end(l, n, ce) == tok_end(l, n + 1, l[n] != 0),
{
}

/// The tokens of block `b` of a macroblock's levels, from position
/// `first`, with context `ctx` (`tok_ws`). Returns where they end.
pub fn put_block(w: &mut EncW, probs: &[u8], t: usize, first: usize, ctx: usize, lv: &[i16], b: usize) -> (end: usize)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        t < 4,
        first <= 1,
        ctx < 3,
        lv_in(lv@),
        b < 25,
    ensures
        final(w).inv(),
        final(w).want@ == old(w).want@ + tok_ws(pr(probs@), t as int, first as int, ctx as int, true, blk_lv(lv@, b as int)),
        end as int == tok_end(blk_lv(lv@, b as int), first as int, true),
{
    hide(tok_ws);
    hide(tok_end);
    hide(step_ws);
    let ghost l = blk_lv(lv@, b as int);
    let ghost pp = pr(probs@);
    let ghost w0 = w.want@;
    let at = 16 * b;
    let mut last: usize = 16;
    while last > first && lv[at + last - 1] == 0
        invariant
            first <= last <= 16,
            at == 16 * b,
            b < 25,
            lv@.len() == 400,
            l == blk_lv(lv@, b as int),
            forall|k: int| last <= k < 16 ==> #[trigger] l[k] == 0,
        decreases last,
    {
        proof {
            assert(l[last - 1] == lv@[at + last - 1] as int);
        }
        last = last - 1;
    }
    proof {
        if last > first {
            assert(l[last - 1] == lv@[at + last - 1] as int);
        }
    }
    let mut n: usize = first;
    let mut c: usize = ctx;
    let mut ce: bool = true;
    while n < 16
        invariant
            first <= n <= 16,
            first <= last <= 16,
            c < 3,
            l == blk_lv(lv@, b as int),
            pp == pr(probs@),
            w0 == old(w).want@,
            at == 16 * b,
            b < 25,
            t < 4,
            probs@.len() == 1056,
            lv_in(lv@),
            w.inv(),
            forall|k: int| last <= k < 16 ==> #[trigger] l[k] == 0,
            last > first ==> l[last - 1] != 0,
            !ce ==> n < last,
            w0 + tok_ws(pp, t as int, first as int, ctx as int, true, l) == w.want@ + tok_ws(pp, t as int, n as int, c as int, ce, l),
            tok_end(l, first as int, true) == tok_end(l, n as int, ce),
        decreases 16 - n,
    {
        let ghost a = w.want@;
        if ce && n >= last {
            let p = token_pidx_x(t, n, c);
            w.put(probs[p], false);
            proof {
                assert(pp[p as int] == probs@[p as int] as int);
                assert(rest_zero(l, n as int));
                lemma_tok_unfold(pp, t as int, n as int, c as int, ce, l);
                assert(w0 + tok_ws(pp, t as int, first as int, ctx as int, true, l) =~= w.want@);
                assert(w.want@ == w0 + tok_ws(pp, t as int, first as int, ctx as int, true, l));
                assert(tok_end(l, first as int, true) == n);
                assert(w.inv());
            }
            return n;
        }
        let v = lv[at + n];
        proof {
            assert(l[n as int] == v as int);
            assert(!(ce && rest_zero(l, n as int))) by {
                if ce {
                    assert(l[last - 1] != 0);
                }
            }
        }
        put_step(w, probs, t, n, c, ce, v, Ghost(l));
        proof {
            lemma_tok_unfold(pp, t as int, n as int, c as int, ce, l);
            assert(a + tok_ws(pp, t as int, n as int, c as int, ce, l) =~= w.want@ + tok_ws(
                pp,
                t as int,
                n + 1,
                nctx(v as int),
                v != 0,
                l,
            ));
        }
        c = if v == 0 {
            0
        } else if v == 1 || v == -1 {
            1
        } else {
            2
        };
        proof {
            assert(c as int == nctx(v as int));
        }
        ce = v != 0;
        n = n + 1;
    }
    proof {
        reveal(tok_ws);
        reveal(tok_end);
        assert(w.want@ + tok_ws(pp, t as int, 16, c as int, ce, l) =~= w.want@);
    }
    16
}

pub proof fn lemma_pb_ok(
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
    ensures
        res_ok(pb(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, n).0),
    decreases n,
{
    if n > 0 {
        lemma_pb_ok(probs, c, lvs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
    }
}

/// The first `n` blocks of a plane (`pb`), with the context flags in
/// `top` and `left`.
fn put_plane(
    w: &mut EncW,
    probs: &[u8],
    lv: &[i16],
    t: usize,
    first: usize,
    base: usize,
    off: usize,
    wd: usize,
    n: usize,
    top: &mut Vec<bool>,
    left: &mut Vec<bool>,
    Ghost(c0): Ghost<EncRes>,
    Ghost(dq_dc): Ghost<int>,
    Ghost(dq_ac): Ghost<int>,
)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        lv_in(lv@),
        res_ok(c0),
        old(top)@ == c0.top,
        old(left)@ == c0.left,
        plane_ok(t as int, first as int, base as int, off as int, wd as int, n as nat),
    ensures
        ({
            let r = pb(pr(probs@), c0, mb_lvs(lv@), t as int, first as int, dq_dc, dq_ac, base as int, off as int, wd as int, n as nat);
            &&& final(w).inv()
            &&& final(w).want@ == old(w).want@ + r.1
            &&& final(top)@ == r.0.top
            &&& final(left)@ == r.0.left
        }),
{
    hide(tok_ws);
    hide(tok_end);
    let ghost pp = pr(probs@);
    let ghost lvs = mb_lvs(lv@);
    let ghost w0 = w.want@;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            w.inv(),
            probs@.len() == 1056,
            lv_in(lv@),
            res_ok(c0),
            pp == pr(probs@),
            lvs == mb_lvs(lv@),
            plane_ok(t as int, first as int, base as int, off as int, wd as int, n as nat),
            ({
                let r = pb(pp, c0, lvs, t as int, first as int, dq_dc, dq_ac, base as int, off as int, wd as int, k as nat);
                &&& w.want@ == w0 + r.1
                &&& top@ == r.0.top
                &&& left@ == r.0.left
            }),
        decreases n - k,
    {
        let ghost r = pb(pp, c0, lvs, t as int, first as int, dq_dc, dq_ac, base as int, off as int, wd as int, k as nat);
        proof {
            lemma_pb_ok(pp, c0, lvs, t as int, first as int, dq_dc, dq_ac, base as int, off as int, wd as int, k as nat);
            assert(k / wd < wd && k % wd < wd) by {
                assert(k < wd * wd);
            }
        }
        let y = off + k / wd;
        let x = off + k % wd;
        let ctx = (if left[y] { 1usize } else { 0 }) + (if top[x] { 1usize } else { 0 });
        let ghost a = w.want@;
        let end = put_block(w, probs, t, first, ctx, lv, base + k);
        let f = end > first;
        top.set(x, f);
        left.set(y, f);
        proof {
            assert(lvs[base + k] == blk_lv(lv@, (base + k) as int));
            assert(ctx as int == pb_ctx(r.0, off as int, wd as int, k as int));
            let r1 = pb(pp, c0, lvs, t as int, first as int, dq_dc, dq_ac, base as int, off as int, wd as int, (k + 1) as nat);
            assert(r1.1 == r.1 + tok_ws(pp, t as int, first as int, ctx as int, true, lvs[base + k]));
            assert(w.want@ =~= w0 + r1.1);
            assert(top@ =~= r1.0.top);
            assert(left@ =~= r1.0.left);
        }
        k = k + 1;
    }
}

/// The macroblock's residual tokens (`mb_res`, not `B_PRED`), with the
/// context flags above and to the left in `top` and `left`.
pub fn put_mb(w: &mut EncW, probs: &[u8], lv: &[i16], top: &mut Vec<bool>, left: &mut Vec<bool>, Ghost(q): Ghost<(int, int, int, int, int, int)>)
    requires
        old(w).inv(),
        probs@.len() == 1056,
        lv_in(lv@),
        old(top)@.len() == 9,
        old(left)@.len() == 9,
    ensures
        ({
            let r = mb_res(pr(probs@), q, false, old(top)@, old(left)@, mb_lvs(lv@));
            &&& final(w).inv()
            &&& final(w).want@ == old(w).want@ + r.1
            &&& final(top)@ == r.0.top
            &&& final(left)@ == r.0.left
            &&& final(top)@.len() == 9
            &&& final(left)@.len() == 9
        }),
{
    hide(tok_ws);
    hide(tok_end);
    hide(pb);
    let ghost pp = pr(probs@);
    let ghost lvs = mb_lvs(lv@);
    let ghost w0 = w.want@;
    let ghost c0 = EncRes { coeffs: Seq::new(384, |i: int| 0int), top: top@, left: left@ };
    let ctx = (if left[8] { 1usize } else { 0 }) + (if top[8] { 1usize } else { 0 });
    let end = put_block(w, probs, 1, 0, ctx, lv, 24);
    let f = end > 0;
    top.set(8, f);
    left.set(8, f);
    let ghost r1 = y2(pp, c0, lvs[24], q.2, q.3);
    proof {
        assert(lvs[24] == blk_lv(lv@, 24));
        assert(w.want@ == w0 + r1.1);
        assert(top@ =~= r1.0.top);
        assert(left@ =~= r1.0.left);
    }
    let ghost wa = w.want@;
    put_plane(w, probs, lv, 0, 1, 0, 0, 4, 16, top, left, Ghost(r1.0), Ghost(q.0), Ghost(q.1));
    let ghost ry = pb(pp, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    let ghost wb = w.want@;
    proof {
        lemma_pb_ok(pp, r1.0, lvs, 0, 1, q.0, q.1, 0, 0, 4, 16);
    }
    put_plane(w, probs, lv, 2, 0, 16, 4, 2, 4, top, left, Ghost(ry.0), Ghost(q.4), Ghost(q.5));
    let ghost ru = pb(pp, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    let ghost wc = w.want@;
    proof {
        lemma_pb_ok(pp, ry.0, lvs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    }
    put_plane(w, probs, lv, 2, 0, 20, 6, 2, 4, top, left, Ghost(ru.0), Ghost(q.4), Ghost(q.5));
    let ghost rv = pb(pp, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
    proof {
        lemma_pb_ok(pp, ru.0, lvs, 2, 0, q.4, q.5, 20, 6, 2, 4);
        let r = mb_res(pp, q, false, c0.top, c0.left, lvs);
        assert(r.0 == rv.0);
        assert(r.1 == r1.1 + (ry.1 + (ru.1 + rv.1)));
        assert(w.want@ =~= w0 + r.1);
    }
}

} // verus!
