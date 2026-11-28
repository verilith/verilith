//! Proofs for the general meta-block writer (`mbw`): numbers in the
//! `NBLTYPES`/`NTREES` form, block type and block count codes, block
//! switch commands, context modes, context maps with several trees and
//! run-length coded zeros, single literals, and static dictionary
//! references.
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use crate::cmeta::*;
#[cfg(verus_only)]
use crate::elemmas::*;
#[cfg(verus_only)]
use crate::pcode::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Numbers 0 to 255 (`varlen8`)
// ---------------------------------------------------------------------------

/// The bits of `v` as `varlen8` reads them, with `n = floor(log2 v)` for
/// `v >= 2`.
pub open spec fn v8_bits(v: int, n: nat) -> Seq<nat> {
    if v == 0 {
        fld(0, 1)
    } else if v == 1 {
        fld(1, 1) + fld(0, 3)
    } else {
        fld(1, 1) + (fld(n, 3) + fld((v - pow2(n)) as nat, n))
    }
}

pub open spec fn v8_ok(v: int, n: nat) -> bool {
    &&& 0 <= v < 256
    &&& v >= 2 ==> 1 <= n <= 7 && pow2(n) <= v < pow2(n + 1)
}

#[verifier::spinoff_prover]
proof fn lemma_v8_big(b: Seq<u8>, w: Seq<nat>, v: int, n: nat, rest: Seq<nat>)
    requires
        v8_ok(v, n),
        v >= 2,
        ext(b, w + (v8_bits(v, n) + rest)),
    ensures
        varlen8(b, w.len() as int) == R::Ok(v, (w.len() + v8_bits(v, n).len()) as int),
        v8_bits(v, n).len() == 4 + n,
{
    lemma_pow2_small();
    let a = fld(1, 1);
    let c = fld(n, 3);
    let x = (v - pow2(n)) as nat;
    let e = fld(x, n);
    assert(v8_bits(v, n) == a + (c + e));
    assert(w + (v8_bits(v, n) + rest) =~= w + (a + (c + (e + rest))));
    lemma_rd(b, w, 1, 1, c + (e + rest));
    assert(w + (a + (c + (e + rest))) =~= (w + a) + (c + (e + rest)));
    lemma_rd(b, w + a, n, 3, e + rest);
    assert((w + a) + (c + (e + rest)) =~= ((w + a) + c) + (e + rest));
    lemma_pow2_unfold(n + 1);
    assert(x < pow2(n));
    lemma_rd(b, (w + a) + c, x, n, rest);
    assert(rd(b, w.len() as int + 1, 3) == Some(n as int));
    assert(rd(b, w.len() as int + 4, n) == Some(x as int));
}

#[verifier::spinoff_prover]
pub proof fn lemma_v8(b: Seq<u8>, w: Seq<nat>, v: int, n: nat, rest: Seq<nat>)
    requires
        v8_ok(v, n),
        ext(b, w + (v8_bits(v, n) + rest)),
    ensures
        varlen8(b, w.len() as int) == R::Ok(v, (w.len() + v8_bits(v, n).len()) as int),
        v8_bits(v, n).len() == if v == 0 { 1 } else if v == 1 { 4 } else { 4 + n },
{
    lemma_pow2_small();
    if v == 0 {
        lemma_rd(b, w, 0, 1, rest);
    } else if v == 1 {
        let a = fld(1, 1);
        let z = fld(0, 3);
        assert(w + (v8_bits(v, n) + rest) =~= w + (a + (z + rest)));
        lemma_rd(b, w, 1, 1, z + rest);
        assert(w + (a + (z + rest)) =~= (w + a) + (z + rest));
        lemma_rd(b, w + a, 0, 3, rest);
    } else {
        lemma_v8_big(b, w, v, n, rest);
    }
}

// ---------------------------------------------------------------------------
// Block types and counts in the header
// ---------------------------------------------------------------------------

pub open spec fn after_nbt(s: St, c: int, v: int, p: int) -> St {
    let s1 = St { pos: p, nbt: s.nbt.update(c, v + 1), ..s };
    if v + 1 >= 2 {
        St { phase: Phase::BTypeCode(c), pc: pc_init(), ..s1 }
    } else {
        St { phase: after_cat(c), ..s1 }
    }
}

/// `NBLTYPES - 1 = v` for category `c`.
#[verifier::spinoff_prover]
pub proof fn lemma_nbt(w: Seq<nat>, s: St, c: int, v: int, n: nat)
    requires
        s.phase == Phase::NBlockTypes(c),
        s.pos == w.len(),
        v8_ok(v, n),
    ensures
        moves(w, v8_bits(v, n), s, after_nbt(s, c, v, (w.len() + v8_bits(v, n).len()) as int)),
{
    let u = v8_bits(v, n);
    let t = after_nbt(s, c, v, (w.len() + u.len()) as int);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        assert(w + u =~= w + (u + Seq::<nat>::empty()));
        lemma_v8(b, w, v, n, Seq::empty());
        crate::decoder::lemma_step_nbt(b, s, c);
    }
    lemma_moves_step(w, u, s, t);
}

/// Block count `len` fits the range of block count symbol `sym`.
pub open spec fn blen_fits(sym: int, len: int) -> bool {
    &&& 0 <= sym < 26
    &&& BLEN_BASE[sym] <= len < BLEN_BASE[sym] + pow2(BLEN_EXTRA[sym] as nat)
}

pub open spec fn blen_bits(code: Seq<u8>, sym: int, len: int) -> Seq<nat> {
    code_of(code, sym) + fld((len - BLEN_BASE[sym]) as nat, BLEN_EXTRA[sym] as nat)
}

pub proof fn lemma_read_blen(b: Seq<u8>, w: Seq<nat>, code: Seq<u8>, sym: int, len: int, rest: Seq<nat>)
    requires
        coded(code, sym),
        blen_fits(sym, len),
        ext(b, w + (blen_bits(code, sym, len) + rest)),
    ensures
        read_blen(code, b, w.len() as int) == R::Ok(len, (w.len() + blen_bits(code, sym, len).len()) as int),
{
    let c = code_of(code, sym);
    let x = (len - BLEN_BASE[sym]) as nat;
    let n = BLEN_EXTRA[sym] as nat;
    let e = fld(x, n);
    assert(w + (blen_bits(code, sym, len) + rest) =~= w + (c + (e + rest)));
    lemma_sym(b, w, code, sym, e + rest);
    assert(w + (c + (e + rest)) =~= (w + c) + (e + rest));
    lemma_rd(b, w + c, x, n, rest);
}

/// The first block count of category `c`.
#[verifier::spinoff_prover]
pub proof fn lemma_bcount(w: Seq<nat>, s: St, c: int, sym: int, len: int)
    requires
        s.phase == Phase::BCount(c),
        s.pos == w.len(),
        0 <= c < s.bcc.len(),
        coded(s.bcc[c], sym),
        blen_fits(sym, len),
    ensures
        moves(w, blen_bits(s.bcc[c], sym, len), s, St {
            phase: after_cat(c),
            pos: (w.len() + blen_bits(s.bcc[c], sym, len).len()) as int,
            blen: s.blen.update(c, len),
            ..s
        }),
{
    let u = blen_bits(s.bcc[c], sym, len);
    let t = St { phase: after_cat(c), pos: (w.len() + u.len()) as int, blen: s.blen.update(c, len), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        assert(w + u =~= w + (u + Seq::<nat>::empty()));
        lemma_read_blen(b, w, s.bcc[c], sym, len, Seq::empty());
        crate::decoder::lemma_step_bcount(b, s, c);
    }
    lemma_moves_step(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Block switch commands
// ---------------------------------------------------------------------------

/// The state reads a block switch for category `c` next.
pub open spec fn switch_phase(s: St, c: int) -> bool {
    &&& s.blen.len() == 3
    &&& 0 <= c < 3
    &&& s.blen[c] == 0
    &&& if c == 0 {
        s.phase is Insert
    } else if c == 1 {
        s.phase is CmdBegin
    } else {
        s.phase is Dist && !s.implicit
    }
}

/// The block type that block type symbol `sym` stands for.
pub open spec fn bsw_type(s: St, c: int, sym: int) -> int {
    let t0 = if sym == 0 {
        s.bt2[c]
    } else if sym == 1 {
        s.bt[c] + 1
    } else {
        sym - 2
    };
    if t0 >= s.nbt[c] {
        t0 - s.nbt[c]
    } else {
        t0
    }
}

pub open spec fn bsw_next(s: St, c: int, sym: int, len: int, p: int) -> St {
    St {
        pos: p,
        bt: s.bt.update(c, bsw_type(s, c, sym)),
        bt2: s.bt2.update(c, s.bt[c]),
        blen: s.blen.update(c, len),
        ..s
    }
}

pub open spec fn bsw_bits(s: St, c: int, sym: int, ls: int, len: int) -> Seq<nat> {
    code_of(s.btc[c], sym) + blen_bits(s.bcc[c], ls, len)
}

#[verifier::spinoff_prover]
proof fn lemma_bsw_at(b: Seq<u8>, w: Seq<nat>, s: St, c: int, sym: int, ls: int, len: int)
    requires
        switch_phase(s, c),
        s.pos == w.len(),
        s.nbt.len() == 3,
        s.btc.len() == 3,
        s.bcc.len() == 3,
        s.nbt[c] >= 2,
        coded(s.btc[c], sym),
        coded(s.bcc[c], ls),
        blen_fits(ls, len),
        ext(b, w + bsw_bits(s, c, sym, ls, len)),
    ensures
        step(b, s) == Step::Next(bsw_next(s, c, sym, len, (w.len() + bsw_bits(s, c, sym, ls, len).len()) as int)),
{
    let a = code_of(s.btc[c], sym);
    let r = blen_bits(s.bcc[c], ls, len);
    lemma_sym(b, w, s.btc[c], sym, r);
    assert(w + (a + r) =~= (w + a) + (r + Seq::<nat>::empty()));
    lemma_read_blen(b, w + a, s.bcc[c], ls, len, Seq::empty());
    crate::decoder::lemma_step_data(b, s);
}

/// A block switch command for category `c`: block type symbol `sym`, then
/// block count `len` with block count symbol `ls`.
pub proof fn lemma_bsw(w: Seq<nat>, s: St, c: int, sym: int, ls: int, len: int)
    requires
        switch_phase(s, c),
        s.pos == w.len(),
        s.nbt.len() == 3,
        s.btc.len() == 3,
        s.bcc.len() == 3,
        s.nbt[c] >= 2,
        coded(s.btc[c], sym),
        coded(s.bcc[c], ls),
        blen_fits(ls, len),
    ensures
        moves(w, bsw_bits(s, c, sym, ls, len), s, bsw_next(s, c, sym, len, (w.len() + bsw_bits(s, c, sym, ls, len).len()) as int)),
{
    let u = bsw_bits(s, c, sym, ls, len);
    let t = bsw_next(s, c, sym, len, (w.len() + u.len()) as int);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_bsw_at(b, w, s, c, sym, ls, len);
    }
    lemma_moves_step(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Context modes
// ---------------------------------------------------------------------------

/// The context mode of the next literal block type.
#[verifier::spinoff_prover]
pub proof fn lemma_cmode(w: Seq<nat>, s: St, mode: int)
    requires
        s.phase is CModes,
        s.pos == w.len(),
        s.cmodes.len() < s.nbt[0],
        0 <= mode < 4,
    ensures
        moves(w, fld(mode as nat, 2), s, St { pos: s.pos + 2, cmodes: s.cmodes.push(mode as u8), ..s }),
{
    lemma_pow2_small();
    let t = St { pos: s.pos + 2, cmodes: s.cmodes.push(mode as u8), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(mode as nat, 2)) implies step(b, s) == Step::Next(t) by {
        assert(w + fld(mode as nat, 2) =~= w + (fld(mode as nat, 2) + Seq::<nat>::empty()));
        lemma_rd(b, w, mode as nat, 2, Seq::empty());
        crate::decoder::lemma_step_cmodes(b, s);
    }
    lemma_moves_step(w, fld(mode as nat, 2), s, t);
}

/// Every literal block type has its mode: on to the literal context map.
pub proof fn lemma_cmodes_end(w: Seq<nat>, s: St)
    requires
        s.phase is CModes,
        s.cmodes.len() >= s.nbt[0],
    ensures
        moves(w, Seq::empty(), s, St { phase: Phase::CMap(0), cm: cm_init(), ..s }),
{
    let t = St { phase: Phase::CMap(0), cm: cm_init(), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_cmodes(b, s);
    }
    lemma_moves_step(w, Seq::empty(), s, t);
}

// ---------------------------------------------------------------------------
// Context maps
// ---------------------------------------------------------------------------

/// `RLEMAX`: a 0 bit, or a 1 bit and `RLEMAX - 1` in 4 bits.
pub open spec fn rle_bits(r: int) -> Seq<nat> {
    if r == 0 {
        fld(0, 1)
    } else {
        fld(1, 1) + fld((r - 1) as nat, 4)
    }
}

/// `NTREES - 1 = v` (at least 1) and `RLEMAX = r`.
#[verifier::spinoff_prover]
pub proof fn lemma_cm_head(w: Seq<nat>, s: St, wh: int, v: int, n: nat, r: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 0,
        s.pos == w.len(),
        v8_ok(v, n),
        v >= 1,
        0 <= r <= 16,
    ensures
        moves(w, v8_bits(v, n) + rle_bits(r), s, St {
            pos: (w.len() + (v8_bits(v, n) + rle_bits(r)).len()) as int,
            cm: Cm { stage: 1, ntrees: v + 1, rlemax: r, ..s.cm },
            pc: pc_init(),
            ..s
        }),
{
    lemma_pow2_small();
    let a = v8_bits(v, n);
    let z = rle_bits(r);
    let u = a + z;
    let t = St { pos: (w.len() + u.len()) as int, cm: Cm { stage: 1, ntrees: v + 1, rlemax: r, ..s.cm }, pc: pc_init(), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_v8(b, w, v, n, z);
        let w1 = w + a;
        if r == 0 {
            assert(w + u =~= w1 + (fld(0, 1) + Seq::<nat>::empty()));
            lemma_rd(b, w1, 0, 1, Seq::empty());
        } else {
            let y = fld((r - 1) as nat, 4);
            assert(w + u =~= w1 + (fld(1, 1) + y));
            lemma_rd(b, w1, 1, 1, y);
            assert(w1 + (fld(1, 1) + y) =~= (w1 + fld(1, 1)) + (y + Seq::<nat>::empty()));
            lemma_rd(b, w1 + fld(1, 1), (r - 1) as nat, 4, Seq::empty());
        }
        crate::decoder::lemma_step_cmap(b, s, wh);
    }
    lemma_moves_step(w, u, s, t);
}

/// What context map symbol `sym` adds to the map (with `e` extra bits for
/// a run of zeros).
pub open spec fn cm_add(rlemax: int, sym: int, e: int) -> Seq<u8> {
    if sym == 0 {
        seq![0u8]
    } else if sym > rlemax {
        seq![(sym - rlemax) as u8]
    } else {
        Seq::new((pow2(sym as nat) + e) as nat, |i: int| 0u8)
    }
}

pub open spec fn cm_sym_bits(code: Seq<u8>, rlemax: int, sym: int, e: int) -> Seq<nat> {
    if 1 <= sym <= rlemax {
        code_of(code, sym) + fld(e as nat, sym as nat)
    } else {
        code_of(code, sym)
    }
}

pub open spec fn cm_sym_ok(s: St, wh: int, sym: int, e: int) -> bool {
    &&& coded(s.cm.code, sym)
    &&& s.cm.map.len() < cmap_size(s, wh)
    &&& (1 <= sym <= s.cm.rlemax ==> 0 <= e < pow2(sym as nat) && s.cm.map.len() + pow2(sym as nat) + e <= cmap_size(s, wh))
}

#[verifier::spinoff_prover]
proof fn lemma_cm_sym_at(b: Seq<u8>, w: Seq<nat>, s: St, wh: int, sym: int, e: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 2,
        s.pos == w.len(),
        cm_sym_ok(s, wh, sym, e),
        ext(b, w + cm_sym_bits(s.cm.code, s.cm.rlemax, sym, e)),
    ensures
        step(b, s) == Step::Next(St {
            pos: (w.len() + cm_sym_bits(s.cm.code, s.cm.rlemax, sym, e).len()) as int,
            cm: Cm { map: s.cm.map + cm_add(s.cm.rlemax, sym, e), ..s.cm },
            ..s
        }),
{
    let c = code_of(s.cm.code, sym);
    if 1 <= sym <= s.cm.rlemax {
        let x = fld(e as nat, sym as nat);
        lemma_sym(b, w, s.cm.code, sym, x);
        assert(w + (c + x) =~= (w + c) + (x + Seq::<nat>::empty()));
        lemma_rd(b, w + c, e as nat, sym as nat, Seq::empty());
    } else {
        assert(w + c =~= w + (c + Seq::<nat>::empty()));
        lemma_sym(b, w, s.cm.code, sym, Seq::empty());
        if sym == 0 {
            assert(s.cm.map.push(0) =~= s.cm.map + seq![0u8]);
        } else {
            assert(s.cm.map.push((sym - s.cm.rlemax) as u8) =~= s.cm.map + seq![(sym - s.cm.rlemax) as u8]);
        }
    }
    crate::decoder::lemma_step_cmap(b, s, wh);
}

/// One context map symbol.
pub proof fn lemma_cm_sym(w: Seq<nat>, s: St, wh: int, sym: int, e: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 2,
        s.pos == w.len(),
        cm_sym_ok(s, wh, sym, e),
    ensures
        moves(w, cm_sym_bits(s.cm.code, s.cm.rlemax, sym, e), s, St {
            pos: (w.len() + cm_sym_bits(s.cm.code, s.cm.rlemax, sym, e).len()) as int,
            cm: Cm { map: s.cm.map + cm_add(s.cm.rlemax, sym, e), ..s.cm },
            ..s
        }),
{
    let u = cm_sym_bits(s.cm.code, s.cm.rlemax, sym, e);
    let t = St { pos: (w.len() + u.len()) as int, cm: Cm { map: s.cm.map + cm_add(s.cm.rlemax, sym, e), ..s.cm }, ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_cm_sym_at(b, w, s, wh, sym, e);
    }
    lemma_moves_step(w, u, s, t);
}

/// The map is complete: on to the `IMTF` bit.
pub proof fn lemma_cm_full(w: Seq<nat>, s: St, wh: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 2,
        s.cm.map.len() >= cmap_size(s, wh),
    ensures
        moves(w, Seq::empty(), s, St { cm: Cm { stage: 3, ..s.cm }, ..s }),
{
    let t = St { cm: Cm { stage: 3, ..s.cm }, ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_cmap(b, s, wh);
    }
    lemma_moves_step(w, Seq::empty(), s, t);
}

/// The `IMTF` bit `x`, which ends the map.
#[verifier::spinoff_prover]
pub proof fn lemma_cm_imtf(w: Seq<nat>, s: St, wh: int, x: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 3,
        s.pos == w.len(),
        0 <= x <= 1,
    ensures
        cmap_finish(St { pos: s.pos + 1, ..s }, wh, s.cm.ntrees, if x == 1 { imtf(s.cm.map) } else { s.cm.map }) is Next,
        moves(w, fld(x as nat, 1), s, match cmap_finish(St { pos: s.pos + 1, ..s }, wh, s.cm.ntrees, if x == 1 { imtf(s.cm.map) } else { s.cm.map }) {
            Step::Next(t) => t,
            _ => s,
        }),
{
    lemma_pow2_small();
    let r = cmap_finish(St { pos: s.pos + 1, ..s }, wh, s.cm.ntrees, if x == 1 { imtf(s.cm.map) } else { s.cm.map });
    let t = match r { Step::Next(t) => t, _ => s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(x as nat, 1)) implies step(b, s) == Step::Next(t) by {
        assert(w + fld(x as nat, 1) =~= w + (fld(x as nat, 1) + Seq::<nat>::empty()));
        lemma_rd(b, w, x as nat, 1, Seq::empty());
        crate::decoder::lemma_step_cmap(b, s, wh);
    }
    lemma_moves_step(w, fld(x as nat, 1), s, t);
}

// ---------------------------------------------------------------------------
// Static dictionary references
// ---------------------------------------------------------------------------

/// The word a reference to distance `d`, past `maxd`, with copy length
/// `len`, stands for: word `addr % 2^NDBITS` of that length, under
/// transform `addr / 2^NDBITS`.
pub open spec fn dict_ref(len: int, d: int, maxd: int) -> Seq<u8> {
    let addr = d - maxd - 1;
    let n = NDBITS[len] as nat;
    transform(dict_word(len, addr % pow2(n) as int), addr / pow2(n) as int)
}

/// Distance `d` from state `s` is a valid dictionary reference.
pub open spec fn dict_ok(s: St, d: int) -> bool {
    let maxd = max_distance(s.out.len() as int, s.wbits);
    let addr = d - maxd - 1;
    &&& d > maxd
    &&& d <= 0x7FFF_FFFC
    &&& 4 <= s.clen <= 24
    &&& (addr / pow2(NDBITS[s.clen] as nat) as int) < NTRANSFORMS
    &&& !(dict_ref(s.clen, d, maxd).len() == 0 && d <= 120)
    &&& dict_ref(s.clen, d, maxd).len() <= s.mrem
}

pub open spec fn dict_next(s: St, d: int, p: int) -> St {
    let wd = dict_ref(s.clen, d, max_distance(s.out.len() as int, s.wbits));
    St {
        phase: after_data(s.mrem - wd.len()),
        pos: p,
        blen: s.blen.update(2, s.blen[2] - 1),
        out: s.out + wd,
        mrem: s.mrem - wd.len(),
        ..s
    }
}

#[verifier::spinoff_prover]
proof fn lemma_dict_at(b: Seq<u8>, w: Seq<nat>, s: St, dcode: int, extra: int)
    requires
        s.phase is Dist,
        !s.implicit,
        s.pos == w.len(),
        s.blen.len() == 3,
        s.blen[2] != 0,
        s.npostfix == 0,
        s.ndirect == 0,
        0 <= dtree(s) < s.dst.len(),
        coded(s.dst[dtree(s)], dcode),
        16 <= dcode,
        0 <= extra < pow2(dext(dcode)),
        dict_ok(s, dist_value(dcode, extra, 0, 0)),
        ext(b, w + dist_bits(s.dst[dtree(s)], dcode, extra)),
    ensures
        step(b, s) == Step::Next(dict_next(s, dist_value(dcode, extra, 0, 0), (w.len() + dist_bits(s.dst[dtree(s)], dcode, extra).len()) as int)),
{
    let c = s.dst[dtree(s)];
    let n = dext(dcode);
    let e = fld(extra as nat, n);
    lemma_bits_of(extra as nat, n);
    lemma_sym(b, w, c, dcode, e);
    let w1 = w + code_of(c, dcode);
    assert(w + (code_of(c, dcode) + e) =~= w1 + (e + Seq::<nat>::empty()));
    lemma_rd(b, w1, extra as nat, n, Seq::empty());
    crate::decoder::lemma_step_data(b, s);
    reveal(resolve);
}

/// A distance code past the window: a static dictionary word.
pub proof fn lemma_dist_dict(w: Seq<nat>, s: St, dcode: int, extra: int)
    requires
        s.phase is Dist,
        !s.implicit,
        s.pos == w.len(),
        s.blen.len() == 3,
        s.blen[2] != 0,
        s.npostfix == 0,
        s.ndirect == 0,
        0 <= dtree(s) < s.dst.len(),
        coded(s.dst[dtree(s)], dcode),
        16 <= dcode,
        0 <= extra < pow2(dext(dcode)),
        dict_ok(s, dist_value(dcode, extra, 0, 0)),
    ensures
        moves(w, dist_bits(s.dst[dtree(s)], dcode, extra), s,
            dict_next(s, dist_value(dcode, extra, 0, 0), (w.len() + dist_bits(s.dst[dtree(s)], dcode, extra).len()) as int)),
{
    let u = dist_bits(s.dst[dtree(s)], dcode, extra);
    let t = dict_next(s, dist_value(dcode, extra, 0, 0), (w.len() + u.len()) as int);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_dict_at(b, w, s, dcode, extra);
    }
    lemma_moves_step(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Literals, one at a time
// ---------------------------------------------------------------------------

/// The index into the literal context map of the next literal.
pub open spec fn lit_idx(s: St) -> int {
    s.bt[0] * 64 + lit_context(s.cmodes[s.bt[0]] as int, p1(s.out), p2(s.out))
}

pub open spec fn after_lit(s: St, x: u8, p: int) -> St {
    let s1 = St { pos: p, out: s.out.push(x), blen: s.blen.update(0, s.blen[0] - 1), ilen: s.ilen - 1, mrem: s.mrem - 1, ..s };
    if s1.ilen > 0 {
        s1
    } else if s1.mrem == 0 {
        St { phase: Phase::MetaDone, ..s1 }
    } else {
        St { phase: Phase::Dist, ..s1 }
    }
}

/// One literal, `x`, with the tree its context picks.
pub proof fn lemma_lit(w: Seq<nat>, s: St, x: u8)
    requires
        s.phase is Insert,
        s.pos == w.len(),
        s.blen[0] != 0,
        s.ilen >= 1,
        s.mrem >= 1,
        0 <= lit_idx(s) < s.cmap.len(),
        0 <= s.cmap[lit_idx(s)] < s.lit.len(),
        coded(s.lit[s.cmap[lit_idx(s)] as int], x as int),
    ensures
        moves(w, code_of(s.lit[s.cmap[lit_idx(s)] as int], x as int), s,
            after_lit(s, x, (w.len() + code_of(s.lit[s.cmap[lit_idx(s)] as int], x as int).len()) as int)),
{
    let u = code_of(s.lit[s.cmap[lit_idx(s)] as int], x as int);
    let t = after_lit(s, x, (w.len() + u.len()) as int);
    assert(lit_tree(lm(s), s.out) == s.cmap[lit_idx(s)] as int);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        assert(w + u =~= w + (u + Seq::<nat>::empty()));
        lemma_lit_at(b, w, s, x, Seq::empty());
    }
    lemma_moves_step(w, u, s, t);
}

} // verus!
