//! Proofs for compressed meta-blocks: the header fields after the length
//! (block types, distance parameters, context modes and maps), and the
//! commands.
#[cfg(verus_only)]
use crate::bitwriter::*;
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
// The header of a compressed meta-block, with one block type per category
// ---------------------------------------------------------------------------

/// `NBLTYPES = 1` for category `c`: a single 0 bit.
#[verifier::spinoff_prover]
pub proof fn lemma_nbt1(w: Seq<nat>, s: St, c: int)
    requires
        s.phase == Phase::NBlockTypes(c),
        s.pos == w.len(),
    ensures
        moves(w, fld(0, 1), s, St { phase: after_cat(c), pos: s.pos + 1, nbt: s.nbt.update(c, 1), ..s }),
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    let t = St { phase: after_cat(c), pos: s.pos + 1, nbt: s.nbt.update(c, 1), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(0, 1)) implies step(b, s) == Step::Next(t) by {
        assert(w + fld(0, 1) =~= w + (fld(0, 1) + Seq::<nat>::empty()));
        lemma_rd(b, w, 0, 1, Seq::empty());
        crate::decoder::lemma_step_nbt(b, s, c);
    }
    lemma_moves_step(w, fld(0, 1), s, t);
}

/// `NPOSTFIX = 0`, `NDIRECT = 0`.
#[verifier::spinoff_prover]
pub proof fn lemma_dparams0(w: Seq<nat>, s: St)
    requires
        s.phase is DistParams,
        s.pos == w.len(),
    ensures
        moves(w, fld(0, 6), s, St { phase: Phase::CModes, pos: s.pos + 6, npostfix: 0, ndirect: 0, cmodes: Seq::empty(), ..s }),
{
    lemma_pow2_small();
    lemma_bits_of(0, 6);
    let t = St { phase: Phase::CModes, pos: s.pos + 6, npostfix: 0, ndirect: 0, cmodes: Seq::empty(), ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(0, 6)) implies step(b, s) == Step::Next(t) by {
        assert(w + fld(0, 6) =~= w + (fld(0, 6) + Seq::<nat>::empty()));
        lemma_rd(b, w, 0, 6, Seq::empty());
        crate::decoder::lemma_step_dparams(b, s);
        assert(0 * pow2(0) == 0);
    }
    lemma_moves_step(w, fld(0, 6), s, t);
}

/// The context mode of the one literal block type, then on to the
/// literal context map.
#[verifier::spinoff_prover]
pub proof fn lemma_cmodes1(w: Seq<nat>, s: St, mode: int)
    requires
        s.phase is CModes,
        s.pos == w.len(),
        s.cmodes.len() == 0,
        s.nbt[0] == 1,
        0 <= mode < 4,
    ensures
        moves(w, fld(mode as nat, 2), s, St { phase: Phase::CMap(0), pos: s.pos + 2, cmodes: seq![mode as u8], cm: cm_init(), ..s }),
{
    lemma_pow2_small();
    lemma_bits_of(mode as nat, 2);
    let s1 = St { pos: s.pos + 2, cmodes: s.cmodes.push(mode as u8), ..s };
    let t = St { phase: Phase::CMap(0), pos: s.pos + 2, cmodes: seq![mode as u8], cm: cm_init(), ..s };
    assert(s.cmodes.push(mode as u8) =~= seq![mode as u8]);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(mode as nat, 2)) implies step(b, s) == Step::Next(s1) by {
        assert(w + fld(mode as nat, 2) =~= w + (fld(mode as nat, 2) + Seq::<nat>::empty()));
        lemma_rd(b, w, mode as nat, 2, Seq::empty());
        crate::decoder::lemma_step_cmodes(b, s);
    }
    lemma_moves_step(w, fld(mode as nat, 2), s, s1);
    let w1 = w + fld(mode as nat, 2);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w1 + Seq::empty()) implies step(b, s1) == Step::Next(t) by {
        crate::decoder::lemma_step_cmodes(b, s1);
    }
    lemma_moves_step(w1, Seq::empty(), s1, t);
    assert(fld(mode as nat, 2) + Seq::<nat>::empty() =~= fld(mode as nat, 2));
    lemma_moves_trans(w, fld(mode as nat, 2), Seq::empty(), s, s1, t);
}

/// A context map with one tree: `NTREES - 1 = 0`, a single 0 bit.
#[verifier::spinoff_prover]
pub proof fn lemma_cmap1(w: Seq<nat>, s: St, wh: int)
    requires
        s.phase == Phase::CMap(wh),
        s.cm.stage == 0,
        s.pos == w.len(),
    ensures
        moves(w, fld(0, 1), s, match cmap_finish(St { pos: s.pos + 1, ..s }, wh, 1, Seq::new(cmap_size(s, wh) as nat, |i: int| 0u8)) {
            Step::Next(t) => t,
            _ => s,
        }),
        cmap_finish(St { pos: s.pos + 1, ..s }, wh, 1, Seq::new(cmap_size(s, wh) as nat, |i: int| 0u8)) is Next,
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    let r = cmap_finish(St { pos: s.pos + 1, ..s }, wh, 1, Seq::new(cmap_size(s, wh) as nat, |i: int| 0u8));
    let t = match r { Step::Next(t) => t, _ => s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(0, 1)) implies step(b, s) == Step::Next(t) by {
        assert(w + fld(0, 1) =~= w + (fld(0, 1) + Seq::<nat>::empty()));
        lemma_rd(b, w, 0, 1, Seq::empty());
        crate::decoder::lemma_step_cmap(b, s, wh);
    }
    lemma_moves_step(w, fld(0, 1), s, t);
}

/// Every code of group `g` read: on to the next group, or the commands.
#[verifier::spinoff_prover]
pub proof fn lemma_trees_next(w: Seq<nat>, s: St, g: int)
    requires
        s.phase == Phase::Trees(g),
        nread(s, g) >= ntrees(s, g),
    ensures
        moves(w, Seq::empty(), s, if g < 2 {
            St { phase: Phase::Trees(g + 1), pc: pc_init(), ..s }
        } else {
            St { phase: Phase::CmdBegin, ..s }
        }),
{
    let t = if g < 2 { St { phase: Phase::Trees(g + 1), pc: pc_init(), ..s } } else { St { phase: Phase::CmdBegin, ..s } };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_trees(b, s, g);
    }
    lemma_moves_step(w, Seq::empty(), s, t);
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

pub proof fn lemma_cells()
    ensures
        forall|i: int| 0 <= i < 11 ==> #[trigger] CELL[i] <= 18 && CELL[i] % 4 <= 2,
{
    assert(forall|i: int| 0 <= i < 11 ==> #[trigger] CELL[i] <= 18 && CELL[i] % 4 <= 2) by (compute);
}

pub proof fn lemma_codes_range(sym: int)
    requires
        0 <= sym < 704,
    ensures
        0 <= ins_code(sym) < 24,
        0 <= cpy_code(sym) < 24,
{
    lemma_cells();
    assert(sym / 64 < 11);
}

/// Insert-and-copy symbol `sym` covers lengths `ilen` and `clen`.
pub open spec fn sym_fits(sym: int, ilen: int, clen: int) -> bool {
    let ic = ins_code(sym);
    let cc = cpy_code(sym);
    &&& 0 <= sym < 704
    &&& INS_BASE[ic] <= ilen < INS_BASE[ic] + pow2(INS_EXTRA[ic] as nat)
    &&& CPY_BASE[cc] <= clen < CPY_BASE[cc] + pow2(CPY_EXTRA[cc] as nat)
}

/// A command's symbol and extra bits, written with code `c`.
pub open spec fn cmd_bits(c: Seq<u8>, sym: int, ilen: int, clen: int) -> Seq<nat> {
    let ic = ins_code(sym);
    let cc = cpy_code(sym);
    code_of(c, sym) + (fld((ilen - INS_BASE[ic]) as nat, INS_EXTRA[ic] as nat) + fld((clen - CPY_BASE[cc]) as nat, CPY_EXTRA[cc] as nat))
}

/// A code can write symbol `x`.
pub open spec fn coded(c: Seq<u8>, x: int) -> bool {
    &&& lens_ok(c)
    &&& 0 <= x < c.len()
    &&& 1 <= c[x]
    &&& (used(c) == 1 ==> first_used(c, 0) == x)
}

pub open spec fn after_cmd(s: St, sym: int, ilen: int, clen: int, p: int) -> St {
    St {
        phase: if ilen > 0 { Phase::Insert } else { Phase::Dist },
        pos: p,
        blen: s.blen.update(1, s.blen[1] - 1),
        ilen,
        clen,
        dctx: dist_context(sym),
        implicit: sym < 128,
        ..s
    }
}

#[verifier::spinoff_prover]
proof fn lemma_cmd_at(b: Seq<u8>, w: Seq<nat>, s: St, sym: int, ilen: int, clen: int)
    requires
        s.phase is CmdBegin,
        s.pos == w.len(),
        s.blen[1] != 0,
        0 <= s.bt[1] < s.cmd.len(),
        coded(s.cmd[s.bt[1]], sym),
        sym_fits(sym, ilen, clen),
        ilen <= s.mrem,
        ext(b, w + cmd_bits(s.cmd[s.bt[1]], sym, ilen, clen)),
    ensures
        step(b, s) == Step::Next(after_cmd(s, sym, ilen, clen, (w.len() + cmd_bits(s.cmd[s.bt[1]], sym, ilen, clen).len()) as int)),
{
    let c = s.cmd[s.bt[1]];
    let ic = ins_code(sym);
    let cc = cpy_code(sym);
    lemma_codes_range(sym);
    let ie = INS_EXTRA[ic] as nat;
    let ce = CPY_EXTRA[cc] as nat;
    let ix = (ilen - INS_BASE[ic]) as nat;
    let cx = (clen - CPY_BASE[cc]) as nat;
    let a = code_of(c, sym);
    let e1 = fld(ix, ie);
    let e2 = fld(cx, ce);
    lemma_bits_of(ix, ie);
    lemma_bits_of(cx, ce);
    lemma_sym(b, w, c, sym, e1 + e2);
    let w1 = w + a;
    assert(w + (a + (e1 + e2)) =~= w1 + (e1 + e2));
    lemma_rd(b, w1, ix, ie, e2);
    let w2 = w1 + e1;
    assert(w1 + (e1 + e2) =~= w2 + (e2 + Seq::<nat>::empty()));
    lemma_rd(b, w2, cx, ce, Seq::empty());
    crate::decoder::lemma_step_data(b, s);
}

/// The insert-and-copy command.
pub proof fn lemma_cmd(w: Seq<nat>, s: St, sym: int, ilen: int, clen: int)
    requires
        s.phase is CmdBegin,
        s.pos == w.len(),
        s.blen[1] != 0,
        0 <= s.bt[1] < s.cmd.len(),
        coded(s.cmd[s.bt[1]], sym),
        sym_fits(sym, ilen, clen),
        ilen <= s.mrem,
    ensures
        moves(w, cmd_bits(s.cmd[s.bt[1]], sym, ilen, clen), s, after_cmd(s, sym, ilen, clen, (w.len() + cmd_bits(s.cmd[s.bt[1]], sym, ilen, clen).len()) as int)),
{
    let u = cmd_bits(s.cmd[s.bt[1]], sym, ilen, clen);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(after_cmd(s, sym, ilen, clen, (w.len() + u.len()) as int)) by {
        lemma_cmd_at(b, w, s, sym, ilen, clen);
    }
    lemma_moves_step(w, u, s, after_cmd(s, sym, ilen, clen, (w.len() + u.len()) as int));
}

/// What literals are read with: the literal context map, block type,
/// context mode and codes.
pub struct LitM {
    pub cmap: Seq<u8>,
    pub bt0: int,
    pub mode: int,
    pub lit: Seq<Seq<u8>>,
}

pub open spec fn lm(s: St) -> LitM {
    LitM { cmap: s.cmap, bt0: s.bt[0], mode: s.cmodes[s.bt[0]] as int, lit: s.lit }
}

pub open spec fn lit_tree(m: LitM, out: Seq<u8>) -> int {
    m.cmap[m.bt0 * 64 + lit_context(m.mode, p1(out), p2(out))] as int
}

pub open spec fn lits_bits(m: LitM, out: Seq<u8>, d: Seq<u8>) -> Seq<nat>
    decreases d.len(),
{
    if d.len() == 0 {
        Seq::empty()
    } else {
        code_of(m.lit[lit_tree(m, out)], d[0] as int) + lits_bits(m, out.push(d[0]), d.subrange(1, d.len() as int))
    }
}

/// Every literal has a code in its tree.
pub open spec fn lits_ok(m: LitM, out: Seq<u8>, d: Seq<u8>) -> bool
    decreases d.len(),
{
    if d.len() == 0 {
        true
    } else {
        let t = lit_tree(m, out);
        &&& 0 <= m.bt0 * 64 + lit_context(m.mode, p1(out), p2(out)) < m.cmap.len()
        &&& 0 <= t < m.lit.len()
        &&& coded(m.lit[t], d[0] as int)
        &&& lits_ok(m, out.push(d[0]), d.subrange(1, d.len() as int))
    }
}

pub open spec fn after_lits(s: St, d: Seq<u8>, p: int) -> St {
    let k = d.len() as int;
    St {
        phase: if s.mrem - k == 0 { Phase::MetaDone } else { Phase::Dist },
        pos: p,
        out: s.out + d,
        blen: s.blen.update(0, s.blen[0] - k),
        ilen: 0,
        mrem: s.mrem - k,
        ..s
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_lit_at(b: Seq<u8>, w: Seq<nat>, s: St, x: u8, rest: Seq<nat>)
    requires
        s.phase is Insert,
        s.pos == w.len(),
        s.blen[0] != 0,
        s.ilen >= 1,
        s.mrem >= 1,
        0 <= s.bt[0] * 64 + lit_context(lm(s).mode, p1(s.out), p2(s.out)) < s.cmap.len(),
        0 <= lit_tree(lm(s), s.out) < s.lit.len(),
        coded(s.lit[lit_tree(lm(s), s.out)], x as int),
        ext(b, w + (code_of(s.lit[lit_tree(lm(s), s.out)], x as int) + rest)),
    ensures
        ({
            let p = (w.len() + code_of(s.lit[lit_tree(lm(s), s.out)], x as int).len()) as int;
            let s1 = St { pos: p, out: s.out.push(x), blen: s.blen.update(0, s.blen[0] - 1), ilen: s.ilen - 1, mrem: s.mrem - 1, ..s };
            step(b, s) == Step::Next(if s1.ilen > 0 { s1 } else if s1.mrem == 0 { St { phase: Phase::MetaDone, ..s1 } } else { St { phase: Phase::Dist, ..s1 } })
        }),
{
    let t = lit_tree(lm(s), s.out);
    lemma_sym(b, w, s.lit[t], x as int, rest);
    crate::decoder::lemma_step_data(b, s);
}

/// The literals of a command.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn lemma_lits(w: Seq<nat>, s: St, d: Seq<u8>)
    requires
        s.phase is Insert,
        s.pos == w.len(),
        s.ilen == d.len(),
        d.len() >= 1,
        s.blen.len() == 3,
        s.blen[0] >= d.len(),
        s.mrem >= d.len(),
        lits_ok(lm(s), s.out, d),
    ensures
        moves(w, lits_bits(lm(s), s.out, d), s, after_lits(s, d, (w.len() + lits_bits(lm(s), s.out, d).len()) as int)),
    decreases d.len(),
{
    let m = lm(s);
    let x = d[0];
    let r = d.subrange(1, d.len() as int);
    let t = lit_tree(m, s.out);
    let c = code_of(m.lit[t], x as int);
    let p = (w.len() + c.len()) as int;
    let s1 = St { pos: p, out: s.out.push(x), blen: s.blen.update(0, s.blen[0] - 1), ilen: s.ilen - 1, mrem: s.mrem - 1, ..s };
    let s2 = if s1.ilen > 0 { s1 } else if s1.mrem == 0 { St { phase: Phase::MetaDone, ..s1 } } else { St { phase: Phase::Dist, ..s1 } };
    assert(lits_bits(m, s.out, d) == c + lits_bits(m, s.out.push(x), r));
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + c) implies step(b, s) == Step::Next(s2) by {
        assert(w + c =~= w + (c + Seq::<nat>::empty()));
        lemma_lit_at(b, w, s, x, Seq::empty());
    }
    lemma_moves_step(w, c, s, s2);
    if d.len() == 1 {
        assert(r =~= Seq::<u8>::empty());
        assert(lits_bits(m, s.out.push(x), r) =~= Seq::<nat>::empty());
        assert(c + Seq::<nat>::empty() =~= c);
        assert(s.out.push(x) =~= s.out + d);
        assert(s2 == after_lits(s, d, p));
    } else {
        assert(lm(s1) == m);
        assert(s1.blen[0] == s.blen[0] - 1);
        assert(s2 == s1);
        lemma_lits(w + c, s1, r);
        assert(s.out.push(x) + r =~= s.out + d);
        let u2 = lits_bits(m, s.out.push(x), r);
        lemma_moves_trans(w, c, u2, s, s1, after_lits(s1, r, ((w + c).len() + u2.len()) as int));
        let k = d.len() as int;
        assert(s1.blen.update(0, s1.blen[0] - r.len()) =~= s.blen.update(0, s.blen[0] - k));
        assert(after_lits(s1, r, ((w + c).len() + u2.len()) as int) == after_lits(s, d, (w.len() + (c + u2).len()) as int));
    }
}

/// Copying `c` bytes from `d` back, each the output byte `d` back.
#[verifier::spinoff_prover]
pub proof fn lemma_copy(w: Seq<nat>, s: St, data: Seq<u8>, q: int)
    requires
        s.phase is Copy,
        s.out == data.subrange(0, q),
        1 <= s.clen <= s.mrem,
        q + s.clen <= data.len(),
        1 <= s.dist <= q,
        forall|k: int| q <= k < q + s.clen ==> #[trigger] data[k] == data[k - s.dist],
    ensures
        moves(w, Seq::empty(), s, St { phase: after_data(s.mrem - s.clen), out: data.subrange(0, q + s.clen), clen: 0, mrem: s.mrem - s.clen, ..s }),
    decreases s.clen,
{
    let x = s.out[s.out.len() - s.dist];
    assert(x == data[q - s.dist]);
    assert(x == data[q]);
    let s1 = St { out: s.out.push(x), clen: s.clen - 1, mrem: s.mrem - 1, ..s };
    assert(s1.out =~= data.subrange(0, q + 1));
    let t = St { phase: after_data(s.mrem - s.clen), out: data.subrange(0, q + s.clen), clen: 0, mrem: s.mrem - s.clen, ..s };
    if s.clen == 1 {
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(t) by {
            crate::decoder::lemma_step_copy(b, s);
        }
        lemma_moves_step(w, Seq::empty(), s, t);
    } else {
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(s1) by {
            crate::decoder::lemma_step_copy(b, s);
        }
        lemma_moves_step(w, Seq::empty(), s, s1);
        lemma_copy(w + Seq::empty(), s1, data, q + 1);
        assert(w + Seq::<nat>::empty() =~= w);
        assert(Seq::<nat>::empty() + Seq::<nat>::empty() =~= Seq::<nat>::empty());
        lemma_moves_trans(w, Seq::empty(), Seq::empty(), s, s1, t);
    }
}

// ---------------------------------------------------------------------------
// Distances
// ---------------------------------------------------------------------------

/// The distance code `dcode` with extra bits `extra` stands for, with
/// `NPOSTFIX = NDIRECT = 0`.
pub open spec fn dval(dcode: int, extra: int, dr: Seq<int>) -> int {
    if dcode < 16 {
        short_dist(dcode, dr)
    } else {
        dist_value(dcode, extra, 0, 0)
    }
}

pub open spec fn dnext(dcode: int, d: int, dr: Seq<int>) -> Seq<int> {
    if dcode == 0 {
        dr
    } else {
        seq![d, dr[0], dr[1], dr[2]]
    }
}

/// Extra bits of distance code `dcode`.
pub open spec fn dext(dcode: int) -> nat {
    if dcode < 16 {
        0
    } else {
        dist_extra(dcode, 0, 0)
    }
}

pub open spec fn dist_bits(c: Seq<u8>, dcode: int, extra: int) -> Seq<nat> {
    code_of(c, dcode) + fld(extra as nat, dext(dcode))
}

/// The distance tree of the command.
pub open spec fn dtree(s: St) -> int {
    s.dmap[s.bt[2] * 4 + s.dctx] as int
}

/// A copy from `d` back can start.
pub open spec fn copy_ok(s: St, d: int) -> bool {
    &&& 1 <= d <= max_distance(s.out.len() as int, s.wbits)
    &&& s.clen <= s.mrem
}

pub proof fn lemma_dist_implicit(w: Seq<nat>, s: St)
    requires
        s.phase is Dist,
        s.implicit,
        copy_ok(s, s.dr[0]),
    ensures
        moves(w, Seq::empty(), s, St { phase: Phase::Copy, dist: s.dr[0], ..s }),
{
    let t = St { phase: Phase::Copy, dist: s.dr[0], ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_data(b, s);
        reveal(resolve);
    }
    lemma_moves_step(w, Seq::empty(), s, t);
}

#[verifier::spinoff_prover]
proof fn lemma_dist_at(b: Seq<u8>, w: Seq<nat>, s: St, dcode: int, extra: int)
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
        0 <= extra < pow2(dext(dcode)),
        copy_ok(s, dval(dcode, extra, s.dr)),
        ext(b, w + dist_bits(s.dst[dtree(s)], dcode, extra)),
    ensures
        step(b, s) == Step::Next(St {
            phase: Phase::Copy,
            pos: (w.len() + dist_bits(s.dst[dtree(s)], dcode, extra).len()) as int,
            blen: s.blen.update(2, s.blen[2] - 1),
            dist: dval(dcode, extra, s.dr),
            dr: dnext(dcode, dval(dcode, extra, s.dr), s.dr),
            ..s
        }),
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
    if dcode < 16 {
        lemma_pow2_small();
        assert(n == 0);
    }
}

pub proof fn lemma_dist_explicit(w: Seq<nat>, s: St, dcode: int, extra: int)
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
        0 <= extra < pow2(dext(dcode)),
        copy_ok(s, dval(dcode, extra, s.dr)),
    ensures
        moves(w, dist_bits(s.dst[dtree(s)], dcode, extra), s, St {
            phase: Phase::Copy,
            pos: (w.len() + dist_bits(s.dst[dtree(s)], dcode, extra).len()) as int,
            blen: s.blen.update(2, s.blen[2] - 1),
            dist: dval(dcode, extra, s.dr),
            dr: dnext(dcode, dval(dcode, extra, s.dr), s.dr),
            ..s
        }),
{
    let u = dist_bits(s.dst[dtree(s)], dcode, extra);
    let t = St {
        phase: Phase::Copy,
        pos: (w.len() + u.len()) as int,
        blen: s.blen.update(2, s.blen[2] - 1),
        dist: dval(dcode, extra, s.dr),
        dr: dnext(dcode, dval(dcode, extra, s.dr), s.dr),
        ..s
    };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_dist_at(b, w, s, dcode, extra);
    }
    lemma_moves_step(w, u, s, t);
}

} // verus!
