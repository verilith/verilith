//! Writing a compressed meta-block: the header with one tree per
//! category, then the commands, each checked first (`check_cmds`) so that
//! the writer only writes what is proven to decode.
use crate::bitwriter::*;
use crate::encoder::Enc;
use crate::mblock::*;
use crate::pcode::{HCode, Plan, put_tree};
use crate::spec::St;
use crate::spec::{INS_BASE, INS_EXTRA, CPY_BASE, CPY_EXTRA, CELL};
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

/// The shape of the state after the header of a compressed meta-block.
pub open spec fn hstate(t: St, s: St, len: int, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> bool {
    &&& t.phase is CmdBegin
    &&& t.out == s.out
    &&& t.wbits == s.wbits
    &&& t.dr == s.dr
    &&& t.mrem == len
    &&& !t.last
    &&& t.blen == seq![BLOCK_CAP, BLOCK_CAP, BLOCK_CAP]
    &&& t.bt == seq![0int, 0, 0]
    &&& t.lit == seq![l]
    &&& t.cmd == seq![c]
    &&& t.dst == seq![d]
    &&& t.cmap == zeros(64)
    &&& t.dmap == zeros(4)
    &&& t.cmodes == seq![0u8]
    &&& t.npostfix == 0
    &&& t.ndirect == 0
}

/// One bit-field step: `put` then the state the lemma gave.
proof fn lemma_adv(w: Seq<nat>, u: Seq<nat>, s: St, t: St, w2: Seq<nat>)
    requires
        good(w, s),
        moves(w, u, s, t),
        t.pos == w.len() + u.len(),
        w2 == w + u,
    ensures
        good(w2, t),
{
    lemma_good_moves(w, u, s, t);
}

/// The header of a compressed meta-block of `len` bytes (not the last).
pub fn put_cheader(e: &mut Enc, len: usize, lp: &Plan, cp: &Plan, dp: &Plan, Ghost(l): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>, Ghost(d): Ghost<Seq<u8>>)
    requires
        old(e).ok(),
        old(e).st@.phase is MetaHeader,
        1 <= len <= 0x1000000,
        lp.ok(l, 256),
        cp.ok(c, 704),
        dp.ok(d, 64),
    ensures
        final(e).ok(),
        final(e).bw.sent() == old(e).bw.sent(),
        hstate(final(e).st@, old(e).st@, len as int, l, c, d),
{
    let ghost w0 = e.bw.bits();
    let ghost s0 = e.st@;
    proof {
        lemma_meta_compressed(w0, s0, len as int, false);
        lemma_pow2_small();
        lemma_bits_of(0, 1);
    }
    e.bw.put(0, 1);
    e.put_mlen(len);
    e.bw.put(0, 1);
    let ghost s1 = begin_compressed(mheader(s0, len as int, false));
    proof {
        assert(e.bw.bits() =~= w0 + meta_bits(len as int, false));
        lemma_adv(w0, meta_bits(len as int, false), s0, s1, e.bw.bits());
    }
    // NBLTYPES = 1, three times.
    let ghost w1 = e.bw.bits();
    proof { lemma_nbt1(w1, s1, 0); }
    e.bw.put(0, 1);
    let ghost s2 = St { phase: after_cat(0), pos: s1.pos + 1, nbt: s1.nbt.update(0, 1), ..s1 };
    proof { lemma_adv(w1, fld(0, 1), s1, s2, e.bw.bits()); }
    let ghost w2 = e.bw.bits();
    proof { lemma_nbt1(w2, s2, 1); }
    e.bw.put(0, 1);
    let ghost s3 = St { phase: after_cat(1), pos: s2.pos + 1, nbt: s2.nbt.update(1, 1), ..s2 };
    proof { lemma_adv(w2, fld(0, 1), s2, s3, e.bw.bits()); }
    let ghost w3 = e.bw.bits();
    proof { lemma_nbt1(w3, s3, 2); }
    e.bw.put(0, 1);
    let ghost s4 = St { phase: after_cat(2), pos: s3.pos + 1, nbt: s3.nbt.update(2, 1), ..s3 };
    proof {
        lemma_adv(w3, fld(0, 1), s3, s4, e.bw.bits());
        assert(s4.nbt =~= seq![1int, 1, 1]);
    }
    // NPOSTFIX = NDIRECT = 0.
    let ghost w4 = e.bw.bits();
    proof { lemma_dparams0(w4, s4); lemma_bits_of(0, 6); }
    e.bw.put(0, 6);
    let ghost s5 = St { phase: Phase::CModes, pos: s4.pos + 6, npostfix: 0, ndirect: 0, cmodes: Seq::empty(), ..s4 };
    proof { lemma_adv(w4, fld(0, 6), s4, s5, e.bw.bits()); }
    // Context mode 0 (LSB6).
    let ghost w5 = e.bw.bits();
    proof { lemma_cmodes1(w5, s5, 0); lemma_bits_of(0, 2); }
    e.bw.put(0, 2);
    let ghost s6 = St { phase: Phase::CMap(0), pos: s5.pos + 2, cmodes: seq![0u8], cm: cm_init(), ..s5 };
    proof { lemma_adv(w5, fld(0, 2), s5, s6, e.bw.bits()); }
    // One literal tree, one distance tree.
    let ghost w6 = e.bw.bits();
    proof { lemma_cmap1(w6, s6, 0); }
    e.bw.put(0, 1);
    let ghost s7 = St { phase: Phase::CMap(1), pos: s6.pos + 1, cmap: zeros(64), ntl: 1, cm: cm_init(), ..s6 };
    proof {
        assert(Seq::new(cmap_size(s6, 0) as nat, |i: int| 0u8) =~= zeros(64));
        lemma_adv(w6, fld(0, 1), s6, s7, e.bw.bits());
    }
    let ghost w7 = e.bw.bits();
    proof { lemma_cmap1(w7, s7, 1); }
    e.bw.put(0, 1);
    let ghost s8 = St { phase: Phase::Trees(0), pos: s7.pos + 1, dmap: zeros(4), ntd: 1, cm: cm_init(), pc: pc_init(), ..s7 };
    proof {
        assert(Seq::new(cmap_size(s7, 1) as nat, |i: int| 0u8) =~= zeros(4));
        lemma_adv(w7, fld(0, 1), s7, s8, e.bw.bits());
    }
    // The trees.
    let ghost w8 = e.bw.bits();
    put_tree(&mut e.bw, lp, 256, Ghost(s8), Ghost(0), Ghost(l));
    let ghost s9 = tree_fin(s8, 0, l, e.bw.bits().len() as int);
    proof {
        lemma_adv(w8, e.bw.bits().subrange(w8.len() as int, e.bw.bits().len() as int), s8, s9, e.bw.bits());
        lemma_trees_next(e.bw.bits(), s9, 0);
        assert(e.bw.bits() + Seq::<nat>::empty() =~= e.bw.bits());
    }
    let ghost s10 = St { phase: Phase::Trees(1), pc: pc_init(), ..s9 };
    proof { lemma_adv(e.bw.bits(), Seq::empty(), s9, s10, e.bw.bits()); }
    let ghost w10 = e.bw.bits();
    put_tree(&mut e.bw, cp, 704, Ghost(s10), Ghost(1), Ghost(c));
    let ghost s11 = tree_fin(s10, 1, c, e.bw.bits().len() as int);
    proof {
        lemma_adv(w10, e.bw.bits().subrange(w10.len() as int, e.bw.bits().len() as int), s10, s11, e.bw.bits());
        lemma_trees_next(e.bw.bits(), s11, 1);
        assert(e.bw.bits() + Seq::<nat>::empty() =~= e.bw.bits());
    }
    let ghost s12 = St { phase: Phase::Trees(2), pc: pc_init(), ..s11 };
    proof {
        lemma_adv(e.bw.bits(), Seq::empty(), s11, s12, e.bw.bits());
        assert(dist_alpha(0, 0) == 64);
    }
    let ghost w12 = e.bw.bits();
    put_tree(&mut e.bw, dp, 64, Ghost(s12), Ghost(2), Ghost(d));
    let ghost s13 = tree_fin(s12, 2, d, e.bw.bits().len() as int);
    proof {
        lemma_adv(w12, e.bw.bits().subrange(w12.len() as int, e.bw.bits().len() as int), s12, s13, e.bw.bits());
        lemma_trees_next(e.bw.bits(), s13, 2);
        assert(e.bw.bits() + Seq::<nat>::empty() =~= e.bw.bits());
    }
    let ghost s14 = St { phase: Phase::CmdBegin, ..s13 };
    proof {
        lemma_adv(e.bw.bits(), Seq::empty(), s13, s14, e.bw.bits());
        assert(s14.lit =~= seq![l]);
        assert(s14.cmd =~= seq![c]);
        assert(s14.dst =~= seq![d]);
    }
    e.st = Ghost(s14);
}


/// The insert and copy length codes of symbol `sym`.
#[inline(always)]
pub fn sym_codes(sym: u16) -> (r: (usize, usize))
    requires
        sym < 704,
    ensures
        r.0 == ins_code(sym as int),
        r.1 == cpy_code(sym as int),
        r.0 < 24,
        r.1 < 24,
{
    proof {
        lemma_codes_range(sym as int);
    }
    let cell = CELL[(sym / 64) as usize] as usize;
    let s = sym as usize;
    ((cell / 8) * 8 + (s / 8) % 8, (cell % 4) * 8 + s % 8)
}

/// The literals `data[q..p]` of a command.
#[verifier::spinoff_prover]
fn put_lits(bw: &mut BitWriter, data: &[u8], q: usize, p: usize, lh: &HCode, Ghost(s1): Ghost<St>) -> (r: Ghost<St>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s1),
        s1.phase is Insert,
        q < p <= data@.len(),
        s1.ilen == p - q,
        s1.out == data@.subrange(0, q as int),
        s1.mrem >= p - q,
        s1.blen.len() == 3,
        s1.blen[0] >= p - q,
        s1.cmap == zeros(64),
        s1.bt[0] == 0,
        s1.cmodes == seq![0u8],
        s1.lit == seq![lh.lens@],
        lh.ok(),
        lits_coded(lh.lens@, data@, q as int, p as int),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        good(final(bw).bits(), r@),
        r@ == after_lits(s1, data@.subrange(q as int, p as int), final(bw).bits().len() as int),
        r@.out == data@.subrange(0, p as int),
{
    let ghost l = lh.lens@;
    let ghost w1 = bw.bits();
    let mut k = q;
    while k < p
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            q <= k <= p,
            p <= data@.len(),
            lh.ok(),
            l == lh.lens@,
            lits_coded(l, data@, q as int, p as int),
            bw.bits() == w1 + lb(l, data@.subrange(q as int, k as int)),
        decreases p - k,
    {
        let b = data[k];
        proof {
            assert(coded(l, data@[k as int] as int));
        }
        let (v, n) = lh.sym(b as usize);
        bw.put64(v, n);
        proof {
            lemma_lb_push(l, data@.subrange(q as int, k as int), b);
            assert(data@.subrange(q as int, k + 1) =~= data@.subrange(q as int, k as int).push(b));
        }
        k = k + 1;
    }
    let ghost dd = data@.subrange(q as int, p as int);
    proof {
        assert forall|k: int| 0 <= k < dd.len() implies #[trigger] coded(l, dd[k] as int) by {
            assert(dd[k] == data@[q + k]);
        }
        assert(lm(s1).lit == seq![l]);
        lemma_lits_single(lm(s1), s1.out, dd, l);
        lemma_lits(w1, s1, dd);
        lemma_adv(w1, lb(l, dd), s1, after_lits(s1, dd, bw.bits().len() as int), bw.bits());
        assert(s1.out + dd =~= data@.subrange(0, p as int));
    }
    Ghost(after_lits(s1, dd, bw.bits().len() as int))
}

/// The distance of command `x`.
#[verifier::spinoff_prover]
fn put_dist(bw: &mut BitWriter, x: &Cmd, dr: &mut [u32; 4], dh: &HCode, Ghost(s2): Ghost<St>) -> (r: Ghost<St>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s2),
        s2.phase is Dist,
        s2.implicit == (x.sym < 128),
        0 <= s2.dctx < 4,
        s2.dr == drs(*old(dr)),
        copy_ok(s2, x.dist as int),
        cdist(*x, s2.dr) == x.dist,
        x.sym >= 128 ==> coded(dh.lens@, x.dcode as int) && (x.extra as nat) < pow2(dext(x.dcode as int)),
        dh.ok(),
        dh.lens@.len() == 64,
        s2.dst == seq![dh.lens@],
        s2.dmap == zeros(4),
        s2.bt.len() == 3,
        s2.bt[2] == 0,
        s2.npostfix == 0,
        s2.ndirect == 0,
        s2.blen.len() == 3,
        s2.blen[2] >= 1,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        good(final(bw).bits(), r@),
        drs(*final(dr)) == cdr(*x, s2.dr),
        r@ == (St { phase: Phase::Copy, pos: r@.pos, blen: r@.blen, dist: x.dist as int, dr: drs(*final(dr)), ..s2 }),
        r@.blen.len() == 3,
        r@.blen[0] == s2.blen[0],
        r@.blen[1] == s2.blen[1],
        r@.blen[2] >= s2.blen[2] - 1,
{
    let ghost d = dh.lens@;
    let ghost w2 = bw.bits();
    let dist = x.dist;
    if x.sym < 128 {
        proof {
            lemma_dist_implicit(w2, s2);
            assert(w2 + Seq::<nat>::empty() =~= w2);
            lemma_adv(w2, Seq::empty(), s2, St { phase: Phase::Copy, dist: s2.dr[0], ..s2 }, bw.bits());
        }
        Ghost(St { phase: Phase::Copy, dist: s2.dr[0], ..s2 })
    } else {
        let dcode = x.dcode;
        proof {
            assert(dtree(s2) == 0);
            lemma_dist_explicit(w2, s2, dcode as int, x.extra as int);
        }
        let (dv, dn) = dh.sym(dcode as usize);
        bw.put64(dv, dn);
        let ne: u32 = if dcode < 16 { 0 } else { 1 + (dcode as u32 - 16) / 2 };
        proof {
            lemma_pow2_small();
            assert(ne == dext(dcode as int));
        }
        bw.put(x.extra, ne);
        let ghost t = St {
            phase: Phase::Copy,
            pos: bw.bits().len() as int,
            blen: s2.blen.update(2, s2.blen[2] - 1),
            dist: dval(dcode as int, x.extra as int, s2.dr),
            dr: dnext(dcode as int, dval(dcode as int, x.extra as int, s2.dr), s2.dr),
            ..s2
        };
        proof {
            assert(bw.bits() =~= w2 + dist_bits(d, dcode as int, x.extra as int));
            lemma_adv(w2, dist_bits(d, dcode as int, x.extra as int), s2, t, bw.bits());
        }
        if dcode != 0 {
            let d1 = dr[0];
            let d2 = dr[1];
            let d3 = dr[2];
            *dr = [dist, d1, d2, d3];
        }
        proof {
            assert(drs(*dr) =~= t.dr);
        }
        Ghost(t)
    }
}

/// The insert and copy length codes of any symbol (0 past the alphabet).
pub fn sym_codes_safe(sym: u16) -> (r: (usize, usize))
    ensures
        r.0 < 24,
        r.1 < 24,
{
    if sym < 704 { sym_codes(sym) } else { (0, 0) }
}

/// Writes command `cs[0]`, at `q`, from the state `s`; returns where the
/// next command starts and its state.
#[verifier::spinoff_prover]
pub fn put_cmd(bw: &mut BitWriter, data: &[u8], q: usize, end: usize, x: &Cmd, dr: &mut [u32; 4], lh: &HCode, ch: &HCode, dh: &HCode, wb: u32,
    Ghost(s): Ghost<St>, Ghost(cs): Ghost<Seq<Cmd>>, Ghost(dro): Ghost<Seq<int>>) -> (r: (usize, Ghost<St>))
    requires
        old(bw).wf(),
        good(old(bw).bits(), s),
        s.phase is CmdBegin,
        cstate(s, data@, q as int, end as int, wb as int, drs(*old(dr)), lh.lens@, ch.lens@, dh.lens@),
        lh.ok(),
        ch.ok(),
        dh.ok(),
        dh.lens@.len() == 64,
        end <= data@.len(),
        cs.len() >= 1,
        cs[0] == *x,
        cmds_ok(data@, q as int, end as int, cs, drs(*old(dr)), dro, wb as int, lh.lens@, ch.lens@, dh.lens@),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        good(final(bw).bits(), r.1@),
        q < r.0 <= end,
        cstate(r.1@, data@, r.0 as int, end as int, wb as int, drs(*final(dr)), lh.lens@, ch.lens@, dh.lens@),
        if r.0 == end { r.1@.phase is MetaDone } else { r.1@.phase is CmdBegin },
        cmds_ok(data@, r.0 as int, end as int, cs.subrange(1, cs.len() as int), drs(*final(dr)), dro, wb as int, lh.lens@, ch.lens@, dh.lens@),
{
    let ghost l = lh.lens@;
    let ghost c = ch.lens@;
    let ghost d = dh.lens@;
    let ghost dr0 = drs(*dr);
    let ghost w0 = bw.bits();
    let sym = x.sym;
    let ilen = x.ins;
    let clen = x.clen;
    proof {
        assert(one_ok(data@, q as int, end as int, cs[0], dr0, cs.len() == 1, wb as int, l, c, d));
        assert(s.cmd[s.bt[1]] == c);
        lemma_cmd(w0, s, sym as int, ilen as int, clen as int);
    }
    let (ic, cc) = sym_codes(sym);
    let (cv, cn) = ch.sym(sym as usize);
    bw.put64(cv, cn);
    proof {
        crate::mblock::lemma_tables_small();
        crate::mblock::lemma_shl1_24();
    }
    bw.put(ilen - INS_BASE[ic], INS_EXTRA[ic] as u32);
    bw.put(clen - CPY_BASE[cc], CPY_EXTRA[cc] as u32);
    let ghost s1 = after_cmd(s, sym as int, ilen as int, clen as int, bw.bits().len() as int);
    proof {
        assert(bw.bits() =~= w0 + cmd_bits(c, sym as int, ilen as int, clen as int));
        lemma_adv(w0, cmd_bits(c, sym as int, ilen as int, clen as int), s, s1, bw.bits());
    }
    let p = q + ilen as usize;
    let ghost mut st = s1;
    if ilen > 0 {
        let g = put_lits(bw, data, q, p, lh, Ghost(s1));
        proof {
            st = g@;
        }
    }
    if p == end {
        proof {
            assert(cs.subrange(1, cs.len() as int) =~= Seq::<Cmd>::empty());
        }
        return (p, Ghost(st));
    }
    proof {
        assert(CPY_BASE[cpy_code(sym as int)] >= 2);
    }
    let g = put_dist(bw, x, dr, dh, Ghost(st));
    // The copy.
    let ghost s3 = g@;
    let ghost s4 = St { phase: after_data(s3.mrem - s3.clen), out: data@.subrange(0, p + s3.clen), clen: 0, mrem: s3.mrem - s3.clen, ..s3 };
    proof {
        lemma_copy(bw.bits(), s3, data@, p as int);
        assert(bw.bits() + Seq::<nat>::empty() =~= bw.bits());
        lemma_adv(bw.bits(), Seq::empty(), s3, s4, bw.bits());
    }
    (p + clen as usize, Ghost(s4))
}


pub open spec fn links(qs: Seq<int>, ds: Seq<Seq<int>>, cs: Seq<Cmd>, end: int, i: int) -> bool {
    forall|k: int| 0 <= k < i ==> qs[k + 1] == #[trigger] nq(qs[k], cs[k], end) && ds[k + 1] == ndr(qs[k], cs[k], end, ds[k])
}

pub open spec fn ok_at(data: Seq<u8>, q: int, end: int, cs: Seq<Cmd>, k: int, dr: Seq<int>, wb: int, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> bool {
    one_ok(data, q, end, cs[k], dr, k + 1 == cs.len(), wb, l, c, d)
}

/// `cs[j..]` from `qs[j]`, given each command's own check.
proof fn lemma_cmds_back(data: Seq<u8>, end: int, cs: Seq<Cmd>, qs: Seq<int>, ds: Seq<Seq<int>>, dro: Seq<int>, wb: int, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>, j: int)
    requires
        0 <= j <= cs.len(),
        qs.len() == cs.len() + 1,
        ds.len() == cs.len() + 1,
        qs[cs.len() as int] == end,
        ds[cs.len() as int] == dro,
        forall|k: int| 0 <= k < cs.len() ==> #[trigger] ok_at(data, qs[k], end, cs, k, ds[k], wb, l, c, d),
        links(qs, ds, cs, end, cs.len() as int),
    ensures
        cmds_ok(data, qs[j], end, cs.subrange(j, cs.len() as int), ds[j], dro, wb, l, c, d),
    decreases cs.len() - j,
{
    let n = cs.len() as int;
    if j < n {
        lemma_cmds_back(data, end, cs, qs, ds, dro, wb, l, c, d, j + 1);
        let t = cs.subrange(j, n);
        assert(t[0] == cs[j]);
        assert(t.subrange(1, t.len() as int) =~= cs.subrange(j + 1, n));
        assert(ok_at(data, qs[j], end, cs, j, ds[j], wb, l, c, d));
        assert(qs[j + 1] == nq(qs[j], cs[j], end));
    } else {
        assert(cs.subrange(j, n) =~= Seq::<Cmd>::empty());
    }
}

/// Symbol `x` has a code in `h`.
#[inline(always)]
fn has_code(h: &HCode, x: usize) -> (r: bool)
    requires
        h.ok(),
    ensures
        r ==> coded(h.lens@, x as int),
{
    x < h.lens.len() && h.lens[x] >= 1 && (h.nused != 1 || h.one == x)
}

/// Checks the commands of a meta-block before anything is written.
#[verifier::spinoff_prover]
pub fn check_cmds(data: &[u8], start: usize, end: usize, cmds: &[Cmd], dr0: [u32; 4], wb: u32, lh: &HCode, ch: &HCode, dh: &HCode) -> (r: Option<[u32; 4]>)
    requires
        lh.ok(),
        ch.ok(),
        dh.ok(),
        start <= end <= data@.len(),
        16 <= wb <= 24,
    ensures
        r matches Some(o) ==> cmds_ok(data@, start as int, end as int, cmds@, drs(dr0), drs(o), wb as int, lh.lens@, ch.lens@, dh.lens@),
{
    let ghost l = lh.lens@;
    let ghost c = ch.lens@;
    let ghost d = dh.lens@;
    let ghost cs = cmds@;
    let n = cmds.len();
    let mut i: usize = 0;
    let mut q = start;
    let mut dr = dr0;
    let ghost mut qs: Seq<int> = seq![start as int];
    let ghost mut ds: Seq<Seq<int>> = seq![drs(dr0)];
    proof {
        lemma_pow2_strictly_increases(4, wb as nat);
        lemma_pow2_small();
    }
    let wmax: u64 = crate::mblock::shl1(wb) - 16;
    proof {
        lemma_pow2_small();
        crate::mblock::lemma_tables_small();
        crate::mblock::lemma_shl1_24();
    }
    while i < n
        invariant
            lh.ok(),
            ch.ok(),
            dh.ok(),
            l == lh.lens@,
            c == ch.lens@,
            d == dh.lens@,
            cs == cmds@,
            n == cs.len(),
            end <= data@.len(),
            16 <= wb <= 24,
            wmax == pow2(wb as nat) - 16,
            forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594,
            forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118,
            forall|k: nat| k <= 24 ==> #[trigger] pow2(k) <= 0x100_0000,
            i <= n,
            qs.len() == i + 1,
            ds.len() == i + 1,
            qs[0] == start,
            ds[0] == drs(dr0),
            qs[i as int] == q,
            ds[i as int] == drs(dr),
            q <= end,
            forall|k: int| 0 <= k < i ==> #[trigger] ok_at(data@, qs[k], end as int, cs, k, ds[k], wb as int, l, c, d),
            links(qs, ds, cs, end as int, i as int),
        decreases n - i,
    {
        let x = &cmds[i];
        if q >= end || x.sym >= 704 || !has_code(ch, x.sym as usize) {
            return None;
        }
        let (ic, cc) = sym_codes(x.sym);
        let ilen = x.ins;
        let clen = x.clen;
        if ilen < INS_BASE[ic] || ilen as u64 >= INS_BASE[ic] as u64 + crate::mblock::shl1(INS_EXTRA[ic] as u32) {
            return None;
        }
        if clen < CPY_BASE[cc] || clen as u64 >= CPY_BASE[cc] as u64 + crate::mblock::shl1(CPY_EXTRA[cc] as u32) {
            return None;
        }
        if ilen as usize > end - q {
            return None;
        }
        let p = q + ilen as usize;
        let mut k = q;
        while k < p
            invariant
                lh.ok(),
                l == lh.lens@,
                q <= k <= p <= end <= data@.len(),
                lits_coded(l, data@, q as int, k as int),
            decreases p - k,
        {
            if !has_code(lh, data[k] as usize) {
                return None;
            }
            k = k + 1;
        }
        let ghost dri = drs(dr);
        if p == end {
            if i + 1 != n {
                return None;
            }
        } else {
            let dist = x.dist;
            if x.sym < 128 {
                if dr[0] != dist {
                    return None;
                }
            } else {
                let dcode = x.dcode;
                if !has_code(dh, dcode as usize) {
                    return None;
                }
                if dcode < 4 {
                    if x.extra != 0 || dr[dcode as usize] != dist {
                        return None;
                    }
                    proof {
                        lemma_pow2_small();
                        assert(dext(dcode as int) == 0);
                        assert((x.extra as nat) < pow2(dext(dcode as int)));
                    }
                } else if dcode < 16 {
                    return None;
                } else {
                    if dist < 1 || dist >= 0x100_0000 {
                        return None;
                    }
                    let (dc, ex, nb) = crate::mblock::dist_code(dist);
                    if dc != dcode || ex != x.extra {
                        return None;
                    }
                    proof {
                        assert((x.extra as nat) < pow2(dext(dcode as int)));
                    }
                }
            }
            if dist < 1 || dist as usize > p || dist as u64 > wmax {
                return None;
            }
            if clen as usize > end - p {
                return None;
            }
            let mut k: usize = 0;
            let cl = clen as usize;
            let ds_ = dist as usize;
            while k < cl
                invariant
                    p + cl <= end <= data@.len(),
                    1 <= ds_ <= p,
                    k <= cl,
                    matches(data@, p as int, ds_ as int, k as int),
                decreases cl - k,
            {
                if data[p + k] != data[p + k - ds_] {
                    return None;
                }
                k = k + 1;
            }
            if x.sym >= 128 && x.dcode != 0 {
                dr = [dist, dr[0], dr[1], dr[2]];
            }
            proof {
                assert(cdist(*x, dri) == dist);
                assert(drs(dr) =~= cdr(*x, dri));
                assert(max_distance(p as int, wb as int) == if (p as int) < wmax { p as int } else { wmax as int });
            }
        }
        let q2 = if p == end { end } else { p + clen as usize };
        proof {
            let pp = q + x.ins;
            assert(q < end);
            assert(coded(c, x.sym as int));
            assert(sym_fits(x.sym as int, x.ins as int, x.clen as int));
            assert(pp <= end);
            assert(lits_coded(l, data@, q as int, pp));
            if pp != end {
                assert(x.sym >= 128 ==> coded(d, x.dcode as int) && (x.extra as nat) < pow2(dext(x.dcode as int)));
                assert(cdist(*x, dri) == x.dist);
                assert(1 <= x.dist <= max_distance(pp, wb as int));
                assert(pp + x.clen <= end);
                assert(matches(data@, pp, x.dist as int, x.clen as int));
            }
            assert(one_ok(data@, q as int, end as int, cs[i as int], dri, i + 1 == n, wb as int, l, c, d));
            assert(ok_at(data@, q as int, end as int, cs, i as int, dri, wb as int, l, c, d));
            let qs0 = qs;
            let ds0 = ds;
            qs = qs.push(q2 as int);
            ds = ds.push(drs(dr));
            assert(cs[i as int] == *x);
            assert(qs[i + 1] == nq(qs[i as int], cs[i as int], end as int));
            assert(ds[i + 1] == ndr(qs[i as int], cs[i as int], end as int, ds[i as int]));
            assert forall|k: int| 0 <= k < i + 1 implies qs[k + 1] == #[trigger] nq(qs[k], cs[k], end as int) && ds[k + 1] == ndr(qs[k], cs[k], end as int, ds[k]) by {
                if k < i {
                    assert(links(qs0, ds0, cs, end as int, i as int));
                    assert(qs[k] == qs0[k] && qs[k + 1] == qs0[k + 1] && ds[k] == ds0[k] && ds[k + 1] == ds0[k + 1]);
                    assert(qs0[k + 1] == nq(qs0[k], cs[k], end as int));
                }
            }
            assert(links(qs, ds, cs, end as int, i + 1));
        }
        q = q2;
        i = i + 1;
    }
    if q != end {
        return None;
    }
    proof {
        lemma_cmds_back(data@, end as int, cs, qs, ds, drs(dr), wb as int, l, c, d, 0);
        assert(cs.subrange(0, n as int) =~= cs);
    }
    Some(dr)
}


/// Writes `data[start..end]` as one compressed meta-block from the commands
/// `cmds`, with codes `lh`, `ch`, `dh` (and their headers `lp`, `cp`,
/// `dp`), if the commands check out; otherwise writes nothing.
pub fn put_compressed(e: &mut Enc, dr: &mut [u32; 4], wb: u32, data: &[u8], start: usize, end: usize, cmds: &[Cmd],
    lh: &HCode, lp: &Plan, ch: &HCode, cp: &Plan, dh: &HCode, dp: &Plan) -> (r: bool)
    requires
        old(e).ok(),
        old(e).st@.phase is MetaHeader,
        old(e).st@.out == data@.subrange(0, start as int),
        old(e).st@.wbits == wb,
        old(e).st@.dr == drs(*old(dr)),
        16 <= wb <= 24,
        start < end <= data@.len(),
        end - start <= 0x100_0000,
        lh.ok(),
        ch.ok(),
        dh.ok(),
        dh.lens@.len() == 64,
        lp.ok(lh.lens@, 256),
        cp.ok(ch.lens@, 704),
        dp.ok(dh.lens@, 64),
    ensures
        final(e).ok(),
        final(e).bw.sent() == old(e).bw.sent(),
        final(e).st@.phase is MetaHeader,
        final(e).st@.wbits == wb,
        final(e).st@.dr == drs(*final(dr)),
        final(e).st@.out == if r { data@.subrange(0, end as int) } else { data@.subrange(0, start as int) },
{
    let ghost l = lh.lens@;
    let ghost c = ch.lens@;
    let ghost d = dh.lens@;
    let ghost cs = cmds@;
    let dro = match check_cmds(data, start, end, cmds, *dr, wb, lh, ch, dh) {
        Some(o) => o,
        None => return false,
    };
    put_cheader(e, end - start, lp, cp, dp, Ghost(l), Ghost(c), Ghost(d));
    let ghost mut st = e.st@;
    let mut q = start;
    let mut i: usize = 0;
    let n = cmds.len();
    proof {
        assert(cs.subrange(0, n as int) =~= cs);
    }
    while q < end
        invariant
            e.bw.wf(),
            e.bw.sent() == old(e).bw.sent(),
            good(e.bw.bits(), st),
            lh.ok(),
            ch.ok(),
            dh.ok(),
            dh.lens@.len() == 64,
            l == lh.lens@,
            c == ch.lens@,
            d == dh.lens@,
            cs == cmds@,
            n == cs.len(),
            end <= data@.len(),
            i <= n,
            start <= q <= end,
            cstate(st, data@, q as int, end as int, wb as int, drs(*dr), l, c, d),
            if q == end { st.phase is MetaDone } else { st.phase is CmdBegin },
            cmds_ok(data@, q as int, end as int, cs.subrange(i as int, n as int), drs(*dr), drs(dro), wb as int, l, c, d),
        decreases end - q,
    {
        if i >= n {
            proof {
                assert(cs.subrange(i as int, n as int) =~= Seq::<Cmd>::empty());
            }
            return false; // unreachable
        }
        let ghost sub = cs.subrange(i as int, n as int);
        proof {
            assert(sub[0] == cmds@[i as int]);
        }
        let (q2, g) = put_cmd(&mut e.bw, data, q, end, &cmds[i], dr, lh, ch, dh, wb, Ghost(st), Ghost(sub), Ghost(drs(dro)));
        proof {
            assert(sub.subrange(1, sub.len() as int) =~= cs.subrange(i + 1, n as int));
            st = g@;
        }
        q = q2;
        i = i + 1;
    }
    let ghost w = e.bw.bits();
    proof {
        lemma_meta_done(w, st);
        assert(w + Seq::<nat>::empty() =~= w);
        lemma_adv(w, Seq::empty(), st, St { phase: Phase::MetaHeader, ..st }, w);
    }
    e.st = Ghost(St { phase: Phase::MetaHeader, ..st });
    true
}

} // verus!
