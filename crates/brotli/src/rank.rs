//! A ranking of the spec's states that every step of a well-formed decoder
//! state strictly lowers. It is what makes streaming terminate: a call to
//! `Stream::decompress` either makes the decoder take a step, which lowers
//! the rank, or hands out output or takes input.
//!
//! The rank is lexicographic: the input bits left, then how far the phase
//! is from the end of its meta-block, then numbers that count down inside
//! the phase (bytes of the meta-block left, block count of the commands,
//! code lengths or context map entries left to read).
use crate::decoder::*;
use crate::spec::*;
#[cfg(verus_only)]
use crate::huffman::hcode_ok;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

/// Larger than every count the ranking compares.
pub open spec fn big() -> int {
    0x100_0000_0000
}

/// `x`, cut to `0 .. big()`.
pub open spec fn cl(x: int) -> int {
    if x < 0 {
        0
    } else if x >= big() {
        big() - 1
    } else {
        x
    }
}

/// Code lengths left to read in a prefix code.
pub open spec fn pc_rank(pc: Pc, alpha: int) -> int {
    if pc.started {
        cl(alpha - pc.lens.len())
    } else {
        0
    }
}

/// The phases, ordered so that a step that reads no bits goes down.
pub open spec fn prank(p: Phase) -> int {
    match p {
        Phase::NBlockTypes(_) => 17,
        Phase::BTypeCode(_) => 16,
        Phase::BCountCode(_) => 15,
        Phase::BCount(_) => 14,
        Phase::DistParams => 13,
        Phase::CModes => 12,
        Phase::CMap(w) => cl(10 - w),
        Phase::Trees(g) => cl(8 - g),
        Phase::CmdBegin | Phase::Insert | Phase::Dist | Phase::Copy => 5,
        Phase::Metadata | Phase::Uncompressed => 3,
        Phase::MetaDone => 2,
        Phase::MetaHeader => 1,
        _ => 0,
    }
}

/// What counts down inside the phase.
pub open spec fn xr(s: St) -> (int, int, int) {
    match s.phase {
        Phase::BTypeCode(_) | Phase::BCountCode(_) => (pc_rank(s.pc, pc_alpha(s)), 0, 0),
        Phase::CMap(w) => (
            cl(3 - s.cm.stage),
            cl(cmap_size(s, w) - s.cm.map.len()),
            pc_rank(s.pc, pc_alpha(s)),
        ),
        Phase::Trees(g) => (cl(ntrees(s, g) - nread(s, g)), pc_rank(s.pc, pc_alpha(s)), 0),
        Phase::CmdBegin => (cl(s.mrem), cl(s.blen[1]), 1),
        Phase::Insert => (cl(s.mrem), cl(s.blen[1]), 0),
        Phase::Dist => (cl(s.mrem), cl(s.blen[1]), 2),
        Phase::Copy => (cl(s.mrem), cl(s.blen[1]), 1),
        _ => (0, 0, 0),
    }
}

/// Input bits left.
pub open spec fn bl(b: Seq<u8>, s: St) -> int {
    if nbits(b) - s.pos < 0 {
        0
    } else {
        nbits(b) - s.pos
    }
}

pub open spec fn rk(b: Seq<u8>, s: St) -> (int, int, int, int, int) {
    (bl(b, s), prank(s.phase), xr(s).0, xr(s).1, xr(s).2)
}

pub open spec fn lex_lt(a: (int, int, int, int, int), c: (int, int, int, int, int)) -> bool {
    a.0 < c.0 || (a.0 == c.0 && (a.1 < c.1 || (a.1 == c.1 && (a.2 < c.2 || (a.2 == c.2 && (a.3
        < c.3 || (a.3 == c.3 && a.4 < c.4)))))))
}

/// `t` ranks below `s`.
pub open spec fn rank_lt(b: Seq<u8>, t: St, s: St) -> bool {
    lex_lt(rk(b, t), rk(b, s))
}

pub proof fn lemma_rank_trans(b: Seq<u8>, a: St, m: St, c: St)
    requires
        rank_lt(b, a, m),
        rank_lt(b, m, c),
    ensures
        rank_lt(b, a, c),
{
}

/// Reading from `pos` ended at `p`: nothing read, or bits that are there.
pub open spec fn adv(b: Seq<u8>, pos: int, p: int) -> bool {
    p == pos || (pos < p && p <= nbits(b))
}

/// Bits were read.
pub open spec fn fwd(b: Seq<u8>, pos: int, p: int) -> bool {
    pos < p && p <= nbits(b)
}

pub proof fn lemma_fwd_rank(b: Seq<u8>, s: St, t: St)
    requires
        fwd(b, s.pos, t.pos),
    ensures
        rank_lt(b, t, s),
{
}

// ---------------------------------------------------------------------------
// Readers
// ---------------------------------------------------------------------------

pub proof fn lemma_decode_from(lens: Seq<u8>, b: Seq<u8>, pos: int, l: nat)
    requires
        l >= 1,
    ensures
        decode_from(lens, b, pos, l) matches Some((s, k)) ==> l <= k && pos + k <= nbits(b) && s
            < lens.len(),
    decreases MAX_BITS + 1 - l,
{
    if l > MAX_BITS || pos + l > nbits(b) {
    } else {
        let v = code_bits(b, pos, l);
        let f = first_code(lens, l);
        if f <= v && v < f + count(lens, l) {
            assert(count_below(lens, l, 0) == 0);
            crate::huffman::lemma_nth_bound(lens, l, (v - f) as nat, 0);
        } else {
            lemma_decode_from(lens, b, pos, l + 1);
        }
    }
}

pub proof fn lemma_rsym(lens: Seq<u8>, b: Seq<u8>, pos: int)
    ensures
        rsym(lens, b, pos) matches R::Ok(sym, p) ==> adv(b, pos, p) && if used(lens) == 1 {
            p == pos && sym == first_used(lens, 0)
        } else {
            pos < p && 0 <= sym < lens.len()
        },
{
    if used(lens) != 1 {
        lemma_decode_from(lens, b, pos, 1);
    }
}

pub proof fn lemma_varlen8(b: Seq<u8>, pos: int)
    ensures
        varlen8(b, pos) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
}

pub proof fn lemma_wbits(b: Seq<u8>, pos: int)
    ensures
        read_wbits(b, pos) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
}

pub proof fn lemma_pad(b: Seq<u8>, pos: int)
    ensures
        pad(b, pos) matches R::Ok(_, p) ==> pos <= p <= nbits(b),
{
}

pub proof fn lemma_meta_len(b: Seq<u8>, pos: int, last: bool)
    ensures
        read_meta_len(b, pos, last) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
    match rd(b, pos, 2) {
        Some(mn) => {
            if mn == 3 {
                match rd(b, pos + 3, 2) {
                    Some(nbytes) => {
                        lemma_pad(b, pos + 5);
                        lemma_pad(b, pos + 5 + 8 * nbytes);
                    },
                    None => {},
                }
            } else {
                lemma_pad(b, pos + 2 + 4 * (mn + 4) + 1);
            }
        },
        None => {},
    }
}

pub proof fn lemma_meta_header(b: Seq<u8>, pos: int)
    ensures
        read_meta_header(b, pos) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
    lemma_meta_len(b, pos + 1, false);
    lemma_meta_len(b, pos + 2, true);
}

pub proof fn lemma_clcl(b: Seq<u8>, pos: int)
    ensures
        read_clcl(b, pos) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
}

pub proof fn lemma_read_cl(b: Seq<u8>, pos: int, i: int, c: Seq<u8>, num: int, space: int)
    ensures
        read_cl(b, pos, i, c, num, space) matches R::Ok(_, p) ==> adv(b, pos, p),
    decreases 18 - i,
{
    if i >= 18 || i < 0 {
    } else {
        lemma_clcl(b, pos);
        match read_clcl(b, pos) {
            R::Ok(v, p) => {
                let cl2 = c.update(CL_ORDER[i] as int, v as u8);
                if v != 0 {
                    lemma_read_cl(b, p, i + 1, cl2, num + 1, space - pow2((5 - v) as nat));
                } else {
                    lemma_read_cl(b, p, i + 1, cl2, num, space);
                }
            },
            _ => {},
        }
    }
}

pub proof fn lemma_simple_syms(b: Seq<u8>, pos: int, n: int, w: nat, alpha: int)
    ensures
        read_simple_syms(b, pos, n, w, alpha) matches R::Ok(_, p) ==> p == pos || (pos <= p && p
            <= nbits(b)),
    decreases n,
{
    if n > 0 {
        lemma_simple_syms(b, pos + w, n - 1, w, alpha);
    }
}

pub proof fn lemma_read_simple(b: Seq<u8>, pos: int, alpha: int)
    ensures
        read_simple(b, pos, alpha) matches PcRes::Fin(_, p) ==> fwd(b, pos, p),
        !(read_simple(b, pos, alpha) is Cont),
{
    match rd(b, pos, 2) {
        Some(nm1) => {
            lemma_simple_syms(b, pos + 2, nm1 + 1, bitlen((alpha - 1) as nat), alpha);
        },
        None => {},
    }
}

/// A step of reading a prefix code: either it reads bits, or it adds a
/// code length to a code already started.
pub proof fn lemma_pc_step(b: Seq<u8>, pos: int, pc: Pc, alpha: int)
    ensures
        match pc_step(b, pos, pc, alpha) {
            PcRes::Cont(pc2, p) => adv(b, pos, p) && (p == pos ==> pc.started && pc2.started
                && pc.lens.len() < pc2.lens.len() < alpha),
            PcRes::Fin(_, p) => adv(b, pos, p),
            _ => true,
        },
{
    if !pc.started {
        match rd(b, pos, 2) {
            Some(hskip) => {
                if hskip == 1 {
                    lemma_read_simple(b, pos + 2, alpha);
                } else {
                    lemma_read_cl(b, pos + 2, hskip as int, Seq::new(18, |i: int| 0u8), 0, 32);
                }
            },
            None => {},
        }
    } else {
        lemma_rsym(pc.cl, b, pos);
    }
}

/// A block count reads bits: at least two extra bits whatever the symbol.
pub proof fn lemma_read_blen(code: Seq<u8>, b: Seq<u8>, pos: int)
    requires
        code.len() == 26,
        used(code) == 1 ==> 0 <= first_used(code, 0) < 26,
    ensures
        read_blen(code, b, pos) matches R::Ok(_, p) ==> fwd(b, pos, p),
{
    lemma_rsym(code, b, pos);
    assert(forall|i: int| 0 <= i < 26 ==> #[trigger] BLEN_EXTRA[i] >= 2) by (compute);
}

/// What a backward copy or dictionary reference changes.
pub proof fn lemma_resolve(s: St, d: int, last: bool)
    ensures
        resolve(s, d, last) matches Step::Next(t) ==> {
            &&& t.pos == s.pos
            &&& t.blen == s.blen
            &&& if t.phase is Copy {
                t.mrem == s.mrem
            } else {
                0 <= t.mrem <= s.mrem && t.phase == after_data(t.mrem)
            }
        },
{
    reveal(resolve);
}

// ---------------------------------------------------------------------------
// One step
// ---------------------------------------------------------------------------

/// A block switch reads bits.
pub proof fn lemma_switch_rank(b: Seq<u8>, d: Decoder, c: int)
    requires
        d.wf(),
        stage(d.ph) == 30,
        0 <= c < 3,
    ensures
        block_switch(d.view(), b, c) matches Step::Next(t) ==> fwd(b, d.pos as int, t.pos),
{
    let s = d.view();
    reveal(cat_ok);
    if s.nbt[c] >= 2 {
        lemma_rsym(s.btc[c], b, s.pos);
        match rsym(s.btc[c], b, s.pos) {
            R::Ok(_, p) => {
                assert(hcode_ok(d.bcc@[c], d.bccl@[c]));
                lemma_read_blen(s.bcc[c], b, p);
            },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rank_header(b: Seq<u8>, d: Decoder)
    requires
        d.wf(),
        stage(d.ph) < 30,
        !(d.ph is Done),
    ensures
        step(b, d.view()) matches Step::Next(t) ==> rank_lt(b, t, d.view()),
{
    let s = d.view();
    reveal(reading_ok);
    reveal(cat_ok);
    reveal(trees_ok);
    reveal(maps_ok);
    match d.ph {
        Ph::WBits => {
            lemma_step_wbits(b, s);
            lemma_wbits(b, s.pos);
        },
        Ph::MetaHeader => {
            lemma_step_header(b, s);
            lemma_meta_header(b, s.pos);
            match read_meta_header(b, s.pos) {
                R::Ok(h, p) => {
                    lemma_pad(b, p);
                },
                _ => {},
            }
        },
        Ph::Metadata => {
            lemma_step_metadata(b, s);
        },
        Ph::Uncompressed => {
            lemma_step_raw(b, s);
        },
        Ph::MetaDone => {
            lemma_step_metadone(b, s);
            lemma_pad(b, s.pos);
        },
        Ph::NBlockTypes(c) => {
            lemma_step_nbt(b, s, c as int);
            lemma_varlen8(b, s.pos);
        },
        Ph::BTypeCode(c) => {
            lemma_step_code(b, s);
            lemma_pc_step(b, s.pos, s.pc, pc_alpha(s));
        },
        Ph::BCountCode(c) => {
            lemma_step_code(b, s);
            lemma_pc_step(b, s.pos, s.pc, pc_alpha(s));
        },
        Ph::BCount(c) => {
            lemma_step_bcount(b, s, c as int);
            assert(hcode_ok(d.bcc@[c as int], d.bccl@[c as int]));
            lemma_read_blen(s.bcc[c as int], b, s.pos);
        },
        Ph::DistParams => {
            lemma_step_dparams(b, s);
        },
        Ph::CModes => {
            lemma_step_cmodes(b, s);
        },
        Ph::CMap(w) => {
            lemma_step_cmap(b, s, w as int);
            lemma_rank_cmap(b, d, w as int);
        },
        Ph::Trees(g) => {
            lemma_step_trees(b, s, g as int);
            lemma_pc_step(b, s.pos, s.pc, pc_alpha(s));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rank_cmap(b: Seq<u8>, d: Decoder, w: int)
    requires
        d.wf(),
        d.ph == Ph::CMap(w as u8),
        0 <= w < 2,
    ensures
        cmap_step(b, d.view(), w) matches Step::Next(t) ==> rank_lt(b, t, d.view()),
{
    let s = d.view();
    reveal(reading_ok);
    reveal(cat_ok);
    reveal(maps_ok);
    let cm = s.cm;
    if cm.stage == 0 {
        lemma_varlen8(b, s.pos);
    } else if cm.stage == 1 {
        lemma_pc_step(b, s.pos, s.pc, pc_alpha(s));
    } else if cm.stage == 2 {
        assert(hcode_ok(d.cm.code, d.cm.lens@));
        assert(1 <= s.nbt[0] <= 256 && 1 <= s.nbt[2] <= 256);
        if cm.map.len() < cmap_size(s, w) {
            lemma_rsym(cm.code, b, s.pos);
            match rsym(cm.code, b, s.pos) {
                R::Ok(sym, p) => {
                    assert(sym >= 0);
                    if sym == 0 {
                        let t = St { pos: p, cm: Cm { map: cm.map.push(0), ..cm }, ..s };
                        assert(t.cm.map.len() == cm.map.len() + 1);
                        assert(cmap_size(t, w) == cmap_size(s, w));
                        assert(pc_alpha(t) == pc_alpha(s));
                        assert(xr(t).0 == xr(s).0);
                        assert(xr(t).1 < xr(s).1);
                        assert(prank(t.phase) == prank(s.phase));
                        if p == s.pos {
                            assert(bl(b, t) == bl(b, s));
                        } else {
                            assert(bl(b, t) < bl(b, s));
                        }
                        assert(rank_lt(b, t, s));
                    } else if sym > cm.rlemax {
                        assert(rank_lt(b, St { pos: p, cm: Cm { map: cm.map.push((sym - cm.rlemax) as u8), ..cm }, ..s }, s));
                    }
                },
                _ => {},
            }
        } else {
            assert(rank_lt(b, St { cm: Cm { stage: 3, ..cm }, ..s }, s));
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rank_data(b: Seq<u8>, d: Decoder)
    requires
        d.wf(),
        stage(d.ph) == 30,
    ensures
        step(b, d.view()) matches Step::Next(t) ==> rank_lt(b, t, d.view()),
{
    let s = d.view();
    reveal(cmd_ok);
    reveal(cat_ok);
    match d.ph {
        Ph::CmdBegin => {
            lemma_step_data(b, s);
            if s.blen[1] == 0 {
                lemma_switch_rank(b, d, 1);
            } else {
                lemma_rsym(s.cmd[s.bt[1]], b, s.pos);
            }
        },
        Ph::Insert => {
            lemma_step_data(b, s);
            if s.blen[0] == 0 {
                lemma_switch_rank(b, d, 0);
            } else {
                let t = s.bt[0];
                let ctx = lit_context(s.cmodes[t] as int, p1(s.out), p2(s.out));
                let tree = s.cmap[t * 64 + ctx] as int;
                lemma_rsym(s.lit[tree], b, s.pos);
            }
        },
        Ph::Dist => {
            lemma_step_data(b, s);
            lemma_rank_dist(b, d);
        },
        Ph::Copy => {
            lemma_step_copy(b, s);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rank_dist(b: Seq<u8>, d: Decoder)
    requires
        d.wf(),
        d.ph == Ph::Dist,
    ensures
        distance(b, d.view()) matches Step::Next(t) ==> rank_lt(b, t, d.view()),
{
    let s = d.view();
    reveal(cmd_ok);
    if s.implicit {
        lemma_resolve(s, s.dr[0], true);
    } else if s.blen[2] == 0 {
        lemma_switch_rank(b, d, 2);
    } else {
        let tree = s.dmap[s.bt[2] * 4 + s.dctx] as int;
        lemma_rsym(s.dst[tree], b, s.pos);
        match rsym(s.dst[tree], b, s.pos) {
            R::Ok(dcode, p) => {
                let s1 = St { pos: p, blen: s.blen.update(2, s.blen[2] - 1), ..s };
                if dcode < 16 {
                    lemma_resolve(s1, short_dist(dcode, s.dr), dcode == 0);
                } else if dcode < 16 + s.ndirect {
                    lemma_resolve(s1, dcode - 15, false);
                } else {
                    let n = dist_extra(dcode, s.npostfix, s.ndirect);
                    lemma_resolve(
                        St { pos: p + n, ..s1 },
                        dist_value(dcode, bits(b, p, n) as int, s.npostfix, s.ndirect),
                        false,
                    );
                }
            },
            _ => {},
        }
    }
}

/// Every step from a well-formed decoder state lowers the rank.
#[verifier::spinoff_prover]
pub proof fn lemma_rank1(b: Seq<u8>, d: Decoder)
    requires
        d.wf(),
        !(d.ph is Done),
    ensures
        step(b, d.view()) matches Step::Next(t) ==> rank_lt(b, t, d.view()),
{
    if stage(d.ph) == 30 {
        lemma_rank_data(b, d);
    } else {
        lemma_rank_header(b, d);
    }
}

/// Several data steps: the meta-block has fewer bytes left.
pub proof fn lemma_rank_bytes(b: Seq<u8>, s: St, t: St)
    requires
        s.phase is Insert || s.phase is Copy || s.phase is Dist || s.phase is CmdBegin,
        t.phase is Insert || t.phase is Copy || t.phase is Dist || t.phase is CmdBegin
            || t.phase is MetaDone,
        adv(b, s.pos, t.pos),
        0 <= t.mrem < s.mrem < big(),
    ensures
        rank_lt(b, t, s),
{
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Runs that end: the state a stream decodes to comes after every state
// reached on the way
// ---------------------------------------------------------------------------

/// Header steps keep the output.
#[verifier::spinoff_prover]
proof fn lemma_out_hdr(b: Seq<u8>, s: St)
    requires
        !(s.phase is Uncompressed || s.phase is CmdBegin || s.phase is Insert || s.phase is Dist
            || s.phase is Copy || s.phase is Done),
    ensures
        step(b, s) matches Step::Next(t) ==> t.out == s.out,
{
    match s.phase {
        Phase::WBits => lemma_step_wbits(b, s),
        Phase::MetaHeader => lemma_step_header(b, s),
        Phase::Metadata => lemma_step_metadata(b, s),
        Phase::NBlockTypes(c) => lemma_step_nbt(b, s, c),
        Phase::BTypeCode(_) | Phase::BCountCode(_) => lemma_step_code(b, s),
        Phase::BCount(c) => lemma_step_bcount(b, s, c),
        Phase::DistParams => lemma_step_dparams(b, s),
        Phase::CModes => lemma_step_cmodes(b, s),
        Phase::CMap(w) => lemma_step_cmap(b, s, w),
        Phase::Trees(g) => lemma_step_trees(b, s, g),
        Phase::MetaDone => lemma_step_metadone(b, s),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_out_switch(b: Seq<u8>, s: St, c: int)
    ensures
        block_switch(s, b, c) matches Step::Next(t) ==> t.out == s.out,
{
}

#[verifier::spinoff_prover]
proof fn lemma_out_resolve(s: St, d: int, last: bool)
    ensures
        resolve(s, d, last) matches Step::Next(t) ==> exists|w: Seq<u8>| t.out == s.out + w,
{
    reveal(resolve);
    if let Step::Next(t) = resolve(s, d, last) {
        if t.phase is Copy {
            assert(t.out == s.out + Seq::<u8>::empty());
        } else {
            let maxd = max_distance(s.out.len() as int, s.wbits);
            let len = s.clen;
            let addr = d - maxd - 1;
            let n = NDBITS[len] as nat;
            let w = transform(dict_word(len, addr % pow2(n) as int), addr / pow2(n) as int);
            assert(t.out == s.out + w);
        }
    }
}

/// Data steps add bytes.
#[verifier::spinoff_prover]
proof fn lemma_out_data(b: Seq<u8>, s: St)
    requires
        s.phase is CmdBegin || s.phase is Insert || s.phase is Dist,
    ensures
        step(b, s) matches Step::Next(t) ==> exists|w: Seq<u8>| t.out == s.out + w,
{
    lemma_step_data(b, s);
    match s.phase {
        Phase::CmdBegin => {
            lemma_out_switch(b, s, 1);
            if let Step::Next(t) = step(b, s) {
                assert(t.out == s.out + Seq::<u8>::empty());
            }
        },
        Phase::Insert => {
            lemma_out_switch(b, s, 0);
            if let Step::Next(t) = step(b, s) {
                if s.blen[0] == 0 {
                    assert(t.out == s.out + Seq::<u8>::empty());
                } else {
                    assert(t.out =~= s.out + seq![t.out.last()]);
                }
            }
        },
        _ => {
            lemma_out_switch(b, s, 2);
            lemma_out_dist(b, s);
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_out_dist(b: Seq<u8>, s: St)
    ensures
        distance(b, s) matches Step::Next(t) ==> exists|w: Seq<u8>| t.out == s.out + w,
{
    lemma_out_switch(b, s, 2);
    if s.implicit {
        lemma_out_resolve(s, s.dr[0], true);
    } else if s.blen[2] == 0 {
        if let Step::Next(t) = distance(b, s) {
            assert(t.out == s.out + Seq::<u8>::empty());
        }
    } else {
        let tree = s.dmap[s.bt[2] * 4 + s.dctx] as int;
        match rsym(s.dst[tree], b, s.pos) {
            R::Ok(dcode, p) => {
                let s1 = St { pos: p, blen: s.blen.update(2, s.blen[2] - 1), ..s };
                if dcode < 16 {
                    lemma_out_resolve(s1, short_dist(dcode, s.dr), dcode == 0);
                } else if dcode < 16 + s.ndirect {
                    lemma_out_resolve(s1, dcode - 15, false);
                } else {
                    let n = dist_extra(dcode, s.npostfix, s.ndirect);
                    lemma_out_resolve(
                        St { pos: p + n, ..s1 },
                        dist_value(dcode, bits(b, p, n) as int, s.npostfix, s.ndirect),
                        false,
                    );
                }
            },
            _ => {},
        }
    }
}

/// A step only adds output.
#[verifier::spinoff_prover]
pub proof fn lemma_step_out(b: Seq<u8>, s: St)
    ensures
        step(b, s) matches Step::Next(t) ==> s.out.is_prefix_of(t.out),
{
    assert forall|w: Seq<u8>| s.out.is_prefix_of(#[trigger] (s.out + w)) by {
        assert((s.out + w).subrange(0, s.out.len() as int) =~= s.out);
    }
    assert(s.out.subrange(0, s.out.len() as int) =~= s.out);
    if s.phase is Done {
        reveal(step);
    } else if s.phase is Uncompressed {
        lemma_step_raw(b, s);
        if let Step::Next(t) = step(b, s) {
            if s.mrem > 0 {
                assert(t.out =~= s.out + seq![t.out.last()]);
            }
        }
    } else if s.phase is Copy {
        lemma_step_copy(b, s);
        let x = s.out[s.out.len() - s.dist];
        assert(s.out.push(x) =~= s.out + seq![x]);
    } else if s.phase is CmdBegin || s.phase is Insert || s.phase is Dist {
        lemma_out_data(b, s);
    } else {
        lemma_out_hdr(b, s);
    }
}

pub proof fn lemma_prefix_trans3(a: Seq<u8>, m: Seq<u8>, c: Seq<u8>)
    requires
        a.is_prefix_of(m),
        m.is_prefix_of(c),
    ensures
        a.is_prefix_of(c),
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == c[i] by {
        assert(a[i] == m.subrange(0, a.len() as int)[i]);
        assert(m[i] == c.subrange(0, m.len() as int)[i]);
    }
    assert(a =~= c.subrange(0, a.len() as int));
}

/// A run only adds output.
pub proof fn lemma_run_out(b: Seq<u8>, s: St, n: nat)
    ensures
        run(b, s, n) matches Step::Next(t) ==> s.out.is_prefix_of(t.out),
    decreases n,
{
    if n == 0 || s.phase is Done {
        assert(s.out.subrange(0, s.out.len() as int) =~= s.out);
    } else {
        lemma_step_out(b, s);
        match step(b, s) {
            Step::Next(s1) => {
                lemma_run_out(b, s1, (n - 1) as nat);
                if let Step::Next(t) = run(b, s1, (n - 1) as nat) {
                    lemma_prefix_trans3(s.out, s1.out, t.out);
                }
            },
            _ => {},
        }
    }
}

/// `m + n` steps are `m` steps and then `n`.
pub proof fn lemma_run_split(b: Seq<u8>, s: St, m: nat, n: nat)
    ensures
        run(b, s, m + n) == match run(b, s, m) {
            Step::Next(t) => run(b, t, n),
            r => r,
        },
    decreases m,
{
    if m == 0 {
    } else if s.phase is Done {
        lemma_run_done(b, s, n);
        lemma_run_done(b, s, m + n);
    } else {
        match step(b, s) {
            Step::Next(s1) => {
                lemma_run_split(b, s1, (m - 1) as nat, n);
                assert((m + n - 1) as nat == (m - 1) as nat + n);
            },
            _ => {},
        }
    }
}

/// `Done` stays.
pub proof fn lemma_run_done(b: Seq<u8>, s: St, n: nat)
    requires
        s.phase is Done,
    ensures
        run(b, s, n) == Step::Next(s),
{
}

/// Where a stream that decodes is on the way: before the end, with part of
/// its output, and with a next step.
#[verifier::spinoff_prover]
pub proof fn lemma_on_way(b: Seq<u8>, k: nat, s: St, nn: nat, f: St)
    requires
        run(b, init(), k) == Step::Next(s),
        run(b, init(), nn) == Step::Next(f),
        f.phase is Done,
    ensures
        s.out.is_prefix_of(f.out),
        s.phase is Done ==> s == f,
        step(b, s) is Next,
{
    if s.phase is Done {
        reveal(step);
    }
    if k <= nn {
        lemma_run_split(b, init(), k, (nn - k) as nat);
        assert(k + (nn - k) as nat == nn);
        lemma_run_out(b, s, (nn - k) as nat);
        if s.phase is Done {
            lemma_run_done(b, s, (nn - k) as nat);
        } else if nn == k {
        } else {
            assert(run(b, s, (nn - k) as nat) is Next);
        }
    } else {
        lemma_run_split(b, init(), nn, (k - nn) as nat);
        assert(nn + (k - nn) as nat == k);
        lemma_run_done(b, f, (k - nn) as nat);
        assert(s.out.subrange(0, s.out.len() as int) =~= s.out);
    }
}

/// A stream that decodes is not rejected.
pub proof fn lemma_decodes_not_rejects(b: Seq<u8>, out: Seq<u8>, used: int)
    requires
        decodes(b, out, used),
    ensures
        !rejects(b),
{
    let f = choose|f: St| #[trigger] reaches(b, f) && f.phase is Done && f.out == out && 8 * used == f.pos;
    let nn = choose|nn: nat| run(b, init(), nn) == Step::Next(f);
    if rejects(b) {
        let n = choose|n: nat| run(b, init(), n) == Step::Bad;
        if n <= nn {
            lemma_run_split(b, init(), n, (nn - n) as nat);
            assert(n + (nn - n) as nat == nn);
        } else {
            lemma_run_split(b, init(), nn, (n - nn) as nat);
            assert(nn + (n - nn) as nat == n);
            lemma_run_done(b, f, (n - nn) as nat);
        }
    }
}

} // verus!
