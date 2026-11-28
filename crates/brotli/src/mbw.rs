//! The meta-block writer: several block types per category (block
//! splitting), literal and distance context maps with several trees
//! (context modeling), and static dictionary references.
//!
//! Nothing it is given is trusted: not the block types and counts, the
//! context modes and maps, the code lengths or the commands. Each item is
//! checked just before it is written, against the state the spec machine
//! is in after the bits so far; if a check fails, the writer takes back
//! everything it wrote for the meta-block (`BitWriter::reset`) and says
//! so, and the caller stores the block instead. So a bug in the planner or
//! the parser costs compression, never correctness.
use crate::bitwriter::*;
use crate::encoder::Enc;
use crate::mblock::*;
use crate::pcode::{HCode, Plan, make_code, make_plan, put_tree, bitlen_exec};
use crate::spec::{St, BLEN_BASE, BLEN_EXTRA, INS_BASE, INS_EXTRA, CPY_BASE, CPY_EXTRA, NDBITS, DOFFSET};
#[cfg(verus_only)]
use crate::cmeta::*;
#[cfg(verus_only)]
use crate::elemmas::*;
#[cfg(verus_only)]
use crate::mblemmas::*;
#[cfg(verus_only)]
use crate::pcode::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// What the planner hands over
// ---------------------------------------------------------------------------

/// One category's blocks: `nbt` block types, the type and length of each
/// block in order (the first block's type is 0, as the format fixes), and
/// the code lengths of the block type code (`nbt + 2` symbols) and the
/// block count code (26). With one block type the rest is not used.
pub struct CatPlan {
    pub nbt: usize,
    pub types: Vec<u8>,
    pub lens: Vec<u32>,
    pub tl: Vec<u8>,
    pub cl: Vec<u8>,
}

/// A meta-block's header, as the planner chose it: the three categories,
/// the context mode of each literal block type, the literal context map
/// (64 entries per literal block type) over `ntl` trees and the distance
/// context map (4 per distance block type) over `ntd` trees, and the code
/// lengths of every tree.
pub struct MbPlan {
    pub cats: Vec<CatPlan>,
    pub modes: Vec<u8>,
    pub lmap: Vec<u8>,
    pub ntl: usize,
    pub dmap: Vec<u8>,
    pub ntd: usize,
    pub lt: Vec<Vec<u8>>,
    pub ct: Vec<Vec<u8>>,
    pub dt: Vec<Vec<u8>>,
}

// ---------------------------------------------------------------------------
// What the header gave the spec machine, as the writer keeps it
// ---------------------------------------------------------------------------

pub struct Hdr {
    pub nbt: Vec<u32>,
    pub btc: Vec<HCode>,
    pub bcc: Vec<HCode>,
    pub modes: Vec<u8>,
    pub cmap: Vec<u8>,
    pub dmap: Vec<u8>,
    pub lt: Vec<HCode>,
    pub ct: Vec<HCode>,
    pub dt: Vec<HCode>,
}

/// The codes `v` are the spec's codes `t`.
pub open spec fn codes_ok(v: Seq<HCode>, t: Seq<Seq<u8>>) -> bool {
    &&& v.len() == t.len()
    &&& forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).ok() && t[i] == v[i].lens@
}

pub open spec fn hdr_ok(h: Hdr, s: St) -> bool {
    &&& h.nbt@.len() == 3
    &&& h.btc@.len() == 3
    &&& h.bcc@.len() == 3
    &&& s.nbt.len() == 3
    &&& s.btc.len() == 3
    &&& s.bcc.len() == 3
    &&& forall|c: int| 0 <= c < 3 ==> s.nbt[c] == #[trigger] h.nbt@[c] as int
    &&& forall|c: int| 0 <= c < 3 ==> (#[trigger] h.btc@[c]).ok() && h.bcc@[c].ok()
    &&& forall|c: int| 0 <= c < 3 && #[trigger] s.nbt[c] >= 2 ==> s.btc[c] == h.btc@[c].lens@ && s.bcc[c] == h.bcc@[c].lens@
    &&& s.cmodes == h.modes@
    &&& s.cmap == h.cmap@
    &&& s.dmap == h.dmap@
    &&& codes_ok(h.lt@, s.lit)
    &&& codes_ok(h.ct@, s.cmd)
    &&& codes_ok(h.dt@, s.dst)
    &&& s.npostfix == 0
    &&& s.ndirect == 0
}

/// What the header set up does not change.
pub proof fn lemma_hdr_keep(h: Hdr, s: St, t: St)
    requires
        hdr_ok(h, s),
        t.nbt == s.nbt,
        t.btc == s.btc,
        t.bcc == s.bcc,
        t.cmodes == s.cmodes,
        t.cmap == s.cmap,
        t.dmap == s.dmap,
        t.lit == s.lit,
        t.cmd == s.cmd,
        t.dst == s.dst,
        t.npostfix == s.npostfix,
        t.ndirect == s.ndirect,
    ensures
        hdr_ok(h, t),
{
}

/// The block state of the three categories, and the next block of each
/// in the plan.
pub struct Bm {
    pub bt: Vec<u32>,
    pub bt2: Vec<u32>,
    pub blen: Vec<u32>,
    pub next: Vec<usize>,
}

pub open spec fn bm_ok(m: Bm, s: St) -> bool {
    &&& m.bt@.len() == 3
    &&& m.bt2@.len() == 3
    &&& m.blen@.len() == 3
    &&& m.next@.len() == 3
    &&& s.bt.len() == 3
    &&& s.bt2.len() == 3
    &&& s.blen.len() == 3
    &&& forall|c: int| 0 <= c < 3 ==> s.bt[c] == #[trigger] m.bt@[c] as int
    &&& forall|c: int| 0 <= c < 3 ==> s.bt2[c] == #[trigger] m.bt2@[c] as int
    &&& forall|c: int| 0 <= c < 3 ==> s.blen[c] == #[trigger] m.blen@[c] as int
}

/// Inside a meta-block's commands: the output is `data[..q]` and the
/// meta-block ends at `end`.
pub open spec fn body(s: St, data: Seq<u8>, q: int, end: int, wb: int, dr: Seq<int>, h: Hdr, m: Bm) -> bool {
    &&& s.out == data.subrange(0, q)
    &&& s.mrem == end - q
    &&& s.wbits == wb
    &&& s.dr == dr
    &&& !s.last
    &&& hdr_ok(h, s)
    &&& bm_ok(m, s)
}

// ---------------------------------------------------------------------------
// Bits only ever get added
// ---------------------------------------------------------------------------

/// `a` is a prefix of `b`.
pub open spec fn grows(a: Seq<nat>, b: Seq<nat>) -> bool {
    &&& a.len() <= b.len()
    &&& b.subrange(0, a.len() as int) == a
}

pub proof fn lemma_grows_refl(a: Seq<nat>)
    ensures
        grows(a, a),
{
    assert(a.subrange(0, a.len() as int) =~= a);
}

pub proof fn lemma_grows_app(a: Seq<nat>, b: Seq<nat>, u: Seq<nat>)
    requires
        grows(a, b),
    ensures
        grows(a, b + u),
{
    assert((b + u).subrange(0, a.len() as int) =~= b.subrange(0, a.len() as int));
}

pub proof fn lemma_grows_trans(a: Seq<nat>, b: Seq<nat>, c: Seq<nat>)
    requires
        grows(a, b),
        grows(b, c),
    ensures
        grows(a, c),
{
    assert(c.subrange(0, a.len() as int) =~= c.subrange(0, b.len() as int).subrange(0, a.len() as int));
}

/// One step of the writer: `u` moves the machine from `s` to `t`.
proof fn lemma_adv(w: Seq<nat>, u: Seq<nat>, s: St, t: St, w2: Seq<nat>)
    requires
        good(w, s),
        moves(w, u, s, t),
        t.pos == (w.len() + u.len()) as int,
        w2 == w + u,
    ensures
        good(w2, t),
{
    lemma_good_moves(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Small pieces
// ---------------------------------------------------------------------------

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

/// Writes `v` (below 256) as `varlen8` reads it.
fn put_v8(bw: &mut BitWriter, v: u32) -> (n: Ghost<nat>)
    requires
        old(bw).wf(),
        v < 256,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        v8_ok(v as int, n@),
        final(bw).bits() == old(bw).bits() + v8_bits(v as int, n@),
{
    let ghost w0 = bw.bits();
    proof {
        lemma_pow2_small();
    }
    if v == 0 {
        bw.put(0, 1);
        Ghost(0)
    } else if v == 1 {
        bw.put(1, 1);
        bw.put(0, 3);
        proof {
            assert(bw.bits() =~= w0 + v8_bits(1, 0));
        }
        Ghost(0)
    } else {
        let b = bitlen_exec(v);
        proof {
            lemma_bitlen_lower(v as nat);
            crate::pcode::lemma_bitlen_bound(v as nat);
            if b < 2 {
                assert(pow2(b as nat) <= 2);
            }
            if b > 8 {
                if b - 1 > 8 { vstd::arithmetic::power2::lemma_pow2_strictly_increases(8, (b - 1) as nat); }
            }
        }
        let n = b - 1;
        let p = shl1(n) as u32;
        proof {
            lemma_pow2_unfold(b as nat);
            assert(n < 8);
        }
        bw.put(1, 1);
        bw.put(n, 3);
        bw.put(v - p, n);
        proof {
            assert((n + 1) as nat == b as nat);
            assert(bw.bits() =~= w0 + v8_bits(v as int, n as nat));
        }
        Ghost(n as nat)
    }
}

pub proof fn lemma_blen_tables()
    ensures
        forall|k: int| 0 <= k < 26 ==> #[trigger] BLEN_EXTRA[k] <= 24 && BLEN_BASE[k] <= 16625,
{
    assert(forall|k: int| 0 <= k < 26 ==> #[trigger] BLEN_EXTRA[k] <= 24 && BLEN_BASE[k] <= 16625) by (compute);
}

/// The block count symbol whose range holds `len`.
pub fn blen_sym(len: u32) -> (r: Option<usize>)
    ensures
        r matches Some(k) ==> blen_fits(k as int, len as int) && k < 26,
{
    proof {
        lemma_blen_tables();
        lemma_shl1_24();
    }
    let mut k: usize = 0;
    while k < 26
        invariant
            k <= 26,
            forall|k: int| 0 <= k < 26 ==> #[trigger] BLEN_EXTRA[k] <= 24 && BLEN_BASE[k] <= 16625,
            forall|j: nat| j <= 24 ==> #[trigger] pow2(j) <= 0x100_0000,
        decreases 26 - k,
    {
        if BLEN_BASE[k] <= len && (len as u64) < BLEN_BASE[k] as u64 + shl1(BLEN_EXTRA[k] as u32) {
            return Some(k);
        }
        k = k + 1;
    }
    None
}

/// Writes block count `len` with code `cc`.
fn put_blen(bw: &mut BitWriter, cc: &HCode, len: u32) -> (r: Option<Ghost<int>>)
    requires
        old(bw).wf(),
        cc.ok(),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r matches Some(ls) ==> coded(cc.lens@, ls@) && blen_fits(ls@, len as int)
            && final(bw).bits() == old(bw).bits() + blen_bits(cc.lens@, ls@, len as int),
        r is None ==> final(bw).bits() == old(bw).bits(),
{
    let ls = match blen_sym(len) {
        Some(k) => k,
        None => return None,
    };
    if !has_code(cc, ls) {
        return None;
    }
    let ghost w0 = bw.bits();
    proof {
        lemma_blen_tables();
        lemma_shl1_24();
    }
    let (v, n) = cc.sym(ls);
    bw.put64(v, n);
    bw.put(len - BLEN_BASE[ls], BLEN_EXTRA[ls] as u32);
    proof {
        assert(bw.bits() =~= w0 + blen_bits(cc.lens@, ls as int, len as int));
    }
    Some(Ghost(ls as int))
}

// ---------------------------------------------------------------------------
// The header
// ---------------------------------------------------------------------------

/// The block types of category `c`: `NBLTYPES`, and with two or more the
/// block type and block count codes and the first block count. Returns
/// `NBLTYPES`, the two codes (unused with one block type) and the first
/// count.
fn put_cat(e: &mut Enc, c: usize, cp: &CatPlan) -> (r: Option<(u32, HCode, HCode, u32)>)
    requires
        old(e).ok(),
        old(e).st@.phase == Phase::NBlockTypes(c as int),
        c < 3,
        old(e).st@.pc == pc_init(),
        old(e).st@.nbt.len() == 3,
        old(e).st@.btc.len() == 3,
        old(e).st@.bcc.len() == 3,
        old(e).st@.blen.len() == 3,
    ensures
        final(e).bw.wf(),
        final(e).bw.sent() == old(e).bw.sent(),
        grows(old(e).bw.bits(), final(e).bw.bits()),
        r matches Some((nb, tc, cc, l0)) ==> {
            &&& final(e).ok()
            &&& 1 <= nb <= 256
            &&& tc.ok()
            &&& cc.ok()
            &&& final(e).st@ == (St {
                phase: after_cat(c as int),
                pos: final(e).st@.pos,
                nbt: old(e).st@.nbt.update(c as int, nb as int),
                btc: if nb >= 2 { old(e).st@.btc.update(c as int, tc.lens@) } else { old(e).st@.btc },
                bcc: if nb >= 2 { old(e).st@.bcc.update(c as int, cc.lens@) } else { old(e).st@.bcc },
                blen: if nb >= 2 { old(e).st@.blen.update(c as int, l0 as int) } else { old(e).st@.blen },
                ..old(e).st@
            })
        },
{
    let ghost w0 = e.bw.bits();
    let ghost s0 = e.st@;
    proof {
        lemma_grows_refl(w0);
    }
    let nb = cp.nbt;
    if nb < 1 || nb > 256 {
        return None;
    }
    let n = put_v8(&mut e.bw, (nb - 1) as u32);
    let ghost w1 = e.bw.bits();
    let ghost s1 = after_nbt(s0, c as int, (nb - 1) as int, w1.len() as int);
    proof {
        lemma_nbt(w0, s0, c as int, (nb - 1) as int, n@);
        lemma_adv(w0, v8_bits((nb - 1) as int, n@), s0, s1, w1);
        lemma_grows_app(w0, w0, v8_bits((nb - 1) as int, n@));
    }
    e.st = Ghost(s1);
    if nb == 1 {
        let d1 = match make_code(vec![1u8, 1u8]) {
            Some(d) => d,
            None => return None,
        };
        let d2 = match make_code(vec![1u8, 1u8]) {
            Some(d) => d,
            None => return None,
        };
        proof {
            assert(s1.nbt == s0.nbt.update(c as int, 1));
        }
        return Some((1, d1, d2, 0));
    }
    if cp.tl.len() != nb + 2 || cp.cl.len() != 26 || cp.lens.len() == 0 {
        return None;
    }
    let tc = match make_code(cp.tl.clone()) {
        Some(x) => x,
        None => return None,
    };
    let tp = match make_plan(&cp.tl) {
        Some(x) => x,
        None => return None,
    };
    let cc = match make_code(cp.cl.clone()) {
        Some(x) => x,
        None => return None,
    };
    let cpl = match make_plan(&cp.cl) {
        Some(x) => x,
        None => return None,
    };
    // The block type code.
    put_tree(&mut e.bw, &tp, nb + 2, Ghost(s1), Ghost(3 + c as int), Ghost(tc.lens@));
    let ghost w2 = e.bw.bits();
    let ghost s2 = tree_fin(s1, 3 + c as int, tc.lens@, w2.len() as int);
    proof {
        lemma_adv(w1, w2.subrange(w1.len() as int, w2.len() as int), s1, s2, w2);
        lemma_grows_app(w0, w1, w2.subrange(w1.len() as int, w2.len() as int));
    }
    // The block count code.
    put_tree(&mut e.bw, &cpl, 26, Ghost(s2), Ghost(6 + c as int), Ghost(cc.lens@));
    let ghost w3 = e.bw.bits();
    let ghost s3 = tree_fin(s2, 6 + c as int, cc.lens@, w3.len() as int);
    proof {
        lemma_adv(w2, w3.subrange(w2.len() as int, w3.len() as int), s2, s3, w3);
        lemma_grows_app(w0, w2, w3.subrange(w2.len() as int, w3.len() as int));
    }
    e.st = Ghost(s3);
    // The first block count.
    let l0 = cp.lens[0];
    let ls = match put_blen(&mut e.bw, &cc, l0) {
        Some(ls) => ls,
        None => return None,
    };
    let ghost w4 = e.bw.bits();
    let ghost s4 = St { phase: after_cat(c as int), pos: w4.len() as int, blen: s3.blen.update(c as int, l0 as int), ..s3 };
    proof {
        assert(s3.bcc[c as int] == cc.lens@);
        lemma_bcount(w3, s3, c as int, ls@, l0 as int);
        lemma_adv(w3, blen_bits(cc.lens@, ls@, l0 as int), s3, s4, w4);
        lemma_grows_app(w0, w3, blen_bits(cc.lens@, ls@, l0 as int));
    }
    e.st = Ghost(s4);
    Some((nb as u32, tc, cc, l0))
}

/// The state after context map `wh` (0 literal, 1 distance) with map `m`
/// over `nt` trees.
pub open spec fn cm_done(s: St, wh: int, nt: int, m: Seq<u8>, p: int) -> St {
    if wh == 0 {
        St { phase: Phase::CMap(1), pos: p, cmap: m, ntl: nt, ..s }
    } else {
        St { phase: Phase::Trees(0), pos: p, dmap: m, ntd: nt, ..s }
    }
}

/// The largest `k <= 16` with `2^k <= r`, for `r >= 1`.
fn log2_16(r: usize) -> (k: u32)
    ensures
        k <= 16,
{
    let mut k: u32 = 0;
    while k < 16 && (r >> (k + 1)) >= 1
        invariant
            k <= 16,
        decreases 16 - k,
    {
        k = k + 1;
    }
    k
}

/// Context map `wh` (0 literal, 1 distance), `map` over `nt` trees, with
/// runs of zeros coded when that helps and no move-to-front. Returns the
/// map the spec holds once it has read it.
#[verifier::rlimit(40)]
fn put_cmap(e: &mut Enc, map: &[u8], nt: usize, size: usize, wh: usize) -> (r: Option<Vec<u8>>)
    requires
        old(e).ok(),
        old(e).st@.phase == Phase::CMap(wh as int),
        wh < 2,
        old(e).st@.cm == cm_init(),
        old(e).st@.pc == pc_init(),
        size == cmap_size(old(e).st@, wh as int),
        1 <= size <= 0x4000,
    ensures
        final(e).bw.wf(),
        final(e).bw.sent() == old(e).bw.sent(),
        grows(old(e).bw.bits(), final(e).bw.bits()),
        r matches Some(m) ==> {
            &&& final(e).ok()
            &&& 1 <= nt <= 256
            &&& final(e).st@ == cm_done(old(e).st@, wh as int, nt as int, m@, final(e).st@.pos)
        },
{
    let ghost w0 = e.bw.bits();
    let ghost s0 = e.st@;
    proof {
        lemma_grows_refl(w0);
        lemma_pow2_small();
    }
    if nt < 1 || nt > 256 || map.len() != size {
        return None;
    }
    if nt == 1 {
        proof {
            lemma_cmap1(w0, s0, wh as int);
        }
        e.bw.put(0, 1);
        let m = vec![0u8; size];
        let ghost w1 = e.bw.bits();
        let ghost s1 = cm_done(s0, wh as int, 1, m@, w1.len() as int);
        proof {
            assert(Seq::new(cmap_size(s0, wh as int) as nat, |i: int| 0u8) =~= m@);
            lemma_bits_of(0, 1);
            assert(w1.len() == s0.pos + 1);
            assert(cmap_finish(St { pos: s0.pos + 1, ..s0 }, wh as int, 1, m@) == Step::Next(s1));
            lemma_adv(w0, fld(0, 1), s0, s1, w1);
            lemma_grows_app(w0, w0, fld(0, 1));
        }
        e.st = Ghost(s1);
        return Some(m);
    }
    // The longest run of zeros picks RLEMAX.
    let mut maxrun: usize = 0;
    let mut run: usize = 0;
    let mut i: usize = 0;
    while i < size
        invariant
            i <= size,
            size == map@.len(),
            run <= i,
            maxrun <= size,
        decreases size - i,
    {
        if map[i] == 0 {
            run = run + 1;
            if run > maxrun {
                maxrun = run;
            }
        } else {
            run = 0;
        }
        i = i + 1;
    }
    let rlemax: u32 = if maxrun < 2 { 0 } else { log2_16(maxrun) };
    let alpha = nt + rlemax as usize;
    // The symbols: (symbol, extra bits).
    let mut syms: Vec<(u16, u16)> = Vec::new();
    let mut freq: Vec<u32> = vec![0u32; alpha];
    let mut i: usize = 0;
    while i < size
        invariant
            i <= size,
            size == map@.len(),
            alpha == nt + rlemax,
            rlemax <= 16,
            2 <= nt <= 256,
            freq@.len() == alpha,
        decreases size - i,
    {
        let v = map[i];
        if v != 0 {
            let sym = v as usize + rlemax as usize;
            if sym < alpha {
                let f = freq[sym];
                if f < 0xFFFF_FFFF {
                    freq.set(sym, f + 1);
                }
            }
            syms.push((sym as u16, 0));
            i = i + 1;
        } else {
            let mut j = i;
            while j < size && map[j] == 0
                invariant
                    i <= j <= size,
                    size == map@.len(),
                decreases size - j,
            {
                j = j + 1;
            }
            let mut r = j - i;
            proof {
                lemma_shl1_24();
            }
            while r > 0
                invariant
                    rlemax <= 16,
                    alpha == nt + rlemax,
                    freq@.len() == alpha,
                    nt >= 1,
                    forall|j: nat| j <= 24 ==> #[trigger] pow2(j) <= 0x100_0000,
                decreases r,
            {
                let k0 = log2_16(r);
                let k = if k0 > rlemax { rlemax } else { k0 };
                let base: usize = if k == 0 { 0 } else { shl1(k) as usize };
                if k == 0 || r < base {
                    // One zero.
                    let f = freq[0];
                    if f < 0xFFFF_FFFF {
                        freq.set(0, f + 1);
                    }
                    syms.push((0, 0));
                    r = r - 1;
                } else {
                    // A run of `base` to `2 base - 1` zeros.
                    let most = 2 * base - 1;
                    let cover = if r >= most { most } else { r };
                    let f = freq[k as usize];
                    if f < 0xFFFF_FFFF {
                        freq.set(k as usize, f + 1);
                    }
                    let ex = cover - base;
                    syms.push((k as u16, if ex > 0xFFFF { 0xFFFF } else { ex as u16 }));
                    r = r - cover;
                }
            }
            i = j;
        }
    }
    let lens = crate::ehuff::huff_lens(&freq, 15);
    let code = match make_code(lens.clone()) {
        Some(x) => x,
        None => return None,
    };
    let plan = match make_plan(&lens) {
        Some(x) => x,
        None => return None,
    };
    // NTREES and RLEMAX.
    let n8 = put_v8(&mut e.bw, (nt - 1) as u32);
    if rlemax == 0 {
        e.bw.put(0, 1);
    } else {
        e.bw.put(1, 1);
        e.bw.put(rlemax - 1, 4);
    }
    let ghost w1 = e.bw.bits();
    let ghost s1 = St { pos: w1.len() as int, cm: Cm { stage: 1, ntrees: nt as int, rlemax: rlemax as int, ..s0.cm }, pc: pc_init(), ..s0 };
    proof {
        let u = v8_bits((nt - 1) as int, n8@) + rle_bits(rlemax as int);
        assert(w1 =~= w0 + u);
        lemma_cm_head(w0, s0, wh as int, (nt - 1) as int, n8@, rlemax as int);
        lemma_adv(w0, u, s0, s1, w1);
        lemma_grows_app(w0, w0, u);
    }
    // The code of the symbols.
    put_tree(&mut e.bw, &plan, alpha, Ghost(s1), Ghost(9 + wh as int), Ghost(code.lens@));
    let ghost w2 = e.bw.bits();
    let ghost s2 = tree_fin(s1, 9 + wh as int, code.lens@, w2.len() as int);
    proof {
        lemma_adv(w1, w2.subrange(w1.len() as int, w2.len() as int), s1, s2, w2);
        lemma_grows_app(w0, w1, w2.subrange(w1.len() as int, w2.len() as int));
        assert(s2.cm.map == Seq::<u8>::empty());
    }
    // The symbols, with the map they make.
    let mut dec: Vec<u8> = Vec::with_capacity(size);
    let ghost mut st = s2;
    let mut k: usize = 0;
    while k < syms.len()
        invariant
            e.bw.wf(),
            e.bw.sent() == old(e).bw.sent(),
            w0 == old(e).bw.bits(),
            grows(w0, e.bw.bits()),
            good(e.bw.bits(), st),
            code.ok(),
            code.lens@.len() == alpha,
            alpha == nt + rlemax,
            2 <= nt <= 256,
            st.phase == Phase::CMap(wh as int),
            st.cm.stage == 2,
            st.cm.code == code.lens@,
            st.cm.rlemax == rlemax as int,
            st.cm.ntrees == nt as int,
            st.cm.map == dec@,
            st == (St { pos: st.pos, cm: st.cm, ..s2 }),
            size == cmap_size(st, wh as int),
            dec@.len() <= size,
            size <= 0x4000,
            rlemax <= 16,
        decreases syms.len() - k,
    {
        let (sym, x) = syms[k];
        let sym = sym as usize;
        if dec.len() >= size || !has_code(&code, sym) {
            return None;
        }
        let ghost wk = e.bw.bits();
        if sym >= 1 && sym <= rlemax as usize {
            proof {
                lemma_shl1_24();
            }
            let base = shl1(sym as u32) as usize;
            let reps = base + x as usize;
            if (x as usize) >= base || reps > size - dec.len() {
                return None;
            }
            proof {
                lemma_cm_sym(wk, st, wh as int, sym as int, x as int);
            }
            let (v, n) = code.sym(sym);
            e.bw.put64(v, n);
            e.bw.put(x as u32, sym as u32);
            let ghost d0 = dec@;
            let mut j: usize = 0;
            while j < reps
                invariant
                    j <= reps,
                    dec@ == d0 + Seq::new(j as nat, |i: int| 0u8),
                    d0.len() + reps <= size,
                    size <= 0x4000,
                decreases reps - j,
            {
                dec.push(0);
                proof {
                    assert(d0 + Seq::new((j + 1) as nat, |i: int| 0u8) =~= (d0 + Seq::new(j as nat, |i: int| 0u8)).push(0u8));
                }
                j = j + 1;
            }
            let ghost u = cm_sym_bits(code.lens@, rlemax as int, sym as int, x as int);
            let ghost t = St { pos: (wk.len() + u.len()) as int, cm: Cm { map: st.cm.map + cm_add(rlemax as int, sym as int, x as int), ..st.cm }, ..st };
            proof {
                assert(e.bw.bits() =~= wk + u);
                assert(cm_add(rlemax as int, sym as int, x as int) =~= Seq::new(reps as nat, |i: int| 0u8));
                assert(dec@ =~= t.cm.map);
                lemma_adv(wk, u, st, t, e.bw.bits());
                lemma_grows_app(w0, wk, u);
                st = t;
            }
        } else {
            proof {
                lemma_cm_sym(wk, st, wh as int, sym as int, 0);
            }
            let (v, n) = code.sym(sym);
            e.bw.put64(v, n);
            let val: u8 = if sym == 0 { 0 } else { (sym - rlemax as usize) as u8 };
            proof {
                assert(sym < code.lens@.len());
            }
            dec.push(val);
            let ghost u = cm_sym_bits(code.lens@, rlemax as int, sym as int, 0);
            let ghost t = St { pos: (wk.len() + u.len()) as int, cm: Cm { map: st.cm.map + cm_add(rlemax as int, sym as int, 0), ..st.cm }, ..st };
            proof {
                assert(e.bw.bits() =~= wk + u);
                assert(dec@ =~= t.cm.map);
                lemma_adv(wk, u, st, t, e.bw.bits());
                lemma_grows_app(w0, wk, u);
                st = t;
            }
        }
        k = k + 1;
    }
    if dec.len() != size {
        return None;
    }
    // The map is full; IMTF = 0.
    let ghost w3 = e.bw.bits();
    let ghost s3 = St { cm: Cm { stage: 3, ..st.cm }, ..st };
    proof {
        lemma_cm_full(w3, st, wh as int);
        assert(w3 + Seq::<nat>::empty() =~= w3);
        lemma_adv(w3, Seq::empty(), st, s3, w3);
        lemma_cm_imtf(w3, s3, wh as int, 0);
    }
    e.bw.put(0, 1);
    let ghost w4 = e.bw.bits();
    let ghost s4 = cm_done(s0, wh as int, nt as int, dec@, w4.len() as int);
    proof {
        lemma_bits_of(0, 1);
        assert(w4.len() == s3.pos + 1);
        assert(cmap_finish(St { pos: s3.pos + 1, ..s3 }, wh as int, nt as int, dec@) == Step::Next(s4));
        lemma_adv(w3, fld(0, 1), s3, s4, w4);
        lemma_grows_app(w0, w3, fld(0, 1));
    }
    e.st = Ghost(s4);
    Some(dec)
}

/// The prefix codes of group `g` read so far.
pub open spec fn group(s: St, g: int) -> Seq<Seq<u8>> {
    if g == 0 {
        s.lit
    } else if g == 1 {
        s.cmd
    } else {
        s.dst
    }
}

/// `s` with the codes of group `g` set to `v`, at bit position `p`.
pub open spec fn with_group(s: St, g: int, v: Seq<Seq<u8>>, p: int) -> St {
    if g == 0 {
        St { pos: p, lit: v, ..s }
    } else if g == 1 {
        St { pos: p, cmd: v, ..s }
    } else {
        St { pos: p, dst: v, ..s }
    }
}

pub open spec fn after_group(g: int) -> Phase {
    if g < 2 {
        Phase::Trees(g + 1)
    } else {
        Phase::CmdBegin
    }
}

/// The `nt` prefix codes of group `g`, with code lengths `lens`.
fn put_trees(e: &mut Enc, lens: &Vec<Vec<u8>>, alpha: usize, g: usize, nt: usize) -> (r: Option<Vec<HCode>>)
    requires
        old(e).ok(),
        old(e).st@.phase == Phase::Trees(g as int),
        g < 3,
        old(e).st@.pc == pc_init(),
        group(old(e).st@, g as int) == Seq::<Seq<u8>>::empty(),
        pc_alpha(old(e).st@) == alpha,
        ntrees(old(e).st@, g as int) == nt,
        2 <= alpha <= 1024,
    ensures
        final(e).bw.wf(),
        final(e).bw.sent() == old(e).bw.sent(),
        grows(old(e).bw.bits(), final(e).bw.bits()),
        r matches Some(v) ==> {
            &&& final(e).ok()
            &&& v@.len() == nt
            &&& codes_ok(v@, group(final(e).st@, g as int))
            &&& final(e).st@ == with_group(St { phase: after_group(g as int), ..old(e).st@ }, g as int, group(final(e).st@, g as int), final(e).st@.pos)
        },
{
    let ghost w0 = e.bw.bits();
    let ghost s0 = e.st@;
    proof {
        lemma_grows_refl(w0);
    }
    if lens.len() != nt {
        return None;
    }
    let mut v: Vec<HCode> = Vec::with_capacity(nt);
    let mut i: usize = 0;
    while i < nt
        invariant
            e.bw.wf(),
            e.bw.sent() == old(e).bw.sent(),
            w0 == old(e).bw.bits(),
            s0 == old(e).st@,
            grows(w0, e.bw.bits()),
            e.ok(),
            i <= nt,
            nt == lens@.len(),
            g < 3,
            2 <= alpha <= 1024,
            v@.len() == i,
            codes_ok(v@, group(e.st@, g as int)),
            e.st@ == with_group(s0, g as int, group(e.st@, g as int), e.st@.pos),
            ntrees(s0, g as int) == nt,
            pc_alpha(s0) == alpha,
            s0.phase == Phase::Trees(g as int),
            s0.pc == pc_init(),
        decreases nt - i,
    {
        let l = &lens[i];
        if l.len() != alpha {
            return None;
        }
        let code = match make_code(l.clone()) {
            Some(x) => x,
            None => return None,
        };
        let plan = match make_plan(l) {
            Some(x) => x,
            None => return None,
        };
        let ghost w1 = e.bw.bits();
        let ghost s1 = e.st@;
        proof {
            assert(nread(s1, g as int) == i);
            assert(ntrees(s1, g as int) == nt);
            assert(pc_alpha(s1) == alpha);
        }
        put_tree(&mut e.bw, &plan, alpha, Ghost(s1), Ghost(g as int), Ghost(code.lens@));
        let ghost w2 = e.bw.bits();
        let ghost s2 = tree_fin(s1, g as int, code.lens@, w2.len() as int);
        proof {
            lemma_adv(w1, w2.subrange(w1.len() as int, w2.len() as int), s1, s2, w2);
            lemma_grows_app(w0, w1, w2.subrange(w1.len() as int, w2.len() as int));
            assert(group(s2, g as int) == group(s1, g as int).push(code.lens@));
        }
        e.st = Ghost(s2);
        let ghost v0 = v@;
        v.push(code);
        proof {
            assert forall|k: int| 0 <= k < v@.len() implies (#[trigger] v@[k]).ok() && group(s2, g as int)[k] == v@[k].lens@ by {
                if k < i {
                    assert(v@[k] == v0[k]);
                }
            }
            assert(s2 == with_group(s0, g as int, group(s2, g as int), s2.pos));
        }
        i = i + 1;
    }
    let ghost w3 = e.bw.bits();
    let ghost s3 = e.st@;
    let ghost s4 = if g < 2 { St { phase: Phase::Trees(g + 1), pc: pc_init(), ..s3 } } else { St { phase: Phase::CmdBegin, ..s3 } };
    proof {
        lemma_trees_next(w3, s3, g as int);
        assert(w3 + Seq::<nat>::empty() =~= w3);
        lemma_adv(w3, Seq::empty(), s3, s4, w3);
    }
    e.st = Ghost(s4);
    Some(v)
}

/// The header of a compressed meta-block of `len` bytes (not the last),
/// up to its first command.
#[verifier::rlimit(60)]
fn put_hdr(e: &mut Enc, len: usize, p: &MbPlan) -> (r: Option<(Hdr, Bm)>)
    requires
        old(e).ok(),
        old(e).st@.phase is MetaHeader,
        1 <= len <= 0x100_0000,
    ensures
        final(e).bw.wf(),
        final(e).bw.sent() == old(e).bw.sent(),
        grows(old(e).bw.bits(), final(e).bw.bits()),
        r matches Some((h, m)) ==> {
            &&& final(e).ok()
            &&& final(e).st@.phase is CmdBegin
            &&& hdr_ok(h, final(e).st@)
            &&& bm_ok(m, final(e).st@)
            &&& final(e).st@.out == old(e).st@.out
            &&& final(e).st@.wbits == old(e).st@.wbits
            &&& final(e).st@.dr == old(e).st@.dr
            &&& final(e).st@.mrem == len
            &&& !final(e).st@.last
        },
{
    let ghost w0 = e.bw.bits();
    let ghost s0 = e.st@;
    proof {
        lemma_grows_refl(w0);
        lemma_meta_compressed(w0, s0, len as int, false);
        lemma_pow2_small();
        lemma_bits_of(0, 1);
    }
    if p.cats.len() != 3 {
        return None;
    }
    e.bw.put(0, 1);
    e.put_mlen(len);
    e.bw.put(0, 1);
    let ghost s1 = begin_compressed(mheader(s0, len as int, false));
    proof {
        assert(e.bw.bits() =~= w0 + meta_bits(len as int, false));
        lemma_adv(w0, meta_bits(len as int, false), s0, s1, e.bw.bits());
        lemma_grows_app(w0, w0, meta_bits(len as int, false));
    }
    e.st = Ghost(s1);
    // The block types of the three categories.
    let ghost wa = e.bw.bits();
    let r0 = put_cat(e, 0, &p.cats[0]);
    proof { lemma_grows_trans(w0, wa, e.bw.bits()); }
    let (nb0, tc0, cc0, l0) = match r0 {
        Some(x) => x,
        None => return None,
    };
    let ghost s2 = e.st@;
    let ghost wb = e.bw.bits();
    let r1 = put_cat(e, 1, &p.cats[1]);
    proof { lemma_grows_trans(w0, wb, e.bw.bits()); }
    let (nb1, tc1, cc1, l1) = match r1 {
        Some(x) => x,
        None => return None,
    };
    let ghost s3 = e.st@;
    let ghost wc = e.bw.bits();
    let r2 = put_cat(e, 2, &p.cats[2]);
    proof { lemma_grows_trans(w0, wc, e.bw.bits()); }
    let (nb2, tc2, cc2, l2) = match r2 {
        Some(x) => x,
        None => return None,
    };
    let ghost s4 = e.st@;
    // NPOSTFIX = NDIRECT = 0.
    let ghost w4 = e.bw.bits();
    proof {
        lemma_dparams0(w4, s4);
        lemma_bits_of(0, 6);
    }
    e.bw.put(0, 6);
    let ghost s5 = St { phase: Phase::CModes, pos: s4.pos + 6, npostfix: 0, ndirect: 0, cmodes: Seq::empty(), ..s4 };
    proof {
        lemma_adv(w4, fld(0, 6), s4, s5, e.bw.bits());
        lemma_grows_app(w0, w4, fld(0, 6));
    }
    e.st = Ghost(s5);
    // The context modes.
    if p.modes.len() != nb0 as usize {
        return None;
    }
    let mut i: usize = 0;
    proof {
        assert(p.modes@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(e.st@ == (St { pos: e.st@.pos, cmodes: p.modes@.subrange(0, 0), ..s5 }));
    }
    while i < nb0 as usize
        invariant
            e.ok(),
            e.bw.sent() == old(e).bw.sent(),
            w0 == old(e).bw.bits(),
            grows(w0, e.bw.bits()),
            i <= nb0,
            p.modes@.len() == nb0,
            e.st@ == (St { pos: e.st@.pos, cmodes: p.modes@.subrange(0, i as int), ..s5 }),
            s5.nbt.len() == 3,
            s5.nbt[0] == nb0 as int,
            s5.phase is CModes,
        decreases nb0 - i,
    {
        let mode = p.modes[i];
        if mode >= 4 {
            return None;
        }
        let ghost wi = e.bw.bits();
        let ghost si = e.st@;
        proof {
            lemma_pow2_small();
            lemma_cmode(wi, si, mode as int);
        }
        e.bw.put(mode as u32, 2);
        let ghost t = St { pos: si.pos + 2, cmodes: si.cmodes.push(mode), ..si };
        proof {
            lemma_bits_of(mode as nat, 2);
            lemma_adv(wi, fld(mode as nat, 2), si, t, e.bw.bits());
            lemma_grows_app(w0, wi, fld(mode as nat, 2));
            assert(p.modes@.subrange(0, i as int).push(mode) =~= p.modes@.subrange(0, i + 1));
        }
        e.st = Ghost(t);
        i = i + 1;
    }
    let ghost w6 = e.bw.bits();
    let ghost s6a = e.st@;
    let ghost s6 = St { phase: Phase::CMap(0), cm: cm_init(), ..s6a };
    proof {
        assert(p.modes@.subrange(0, nb0 as int) =~= p.modes@);
        lemma_cmodes_end(w6, s6a);
        assert(w6 + Seq::<nat>::empty() =~= w6);
        lemma_adv(w6, Seq::empty(), s6a, s6, w6);
    }
    e.st = Ghost(s6);
    // The context maps.
    let ghost wd = e.bw.bits();
    let r3 = put_cmap(e, p.lmap.as_slice(), p.ntl, (nb0 as usize) * 64, 0);
    proof { lemma_grows_trans(w0, wd, e.bw.bits()); }
    let cmap = match r3 {
        Some(x) => x,
        None => return None,
    };
    let ghost s7 = e.st@;
    let ghost we = e.bw.bits();
    let r4 = put_cmap(e, p.dmap.as_slice(), p.ntd, (nb2 as usize) * 4, 1);
    proof { lemma_grows_trans(w0, we, e.bw.bits()); }
    let dmap = match r4 {
        Some(x) => x,
        None => return None,
    };
    let ghost s8 = e.st@;
    proof {
        assert(dist_alpha(0, 0) == 64);
    }
    // The trees.
    let ghost wf = e.bw.bits();
    let r5 = put_trees(e, &p.lt, 256, 0, p.ntl);
    proof { lemma_grows_trans(w0, wf, e.bw.bits()); }
    let lt = match r5 {
        Some(x) => x,
        None => return None,
    };
    let ghost s9 = e.st@;
    let ghost wg = e.bw.bits();
    let r6 = put_trees(e, &p.ct, 704, 1, nb1 as usize);
    proof { lemma_grows_trans(w0, wg, e.bw.bits()); }
    let ct = match r6 {
        Some(x) => x,
        None => return None,
    };
    let ghost s10 = e.st@;
    let ghost wh = e.bw.bits();
    let r7 = put_trees(e, &p.dt, 64, 2, p.ntd);
    proof { lemma_grows_trans(w0, wh, e.bw.bits()); }
    let dt = match r7 {
        Some(x) => x,
        None => return None,
    };
    let ghost s11 = e.st@;
    let nbt = vec![nb0, nb1, nb2];
    let btc = vec![tc0, tc1, tc2];
    let bcc = vec![cc0, cc1, cc2];
    let cap: u32 = 0x100_0000;
    let blen = vec![if nb0 >= 2 { l0 } else { cap }, if nb1 >= 2 { l1 } else { cap }, if nb2 >= 2 { l2 } else { cap }];
    let h = Hdr { nbt, btc, bcc, modes: p.modes.clone(), cmap, dmap, lt, ct, dt };
    let m = Bm { bt: vec![0, 0, 0], bt2: vec![1, 1, 1], blen, next: vec![1, 1, 1] };
    proof {
        assert(s11.lit == s9.lit);
        assert(s11.cmd == s10.cmd);
        assert(h.modes@ == p.modes@);
        assert(s11.nbt =~= seq![nb0 as int, nb1 as int, nb2 as int]);
        assert(forall|c: int| 0 <= c < 3 ==> s11.nbt[c] == #[trigger] h.nbt@[c] as int);
        assert(s11.bt =~= seq![0int, 0, 0]);
        assert(s11.bt2 =~= seq![1int, 1, 1]);
        assert(forall|c: int| 0 <= c < 3 ==> s11.blen[c] == #[trigger] m.blen@[c] as int);
    }
    Some((h, m))
}

// ---------------------------------------------------------------------------
// The commands
// ---------------------------------------------------------------------------

/// The block state changes only in the block fields.
pub open spec fn same_but_blocks(t: St, s: St) -> bool {
    t == (St { pos: t.pos, bt: t.bt, bt2: t.bt2, blen: t.blen, ..s })
}

/// A block switch for category `c`, to the plan's next block.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn put_switch(bw: &mut BitWriter, h: &Hdr, m: &mut Bm, cats: &Vec<CatPlan>, c: usize, Ghost(s): Ghost<St>) -> (r: Option<Ghost<St>>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s),
        switch_phase(s, c as int),
        hdr_ok(*h, s),
        bm_ok(*old(m), s),
        c < 3,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        grows(old(bw).bits(), final(bw).bits()),
        r matches Some(t) ==> {
            &&& good(final(bw).bits(), t@)
            &&& bm_ok(*final(m), t@)
            &&& hdr_ok(*h, t@)
            &&& same_but_blocks(t@, s)
            &&& final(m).blen@[c as int] != 0
            &&& forall|k: int| 0 <= k < 3 && k != c ==> #[trigger] final(m).blen@[k] == old(m).blen@[k]
        },
{
    let ghost w0 = bw.bits();
    proof {
        lemma_grows_refl(w0);
    }
    let nb = h.nbt[c];
    if nb < 2 || c >= cats.len() {
        return None;
    }
    let k = m.next[c];
    let cp = &cats[c];
    if k >= cp.types.len() || k >= cp.lens.len() {
        return None;
    }
    let t = cp.types[k] as u32;
    let len = cp.lens[k];
    let bt = m.bt[c];
    let bt2 = m.bt2[c];
    let nxt: u64 = if bt as u64 + 1 >= nb as u64 { bt as u64 + 1 - nb as u64 } else { bt as u64 + 1 };
    let sym: usize = if t == bt2 { 0 } else if t as u64 == nxt { 1 } else { t as usize + 2 };
    let tc = &h.btc[c];
    let cc = &h.bcc[c];
    if !has_code(tc, sym) {
        return None;
    }
    let ls = match blen_sym(len) {
        Some(x) => x,
        None => return None,
    };
    if !has_code(cc, ls) {
        return None;
    }
    // The type the spec switches to.
    let t0: u64 = if sym == 0 { bt2 as u64 } else if sym == 1 { bt as u64 + 1 } else { sym as u64 - 2 };
    let tt: u64 = if t0 >= nb as u64 { t0 - nb as u64 } else { t0 };
    if tt >= 0x1_0000 {
        return None;
    }
    proof {
        lemma_blen_tables();
        lemma_shl1_24();
        assert(s.nbt[c as int] == nb as int);
        assert(s.btc[c as int] == tc.lens@);
        assert(s.bcc[c as int] == cc.lens@);
        lemma_bsw(w0, s, c as int, sym as int, ls as int, len as int);
        assert(bsw_type(s, c as int, sym as int) == tt as int);
    }
    let (v, n) = tc.sym(sym);
    bw.put64(v, n);
    let (v2, n2) = cc.sym(ls);
    bw.put64(v2, n2);
    bw.put(len - BLEN_BASE[ls], BLEN_EXTRA[ls] as u32);
    let ghost u = bsw_bits(s, c as int, sym as int, ls as int, len as int);
    let ghost t2 = bsw_next(s, c as int, sym as int, len as int, (w0.len() + u.len()) as int);
    proof {
        assert(bw.bits() =~= w0 + u);
        lemma_adv(w0, u, s, t2, bw.bits());
        lemma_grows_app(w0, w0, u);
    }
    m.bt2.set(c, bt);
    m.bt.set(c, tt as u32);
    m.blen.set(c, len);
    m.next.set(c, k + 1);
    proof {
        assert(BLEN_BASE[ls as int] >= 1) by {
            assert(forall|k: int| 0 <= k < 26 ==> #[trigger] BLEN_BASE[k] >= 1) by (compute);
        }
        assert forall|j: int| 0 <= j < 3 implies t2.bt[j] == #[trigger] m.bt@[j] as int by {}
        assert forall|j: int| 0 <= j < 3 implies t2.bt2[j] == #[trigger] m.bt2@[j] as int by {}
        assert forall|j: int| 0 <= j < 3 implies t2.blen[j] == #[trigger] m.blen@[j] as int by {}
    }
    Some(Ghost(t2))
}

/// The literals `data[q..p]` of a command, each with the tree its block
/// type and context pick, switching literal blocks where the counts say.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn put_lits(bw: &mut BitWriter, data: &[u8], q: usize, p: usize, h: &Hdr, m: &mut Bm, cats: &Vec<CatPlan>, Ghost(s1): Ghost<St>) -> (r: Option<Ghost<St>>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s1),
        s1.phase is Insert,
        q < p <= data@.len(),
        s1.ilen == p - q,
        s1.out == data@.subrange(0, q as int),
        s1.mrem >= p - q,
        hdr_ok(*h, s1),
        bm_ok(*old(m), s1),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        grows(old(bw).bits(), final(bw).bits()),
        r matches Some(t) ==> {
            &&& good(final(bw).bits(), t@)
            &&& hdr_ok(*h, t@)
            &&& bm_ok(*final(m), t@)
            &&& t@.out == data@.subrange(0, p as int)
            &&& t@.mrem == s1.mrem - (p - q)
            &&& t@.phase == (if t@.mrem == 0 { Phase::MetaDone } else { Phase::Dist })
            &&& t@ == (St { phase: t@.phase, pos: t@.pos, out: t@.out, blen: t@.blen, bt: t@.bt, bt2: t@.bt2, ilen: 0, mrem: t@.mrem, ..s1 })
            &&& final(m).blen@[1] == old(m).blen@[1]
            &&& final(m).blen@[2] == old(m).blen@[2]
        },
{
    let ghost w0 = bw.bits();
    let ghost mut st = s1;
    proof {
        lemma_grows_refl(w0);
    }
    let mut k = q;
    while k < p
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            w0 == old(bw).bits(),
            grows(w0, bw.bits()),
            good(bw.bits(), st),
            q <= k <= p <= data@.len(),
            st.phase is Insert,
            st.ilen == p - k,
            st.out == data@.subrange(0, k as int),
            st.mrem == s1.mrem - (k - q),
            s1.mrem >= p - q,
            hdr_ok(*h, st),
            bm_ok(*m, st),
            st == (St { phase: st.phase, pos: st.pos, out: st.out, blen: st.blen, bt: st.bt, bt2: st.bt2, ilen: st.ilen, mrem: st.mrem, ..s1 }),
            m.blen@[1] == old(m).blen@[1],
            m.blen@[2] == old(m).blen@[2],
        decreases p - k,
    {
        if m.blen[0] == 0 {
            let ghost wk = bw.bits();
            let ghost m0 = *m;
            let g = put_switch(bw, h, m, cats, 0, Ghost(st));
            proof {
                lemma_grows_trans(w0, wk, bw.bits());
            }
            match g {
                Some(t) => {
                    proof {
                        assert(m.blen@[1] == m0.blen@[1]);
                        assert(m.blen@[2] == m0.blen@[2]);
                        st = t@;
                    }
                },
                None => return None,
            }
        }
        let bt0 = m.bt[0] as usize;
        if bt0 >= h.modes.len() || bt0 >= 0x1_0000 {
            return None;
        }
        let mode = h.modes[bt0];
        if mode >= 4 {
            return None;
        }
        let b1: u8 = if k >= 1 { data[k - 1] } else { 0 };
        let b2: u8 = if k >= 2 { data[k - 2] } else { 0 };
        let ctx = crate::decoder::lit_ctx(mode as usize, b1, b2);
        let idx = bt0 * 64 + ctx;
        if idx >= h.cmap.len() {
            return None;
        }
        let tree = h.cmap[idx] as usize;
        if tree >= h.lt.len() {
            return None;
        }
        let x = data[k];
        let lh = &h.lt[tree];
        if !has_code(lh, x as usize) {
            return None;
        }
        let ghost wk = bw.bits();
        proof {
            assert(st.out.len() == k);
            assert(p1(st.out) == b1);
            assert(p2(st.out) == b2);
            assert(st.cmodes[st.bt[0]] == mode);
            assert(lit_idx(st) == idx);
            assert(st.lit[tree as int] == lh.lens@);
            lemma_lit(wk, st, x);
        }
        let (v, n) = lh.sym(x as usize);
        bw.put64(v, n);
        let ghost u = code_of(lh.lens@, x as int);
        let ghost t = after_lit(st, x, (wk.len() + u.len()) as int);
        proof {
            lemma_adv(wk, u, st, t, bw.bits());
            lemma_grows_app(w0, wk, u);
            assert(data@.subrange(0, k as int).push(x) =~= data@.subrange(0, k + 1));
        }
        let b0 = m.blen[0];
        m.blen.set(0, b0 - 1);
        proof {
            st = t;
            assert forall|j: int| 0 <= j < 3 implies st.blen[j] == #[trigger] m.blen@[j] as int by {}
        }
        k = k + 1;
        if k == p {
            return Some(Ghost(st));
        }
    }
    None
}

/// The distance `d` that code `dcode` (below 16) stands for.
fn short_dist_exec(dcode: u8, dr: [u32; 4]) -> (r: i64)
    requires
        dcode < 16,
    ensures
        r as int == short_dist(dcode as int, drs(dr)),
{
    let k = dcode as i64;
    if dcode < 4 {
        dr[dcode as usize] as i64
    } else if dcode < 10 {
        let j = k - 4;
        let delta = if j % 2 == 0 { -(j / 2 + 1) } else { j / 2 + 1 };
        dr[0] as i64 + delta
    } else {
        let j = k - 10;
        let delta = if j % 2 == 0 { -(j / 2 + 1) } else { j / 2 + 1 };
        dr[1] as i64 + delta
    }
}

/// `dist_value(dcode, extra, 0, 0)`, for `16 <= dcode < 64`.
fn dist_value_exec(dcode: u8, extra: u32) -> (r: i64)
    requires
        16 <= dcode < 64,
        (extra as nat) < pow2(dext(dcode as int)),
    ensures
        r as int == dist_value(dcode as int, extra as int, 0, 0),
        r >= 1,
{
    let x = (dcode - 16) as u32;
    let nb = 1 + x / 2;
    let ghost xi = dcode as int - 16;
    proof {
        lemma_pow2_small();
        crate::mblock::lemma_shl1_24();
        assert(nb <= 24);
        assert(xi / 1 == xi);
        assert(xi % 1 == 0);
        assert(dist_extra(dcode as int, 0, 0) == nb);
        assert(dext(dcode as int) == nb);
    }
    let p = shl1(nb) as i64;
    proof {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, nb as nat);
        assert(2 <= p <= 0x100_0000);
        assert((extra as int) < p);
        assert(dist_value(dcode as int, extra as int, 0, 0) == ((2 + xi % 2) * p - 4 + extra) * 1 + 0 + 0 + 1);
    }
    let off = if x % 2 == 0 { 2 * p - 4 } else { 3 * p - 4 };
    off + extra as i64 + 1
}

/// Where a copy from distance `d` can reach back to: the output so far,
/// at most the window.
pub open spec fn maxd_of(p: int, wb: int) -> int {
    max_distance(p, wb)
}

/// The command `x` at `q`, then its literals, distance and copy (or
/// dictionary word). Returns where the next command starts.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn put_cmd(bw: &mut BitWriter, data: &[u8], q: usize, end: usize, x: &Cmd, dr: &mut [u32; 4], h: &Hdr, m: &mut Bm, cats: &Vec<CatPlan>, wb: u32,
    Ghost(s): Ghost<St>) -> (r: Option<(usize, Ghost<St>)>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s),
        s.phase is CmdBegin,
        body(s, data@, q as int, end as int, wb as int, drs(*old(dr)), *h, *old(m)),
        q < end <= data@.len(),
        16 <= wb <= 24,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        grows(old(bw).bits(), final(bw).bits()),
        r matches Some((q2, t)) ==> {
            &&& good(final(bw).bits(), t@)
            &&& q < q2 <= end
            &&& body(t@, data@, q2 as int, end as int, wb as int, drs(*final(dr)), *h, *final(m))
            &&& if q2 == end { t@.phase is MetaDone } else { t@.phase is CmdBegin }
        },
{
    let ghost w0 = bw.bits();
    let ghost mut st = s;
    proof {
        lemma_grows_refl(w0);
        lemma_pow2_small();
        crate::mblock::lemma_tables_small();
        crate::mblock::lemma_shl1_24();
    }
    // A command block switch.
    if m.blen[1] == 0 {
        let g = put_switch(bw, h, m, cats, 1, Ghost(st));
        match g {
            Some(t) => {
                proof {
                    st = t@;
                }
            },
            None => return None,
        }
    }
    let ghost w1 = bw.bits();
    proof {
        assert(grows(w0, w1));
    }
    // The insert-and-copy symbol.
    let sym = x.sym;
    if sym >= 704 {
        return None;
    }
    let bt1 = m.bt[1] as usize;
    if bt1 >= h.ct.len() {
        return None;
    }
    let ch = &h.ct[bt1];
    if !has_code(ch, sym as usize) {
        return None;
    }
    let (ic, cc) = crate::cwrite::sym_codes(sym);
    let ilen = x.ins;
    let clen = x.clen;
    if ilen < INS_BASE[ic] || ilen as u64 >= INS_BASE[ic] as u64 + shl1(INS_EXTRA[ic] as u32) {
        return None;
    }
    if clen < CPY_BASE[cc] || clen as u64 >= CPY_BASE[cc] as u64 + shl1(CPY_EXTRA[cc] as u32) {
        return None;
    }
    if ilen as usize > end - q {
        return None;
    }
    proof {
        assert(st.cmd[st.bt[1]] == ch.lens@);
        lemma_cmd(w1, st, sym as int, ilen as int, clen as int);
    }
    let (cv, cn) = ch.sym(sym as usize);
    bw.put64(cv, cn);
    bw.put(ilen - INS_BASE[ic], INS_EXTRA[ic] as u32);
    bw.put(clen - CPY_BASE[cc], CPY_EXTRA[cc] as u32);
    let ghost u1 = cmd_bits(ch.lens@, sym as int, ilen as int, clen as int);
    let ghost s1 = after_cmd(st, sym as int, ilen as int, clen as int, (w1.len() + u1.len()) as int);
    proof {
        assert(bw.bits() =~= w1 + u1);
        lemma_adv(w1, u1, st, s1, bw.bits());
        lemma_grows_app(w0, w1, u1);
        lemma_hdr_keep(*h, st, s1);
    }
    let b1 = m.blen[1];
    m.blen.set(1, b1 - 1);
    proof {
        st = s1;
        assert forall|j: int| 0 <= j < 3 implies st.blen[j] == #[trigger] m.blen@[j] as int by {}
    }
    // The literals.
    let p = q + ilen as usize;
    if ilen > 0 {
        let ghost w2 = bw.bits();
        let g = put_lits(bw, data, q, p, h, m, cats, Ghost(st));
        proof {
            lemma_grows_trans(w0, w2, bw.bits());
        }
        match g {
            Some(t) => {
                proof {
                    st = t@;
                }
            },
            None => return None,
        }
        if p == end {
            return Some((p, Ghost(st)));
        }
    }
    proof {
        assert(st.phase is Dist);
        assert(st.out == data@.subrange(0, p as int));
        assert(st.mrem == end - p);
        assert(st.clen == clen);
        assert(st.dctx == dist_context(sym as int));
        assert(st.implicit == (sym < 128));
        assert(st.dr == drs(*dr));
        assert(CPY_BASE[cc as int] >= 2);
    }
    let ghost w2 = bw.bits();
    let g = put_dist(bw, data, p, end, x, cc, dr, h, m, cats, wb, Ghost(st));
    proof {
        lemma_grows_trans(w0, w2, bw.bits());
    }
    g
}

/// The distance of command `x`, whose literals end at `p`, then its copy
/// or dictionary word.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn put_dist(bw: &mut BitWriter, data: &[u8], p: usize, end: usize, x: &Cmd, cc: usize, dr: &mut [u32; 4], h: &Hdr, m: &mut Bm, cats: &Vec<CatPlan>, wb: u32,
    Ghost(s): Ghost<St>) -> (r: Option<(usize, Ghost<St>)>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s),
        s.phase is Dist,
        s.out == data@.subrange(0, p as int),
        s.mrem == end - p,
        s.wbits == wb,
        s.dr == drs(*old(dr)),
        !s.last,
        hdr_ok(*h, s),
        bm_ok(*old(m), s),
        s.clen == x.clen,
        x.sym < 704,
        cc == cpy_code(x.sym as int),
        cc < 24,
        s.dctx == dist_context(x.sym as int),
        s.implicit == (x.sym < 128),
        CPY_BASE[cc as int] >= 2,
        x.clen >= CPY_BASE[cc as int],
        p < end <= data@.len(),
        16 <= wb <= 24,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        grows(old(bw).bits(), final(bw).bits()),
        r matches Some((q2, t)) ==> {
            &&& good(final(bw).bits(), t@)
            &&& p < q2 <= end
            &&& body(t@, data@, q2 as int, end as int, wb as int, drs(*final(dr)), *h, *final(m))
            &&& if q2 == end { t@.phase is MetaDone } else { t@.phase is CmdBegin }
        },
{
    let ghost w0 = bw.bits();
    let ghost mut st = s;
    let clen = x.clen;
    let sym = x.sym;
    proof {
        lemma_grows_refl(w0);
        lemma_pow2_small();
        crate::mblock::lemma_shl1_24();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, wb as nat);
    }
    let wmax: u64 = shl1(wb) - 16;
    let maxd: u64 = if (p as u64) < wmax { p as u64 } else { wmax };
    proof {
        assert(maxd as int == max_distance(p as int, wb as int));
    }
    if sym < 128 {
        // The last distance, implicitly.
        let d = dr[0];
        if d < 1 || d as u64 > maxd || clen as usize > end - p {
            return None;
        }
        let ghost s3 = St { phase: Phase::Copy, dist: st.dr[0], ..st };
        proof {
            lemma_dist_implicit(w0, st);
            assert(w0 + Seq::<nat>::empty() =~= w0);
            lemma_adv(w0, Seq::empty(), st, s3, w0);
        }
        return finish_copy(bw, data, p, end, d, clen, Ghost(s3), Ghost(w0), Ghost(*h), Ghost(*m), Ghost(drs(*dr)), wb);
    }
    // A distance block switch.
    if m.blen[2] == 0 {
        let g = put_switch(bw, h, m, cats, 2, Ghost(st));
        match g {
            Some(t) => {
                proof {
                    st = t@;
                }
            },
            None => return None,
        }
    }
    let ghost w1 = bw.bits();
    // The distance code.
    let cb = CPY_BASE[cc];
    let dctx: usize = if cb > 4 { 3 } else { (cb - 2) as usize };
    let bt2 = m.bt[2] as usize;
    if bt2 >= 0x1_0000 {
        return None;
    }
    let di = bt2 * 4 + dctx;
    if di >= h.dmap.len() {
        return None;
    }
    let dti = h.dmap[di] as usize;
    if dti >= h.dt.len() {
        return None;
    }
    let dh = &h.dt[dti];
    let dcode = x.dcode;
    if dcode >= 64 || !has_code(dh, dcode as usize) {
        return None;
    }
    let ne: u32 = if dcode < 16 { 0 } else { 1 + (dcode as u32 - 16) / 2 };
    proof {
        assert(ne == dext(dcode as int));
        assert(ne <= 24);
    }
    if x.extra as u64 >= shl1(ne) {
        return None;
    }
    let d: i64 = if dcode < 16 { short_dist_exec(dcode, *dr) } else { dist_value_exec(dcode, x.extra) };
    proof {
        assert(dtree(st) == dti as int);
        assert(st.dst[dti as int] == dh.lens@);
        assert(d as int == dval(dcode as int, x.extra as int, st.dr));
    }
    if d >= 1 && d as u64 <= maxd {
        // A copy from the window.
        if clen as usize > end - p {
            return None;
        }
        proof {
            lemma_dist_explicit(w1, st, dcode as int, x.extra as int);
        }
        let (dv, dn) = dh.sym(dcode as usize);
        bw.put64(dv, dn);
        bw.put(x.extra, ne);
        let ghost u = dist_bits(dh.lens@, dcode as int, x.extra as int);
        let ghost s3 = St {
            phase: Phase::Copy,
            pos: (w1.len() + u.len()) as int,
            blen: st.blen.update(2, st.blen[2] - 1),
            dist: d as int,
            dr: dnext(dcode as int, d as int, st.dr),
            ..st
        };
        proof {
            assert(bw.bits() =~= w1 + u);
            lemma_adv(w1, u, st, s3, bw.bits());
            lemma_grows_app(w0, w1, u);
        }
        if dcode != 0 {
            let d1 = dr[0];
            let d2 = dr[1];
            let d3 = dr[2];
            *dr = [d as u32, d1, d2, d3];
        }
        let b2 = m.blen[2];
        m.blen.set(2, b2 - 1);
        proof {
            assert(drs(*dr) =~= s3.dr);
            assert forall|j: int| 0 <= j < 3 implies s3.blen[j] == #[trigger] m.blen@[j] as int by {}
        }
        return finish_copy(bw, data, p, end, d as u32, clen, Ghost(s3), Ghost(w0), Ghost(*h), Ghost(*m), Ghost(drs(*dr)), wb);
    }
    if dcode < 16 || d as u64 <= maxd || d > 0x7FFF_FFFC || clen < 4 || clen > 24 {
        return None;
    }
    // A static dictionary word.
    let out = match dict_out(d as u64, maxd, clen) {
        Some(o) => o,
        None => return None,
    };
    let wl = out.len();
    if wl == 0 || wl > end - p || !same_bytes(data, p, out.as_slice()) {
        return None;
    }
    proof {
        assert(maxd as int == max_distance(st.out.len() as int, st.wbits));
        assert(dict_ok(st, d as int));
        lemma_dist_dict(w1, st, dcode as int, x.extra as int);
    }
    let (dv, dn) = dh.sym(dcode as usize);
    bw.put64(dv, dn);
    bw.put(x.extra, ne);
    let ghost u = dist_bits(dh.lens@, dcode as int, x.extra as int);
    let ghost s4 = dict_next(st, d as int, (w1.len() + u.len()) as int);
    proof {
        assert(bw.bits() =~= w1 + u);
        lemma_adv(w1, u, st, s4, bw.bits());
        lemma_grows_app(w0, w1, u);
        assert(data@.subrange(0, p as int) + out@ =~= data@.subrange(0, (p + wl) as int));
    }
    let b2 = m.blen[2];
    m.blen.set(2, b2 - 1);
    proof {
        assert forall|j: int| 0 <= j < 3 implies s4.blen[j] == #[trigger] m.blen@[j] as int by {}
    }
    Some((p + wl, Ghost(s4)))
}

/// The bytes of `data` from `p` are `w`.
#[verifier::spinoff_prover]
fn same_bytes(data: &[u8], p: usize, w: &[u8]) -> (r: bool)
    ensures
        r ==> p + w@.len() <= data@.len() && data@.subrange(p as int, p + w@.len()) == w@,
{
    if p > data.len() || w.len() > data.len() - p {
        return false;
    }
    let n = w.len();
    let e = p + n;
    let mut k: usize = p;
    while k < e
        invariant
            p <= k <= e,
            e == p + n,
            n == w@.len(),
            e <= data@.len(),
            forall|i: int| 0 <= i < k - p ==> #[trigger] w@[i] == data@[p + i],
        decreases e - k,
    {
        if verilith_core::prims::get(data, k) != verilith_core::prims::get(w, k - p) {
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(data@.subrange(p as int, p + n) =~= w@);
    }
    true
}

/// The word a dictionary reference to `d` (past `maxd`) with copy length
/// `len` stands for, if it is a valid one.
fn dict_out(d: u64, maxd: u64, len: u32) -> (r: Option<Vec<u8>>)
    requires
        maxd < d <= 0x7FFF_FFFC,
        4 <= len <= 24,
    ensures
        r matches Some(o) ==> {
            &&& o@ == dict_ref(len as int, d as int, maxd as int)
            &&& ((d as int - maxd - 1) / pow2(NDBITS[len as int] as nat) as int) < NTRANSFORMS
        },
{
    let addr = d - maxd - 1;
    let nd = NDBITS[len as usize] as u32;
    proof {
        assert(forall|k: int| 0 <= k < 25 ==> #[trigger] NDBITS[k] <= 24) by (compute);
        assert(forall|k: int| 0 <= k < 25 ==> #[trigger] DOFFSET[k] <= 122784) by (compute);
        crate::mblock::lemma_shl1_24();
    }
    let pw = shl1(nd);
    let idx = addr % pw;
    let tid = addr / pw;
    if tid >= 121 {
        return None;
    }
    let l = len as u64;
    if idx > 0x10_0000 {
        return None;
    }
    proof {
        assert((idx + 1) * l <= 0x1000_0000) by (nonlinear_arith)
            requires
                idx <= 0x10_0000,
                l <= 24,
        ;
    }
    if DOFFSET[len as usize] as u64 + (idx + 1) * l > 122784 {
        return None;
    }
    let word = crate::words::dict_word(len as usize, idx as usize);
    let mut out: Vec<u8> = Vec::new();
    let mut mid: Vec<u8> = Vec::new();
    crate::words::transform_into(&mut out, &mut mid, word, tid as usize);
    Some(out)
}

/// The copy of `clen` bytes from `d` back, at `p`.
#[verifier::spinoff_prover]
fn finish_copy(bw: &mut BitWriter, data: &[u8], p: usize, end: usize, d: u32, clen: u32, Ghost(s3): Ghost<St>, Ghost(w0): Ghost<Seq<nat>>,
    Ghost(h): Ghost<Hdr>, Ghost(m): Ghost<Bm>, Ghost(dr): Ghost<Seq<int>>, wb: u32) -> (r: Option<(usize, Ghost<St>)>)
    requires
        old(bw).wf(),
        good(old(bw).bits(), s3),
        grows(w0, old(bw).bits()),
        s3.phase is Copy,
        s3.out == data@.subrange(0, p as int),
        s3.mrem == end - p,
        s3.clen == clen,
        s3.dist == d,
        s3.wbits == wb,
        s3.dr == dr,
        !s3.last,
        hdr_ok(h, s3),
        bm_ok(m, s3),
        1 <= d <= p,
        clen >= 2,
        p + clen <= end <= data@.len(),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        grows(w0, final(bw).bits()),
        r matches Some((q2, t)) ==> {
            &&& good(final(bw).bits(), t@)
            &&& q2 == p + clen
            &&& body(t@, data@, q2 as int, end as int, wb as int, dr, h, m)
            &&& if q2 == end { t@.phase is MetaDone } else { t@.phase is CmdBegin }
        },
{
    let cl = clen as usize;
    let ds = d as usize;
    let k = verilith_core::lz::eq_len(data, p - ds, p, cl);
    if k != cl {
        return None;
    }
    let ghost w = bw.bits();
    let ghost s4 = St { phase: after_data(s3.mrem - s3.clen), out: data@.subrange(0, p + s3.clen), clen: 0, mrem: s3.mrem - s3.clen, ..s3 };
    proof {
        assert forall|j: int| p <= j < p + cl implies #[trigger] data@[j] == data@[j - ds] by {
            assert(data@[(p - ds) + (j - p)] == data@[p + (j - p)]);
        }
        lemma_copy(w, s3, data@, p as int);
        assert(w + Seq::<nat>::empty() =~= w);
        lemma_adv(w, Seq::empty(), s3, s4, w);
    }
    Some((p + cl, Ghost(s4)))
}

/// Writes `data[start..end]` as one compressed meta-block with the header
/// `p` and the commands `cmds`, or returns false (having written bits that
/// the caller takes back).
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn put_mb_in(e: &mut Enc, dr: &mut [u32; 4], wb: u32, data: &[u8], start: usize, end: usize, cmds: &[Cmd], p: &MbPlan) -> (r: bool)
    requires
        old(e).ok(),
        old(e).st@.phase is MetaHeader,
        old(e).st@.out == data@.subrange(0, start as int),
        old(e).st@.wbits == wb,
        old(e).st@.dr == drs(*old(dr)),
        16 <= wb <= 24,
        start < end <= data@.len(),
        end - start <= 0x100_0000,
    ensures
        final(e).bw.wf(),
        final(e).bw.sent() == old(e).bw.sent(),
        grows(old(e).bw.bits(), final(e).bw.bits()),
        r ==> {
            &&& final(e).ok()
            &&& final(e).st@.phase is MetaHeader
            &&& final(e).st@.wbits == wb
            &&& final(e).st@.dr == drs(*final(dr))
            &&& final(e).st@.out == data@.subrange(0, end as int)
        },
{
    let ghost w0 = e.bw.bits();
    let hm = put_hdr(e, end - start, p);
    let (h, mut m) = match hm {
        Some(x) => x,
        None => return false,
    };
    let ghost mut st = e.st@;
    let mut q = start;
    let mut i: usize = 0;
    let n = cmds.len();
    while q < end
        invariant
            e.bw.wf(),
            e.bw.sent() == old(e).bw.sent(),
            w0 == old(e).bw.bits(),
            grows(w0, e.bw.bits()),
            good(e.bw.bits(), st),
            start <= q <= end,
            end <= data@.len(),
            16 <= wb <= 24,
            n == cmds@.len(),
            body(st, data@, q as int, end as int, wb as int, drs(*dr), h, m),
            if q == end { st.phase is MetaDone } else { st.phase is CmdBegin },
        decreases end - q,
    {
        if i >= n {
            return false;
        }
        let ghost wq = e.bw.bits();
        let g = put_cmd(&mut e.bw, data, q, end, &cmds[i], dr, &h, &mut m, &p.cats, wb, Ghost(st));
        proof {
            lemma_grows_trans(w0, wq, e.bw.bits());
        }
        match g {
            Some((q2, t)) => {
                proof {
                    st = t@;
                }
                q = q2;
            },
            None => return false,
        }
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

/// Writes `data[start..end]` as one compressed meta-block with the header
/// `p` and the commands `cmds`, if every check passes and it is no larger
/// than storing the bytes; otherwise writes nothing and returns false.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn put_mb(e: &mut Enc, dr: &mut [u32; 4], wb: u32, data: &[u8], start: usize, end: usize, cmds: &[Cmd], p: &MbPlan) -> (r: bool)
    requires
        old(e).ok(),
        old(e).st@.phase is MetaHeader,
        old(e).st@.out == data@.subrange(0, start as int),
        old(e).st@.wbits == wb,
        old(e).st@.dr == drs(*old(dr)),
        16 <= wb <= 24,
        start < end <= data@.len(),
        end - start <= 0x100_0000,
    ensures
        final(e).ok(),
        final(e).bw.sent() == old(e).bw.sent(),
        final(e).st@.phase is MetaHeader,
        final(e).st@.wbits == wb,
        final(e).st@.dr == drs(*final(dr)),
        final(e).st@.out == if r { data@.subrange(0, end as int) } else { data@.subrange(0, start as int) },
{
    let mk = e.bw.mark();
    let ghost s0 = e.st@;
    let dr0 = *dr;
    if put_mb_in(e, dr, wb, data, start, end, cmds, p) {
        // A stored block costs about its bytes and a few header bytes.
        let used = e.bw.bits_since(&mk);
        let stored = 8 * (end - start) as u64 + 48;
        if used <= stored {
            return true;
        }
    }
    e.bw.reset(&mk);
    e.st = Ghost(s0);
    *dr = dr0;
    false
}

} // verus!
