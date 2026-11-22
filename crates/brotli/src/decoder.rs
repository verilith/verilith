//! The decoder: `spec::St` as Rust state, and `Decoder::run`, which takes
//! steps of `spec::step` over a window of the input until the window ends,
//! the output ring is full, the stream ends, or it is malformed.
//!
//! Output goes to a ring buffer that holds at least the last
//! `spec::max_distance` bytes, and every byte not yet handed to the caller.
//!
//! The proof: the decoder keeps a ghost count `steps` of spec steps taken,
//! and `run(b, init(), steps)` is the decoder's state (`reached`). Each
//! exec step takes one or more spec steps.
use crate::bitread::*;
use crate::dict::*;
use crate::huffman::*;
use crate::items::*;
use crate::prefix::*;
use crate::words::*;
#[cfg(verus_only)]
use crate::spec;
#[cfg(verus_only)]
use crate::spec::{bits, Cm, Kind, Pc, Phase, St, Step, R};
#[cfg(verus_only)]
use verilith_core::bits::lemma_bits_bound;
use crate::spec::{CELL, CPY_BASE, CPY_EXTRA, DOFFSET, INS_BASE, INS_EXTRA, NDBITS};
use crate::tables::{CONTEXT_LUT, PREFIX_SUFFIX, PS_MAP, TRANSFORMS};
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub const BLOCK_CAP: u32 = 0x100_0000;

/// A dictionary word, transformed, is shorter than this.
pub const MAX_WORD: u64 = 64;

#[verifier::spinoff_prover]
pub proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// Output beyond this many bytes is refused (`Status::Limit`).
pub const MAX_OUT: u64 = 0x4000_0000_0000_0000;

/// `spec::Phase`, with the category, map or group as a number.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum Ph {
    WBits,
    MetaHeader,
    Metadata,
    Uncompressed,
    NBlockTypes(u8),
    BTypeCode(u8),
    BCountCode(u8),
    BCount(u8),
    DistParams,
    CModes,
    CMap(u8),
    Trees(u8),
    CmdBegin,
    Insert,
    Dist,
    Copy,
    MetaDone,
    Done,
}

pub open spec fn phase_of(p: Ph) -> Phase {
    match p {
        Ph::WBits => Phase::WBits,
        Ph::MetaHeader => Phase::MetaHeader,
        Ph::Metadata => Phase::Metadata,
        Ph::Uncompressed => Phase::Uncompressed,
        Ph::NBlockTypes(c) => Phase::NBlockTypes(c as int),
        Ph::BTypeCode(c) => Phase::BTypeCode(c as int),
        Ph::BCountCode(c) => Phase::BCountCode(c as int),
        Ph::BCount(c) => Phase::BCount(c as int),
        Ph::DistParams => Phase::DistParams,
        Ph::CModes => Phase::CModes,
        Ph::CMap(w) => Phase::CMap(w as int),
        Ph::Trees(g) => Phase::Trees(g as int),
        Ph::CmdBegin => Phase::CmdBegin,
        Ph::Insert => Phase::Insert,
        Ph::Dist => Phase::Dist,
        Ph::Copy => Phase::Copy,
        Ph::MetaDone => Phase::MetaDone,
        Ph::Done => Phase::Done,
    }
}

/// How far into a compressed meta-block's header the phase is (0 and 1:
/// not in a compressed meta-block; 30: the commands).
pub open spec fn stage(p: Ph) -> int {
    match p {
        Ph::WBits => 0,
        Ph::NBlockTypes(c) => 10 + 4 * c,
        Ph::BTypeCode(c) => 11 + 4 * c,
        Ph::BCountCode(c) => 12 + 4 * c,
        Ph::BCount(c) => 13 + 4 * c,
        Ph::DistParams => 22,
        Ph::CModes => 23,
        Ph::CMap(w) => 24 + w,
        Ph::Trees(g) => 26 + g,
        Ph::CmdBegin | Ph::Insert | Ph::Dist | Ph::Copy => 30,
        _ => 1,
    }
}

/// The indices in the phase are in range.
pub open spec fn ph_ok(p: Ph) -> bool {
    match p {
        Ph::NBlockTypes(c) | Ph::BTypeCode(c) | Ph::BCountCode(c) | Ph::BCount(c) => c < 3,
        Ph::CMap(w) => w < 2,
        Ph::Trees(g) => g < 3,
        _ => true,
    }
}

/// Why `run` stopped.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum Status {
    /// The window ends before the next item.
    Short,
    /// The stream is malformed.
    Bad,
    /// The stream ended.
    Done,
    /// The output ring is full: hand some output to the caller first.
    Full,
    /// `run` did its share of steps; call again.
    Yield,
    /// The output would exceed `MAX_OUT` bytes.
    Limit,
}

/// The decoder's state for reading a context map (`spec::Cm`).
pub struct Cmx {
    pub stage: u8,
    pub ntrees: u32,
    pub rlemax: u32,
    pub code: HCode,
    pub map: Vec<u8>,
    /// The code lengths of `code`.
    pub lens: Ghost<Seq<u8>>,
}

impl Cmx {
    pub open spec fn view(&self) -> Cm {
        Cm {
            stage: self.stage as int,
            ntrees: self.ntrees as int,
            rlemax: self.rlemax as int,
            code: self.lens@,
            map: self.map@,
        }
    }

    #[verifier::spinoff_prover]
    pub fn new() -> (r: Cmx)
        ensures
            r.view() == spec::cm_init(),
    {
        let r = Cmx { stage: 0, ntrees: 0, rlemax: 0, code: empty_code(), map: Vec::new(), lens: Ghost(Seq::empty()) };
        assert(r.map@ =~= Seq::<u8>::empty());
        r
    }
}

pub struct Decoder {
    pub ph: Ph,
    pub pos: u64,
    pub wbits: u32,
    pub last: bool,
    pub mrem: u32,
    pub nbt: [u32; 3],
    pub btc: Vec<HCode>,
    pub bcc: Vec<HCode>,
    pub blen: [u32; 3],
    pub bt: [u32; 3],
    pub bt2: [u32; 3],
    pub npostfix: u32,
    pub ndirect: u32,
    /// Extra bit count and base of every distance code, for the
    /// parameters `dnp` and `dnd`; empty until first built.
    pub dtab: Vec<u64>,
    pub dnp: u32,
    pub dnd: u32,
    pub cmodes: Vec<u8>,
    pub cmap: Vec<u8>,
    pub dmap: Vec<u8>,
    pub ntl: u32,
    pub ntd: u32,
    pub lit: Vec<HCode>,
    pub litf: Vec<u32>,
    pub litt: u64,
    pub dstf: Vec<u32>,
    pub dstt: u64,
    pub cmd: Vec<HCode>,
    pub dst: Vec<HCode>,
    pub dr: [u32; 4],
    pub ilen: u32,
    pub clen: u32,
    pub dctx: u32,
    pub implicit: bool,
    pub dist: u32,
    pub pc: Pcx,
    pub cm: Cmx,
    /// The output ring: byte `i` of the output is at `ring[i % ring.len()]`
    /// (the size is a power of two, `1 << rbits`, or 0 before any output).
    pub ring: Vec<u8>,
    pub rbits: u32,
    /// Bytes decoded, and bytes handed out.
    pub total: u64,
    pub flushed: u64,
    /// Scratch space for a transformed dictionary word.
    pub word: Vec<u8>,
    /// The code lengths of the prefix codes.
    pub btcl: Ghost<Seq<Seq<u8>>>,
    pub bccl: Ghost<Seq<Seq<u8>>>,
    pub litl: Ghost<Seq<Seq<u8>>>,
    pub cmdl: Ghost<Seq<Seq<u8>>>,
    pub dstl: Ghost<Seq<Seq<u8>>>,
    /// Everything decoded.
    pub out: Ghost<Seq<u8>>,
    /// Spec steps taken.
    pub steps: Ghost<nat>,
}

pub open spec fn seq3(a: [u32; 3]) -> Seq<int> {
    seq![a[0] as int, a[1] as int, a[2] as int]
}

/// Entry `dcode` of the distance table: the number of extra bits in the low
/// byte, the distance with all extra bits zero above it.
pub open spec fn dt_ent(dcode: int, np: int, nd: int) -> int {
    if dcode < 16 {
        0
    } else if dcode < 16 + nd {
        (dcode - 15) * 256
    } else {
        spec::dist_value(dcode, 0, np, nd) * 256 + spec::dist_extra(dcode, np, nd)
    }
}

/// The fields of a far entry fit their bytes.
pub open spec fn dt_fits(dcode: int, np: int, nd: int) -> bool {
    dcode >= 16 + nd ==> 1 <= spec::dist_extra(dcode, np, nd) <= 24 && 1 <= spec::dist_value(dcode, 0, np, nd) < 0x4000_0000
}

/// What a table entry says once split into its two fields.
#[verifier::spinoff_prover]
pub proof fn lemma_dt_ent(dcode: int, np: u32, nd: u32, ent: u64)
    requires
        np <= 3,
        nd <= 120,
        16 <= dcode < spec::dist_alpha(np as int, nd as int),
        ent == dt_ent(dcode, np as int, nd as int),
        dt_fits(dcode, np as int, nd as int),
    ensures
        dcode < 16 + nd ==> ent & 0xff == 0 && ent >> 8 == dcode - 15,
        dcode >= 16 + nd ==> (ent & 0xff) as nat == spec::dist_extra(dcode, np as int, nd as int) && 1 <= (ent & 0xff) <= 24
            && ent >> 8 == spec::dist_value(dcode, 0, np as int, nd as int) && 1 <= (ent >> 8) < 0x4000_0000,
{
    lemma2_to64();
    lemma_pow2_le(np as nat, 3);
    if dcode < 16 + nd {
        let v = (dcode - 15) as u64;
        assert(ent & 0xff == 0 && ent >> 8 == v) by (bit_vector)
            requires
                ent == v * 256,
                v < 0x1000,
        ;
    } else {
        let v = spec::dist_value(dcode, 0, np as int, nd as int) as u64;
        let n = spec::dist_extra(dcode, np as int, nd as int) as u64;
        assert(ent & 0xff == n && ent >> 8 == v) by (bit_vector)
            requires
                ent == v * 256 + n,
                v < 0x4000_0000,
                n <= 24,
        ;
    }
}

/// The distance is linear in its extra bits.
pub proof fn lemma_dist_value_lin(dcode: int, e: int, np: int, nd: int)
    ensures
        spec::dist_value(dcode, e, np, nd) == spec::dist_value(dcode, 0, np, nd) + e * pow2(np as nat),
{
    let x = dcode - nd - 16;
    let nb = spec::dist_extra(dcode, np, nd);
    let hcode = x / pow2(np as nat) as int;
    let offset = (2 + hcode % 2) * pow2(nb) - 4;
    let pp = pow2(np as nat) as int;
    assert((offset + e) * pp == (offset + 0) * pp + e * pp) by (nonlinear_arith);
}

#[verifier::opaque]
pub open spec fn dtab_ok(t: Seq<u64>, np: u32, nd: u32) -> bool {
    &&& np <= 3
    &&& nd <= 120
    &&& t.len() == spec::dist_alpha(np as int, nd as int)
    &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] == dt_ent(i, np as int, nd as int) && dt_fits(i, np as int, nd as int)
}

/// The distance table for `np` and `nd`.
#[verifier::spinoff_prover]
pub fn mk_dtab(np: u32, nd: u32) -> (v: Vec<u64>)
    requires
        np <= 3,
        nd <= 120,
    ensures
        dtab_ok(v@, np, nd),
        v@.len() != 0,
{
    proof {
        lemma2_to64();
        lemma_pow2_le(np as nat, 3);
        vstd::bits::lemma_u32_shl_is_mul(48, np);
    }
    let alpha = (16 + nd + (48u32 << np)) as usize;
    let mut v: Vec<u64> = Vec::with_capacity(alpha);
    let mut i: usize = 0;
    while i < alpha
        invariant
            np <= 3,
            nd <= 120,
            alpha == spec::dist_alpha(np as int, nd as int),
            alpha <= 520,
            i <= alpha,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == dt_ent(j, np as int, nd as int) && dt_fits(j, np as int, nd as int),
        decreases alpha - i,
    {
        let e: u64 = if i < 16 {
            0
        } else if i < 16 + nd as usize {
            (i as u64 - 15) * 256
        } else {
            let nb = dist_nbits(i as u32, np, nd);
            proof {
                lemma_pow2_pos(nb as nat);
            }
            let d = dist_val(i as u32, 0, np, nd, nb);
            d * 256 + nb
        };
        v.push(e);
        i = i + 1;
    }
    proof {
        reveal(dtab_ok);
    }
    v
}

/// The last four distances `dr`, held as a ring `drb` whose newest entry
/// is at `di`.
pub open spec fn dr_ring(drb: [u32; 4], di: usize, dr: [u32; 4]) -> bool {
    &&& di < 4
    &&& dr[0] == drb[di as int]
    &&& dr[1] == drb[(di + 1) % 4]
    &&& dr[2] == drb[(di + 2) % 4]
    &&& dr[3] == drb[(di + 3) % 4]
}

pub open spec fn seq4(a: [u32; 4]) -> Seq<int> {
    seq![a[0] as int, a[1] as int, a[2] as int, a[3] as int]
}

/// Every code is a valid table for its lengths, over `alpha` symbols.
pub open spec fn codes_ok(h: Seq<HCode>, l: Seq<Seq<u8>>, alpha: int) -> bool {
    &&& h.len() == l.len()
    &&& forall|i: int| 0 <= i < h.len() ==> #[trigger] hcode_ok(h[i], l[i]) && l[i].len() == alpha
}

#[verifier::spinoff_prover]
pub proof fn lemma_codes_push(h: Seq<HCode>, l: Seq<Seq<u8>>, x: HCode, lx: Seq<u8>, alpha: int)
    requires
        codes_ok(h, l, alpha),
        hcode_ok(x, lx),
        lx.len() == alpha,
    ensures
        codes_ok(h.push(x), l.push(lx), alpha),
{
    assert forall|i: int| 0 <= i < h.len() + 1 implies #[trigger] hcode_ok(h.push(x)[i], l.push(lx)[i])
        && l.push(lx)[i].len() == alpha by {
        if i < h.len() {
            assert(h.push(x)[i] == h[i]);
            assert(l.push(lx)[i] == l[i]);
            assert(hcode_ok(h[i], l[i]));
        }
    }
}

/// `run` takes `n` steps from `s`: the step after a reached state.
#[verifier::spinoff_prover]
pub proof fn lemma_run_extend(b: Seq<u8>, s0: St, n: nat, s: St)
    requires
        spec::run(b, s0, n) == Step::Next(s),
        !(s.phase is Done),
    ensures
        spec::run(b, s0, n + 1) == spec::step(b, s),
    decreases n,
{
    if n == 0 {
        assert(s == s0);
        match spec::step(b, s0) {
            Step::Next(s1) => {
                assert(spec::run(b, s1, 0) == Step::Next(s1));
            },
            _ => {},
        }
    } else {
        assert(!(s0.phase is Done)) by {
            if s0.phase is Done {
                assert(spec::run(b, s0, n) == Step::Next(s0));
            }
        }
        match spec::step(b, s0) {
            Step::Next(s1) => {
                lemma_run_extend(b, s1, (n - 1) as nat, s);
                assert((n + 1 - 1) as nat == n);
            },
            _ => {},
        }
    }
}

/// The step after a reached state is malformed: the stream is rejected.
#[verifier::spinoff_prover]
pub proof fn lemma_rejects(b: Seq<u8>, n: nat, s: St)
    requires
        spec::run(b, spec::init(), n) == Step::Next(s),
        !(s.phase is Done),
        spec::step(b, s) is Bad,
    ensures
        spec::rejects(b),
{
    lemma_run_extend(b, spec::init(), n, s);
}

/// The ring holds the last `ring.len() - 16` bytes of output (all of the
/// last `ring.len()` until it wraps), and every byte not handed out yet.
#[verifier::opaque]
pub open spec fn ring_ok(ring: Seq<u8>, rbits: u32, total: u64, flushed: u64, out: Seq<u8>, ph: Ph, mrem: u32, wbits: u32) -> bool {
    let r = ring.len() as int;
    let win = pow2(wbits as nat) as int;
    &&& total == out.len()
    &&& flushed <= total
    &&& total <= MAX_OUT
    &&& total + (if ph == Ph::Metadata { 0 } else { mrem as int }) <= MAX_OUT
    &&& rbits <= 24
    &&& (r == 0 ==> total == 0)
    &&& (r > 0 ==> r == pow2(rbits as nat) && 1024 <= r && ph != Ph::WBits && r <= win)
    &&& total - flushed <= r
    // The 16 bytes ahead of the write position may have been overwritten by
    // a wide copy once the ring has wrapped, unless they are still owed.
    &&& forall|i: int|
        0 <= i < total && i >= total - r && (i >= total - r + 16 || i >= flushed || total <= r) ==> #[trigger] out[i]
            == ring[i % r]
    // Below the window size, the ring holds all of the meta-block.
    &&& (r < win ==> total + (if ph == Ph::Metadata { 0 } else { mrem as int }) <= r)
}

/// The block type information of category `c`.
#[verifier::opaque]
pub open spec fn cat_ok(
    ph: Ph,
    c: int,
    nbt: [u32; 3],
    bt: [u32; 3],
    bt2: [u32; 3],
    blen: [u32; 3],
    btc: Seq<HCode>,
    btcl: Seq<Seq<u8>>,
    bcc: Seq<HCode>,
    bccl: Seq<Seq<u8>>,
) -> bool {
    let st = stage(ph);
    let n = nbt[c] as int;
    if st <= 10 + 4 * c {
        n == 1 && bt[c] == 0 && bt2[c] == 1 && blen[c] == BLOCK_CAP
    } else {
        &&& 1 <= n <= 256
        &&& (st <= 13 + 4 * c ==> n >= 2)
        &&& bt[c] < n
        &&& (n >= 2 ==> bt2[c] < n)
        &&& (n < 2 ==> bt2[c] == 1)
        &&& blen[c] <= 16625 + 0xff_ffff
        &&& (n >= 2 && st > 11 + 4 * c ==> hcode_ok(btc[c], btcl[c]) && btcl[c].len() == n + 2)
        &&& (n >= 2 && st > 12 + 4 * c ==> hcode_ok(bcc[c], bccl[c]) && bccl[c].len() == 26)
    }
}

/// The meta-block header from `NPOSTFIX` on.
#[verifier::opaque]
pub open spec fn maps_ok(
    ph: Ph,
    npostfix: u32,
    ndirect: u32,
    nbt: [u32; 3],
    cmodes: Seq<u8>,
    cmap: Seq<u8>,
    ntl: u32,
    dmap: Seq<u8>,
    ntd: u32,
) -> bool {
    let st = stage(ph);
    &&& (st > 22 ==> npostfix <= 3 && ndirect <= 120)
    &&& (st == 23 ==> cmodes.len() <= nbt[0])
    &&& (st > 23 ==> cmodes.len() == nbt[0])
    &&& (st >= 23 ==> forall|i: int| 0 <= i < cmodes.len() ==> #[trigger] cmodes[i] < 4)
    &&& (st > 24 ==> cmap.len() == 64 * nbt[0] && 1 <= ntl <= 256 && forall|i: int|
        0 <= i < cmap.len() ==> #[trigger] cmap[i] < ntl)
    &&& (st > 25 ==> dmap.len() == 4 * nbt[2] && 1 <= ntd <= 256 && forall|i: int|
        0 <= i < dmap.len() ==> #[trigger] dmap[i] < ntd)
}

/// The prefix codes of the meta-block.
#[verifier::opaque]
pub open spec fn trees_ok(
    ph: Ph,
    nbt: [u32; 3],
    ntl: u32,
    ntd: u32,
    npostfix: u32,
    ndirect: u32,
    lit: Seq<HCode>,
    litl: Seq<Seq<u8>>,
    cmd: Seq<HCode>,
    cmdl: Seq<Seq<u8>>,
    dst: Seq<HCode>,
    dstl: Seq<Seq<u8>>,
) -> bool {
    let st = stage(ph);
    &&& codes_ok(lit, litl, 256)
    &&& codes_ok(cmd, cmdl, 704)
    &&& codes_ok(dst, dstl, spec::dist_alpha(npostfix as int, ndirect as int))
    &&& (st < 26 ==> lit.len() == 0)
    &&& (st < 27 ==> cmd.len() == 0)
    &&& (st < 28 ==> dst.len() == 0)
    &&& (st == 26 ==> lit.len() <= ntl)
    &&& (st == 27 ==> cmd.len() <= nbt[1])
    &&& (st == 28 ==> dst.len() <= ntd)
    &&& (st > 26 ==> lit.len() == ntl)
    &&& (st > 27 ==> cmd.len() == nbt[1])
    &&& (st > 28 ==> dst.len() == ntd)
}

/// `spec::pc_alpha`, from the fields it reads.
pub open spec fn alpha_of(ph: Ph, nbt: [u32; 3], npostfix: u32, ndirect: u32, cm: Cm) -> int {
    match ph {
        Ph::BTypeCode(c) => nbt[c as int] + 2,
        Ph::BCountCode(_) => 26,
        Ph::CMap(_) => cm.ntrees + cm.rlemax,
        Ph::Trees(g) => if g == 0 {
            256
        } else if g == 1 {
            704
        } else {
            spec::dist_alpha(npostfix as int, ndirect as int)
        },
        _ => 0,
    }
}

/// `spec::cmap_size`, from the fields it reads.
pub open spec fn cmap_size_of(nbt: [u32; 3], w: int) -> int {
    if w == 0 {
        nbt[0] * 64
    } else {
        nbt[2] * 4
    }
}

/// Reading a prefix code or a context map.
#[verifier::opaque]
pub open spec fn reading_ok(ph: Ph, nbt: [u32; 3], npostfix: u32, ndirect: u32, pc: Pcx, cm: Cmx) -> bool {
    let a = alpha_of(ph, nbt, npostfix, ndirect, cm.view());
    &&& pc.inv(a)
    &&& (pc.started ==> 2 <= a <= 2328)
    &&& match ph {
        Ph::CMap(w) => {
            let size = cmap_size_of(nbt, w as int);
            &&& cm.stage <= 3
            &&& (cm.stage != 1 ==> !pc.started)
            &&& (cm.stage == 0 ==> cm.view() == spec::cm_init())
            &&& (cm.stage >= 1 ==> 2 <= cm.ntrees <= 256 && cm.rlemax <= 16)
            &&& (cm.stage >= 2 ==> hcode_ok(cm.code, cm.lens@) && cm.lens@.len() == cm.ntrees + cm.rlemax)
            &&& cm.map@.len() <= size
            &&& (cm.stage == 3 ==> cm.map@.len() == size)
            &&& forall|i: int| 0 <= i < cm.map@.len() ==> #[trigger] cm.map@[i] < cm.ntrees
        },
        _ => cm.view() == spec::cm_init(),
    }
}

/// The command in progress.
#[verifier::opaque]
pub open spec fn cmd_ok(
    ph: Ph,
    dctx: u32,
    dr: [u32; 4],
    ilen: u32,
    clen: u32,
    mrem: u32,
    dist: u32,
    total: u64,
    wbits: u32,
) -> bool {
    &&& dctx < 4
    &&& forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] dr[i] <= 0x7fff_fffc
    &&& (ph == Ph::Insert ==> 1 <= ilen <= mrem)
    &&& (ph == Ph::Insert || ph == Ph::Dist ==> 2 <= clen <= 2118 + 0xff_ffff)
    &&& (ph == Ph::Copy ==> 1 <= clen <= mrem && 1 <= dist <= spec::max_distance(total as int, wbits as int))
    &&& (ph == Ph::MetaHeader || ph == Ph::WBits || ph == Ph::MetaDone ==> mrem == 0)
}

impl Decoder {
    pub open spec fn view(&self) -> St {
        St {
            phase: phase_of(self.ph),
            pos: self.pos as int,
            out: self.out@,
            wbits: self.wbits as int,
            last: self.last,
            mrem: self.mrem as int,
            nbt: seq3(self.nbt),
            btc: self.btcl@,
            bcc: self.bccl@,
            blen: seq3(self.blen),
            bt: seq3(self.bt),
            bt2: seq3(self.bt2),
            npostfix: self.npostfix as int,
            ndirect: self.ndirect as int,
            cmodes: self.cmodes@,
            cmap: self.cmap@,
            dmap: self.dmap@,
            ntl: self.ntl as int,
            ntd: self.ntd as int,
            lit: self.litl@,
            cmd: self.cmdl@,
            dst: self.dstl@,
            dr: seq4(self.dr),
            ilen: self.ilen as int,
            clen: self.clen as int,
            dctx: self.dctx as int,
            implicit: self.implicit,
            dist: self.dist as int,
            pc: self.pc.view(),
            cm: self.cm.view(),
        }
    }

    /// The decoder is in the state the spec reaches after `steps` steps.
    pub open spec fn reached(&self, b: Seq<u8>) -> bool {
        spec::run(b, spec::init(), self.steps@) == Step::Next(self.view())
    }

    /// Codes read so far in group `Trees(g)`, and how many there are.
    pub open spec fn nread(&self) -> int {
        match self.ph {
            Ph::Trees(g) => if g == 0 {
                self.lit@.len() as int
            } else if g == 1 {
                self.cmd@.len() as int
            } else {
                self.dst@.len() as int
            },
            _ => 0,
        }
    }

    pub open spec fn ntrees(&self) -> int {
        match self.ph {
            Ph::Trees(g) => if g == 0 {
                self.ntl as int
            } else if g == 1 {
                self.nbt[1] as int
            } else {
                self.ntd as int
            },
            _ => 0,
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& ph_ok(self.ph)
        &&& (self.ph != Ph::WBits ==> 10 <= self.wbits <= 24)
        &&& (self.ph == Ph::WBits ==> self.pos == 0 && self.total == 0 && self.ring@.len() == 0)
        &&& self.btc@.len() == 3 && self.bcc@.len() == 3
        &&& self.btcl@.len() == 3 && self.bccl@.len() == 3
        &&& self.word@.len() == 0
        &&& (self.ph == Ph::Metadata || self.ph == Ph::Uncompressed || self.ph == Ph::Done ==> self.pos % 8 == 0)
        &&& ring_ok(self.ring@, self.rbits, self.total, self.flushed, self.out@, self.ph, self.mrem, self.wbits)
        &&& (stage(self.ph) >= 10 ==> {
            &&& cat_ok(self.ph, 0, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@)
            &&& cat_ok(self.ph, 1, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@)
            &&& cat_ok(self.ph, 2, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@)
            &&& maps_ok(self.ph, self.npostfix, self.ndirect, self.nbt, self.cmodes@, self.cmap@, self.ntl, self.dmap@, self.ntd)
            &&& trees_ok(self.ph, self.nbt, self.ntl, self.ntd, self.npostfix, self.ndirect, self.lit@, self.litl@, self.cmd@, self.cmdl@, self.dst@, self.dstl@)
        })
        &&& reading_ok(self.ph, self.nbt, self.npostfix, self.ndirect, self.pc, self.cm)
        &&& (self.dtab@.len() != 0 ==> dtab_ok(self.dtab@, self.dnp, self.dnd))
        &&& (self.litf@.len() != 0 ==> flat_ok(self.litf@, self.lit@, self.litt))
        &&& (self.dstf@.len() != 0 ==> flat_ok(self.dstf@, self.dst@, self.dstt))
        &&& (10 <= stage(self.ph) < 30 ==> self.litf@.len() == 0 && self.dstf@.len() == 0)
        &&& (stage(self.ph) > 22 ==> self.dtab@.len() != 0 && self.dnp == self.npostfix && self.dnd == self.ndirect)
        &&& (self.ph is Trees ==> self.nread() >= self.ntrees() ==> !self.pc.started)
        &&& cmd_ok(self.ph, self.dctx, self.dr, self.ilen, self.clen, self.mrem, self.dist, self.total, self.wbits)
    }

    #[verifier::spinoff_prover]
    pub fn new() -> (r: Decoder)
        ensures
            r.wf(),
            r.view() == spec::init(),
            r.steps@ == 0,
            r.flushed == 0,
    {
        let ghost e3: Seq<Seq<u8>> = seq![Seq::empty(), Seq::empty(), Seq::empty()];
        let r = Decoder {
            ph: Ph::WBits,
            pos: 0,
            wbits: 0,
            last: false,
            mrem: 0,
            nbt: [1, 1, 1],
            btc: vec![empty_code(), empty_code(), empty_code()],
            bcc: vec![empty_code(), empty_code(), empty_code()],
            blen: [BLOCK_CAP, BLOCK_CAP, BLOCK_CAP],
            bt: [0, 0, 0],
            bt2: [1, 1, 1],
            npostfix: 0,
            ndirect: 0,
            dtab: Vec::new(),
            dnp: 0,
            dnd: 0,
            cmodes: Vec::new(),
            cmap: Vec::new(),
            dmap: Vec::new(),
            ntl: 0,
            ntd: 0,
            lit: Vec::new(),
            litf: Vec::new(),
            litt: 0,
            dstf: Vec::new(),
            dstt: 0,
            cmd: Vec::new(),
            dst: Vec::new(),
            dr: [4, 11, 15, 16],
            ilen: 0,
            clen: 0,
            dctx: 0,
            implicit: false,
            dist: 0,
            pc: Pcx::new(),
            cm: Cmx::new(),
            ring: Vec::new(),
            rbits: 0,
            total: 0,
            flushed: 0,
            word: Vec::new(),
            btcl: Ghost(e3),
            bccl: Ghost(e3),
            litl: Ghost(Seq::empty()),
            cmdl: Ghost(Seq::empty()),
            dstl: Ghost(Seq::empty()),
            out: Ghost(Seq::empty()),
            steps: Ghost(0),
        };
        proof {
            assert(r.cmodes@ =~= Seq::<u8>::empty());
            assert(r.cmap@ =~= Seq::<u8>::empty());
            assert(r.dmap@ =~= Seq::<u8>::empty());
            assert(seq3(r.nbt) =~= seq![1int, 1, 1]);
            assert(seq3(r.blen) =~= seq![spec::BLOCK_CAP, spec::BLOCK_CAP, spec::BLOCK_CAP]);
            assert(seq3(r.bt) =~= seq![0int, 0, 0]);
            assert(seq3(r.bt2) =~= seq![1int, 1, 1]);
            assert(seq4(r.dr) =~= seq![4int, 11, 15, 16]);
            assert(r.view() =~= spec::init());
            reveal(ring_ok);
            reveal(reading_ok);
            reveal(cmd_ok);
            assert(r.pc.inv(0));
        }
        r
    }

    /// Bytes decoded but not handed out yet.
    #[verifier::spinoff_prover]
    pub fn pending(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.total - self.flushed,
    {
        proof {
            reveal(ring_ok);
        }
        self.total - self.flushed
    }

    /// Room in the ring for more output.
    #[verifier::spinoff_prover]
    pub fn room(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.ring@.len() - (self.total - self.flushed),
    {
        proof {
            reveal(ring_ok);
        }
        self.ring.len() as u64 - (self.total - self.flushed)
    }

    /// Copies decoded bytes out to `out[at..]`. Returns how many: as many
    /// as are waiting and fit.
    #[verifier::loop_isolation(false)]
    #[verifier::spinoff_prover]
    pub fn flush(&mut self, out: &mut [u8], at: usize) -> (n: usize)
        requires
            old(self).wf(),
            at <= old(out)@.len(),
        ensures
            final(self).wf(),
            final(self).flushed == old(self).flushed + n,
            final(self).view() == old(self).view(),
            final(self).steps == old(self).steps,
            final(self).ring == old(self).ring,
            n == vstd::math::min((old(self).total - old(self).flushed) as int, old(out)@.len() - at),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, at as int) == old(out)@.subrange(0, at as int),
            final(out)@.subrange(at as int, at + n) == old(self).out@.subrange(
                old(self).flushed as int,
                old(self).flushed + n,
            ),
    {
        let ghost o = self.out@;
        let ghost out0 = out@;
        proof {
            reveal(ring_ok);
        }
        let mut n = (self.total - self.flushed) as usize;
        if n > out.len() - at {
            n = out.len() - at;
        }
        if n == 0 {
            assert(out@.subrange(at as int, at + n) =~= o.subrange(self.flushed as int, self.flushed + n));
            return 0;
        }
        let r = self.ring.len() as u64;
        let mask = r - 1;
        let mut k: usize = 0;
        while k < n
            invariant
                r == self.ring@.len(),
                r > 0,
                r == pow2(self.rbits as nat),
                mask == r - 1,
                k <= n,
                n <= self.total - self.flushed,
                at + n <= out@.len(),
                out@.len() == out0.len(),
                out@.subrange(0, at as int) == out0.subrange(0, at as int),
                forall|j: int| at <= j < at + k ==> #[trigger] out@[j] == o[self.flushed + j - at],
            decreases n - k,
        {
            let ghost f = self.flushed;
            let i = (self.flushed + k as u64) & mask;
            proof {
                lemma_and_mask((self.flushed + k as u64) as u64, self.rbits as u64);
                lemma_mask(self.rbits as u64);
            }
            // Copy the contiguous part of the ring.
            let mut m = (r - i) as usize;
            if m > n - k {
                m = n - k;
            }
            let ghost out1 = out@;
            verilith_core::prims::copy_in(out, at + k, self.ring.as_slice(), i as usize, m);
            proof {
                assert forall|j: int| at <= j < at + k + m implies #[trigger] out@[j] == o[self.flushed + j - at] by {
                    if j < at + k {
                        assert(out@[j] == out1[j]);
                    } else {
                        let q = self.flushed + j - at;
                        assert(out@[j] == (out1.subrange(0, (at + k) as int) + self.ring@.subrange(i as int, i + m)
                            + out1.subrange(at + k + m, out1.len() as int))[j]);
                        assert(out@[j] == self.ring@[i + (j - at - k)]);
                        assert(q % (r as int) == i + (j - at - k)) by {
                            let base = (f + k) as int;
                            assert(base % (r as int) == i);
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base, r as int);
                            vstd::arithmetic::mul::lemma_mul_is_commutative(base / (r as int), r as int);
                            assert(i + (j - at - k) < r);
                            assert(q == (base / (r as int)) * (r as int) + (i + (j - at - k)));
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                                q,
                                r as int,
                                base / (r as int),
                                i + (j - at - k),
                            );
                        }
                        assert(q >= self.total - r);
                    }
                }
                assert(out@.subrange(0, at as int) =~= out0.subrange(0, at as int)) by {
                    assert forall|j: int| 0 <= j < at implies out@[j] == out0[j] by {
                        assert(out@[j] == out1[j]);
                        assert(out1.subrange(0, at as int)[j] == out0.subrange(0, at as int)[j]);
                    }
                }
            }
            k = k + m;
        }
        self.flushed = self.flushed + n as u64;
        assert(out@.subrange(at as int, at + n) =~= o.subrange(self.flushed - n, self.flushed as int));
        n
    }

    /// Hands out up to `max` decoded bytes without copying: a contiguous
    /// piece of the ring.
    #[verifier::spinoff_prover]
    pub fn take(&mut self, max: usize) -> (r: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).flushed == old(self).flushed + r@.len(),
            final(self).view() == old(self).view(),
            final(self).steps == old(self).steps,
            r@ == old(self).out@.subrange(old(self).flushed as int, old(self).flushed + r@.len()),
    {
        proof {
            reveal(ring_ok);
        }
        let mut n = self.total - self.flushed;
        if n > max as u64 {
            n = max as u64;
        }
        if n == 0 {
            assert(self.ring@.subrange(0, 0) =~= self.out@.subrange(self.flushed as int, self.flushed as int));
            return slice_subrange(self.ring.as_slice(), 0, 0);
        }
        let r = self.ring.len() as u64;
        let i = self.flushed & (r - 1);
        proof {
            lemma_and_mask(self.flushed, self.rbits as u64);
            lemma_mask(self.rbits as u64);
        }
        if n > r - i {
            n = r - i;
        }
        let ghost f = self.flushed;
        self.flushed = self.flushed + n;
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] self.ring@.subrange(i as int, i + n)[j]
                == self.out@.subrange(f as int, f + n)[j] by {
                let q = f + j;
                assert(self.out@[q] == self.ring@[q % (r as int)]);
                assert(q % (r as int) == i + j) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(f as int, r as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(q, r as int, f as int / (r as int), i + j);
                }
            }
            assert(self.ring@.subrange(i as int, i + n) =~= self.out@.subrange(f as int, f + n));
        }
        slice_subrange(self.ring.as_slice(), i as usize, (i + n) as usize)
    }
}

/// With meta-block bytes left to write, the ring is allocated.
#[verifier::spinoff_prover]
pub proof fn lemma_ring_big(d: Decoder)
    requires
        d.wf(),
        d.mrem >= 1,
        d.ph != Ph::Metadata,
    ensures
        d.ring@.len() >= 1024,
{
    reveal(ring_ok);
    reveal(cmd_ok);
    vstd::arithmetic::power2::lemma_pow2_pos(d.wbits as nat);
}

/// `wx` holds the `c` bits of the stream at `pos`, inside the window.
pub open spec fn win_ok(src: Seq<u8>, base: u64, pos: u64, wx: u64, c: u64, b: Seq<u8>) -> bool {
    &&& c <= 56
    &&& wx as nat == bits(b, pos as int, c as nat)
    &&& wx < pow2(c as nat)
    &&& pos + c <= lim(src, base as int)
}

/// The window was read in full: as many bits as fit, or up to its end.
pub open spec fn fresh(src: Seq<u8>, base: u64, pos: u64, c: u64) -> bool {
    c == 56 || pos + c == lim(src, base as int)
}

/// `step_ok`, for a step given a window: `Short` says the spec stops only
/// when the window was fresh.
pub open spec fn wstep_ok(o: Decoder, n: Decoder, r: Option<Status>, src: Seq<u8>, base: u64, b: Seq<u8>, fr: bool) -> bool {
    if r == Some(Status::Short) {
        n == o && (fr ==> full(src, base as int, b) ==> spec::step(b, o.view()) is Short)
    } else {
        step_ok(o, n, r, src, base, b)
    }
}

/// What one exec step did, from `o` to `n`.
pub open spec fn step_ok(o: Decoder, n: Decoder, r: Option<Status>, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    match r {
        None => moved(o, n, src, base, b) && o.steps@ < n.steps@ && crate::rank::rank_lt(b, n.view(), o.view()),
        Some(Status::Done) => moved(o, n, src, base, b) && n.ph == Ph::Done && (o.ph == Ph::Done ==> n == o)
            && (o.ph != Ph::Done ==> crate::rank::rank_lt(b, n.view(), o.view())),
        Some(Status::Bad) => spec::rejects(b),
        Some(Status::Short) => n == o && (full(src, base as int, b) ==> spec::step(b, o.view()) is Short),
        Some(Status::Full) => n == o && n.ring@.len() - (n.total - n.flushed) < MAX_WORD && n.ring@.len() >= 1024,
        Some(Status::Limit) => n == o && o.total + 0x1_0000_0000 > MAX_OUT,
        Some(Status::Yield) => false,
    }
}

/// What `Decoder::run` did, from `o` to `n`.
pub open spec fn run_ok(o: Decoder, n: Decoder, r: Status, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    match r {
        Status::Bad => spec::rejects(b),
        _ => {
            &&& moved(o, n, src, base, b)
            &&& (r is Done ==> n.ph == Ph::Done)
            &&& (r is Short ==> (full(src, base as int, b) ==> spec::step(b, n.view()) is Short))
            &&& (r is Full ==> n.ring@.len() - (n.total - n.flushed) < MAX_WORD && n.ring@.len() >= 1024)
            &&& (r is Limit ==> n.total + 0x1_0000_0000 > MAX_OUT)
            &&& (r is Yield ==> o.steps@ < n.steps@ && crate::rank::rank_lt(b, n.view(), o.view()))
            &&& (n == o || crate::rank::rank_lt(b, n.view(), o.view()))
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_moved_trans(o: Decoder, m: Decoder, n: Decoder, src: Seq<u8>, base: u64, b: Seq<u8>)
    requires
        moved(o, m, src, base, b),
        moved(m, n, src, base, b),
    ensures
        moved(o, n, src, base, b),
{
    assert(o.out@.is_prefix_of(n.out@)) by {
        assert forall|i: int| 0 <= i < o.out@.len() implies o.out@[i] == n.out@[i] by {
            assert(o.out@[i] == m.out@.subrange(0, o.out@.len() as int)[i]);
            assert(m.out@[i] == n.out@.subrange(0, m.out@.len() as int)[i]);
        }
        assert(o.out@ =~= n.out@.subrange(0, o.out@.len() as int));
    }
}

/// `n` is reached after `o`, with more output and nothing more handed out.
pub open spec fn moved(o: Decoder, n: Decoder, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    &&& n.wf()
    &&& n.reached(b)
    &&& n.flushed == o.flushed
    &&& o.out@.is_prefix_of(n.out@)
    &&& o.pos <= n.pos <= lim(src, base as int)
    &&& o.steps@ <= n.steps@
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_metadone(b: Seq<u8>, s: St)
    requires
        s.phase is MetaDone,
    ensures
        spec::step(b, s) == if s.last {
            match spec::pad(b, s.pos) {
                R::Ok(_, p) => Step::Next(St { phase: Phase::Done, pos: p, ..s }),
                R::Bad => Step::Bad,
                R::Short => Step::Short,
            }
        } else {
            Step::Next(St { phase: Phase::MetaHeader, ..s })
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_wbits(b: Seq<u8>, s: St)
    requires
        s.phase is WBits,
    ensures
        spec::step(b, s) == match spec::read_wbits(b, s.pos) {
            R::Ok(w, p) => Step::Next(St { phase: Phase::MetaHeader, pos: p, wbits: w, ..s }),
            R::Bad => Step::Bad,
            R::Short => Step::Short,
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_header(b: Seq<u8>, s: St)
    requires
        s.phase is MetaHeader,
    ensures
        spec::step(b, s) == match spec::read_meta_header(b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(h, p) => {
                let s1 = St { pos: p, last: h.last, mrem: h.len, ..s };
                match h.kind {
                    Kind::EmptyLast => match spec::pad(b, p) {
                        R::Ok(_, p2) => Step::Next(St { phase: Phase::Done, pos: p2, ..s1 }),
                        R::Bad => Step::Bad,
                        R::Short => Step::Short,
                    },
                    Kind::Metadata => Step::Next(St { phase: Phase::Metadata, ..s1 }),
                    Kind::Uncompressed => Step::Next(St { phase: Phase::Uncompressed, ..s1 }),
                    Kind::Compressed => Step::Next(spec::begin_compressed(s1)),
                }
            },
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_metadata(b: Seq<u8>, s: St)
    requires
        s.phase is Metadata,
    ensures
        spec::step(b, s) == if s.mrem <= 0 {
            Step::Next(St { phase: Phase::MetaDone, ..s })
        } else {
            match spec::rd(b, s.pos, 8) {
                None => Step::Short,
                Some(_) => Step::Next(St { pos: s.pos + 8, mrem: s.mrem - 1, ..s }),
            }
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_raw(b: Seq<u8>, s: St)
    requires
        s.phase is Uncompressed,
    ensures
        spec::step(b, s) == if s.mrem <= 0 {
            Step::Next(St { phase: Phase::MetaDone, ..s })
        } else {
            match spec::rd(b, s.pos, 8) {
                None => Step::Short,
                Some(x) => Step::Next(St { pos: s.pos + 8, mrem: s.mrem - 1, out: s.out.push(x as u8), ..s }),
            }
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_nbt(b: Seq<u8>, s: St, c: int)
    requires
        s.phase == Phase::NBlockTypes(c),
    ensures
        spec::step(b, s) == match spec::varlen8(b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(v, p) => {
                let s1 = St { pos: p, nbt: s.nbt.update(c, v + 1), ..s };
                if v + 1 >= 2 {
                    Step::Next(St { phase: Phase::BTypeCode(c), pc: spec::pc_init(), ..s1 })
                } else {
                    Step::Next(St { phase: spec::after_cat(c), ..s1 })
                }
            },
        },
{
    reveal(spec::step);
}

/// Reading a prefix code: the step in phases `BTypeCode`, `BCountCode`
/// and `Trees` (with codes left to read) and stage 1 of `CMap`.
#[verifier::spinoff_prover]
pub proof fn lemma_step_code(b: Seq<u8>, s: St)
    requires
        s.phase is BTypeCode || s.phase is BCountCode,
    ensures
        spec::step(b, s) == match spec::pc_step(b, s.pos, s.pc, spec::pc_alpha(s)) {
            spec::PcRes::Bad => Step::Bad,
            spec::PcRes::Short => Step::Short,
            spec::PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
            spec::PcRes::Fin(lens, p) => match s.phase {
                Phase::BTypeCode(c) => Step::Next(St {
                    phase: Phase::BCountCode(c),
                    pos: p,
                    btc: s.btc.update(c, lens),
                    pc: spec::pc_init(),
                    ..s
                }),
                Phase::BCountCode(c) => Step::Next(St {
                    phase: Phase::BCount(c),
                    pos: p,
                    bcc: s.bcc.update(c, lens),
                    pc: spec::pc_init(),
                    ..s
                }),
                _ => Step::Bad,
            },
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_bcount(b: Seq<u8>, s: St, c: int)
    requires
        s.phase == Phase::BCount(c),
    ensures
        spec::step(b, s) == match spec::read_blen(s.bcc[c], b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(len, p) => Step::Next(St { phase: spec::after_cat(c), pos: p, blen: s.blen.update(c, len), ..s }),
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_dparams(b: Seq<u8>, s: St)
    requires
        s.phase is DistParams,
    ensures
        spec::step(b, s) == match spec::rd(b, s.pos, 6) {
            None => Step::Short,
            Some(v) => {
                let np = (v % 4) as int;
                Step::Next(St {
                    phase: Phase::CModes,
                    pos: s.pos + 6,
                    npostfix: np,
                    ndirect: (v / 4) as int * pow2(np as nat),
                    cmodes: Seq::empty(),
                    ..s
                })
            },
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_cmodes(b: Seq<u8>, s: St)
    requires
        s.phase is CModes,
    ensures
        spec::step(b, s) == if s.cmodes.len() >= s.nbt[0] {
            Step::Next(St { phase: Phase::CMap(0), cm: spec::cm_init(), ..s })
        } else {
            match spec::rd(b, s.pos, 2) {
                None => Step::Short,
                Some(m) => Step::Next(St { pos: s.pos + 2, cmodes: s.cmodes.push(m as u8), ..s }),
            }
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_cmap(b: Seq<u8>, s: St, w: int)
    requires
        s.phase == Phase::CMap(w),
    ensures
        spec::step(b, s) == spec::cmap_step(b, s, w),
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_trees(b: Seq<u8>, s: St, g: int)
    requires
        s.phase == Phase::Trees(g),
    ensures
        spec::step(b, s) == if spec::nread(s, g) >= spec::ntrees(s, g) {
            if g < 2 {
                Step::Next(St { phase: Phase::Trees(g + 1), pc: spec::pc_init(), ..s })
            } else {
                Step::Next(St { phase: Phase::CmdBegin, ..s })
            }
        } else {
            match spec::pc_step(b, s.pos, s.pc, spec::pc_alpha(s)) {
                spec::PcRes::Bad => Step::Bad,
                spec::PcRes::Short => Step::Short,
                spec::PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
                spec::PcRes::Fin(lens, p) => {
                    let s1 = St { pos: p, pc: spec::pc_init(), ..s };
                    if g == 0 {
                        Step::Next(St { lit: s.lit.push(lens), ..s1 })
                    } else if g == 1 {
                        Step::Next(St { cmd: s.cmd.push(lens), ..s1 })
                    } else {
                        Step::Next(St { dst: s.dst.push(lens), ..s1 })
                    }
                },
            }
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_data(b: Seq<u8>, s: St)
    requires
        s.phase is CmdBegin || s.phase is Insert || s.phase is Dist,
    ensures
        spec::step(b, s) == match s.phase {
            Phase::CmdBegin => if s.blen[1] == 0 {
                spec::block_switch(s, b, 1)
            } else {
                spec::command(b, s)
            },
            Phase::Insert => if s.blen[0] == 0 {
                spec::block_switch(s, b, 0)
            } else {
                spec::literal(b, s)
            },
            _ => spec::distance(b, s),
        },
{
    reveal(spec::step);
}

#[verifier::spinoff_prover]
pub proof fn lemma_step_copy(b: Seq<u8>, s: St)
    requires
        s.phase is Copy,
    ensures
        spec::step(b, s) == {
            let x = s.out[s.out.len() - s.dist];
            let s1 = St { out: s.out.push(x), clen: s.clen - 1, mrem: s.mrem - 1, ..s };
            if s1.clen == 0 {
                Step::Next(St { phase: spec::after_data(s1.mrem), ..s1 })
            } else {
                Step::Next(s1)
            }
        },
{
    reveal(spec::step);
}

/// What the data phases read from the meta-block header.
#[verifier::spinoff_prover]
pub proof fn lemma_data_facts(d: Decoder)
    requires
        d.wf(),
        stage(d.ph) == 30,
    ensures
        forall|c: int| 0 <= c < 3 ==> 1 <= #[trigger] d.nbt[c] <= 256 && d.bt[c] < d.nbt[c],
        forall|c: int| 0 <= c < 3 ==> #[trigger] d.nbt[c] >= 2 ==> d.bt2[c] < d.nbt[c] && hcode_ok(d.btc@[c], d.btcl@[c])
            && d.btcl@[c].len() == d.nbt[c] + 2 && hcode_ok(d.bcc@[c], d.bccl@[c]) && d.bccl@[c].len() == 26,
        d.npostfix <= 3 && d.ndirect <= 120,
        d.cmodes@.len() == d.nbt[0],
        forall|i: int| 0 <= i < d.cmodes@.len() ==> #[trigger] d.cmodes@[i] < 4,
        d.cmap@.len() == 64 * d.nbt[0],
        forall|i: int| 0 <= i < d.cmap@.len() ==> #[trigger] d.cmap@[i] < d.ntl,
        d.dmap@.len() == 4 * d.nbt[2],
        forall|i: int| 0 <= i < d.dmap@.len() ==> #[trigger] d.dmap@[i] < d.ntd,
        d.lit@.len() == d.ntl && d.cmd@.len() == d.nbt[1] && d.dst@.len() == d.ntd,
        codes_ok(d.lit@, d.litl@, 256),
        codes_ok(d.cmd@, d.cmdl@, 704),
        codes_ok(d.dst@, d.dstl@, spec::dist_alpha(d.npostfix as int, d.ndirect as int)),
        !d.pc.started,
        d.cm.view() == spec::cm_init(),
{
    reveal(cat_ok);
    reveal(maps_ok);
    reveal(trees_ok);
    reveal(reading_ok);
}

/// The header parts of `wf` hold after a data step that keeps the header
/// and only uses up block counts.
#[verifier::spinoff_prover]
pub proof fn lemma_wf_data(o: Decoder, n: Decoder)
    requires
        o.wf(),
        stage(o.ph) == 30,
        stage(n.ph) == 30 || n.ph == Ph::MetaDone,
        n.nbt == o.nbt && n.bt == o.bt && n.bt2 == o.bt2,
        forall|c: int| 0 <= c < 3 ==> #[trigger] n.blen[c] <= o.blen[c],
        n.btc == o.btc && n.btcl == o.btcl && n.bcc == o.bcc && n.bccl == o.bccl,
        n.npostfix == o.npostfix && n.ndirect == o.ndirect,
        n.cmodes == o.cmodes && n.cmap == o.cmap && n.ntl == o.ntl && n.dmap == o.dmap && n.ntd == o.ntd,
        n.lit == o.lit && n.litl == o.litl && n.cmd == o.cmd && n.cmdl == o.cmdl && n.dst == o.dst && n.dstl == o.dstl,
        n.pc == o.pc && n.cm == o.cm,
    ensures
        stage(n.ph) >= 10 ==> {
            &&& cat_ok(n.ph, 0, n.nbt, n.bt, n.bt2, n.blen, n.btc@, n.btcl@, n.bcc@, n.bccl@)
            &&& cat_ok(n.ph, 1, n.nbt, n.bt, n.bt2, n.blen, n.btc@, n.btcl@, n.bcc@, n.bccl@)
            &&& cat_ok(n.ph, 2, n.nbt, n.bt, n.bt2, n.blen, n.btc@, n.btcl@, n.bcc@, n.bccl@)
            &&& maps_ok(n.ph, n.npostfix, n.ndirect, n.nbt, n.cmodes@, n.cmap@, n.ntl, n.dmap@, n.ntd)
            &&& trees_ok(n.ph, n.nbt, n.ntl, n.ntd, n.npostfix, n.ndirect, n.lit@, n.litl@, n.cmd@, n.cmdl@, n.dst@, n.dstl@)
        },
        reading_ok(n.ph, n.nbt, n.npostfix, n.ndirect, n.pc, n.cm),
        n.ph is Trees ==> n.nread() >= n.ntrees() ==> !n.pc.started,
{
    reveal(cat_ok);
    reveal(maps_ok);
    reveal(trees_ok);
    reveal(reading_ok);
    assert(n.blen[0] <= o.blen[0] && n.blen[1] <= o.blen[1] && n.blen[2] <= o.blen[2]);
}

/// One literal written: the decoder after it is well formed and reached.
#[verifier::spinoff_prover]
pub proof fn lemma_lit_next(b: Seq<u8>, d: Decoder, n: Decoder, x: u8, p: u64)
    requires
        d.wf(),
        d.reached(b),
        d.ph == Ph::Insert,
        d.blen[0] != 0,
        d.ring@.len() - (d.total - d.flushed) > 0,
        n == (Decoder {
            pos: p,
            total: n.total,
            ring: n.ring,
            out: n.out,
            blen: n.blen,
            ilen: n.ilen,
            mrem: n.mrem,
            ph: n.ph,
            steps: n.steps,
            ..d
        }),
        n.total == d.total + 1,
        n.out@ == d.out@.push(x),
        d.ring@.len() > 0,
        n.ring@ == d.ring@.update(d.total as int % d.ring@.len() as int, x),
        n.blen[0] == d.blen[0] - 1 && n.blen[1] == d.blen[1] && n.blen[2] == d.blen[2],
        n.ilen == d.ilen - 1,
        n.mrem == d.mrem - 1,
        n.steps@ == d.steps@ + 1,
        n.ph == (if n.ilen == 0 {
            if n.mrem == 0 {
                Ph::MetaDone
            } else {
                Ph::Dist
            }
        } else {
            Ph::Insert
        }),
        spec::step(b, d.view()) == Step::Next(n.view()),
    ensures
        n.wf(),
        n.reached(b),
        d.out@.is_prefix_of(n.out@),
{
    reveal(ring_ok);
    let rr = d.ring@.len() as int;
    let t = d.total as int;
    assert forall|j: int| 0 <= j < n.total && j >= n.total - rr && (j >= n.total - rr + 16 || j >= n.flushed || n.total <= rr) implies #[trigger] n.out@[j] == n.ring@[j % rr] by {
        if j < t {
            assert(j % rr != t % rr) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, rr);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t, rr);
                assert(t - j < rr);
                if j % rr == t % rr {
                    vstd::arithmetic::mul::lemma_mul_is_distributive_sub(rr, t / rr, j / rr);
                    assert(t - j == rr * (t / rr - j / rr));
                    if t / rr - j / rr >= 1 {
                        vstd::arithmetic::mul::lemma_mul_inequality(1, t / rr - j / rr, rr);
                    } else {
                        vstd::arithmetic::mul::lemma_mul_inequality(t / rr - j / rr, 0, rr);
                    }
                }
            }
            assert(n.ring@[j % rr] == d.ring@[j % rr]);
        } else {
            vstd::arithmetic::div_mod::lemma_mod_bound(j, rr);
        }
    }
    lemma_ring_basic(d);
    assert(ring_ok(n.ring@, n.rbits, n.total, n.flushed, n.out@, d.ph, n.mrem, n.wbits));
    lemma_ring_ph(n.ring@, n.rbits, n.total, n.flushed, n.out@, d.ph, n.ph, n.mrem, n.wbits);
    assert(1 <= d.ilen <= d.mrem) by {
        reveal(cmd_ok);
    }
    assert(cmd_ok(n.ph, n.dctx, n.dr, n.ilen, n.clen, n.mrem, n.dist, n.total, n.wbits)) by {
        reveal(cmd_ok);
    }
    lemma_wf_data(d, n);
    lemma_run_extend(b, spec::init(), d.steps@, d.view());
    assert(d.out@.is_prefix_of(n.out@)) by {
        assert(n.out@.subrange(0, d.out@.len() as int) =~= d.out@);
    }
}

/// `a` is a prefix of `b`, and `b` of `c`.
pub proof fn lemma_prefix_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        a.is_prefix_of(b),
        b.is_prefix_of(c),
    ensures
        a.is_prefix_of(c),
{
    assert forall|j: int| 0 <= j < a.len() implies a[j] == c[j] by {
        assert(a[j] == b.subrange(0, a.len() as int)[j]);
        assert(b[j] == c.subrange(0, b.len() as int)[j]);
    }
    assert(c.subrange(0, a.len() as int) =~= a);
}

/// The literal `lit_fast` read, written: `nx` is the next state.
#[verifier::spinoff_prover]
pub proof fn lemma_lit_ok(b: Seq<u8>, cur: Decoder, nx: Decoder, ctx: int, tree: int, xs: u64, p: u64)
    requires
        ctx == spec::lit_context(cur.cmodes@[cur.bt[0] as int] as int, spec::p1(cur.out@), spec::p2(cur.out@)),
        0 <= ctx < 64,
        cur.wf(),
        cur.reached(b),
        cur.ph == Ph::Insert,
        cur.blen[0] != 0,
        cur.ring@.len() - (cur.total - cur.flushed) > 0,
        cur.ring@.len() > 0,
        tree == cur.cmap@[cur.bt[0] * 64 + ctx],
        spec::rsym(cur.litl@[tree], b, cur.pos as int) == R::Ok(xs as int, p as int),
        xs < 256,
        nx == (Decoder {
            pos: p,
            total: (cur.total + 1) as u64,
            ring: nx.ring,
            out: Ghost(cur.out@.push(xs as u8)),
            blen: [(cur.blen[0] - 1) as u32, cur.blen[1], cur.blen[2]],
            ilen: (cur.ilen - 1) as u32,
            mrem: (cur.mrem - 1) as u32,
            ph: if cur.ilen == 1 {
                if cur.mrem == 1 {
                    Ph::MetaDone
                } else {
                    Ph::Dist
                }
            } else {
                Ph::Insert
            },
            steps: Ghost(cur.steps@ + 1),
            ..cur
        }),
        nx.ring@ == cur.ring@.update(cur.total as int % cur.ring@.len() as int, xs as u8),
    ensures
        nx.wf(),
        nx.reached(b),
        cur.out@.is_prefix_of(nx.out@),
{
    let s0 = cur.view();
    lemma_cur_tree(cur, 0);
    lemma_ring_basic(cur);
    assert(1 <= cur.ilen <= cur.mrem) by {
        reveal(cmd_ok);
    }
    assert(cur.bt[0] * 64 + ctx < 64 * cur.nbt[0]) by (nonlinear_arith)
        requires
            cur.bt[0] < cur.nbt[0],
            0 <= ctx < 64,
    ;
    assert(s0.bt[0] == cur.bt[0] && s0.cmodes == cur.cmodes@ && s0.cmap == cur.cmap@ && s0.lit == cur.litl@);
    lemma_lit(b, s0, tree);
    assert(seq3(nx.blen) =~= s0.blen.update(0, s0.blen[0] - 1));
    assert(((xs as int) as u8) == xs as u8);
    assert(spec::step(b, s0) == Step::Next(nx.view()));
    lemma_lit_next(b, cur, nx, xs as u8, p);
}

/// The decoder after `k` literals of `lit_fast`, written to `ring` and
/// `out`, with the position at `pos`.
pub open spec fn fast_state(o: Decoder, ring: Vec<u8>, pos: u64, out: Seq<u8>, k: int) -> Decoder {
    Decoder {
        pos: pos,
        total: (o.total + k) as u64,
        ring: ring,
        out: Ghost(out),
        blen: [(o.blen[0] - k) as u32, o.blen[1], o.blen[2]],
        ilen: (o.ilen - k) as u32,
        mrem: (o.mrem - k) as u32,
        ph: if o.ilen - k == 0 {
            if o.mrem - k == 0 {
                Ph::MetaDone
            } else {
                Ph::Dist
            }
        } else {
            Ph::Insert
        },
        steps: Ghost(o.steps@ + k as nat),
        ..o
    }
}

/// `fast_state` is well formed and reached (opaque, to keep `lit_fast`'s
/// loop small).
#[verifier::opaque]
pub open spec fn fast_ok(b: Seq<u8>, o: Decoder, ring: Vec<u8>, pos: u64, out: Seq<u8>, k: int) -> bool {
    fast_state(o, ring, pos, out, k).wf() && fast_state(o, ring, pos, out, k).reached(b)
}

/// No literals yet: the state is the start.
pub proof fn lemma_fast0(o: Decoder)
    requires
        o.ph == Ph::Insert,
        o.ilen >= 1,
    ensures
        fast_state(o, o.ring, o.pos, o.out@, 0) == o,
{
    let f = fast_state(o, o.ring, o.pos, o.out@, 0);
    assert(f.blen[0] == o.blen[0] && f.blen[1] == o.blen[1] && f.blen[2] == o.blen[2]);
    assert(f.blen =~= o.blen);
    assert(f.steps@ == o.steps@);
    assert(f.out@ == o.out@);
}

/// One more literal of `lit_fast`.
#[verifier::spinoff_prover]
pub proof fn lemma_fast_next(
    b: Seq<u8>,
    o: Decoder,
    ring: Vec<u8>,
    ring2: Vec<u8>,
    pos: u64,
    p: u64,
    out: Seq<u8>,
    k: int,
    ctx: int,
    tree: int,
    xs: u64,
)
    requires
        o.ilen <= o.mrem,
        0 <= k < o.ilen,
        k < o.blen[0],
        k < o.ring@.len() - (o.total - o.flushed),
        fast_ok(b, o, ring, pos, out, k),
        ring@.len() == o.ring@.len(),
        ring@.len() > 0,
        out.len() == o.total + k,
        ctx == spec::lit_context(o.cmodes@[o.bt[0] as int] as int, spec::p1(out), spec::p2(out)),
        0 <= ctx < 64,
        tree == o.cmap@[o.bt[0] * 64 + ctx],
        spec::rsym(o.litl@[tree], b, pos as int) == R::Ok(xs as int, p as int),
        xs < 256,
        ring2@ == ring@.update((o.total + k) % ring@.len() as int, xs as u8),
    ensures
        fast_ok(b, o, ring2, p, out.push(xs as u8), k + 1),
        out.is_prefix_of(out.push(xs as u8)),
{
    reveal(fast_ok);
    let cur = fast_state(o, ring, pos, out, k);
    let nx = fast_state(o, ring2, p, out.push(xs as u8), k + 1);
    assert(cur.ph == Ph::Insert);
    assert(cur.blen[0] != 0);
    lemma_ring_basic(cur);
    assert(1 <= cur.ilen <= cur.mrem) by {
        reveal(cmd_ok);
    }
    assert(cur.mrem == o.mrem - k && cur.ilen == o.ilen - k);
    assert(nx.blen =~= [(cur.blen[0] - 1) as u32, cur.blen[1], cur.blen[2]]);
    assert(nx.steps@ == cur.steps@ + 1);
    assert(nx.out == Ghost(cur.out@.push(xs as u8)));
    assert(nx.steps == Ghost(cur.steps@ + 1));
    assert(nx.total == (cur.total + 1) as u64);
    assert(nx.ilen == (cur.ilen - 1) as u32);
    assert(nx.mrem == (cur.mrem - 1) as u32);
    assert(nx.ph == (if cur.ilen == 1 { if cur.mrem == 1 { Ph::MetaDone } else { Ph::Dist } } else { Ph::Insert }));
    assert(nx.blen == [(cur.blen[0] - 1) as u32, cur.blen[1], cur.blen[2]]);
    assert(nx == (Decoder {
        pos: p,
        total: (cur.total + 1) as u64,
        ring: nx.ring,
        out: Ghost(cur.out@.push(xs as u8)),
        blen: [(cur.blen[0] - 1) as u32, cur.blen[1], cur.blen[2]],
        ilen: (cur.ilen - 1) as u32,
        mrem: (cur.mrem - 1) as u32,
        ph: if cur.ilen == 1 {
            if cur.mrem == 1 {
                Ph::MetaDone
            } else {
                Ph::Dist
            }
        } else {
            Ph::Insert
        },
        steps: Ghost(cur.steps@ + 1),
        ..cur
    }));
    lemma_lit_ok(b, cur, nx, ctx, tree, xs, p);
    assert(out.push(xs as u8).subrange(0, out.len() as int) =~= out);
}

/// `lit_fast` meets the end of the window at its first literal.
#[verifier::spinoff_prover]
pub proof fn lemma_fast_short(b: Seq<u8>, o: Decoder, ctx: int, tree: int)
    requires
        fast_ok(b, o, o.ring, o.pos, o.out@, 0),
        o.ilen >= 1,
        o.ph == Ph::Insert,
        o.blen[0] != 0,
        ctx == spec::lit_context(o.cmodes@[o.bt[0] as int] as int, spec::p1(o.out@), spec::p2(o.out@)),
        0 <= ctx < 64,
        tree == o.cmap@[o.bt[0] * 64 + ctx],
    ensures
        spec::rsym(o.litl@[tree], b, o.pos as int) is Short ==> spec::step(b, o.view()) is Short,
{
    reveal(fast_ok);
    lemma_fast0(o);
    let s0 = o.view();
    lemma_cur_tree(o, 0);
    assert(o.bt[0] * 64 + ctx < 64 * o.nbt[0]) by (nonlinear_arith)
        requires
            o.bt[0] < o.nbt[0],
            0 <= ctx < 64,
    ;
    assert(s0.bt[0] == o.bt[0] && s0.cmodes == o.cmodes@ && s0.cmap == o.cmap@ && s0.lit == o.litl@);
    lemma_lit(b, s0, tree);
}

/// The ring index of output byte `t`.
pub proof fn lemma_ring_idx(t: u64, rbits: u32, r: u64)
    requires
        rbits < 64,
        r as nat == pow2(rbits as nat),
    ensures
        (t & lowmask(rbits as u64)) as int == t as int % r as int,
        (t & lowmask(rbits as u64)) < r,
{
    lemma_and_mask(t, rbits as u64);
    lemma_pow2_pos(rbits as nat);
}

/// `ring_ok` does not depend on the phase, except for `Metadata`.
#[verifier::spinoff_prover]
pub proof fn lemma_ring_ph(ring: Seq<u8>, rbits: u32, total: u64, flushed: u64, out: Seq<u8>, ph1: Ph, ph2: Ph, mrem: u32, wbits: u32)
    requires
        ring_ok(ring, rbits, total, flushed, out, ph1, mrem, wbits),
        ph1 != Ph::Metadata,
        ph2 != Ph::Metadata && ph2 != Ph::WBits,
    ensures
        ring_ok(ring, rbits, total, flushed, out, ph2, mrem, wbits),
{
    reveal(ring_ok);
}

/// The facts about the ring that the data phases use.
#[verifier::spinoff_prover]
pub proof fn lemma_ring_basic(d: Decoder)
    requires
        d.wf(),
    ensures
        d.total == d.out@.len(),
        d.flushed <= d.total,
        d.total <= MAX_OUT,
        d.total - d.flushed <= d.ring@.len(),
        d.ring@.len() > 0 ==> d.ring@.len() >= 1024,
        d.ph != Ph::Metadata ==> d.total + d.mrem <= MAX_OUT,
{
    reveal(ring_ok);
}

/// What a command or literal step reads from the header: the current
/// tree of category `c`.
#[verifier::spinoff_prover]
pub proof fn lemma_cur_tree(d: Decoder, c: int)
    requires
        d.wf(),
        stage(d.ph) == 30,
        0 <= c < 2,
    ensures
        d.cmdl@.len() == d.cmd@.len() && d.litl@.len() == d.lit@.len(),
        c == 1 ==> d.bt[1] < d.cmd@.len() && hcode_ok(d.cmd@[d.bt[1] as int], d.cmdl@[d.bt[1] as int])
            && d.cmdl@[d.bt[1] as int].len() == 704,
        c == 0 ==> d.cmodes@.len() == d.nbt[0] && d.nbt[0] <= 256,
        c == 0 ==> d.bt[0] < d.cmodes@.len() && d.cmodes@[d.bt[0] as int] < 4 && d.cmap@.len() == 64 * d.nbt[0],
        c == 0 ==> forall|i: int| 0 <= i < d.cmap@.len() ==> #[trigger] d.cmap@[i] < d.lit@.len(),
        c == 0 ==> forall|i: int| 0 <= i < d.lit@.len() ==> #[trigger] hcode_ok(d.lit@[i], d.litl@[i]) && d.litl@[i].len() == 256,
{
    lemma_data_facts(d);
}

/// A command whose lengths were read: the step it takes.
#[verifier::spinoff_prover]
pub proof fn lemma_cmd(b: Seq<u8>, s: St, sym: int, p: int, ic: int, cc: int, ix: int, cx: int)
    requires
        s.phase is CmdBegin && s.blen[1] != 0,
        0 <= s.bt[1] < s.cmd.len(),
        spec::rsym(s.cmd[s.bt[1]], b, s.pos) == R::Ok(sym, p),
        ic == spec::ins_code(sym) && 0 <= ic < 24,
        cc == spec::cpy_code(sym) && 0 <= cc < 24,
        spec::rd(b, p, INS_EXTRA[ic] as nat) == Some(ix),
        spec::rd(b, p + INS_EXTRA[ic], CPY_EXTRA[cc] as nat) == Some(cx),
    ensures
        ({
            let ilen = INS_BASE[ic] as int + ix;
            let clen = CPY_BASE[cc] as int + cx;
            spec::step(b, s) == if ilen > s.mrem {
                Step::Bad
            } else {
                Step::Next(St {
                    phase: if ilen > 0 { Phase::Insert } else { Phase::Dist },
                    pos: p + INS_EXTRA[ic] + CPY_EXTRA[cc],
                    blen: s.blen.update(1, s.blen[1] - 1),
                    ilen,
                    clen,
                    dctx: if CPY_BASE[cc] > 4 { 3 } else { CPY_BASE[cc] - 2 },
                    implicit: sym < 128,
                    ..s
                })
            }
        }),
{
    lemma_step_data(b, s);
}

/// A command that runs out of input before its lengths are read.
#[verifier::spinoff_prover]
pub proof fn lemma_cmd_short(b: Seq<u8>, s: St)
    requires
        s.phase is CmdBegin && s.blen[1] != 0,
        0 <= s.bt[1] < s.cmd.len(),
    ensures
        spec::rsym(s.cmd[s.bt[1]], b, s.pos) is Short ==> spec::step(b, s) is Short,
        spec::rsym(s.cmd[s.bt[1]], b, s.pos) is Bad ==> spec::step(b, s) is Bad,
        spec::rsym(s.cmd[s.bt[1]], b, s.pos) matches R::Ok(sym, p) ==> {
                let ie = INS_EXTRA[spec::ins_code(sym)] as nat;
                let ce = CPY_EXTRA[spec::cpy_code(sym)] as nat;
                &&& spec::rd(b, p, ie) is None ==> spec::step(b, s) is Short
                &&& (spec::rd(b, p, ie) is Some && spec::rd(b, p + ie, ce) is None) ==> spec::step(b, s) is Short
            },
{
    lemma_step_data(b, s);
}

/// A switch of category `c` when its block count is used up.
#[verifier::spinoff_prover]
pub proof fn lemma_step_sw(b: Seq<u8>, s: St, c: int)
    requires
        (c == 1 && s.phase is CmdBegin && s.blen[1] == 0) || (c == 0 && s.phase is Insert && s.blen[0] == 0)
            || (c == 2 && s.phase is Dist && !s.implicit && s.blen[2] == 0),
    ensures
        spec::step(b, s) == spec::block_switch(s, b, c),
{
    lemma_step_data(b, s);
}

/// One literal, once its tree is known: the step it takes.
#[verifier::spinoff_prover]
pub proof fn lemma_lit(b: Seq<u8>, s: St, tree: int)
    requires
        s.phase is Insert && s.blen[0] != 0,
        0 <= s.bt[0] < s.cmodes.len(),
        0 <= s.bt[0] * 64 + spec::lit_context(s.cmodes[s.bt[0]] as int, spec::p1(s.out), spec::p2(s.out)) < s.cmap.len(),
        tree == s.cmap[s.bt[0] * 64 + spec::lit_context(s.cmodes[s.bt[0]] as int, spec::p1(s.out), spec::p2(s.out))],
        0 <= tree < s.lit.len(),
    ensures
        spec::rsym(s.lit[tree], b, s.pos) is Short ==> spec::step(b, s) is Short,
        spec::rsym(s.lit[tree], b, s.pos) is Bad ==> spec::step(b, s) is Bad,
        spec::rsym(s.lit[tree], b, s.pos) matches R::Ok(x, p) ==> {
            let s1 = St {
                pos: p,
                out: s.out.push(x as u8),
                blen: s.blen.update(0, s.blen[0] - 1),
                ilen: s.ilen - 1,
                mrem: s.mrem - 1,
                ..s
            };
            spec::step(b, s) == if s1.ilen > 0 {
                Step::Next(s1)
            } else if s1.mrem == 0 {
                Step::Next(St { phase: Phase::MetaDone, ..s1 })
            } else {
                Step::Next(St { phase: Phase::Dist, ..s1 })
            }
        },
{
    lemma_step_data(b, s);
}

/// The distance phase with an implicit distance (insert-and-copy codes
/// below 128 reuse the last distance).
#[verifier::spinoff_prover]
pub proof fn lemma_dist_implicit(b: Seq<u8>, s: St)
    requires
        s.phase is Dist && s.implicit,
    ensures
        spec::step(b, s) == spec::resolve(s, s.dr[0], true),
{
    lemma_step_data(b, s);
}

/// The distance phase with a distance code to read from tree `tree`.
#[verifier::spinoff_prover]
pub proof fn lemma_dist(b: Seq<u8>, s: St, tree: int)
    requires
        s.phase is Dist && !s.implicit && s.blen[2] != 0,
        0 <= s.bt[2] * 4 + s.dctx < s.dmap.len(),
        tree == s.dmap[s.bt[2] * 4 + s.dctx],
        0 <= tree < s.dst.len(),
    ensures
        spec::rsym(s.dst[tree], b, s.pos) is Short ==> spec::step(b, s) is Short,
        spec::rsym(s.dst[tree], b, s.pos) is Bad ==> spec::step(b, s) is Bad,
{
    lemma_step_data(b, s);
}

/// The distance code `dcode` read, ending at `p`.
#[verifier::spinoff_prover]
pub proof fn lemma_dist_code(b: Seq<u8>, s: St, tree: int, dcode: int, p: int)
    requires
        s.phase is Dist && !s.implicit && s.blen[2] != 0,
        0 <= s.bt[2] * 4 + s.dctx < s.dmap.len(),
        tree == s.dmap[s.bt[2] * 4 + s.dctx],
        0 <= tree < s.dst.len(),
        spec::rsym(s.dst[tree], b, s.pos) == R::Ok(dcode, p),
    ensures
        dcode < 16 && spec::short_dist(dcode, s.dr) <= 0 ==> spec::step(b, s) is Bad,
        dcode < 16 && spec::short_dist(dcode, s.dr) > 0 ==> spec::step(b, s) == spec::resolve(
            St { pos: p, blen: s.blen.update(2, s.blen[2] - 1), ..s },
            spec::short_dist(dcode, s.dr),
            dcode == 0,
        ),
        16 <= dcode < 16 + s.ndirect ==> spec::step(b, s) == spec::resolve(
            St { pos: p, blen: s.blen.update(2, s.blen[2] - 1), ..s },
            dcode - 15,
            false,
        ),
        dcode >= 16 && dcode >= 16 + s.ndirect && spec::rd(b, p, spec::dist_extra(dcode, s.npostfix, s.ndirect)) is None
            ==> spec::step(b, s) is Short,
{
    lemma_step_data(b, s);
}

/// The distance code `dcode` read, ending at `p`, and its extra bits `e`.
#[verifier::spinoff_prover]
pub proof fn lemma_dist_far(b: Seq<u8>, s: St, tree: int, dcode: int, p: int, e: int)
    requires
        s.phase is Dist && !s.implicit && s.blen[2] != 0,
        0 <= s.bt[2] * 4 + s.dctx < s.dmap.len(),
        tree == s.dmap[s.bt[2] * 4 + s.dctx],
        0 <= tree < s.dst.len(),
        spec::rsym(s.dst[tree], b, s.pos) == R::Ok(dcode, p),
        dcode >= 16 && dcode >= 16 + s.ndirect,
        spec::rd(b, p, spec::dist_extra(dcode, s.npostfix, s.ndirect)) == Some(e),
    ensures
        spec::step(b, s) == spec::resolve(
            St {
                pos: p + spec::dist_extra(dcode, s.npostfix, s.ndirect),
                blen: s.blen.update(2, s.blen[2] - 1),
                ..s
            },
            spec::dist_value(dcode, e, s.npostfix, s.ndirect),
            false,
        ),
{
    lemma_step_data(b, s);
}

/// `resolve` within the window: a backward copy.
#[verifier::spinoff_prover]
pub proof fn lemma_resolve_copy(s: St, d: int, last: bool)
    requires
        d <= spec::max_distance(s.out.len() as int, s.wbits),
    ensures
        spec::resolve(s, d, last) == if s.clen > s.mrem {
            Step::Bad
        } else {
            Step::Next(St {
                phase: Phase::Copy,
                dist: d,
                dr: if last { s.dr } else { seq![d, s.dr[0], s.dr[1], s.dr[2]] },
                ..s
            })
        },
{
    reveal(spec::resolve);
}

/// `resolve` past the window: a dictionary word.
#[verifier::spinoff_prover]
pub proof fn lemma_resolve_dict(s: St, d: int, last: bool)
    requires
        d > spec::max_distance(s.out.len() as int, s.wbits),
    ensures
        (d > 0x7FFF_FFFC || s.clen < 4 || s.clen > 24) ==> spec::resolve(s, d, last) is Bad,
        !(d > 0x7FFF_FFFC || s.clen < 4 || s.clen > 24) ==> {
            let addr = d - spec::max_distance(s.out.len() as int, s.wbits) - 1;
            let n = NDBITS[s.clen] as nat;
            let idx = addr % pow2(n) as int;
            let tid = addr / pow2(n) as int;
            &&& tid >= 121 ==> spec::resolve(s, d, last) is Bad
            &&& tid < 121 ==> {
                let w = spec::transform(spec::dict_word(s.clen, idx), tid);
                &&& (w.len() == 0 && d <= 120) ==> spec::resolve(s, d, last) is Bad
                &&& w.len() > s.mrem ==> spec::resolve(s, d, last) is Bad
                &&& (!(w.len() == 0 && d <= 120) && w.len() <= s.mrem) ==> spec::resolve(s, d, last) == Step::Next(St {
                    phase: spec::after_data(s.mrem - w.len()),
                    out: s.out + w,
                    mrem: s.mrem - w.len(),
                    ..s
                })
            }
        },
{
    reveal(spec::resolve);
}

/// What the distance phase reads from the header and the command.
#[verifier::spinoff_prover]
pub proof fn lemma_dist_facts(d: Decoder)
    requires
        d.wf(),
        d.ph == Ph::Dist,
    ensures
        d.bt[2] < d.nbt[2] <= 256,
        d.dctx < 4,
        d.dmap@.len() == 4 * d.nbt[2],
        forall|i: int| 0 <= i < d.dmap@.len() ==> #[trigger] d.dmap@[i] < d.dst@.len(),
        d.dstl@.len() == d.dst@.len(),
        forall|i: int| 0 <= i < d.dst@.len() ==> #[trigger] hcode_ok(d.dst@[i], d.dstl@[i])
            && d.dstl@[i].len() == spec::dist_alpha(d.npostfix as int, d.ndirect as int),
        d.npostfix <= 3 && d.ndirect <= 120,
        forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] d.dr[i] <= 0x7fff_fffc,
        2 <= d.clen <= 2118 + 0xff_ffff,
        10 <= d.wbits <= 24,
{
    lemma_data_facts(d);
    reveal(cmd_ok);
}

/// Counting up by one inside the ring, without wrapping.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_inc(a: int, r: int)
    requires
        0 <= a,
        0 < r,
        a % r + 1 < r,
    ensures
        (a + 1) % r == a % r + 1,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, r);
    assert(a + 1 == (a / r) * r + (a % r + 1)) by (nonlinear_arith)
        requires
            a == r * (a / r) + a % r,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a + 1, r, a / r, a % r + 1);
}

/// Counting up by `j` inside the ring, without wrapping.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add(a: int, r: int, j: int)
    requires
        0 <= a,
        0 <= j,
        0 < r,
        a % r + j < r,
    ensures
        (a + j) % r == a % r + j,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, r);
    assert(a + j == (a / r) * r + (a % r + j)) by (nonlinear_arith)
        requires
            a == r * (a / r) + a % r,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a + j, r, a / r, a % r + j);
}

/// Positions of the last `r - m` bytes before `t` lie outside the ring
/// range `t % r .. t % r + m`.
#[verifier::spinoff_prover]
pub proof fn lemma_ring_gap(i: int, t: int, r: int, ti: int, m: int)
    requires
        0 <= i < t,
        t + m - r <= i,
        0 < r,
        ti == t % r,
        1 <= m,
        ti + m <= r,
    ensures
        !(ti <= i % r < ti + m),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, r);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t, r);
    let p = i / r;
    let q = t / r;
    if ti <= i % r < ti + m {
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(r, p, q);
        let k = p - q;
        assert(r * k > -r && r * k < 0);
        if k >= 0 {
            vstd::arithmetic::mul::lemma_mul_nonnegative(r, k);
        } else {
            vstd::arithmetic::mul::lemma_mul_inequality(1, -k, r);
            assert(r * k == -(r * (-k))) by (nonlinear_arith);
            assert(r * (-k) == (-k) * r) by (nonlinear_arith);
        }
    }
}

/// `buf[dst..dst + 16] = buf[src..src + 16]`, when the source ends before
/// the destination starts.
#[verifier::spinoff_prover]
#[inline(always)]
fn copy16(buf: &mut [u8], src: usize, dst: usize)
    requires
        src + 16 <= dst,
        dst + 16 <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        forall|j: int|
            0 <= j < final(buf)@.len() ==> #[trigger] final(buf)@[j] == if dst <= j < dst + 16 {
                old(buf)@[j - dst + src]
            } else {
                old(buf)@[j]
            },
{
    let len = buf.len();
    assert(dst + 16 <= len);
    verilith_core::prims::copy8(buf, src, dst);
    verilith_core::prims::copy8(buf, src + 8, dst + 8);
}

/// `buf[dst..dst + n] = buf[src..src + n]` in 8-byte words, when the
/// source ends before the destination starts.
#[verifier::spinoff_prover]
#[inline(always)]
fn copy_words(buf: &mut [u8], src: usize, dst: usize, n: usize)
    requires
        src + n <= old(buf)@.len(),
        dst + n <= old(buf)@.len(),
        src + n <= dst,
        n >= 8,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        forall|j: int|
            0 <= j < final(buf)@.len() ==> #[trigger] final(buf)@[j] == if dst <= j < dst + n {
                old(buf)@[j - dst + src]
            } else {
                old(buf)@[j]
            },
{
    let ghost o = buf@;
    let len = buf.len();
    let mut k: usize = 0;
    while k + 8 <= n
        invariant
            k <= n,
            o.len() == len,
            src + n <= o.len(),
            dst + n <= o.len(),
            src + n <= dst,
            buf@.len() == o.len(),
            forall|j: int|
                0 <= j < buf@.len() ==> #[trigger] buf@[j] == if dst <= j < dst + k {
                    o[j - dst + src]
                } else {
                    o[j]
                },
        decreases n - k,
    {
        verilith_core::prims::copy8(buf, src + k, dst + k);
        k = k + 8;
    }
    if k < n {
        // The last 8 bytes, overlapping some already copied.
        verilith_core::prims::copy8(buf, src + n - 8, dst + n - 8);
    }
}

/// Two ring positions `d` apart: either `d` apart in the ring too, or
/// wrapped around it.
#[verifier::spinoff_prover]
pub proof fn lemma_ring_order(a: int, d: int, r: int)
    requires
        0 <= a,
        1 <= d <= r,
    ensures
        (a + d) % r == a % r + d || (a + d) % r == a % r + d - r,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, r);
    let q = a / r;
    let m = a % r;
    assert(a + d == q * r + (m + d)) by (nonlinear_arith)
        requires
            a == r * q + m,
    ;
    if m + d < r {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a + d, r, q, m + d);
    } else {
        assert(a + d == (q + 1) * r + (m + d - r)) by (nonlinear_arith)
            requires
                a + d == q * r + (m + d),
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a + d, r, q + 1, m + d - r);
    }
}

/// The state after `m` steps of a copy from `s`.
pub open spec fn copied(s: St, m: int) -> St {
    let l = s.out.len() - s.dist;
    St {
        phase: if m == s.clen { spec::after_data(s.mrem - m) } else { s.phase },
        out: s.out + s.out.subrange(l, l + m),
        clen: s.clen - m,
        mrem: s.mrem - m,
        ..s
    }
}

/// `m` copy steps at once, when no copied byte is one the copy wrote.
#[verifier::spinoff_prover]
pub proof fn lemma_copy_run(b: Seq<u8>, s0: St, n0: nat, s: St, m: int)
    requires
        spec::run(b, s0, n0) == Step::Next(s),
        s.phase is Copy,
        1 <= m <= s.clen,
        m <= s.dist,
        1 <= s.dist <= s.out.len(),
    ensures
        spec::run(b, s0, n0 + m as nat) == Step::Next(copied(s, m)),
    decreases m,
{
    let l = s.out.len() - s.dist;
    if m == 1 {
        lemma_run_extend(b, s0, n0, s);
        lemma_step_copy(b, s);
        assert(s.out.push(s.out[s.out.len() - s.dist]) =~= s.out + s.out.subrange(l, l + 1));
    } else {
        lemma_copy_run(b, s0, n0, s, m - 1);
        let t = copied(s, m - 1);
        assert(t.phase is Copy);
        lemma_run_extend(b, s0, (n0 + (m - 1) as nat) as nat, t);
        lemma_step_copy(b, t);
        assert(t.out.len() == s.out.len() + m - 1);
        assert(t.out[t.out.len() - t.dist] == s.out[l + m - 1]);
        assert(t.out.push(t.out[t.out.len() - t.dist]) =~= s.out + s.out.subrange(l, l + m));
        assert((n0 + (m - 1) as nat) as nat + 1 == n0 + m as nat);
    }
}

/// Metadata bytes: `k` steps skip `k` bytes.
#[verifier::spinoff_prover]
proof fn lemma_skip(b: Seq<u8>, n: nat, s: St, k: nat)
    requires
        spec::run(b, spec::init(), n) == Step::Next(s),
        s.phase is Metadata,
        s.mrem >= k,
        s.pos >= 0,
        s.pos + 8 * k <= verilith_core::bits::nbits(b),
    ensures
        spec::run(b, spec::init(), n + k) == Step::Next(St { pos: s.pos + 8 * k, mrem: s.mrem - k, ..s }),
    decreases k,
{
    if k == 0 {
        assert(St { pos: s.pos + 8 * k, mrem: s.mrem - k, ..s } == s);
    } else {
        lemma_step_metadata(b, s);
        lemma_run_extend(b, spec::init(), n, s);
        let s1 = St { pos: s.pos + 8, mrem: s.mrem - 1, ..s };
        assert(spec::step(b, s) == Step::Next(s1));
        lemma_skip(b, n + 1, s1, (k - 1) as nat);
        assert(n + 1 + (k - 1) as nat == n + k);
        assert(St { pos: s1.pos + 8 * (k - 1), mrem: s1.mrem - (k - 1), ..s1 } == St {
            pos: s.pos + 8 * k,
            mrem: s.mrem - k,
            ..s
        });
    }
}

/// The decoder after the command step that reads these lengths.
pub open spec fn cmd_next(g: Decoder, ilen: u32, clen: u32, dctx: u32, implicit: bool, p: u64) -> Decoder {
    Decoder {
        pos: p,
        blen: [g.blen[0], (g.blen[1] - 1) as u32, g.blen[2]],
        ilen: ilen,
        clen: clen,
        dctx: dctx,
        implicit: implicit,
        ph: if ilen > 0 { Ph::Insert } else { Ph::Dist },
        steps: Ghost(g.steps@ + 1),
        ..g
    }
}

/// The decoder after the distance step that resolves to a backward copy.
pub open spec fn dist_next(g: Decoder, d: u32, last: bool, p: u64, blen2: u32) -> Decoder {
    Decoder {
        pos: p,
        blen: [g.blen[0], g.blen[1], blen2],
        dist: d,
        dr: if last { g.dr } else { [d, g.dr[0], g.dr[1], g.dr[2]] },
        ph: Ph::Copy,
        steps: Ghost(g.steps@ + 1),
        ..g
    }
}

/// A distance within the window, with room for the copy in the
/// meta-block: the step to `dist_next`.
#[verifier::spinoff_prover]
pub proof fn lemma_dist_next(g: Decoder, d: u64, last: bool, p: u64, blen2: u32, src: Seq<u8>, base: u64, b: Seq<u8>)
    requires
        g.wf(),
        g.reached(b),
        g.ph == Ph::Dist,
        g.pos <= p <= lim(src, base as int),
        blen2 <= g.blen[2],
        1 <= d < 0x8000_0000,
        spec::step(b, g.view()) == spec::resolve(
            St { pos: p as int, blen: seq3(g.blen).update(2, blen2 as int), ..g.view() },
            d as int,
            last,
        ),
        d <= spec::max_distance(g.total as int, g.wbits as int),
        g.clen <= g.mrem,
    ensures
        step_ok(g, dist_next(g, d as u32, last, p, blen2), None, src, base, b),
{
    crate::rank::lemma_rank1(b, g);
    let s0 = g.view();
    let o = g;
    let s1 = St { pos: p as int, blen: seq3(o.blen).update(2, blen2 as int), ..s0 };
    lemma_dist_facts(o);
    lemma_ring_basic(o);
    lemma2_to64();
    lemma_resolve_copy(s1, d as int, last);
    let n = dist_next(g, d as u32, last, p, blen2);
    assert(seq3(n.blen) =~= s1.blen);
    if !last {
        assert(seq4(n.dr) =~= seq![d as int, s0.dr[0], s0.dr[1], s0.dr[2]]);
    }
    assert(spec::step(b, s0) == Step::Next(n.view()));
    lemma_run_extend(b, spec::init(), o.steps@, s0);
    lemma_ring_ph(n.ring@, n.rbits, n.total, n.flushed, n.out@, o.ph, n.ph, n.mrem, n.wbits);
    assert(cmd_ok(n.ph, n.dctx, n.dr, n.ilen, n.clen, n.mrem, n.dist, n.total, n.wbits)) by {
        reveal(cmd_ok);
    }
    lemma_wf_data(o, n);
    assert(o.out@.is_prefix_of(n.out@)) by {
        assert(o.out@.subrange(0, o.out@.len() as int) =~= o.out@);
    }
    assert(n.wf());
    assert(n.reached(b));
    assert(moved(g, n, src, base, b));
}

/// The decoder after `m` bytes of a copy that reads none of the bytes it
/// writes, with the ring as it is then.
pub open spec fn copy_next(g: Decoder, ring: Vec<u8>, m: u64) -> Decoder {
    let l = g.total - g.dist;
    Decoder {
        ring: ring,
        total: (g.total + m) as u64,
        clen: (g.clen - m) as u32,
        mrem: (g.mrem - m) as u32,
        ph: if m == g.clen {
            if g.mrem - m == 0 {
                Ph::MetaDone
            } else {
                Ph::CmdBegin
            }
        } else {
            Ph::Copy
        },
        out: Ghost(g.out@ + g.out@.subrange(l, l + m)),
        steps: Ghost(g.steps@ + m as nat),
        ..g
    }
}

/// `buf[dst..dst + n] = buf[src..src + n]` for `n < 8`, as two reads and
/// two writes of 4, 2 or 1 bytes that overlap in the middle. Every byte
/// is read before any is written, so the ranges may overlap.
#[verifier::spinoff_prover]
#[inline(always)]
fn copy_small(buf: &mut [u8], src: usize, dst: usize, n: usize)
    requires
        1 <= n < 8,
        src + n <= old(buf)@.len(),
        dst + n <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        forall|j: int|
            0 <= j < final(buf)@.len() ==> #[trigger] final(buf)@[j] == if dst <= j < dst + n {
                old(buf)@[j - dst + src]
            } else {
                old(buf)@[j]
            },
{
    let len = buf.len();
    assert(src + n <= len && dst + n <= len);
    if n >= 4 {
        let a0 = verilith_core::prims::get(buf, src);
        let a1 = verilith_core::prims::get(buf, src + 1);
        let a2 = verilith_core::prims::get(buf, src + 2);
        let a3 = verilith_core::prims::get(buf, src + 3);
        let e = src + n - 4;
        let b0 = verilith_core::prims::get(buf, e);
        let b1 = verilith_core::prims::get(buf, e + 1);
        let b2 = verilith_core::prims::get(buf, e + 2);
        let b3 = verilith_core::prims::get(buf, e + 3);
        verilith_core::prims::set(buf, dst, a0);
        verilith_core::prims::set(buf, dst + 1, a1);
        verilith_core::prims::set(buf, dst + 2, a2);
        verilith_core::prims::set(buf, dst + 3, a3);
        let f = dst + n - 4;
        verilith_core::prims::set(buf, f, b0);
        verilith_core::prims::set(buf, f + 1, b1);
        verilith_core::prims::set(buf, f + 2, b2);
        verilith_core::prims::set(buf, f + 3, b3);
    } else if n >= 2 {
        let a0 = verilith_core::prims::get(buf, src);
        let a1 = verilith_core::prims::get(buf, src + 1);
        let e = src + n - 2;
        let b0 = verilith_core::prims::get(buf, e);
        let b1 = verilith_core::prims::get(buf, e + 1);
        verilith_core::prims::set(buf, dst, a0);
        verilith_core::prims::set(buf, dst + 1, a1);
        let f = dst + n - 2;
        verilith_core::prims::set(buf, f, b0);
        verilith_core::prims::set(buf, f + 1, b1);
    } else {
        let a0 = verilith_core::prims::get(buf, src);
        verilith_core::prims::set(buf, dst, a0);
    }
}

/// The decoder after the whole of a copy, with the ring, output and step
/// count as they are then.
pub open spec fn copy_done(g: Decoder, ring: Vec<u8>, out: Ghost<Seq<u8>>, steps: Ghost<nat>) -> Decoder {
    Decoder {
        ring: ring,
        total: (g.total + g.clen) as u64,
        clen: 0,
        mrem: (g.mrem - g.clen) as u32,
        ph: if g.mrem == g.clen { Ph::MetaDone } else { Ph::CmdBegin },
        out: out,
        steps: steps,
        ..g
    }
}

/// The decoder after a dictionary word of `wl` bytes went out, with the
/// ring and output as they are then.
pub open spec fn dict_next(g: Decoder, ring: Vec<u8>, out: Ghost<Seq<u8>>, wl: u64, p: u64, blen2: u32) -> Decoder {
    Decoder {
        ring: ring,
        total: (g.total + wl) as u64,
        mrem: (g.mrem - wl) as u32,
        pos: p,
        blen: [g.blen[0], g.blen[1], blen2],
        ph: if g.mrem == wl { Ph::MetaDone } else { Ph::CmdBegin },
        out: out,
        steps: Ghost(g.steps@ + 1),
        ..g
    }
}

/// `dict_next` after the word `w` was written to the ring at `ti`: well
/// formed, and the step the spec takes.
#[verifier::spinoff_prover]
pub proof fn lemma_dict_next(g: Decoder, ring: Vec<u8>, w: Seq<u8>, p: u64, blen2: u32, ti: int, e: int, b: Seq<u8>)
    requires
        g.wf(),
        g.reached(b),
        g.ph == Ph::Dist,
        blen2 <= g.blen[2],
        g.ring@.len() > 0,
        ring@.len() == g.ring@.len(),
        ti == g.total as int % g.ring@.len() as int,
        1 <= w.len() <= g.mrem,
        w.len() <= g.ring@.len() - (g.total - g.flushed),
        ti + w.len() <= g.ring@.len(),
        // The word is in the ring; up to `e` bytes after it, which the
        // ring no longer has to hold, may have been overwritten.
        0 <= e <= 16,
        w.len() + e <= g.ring@.len() - (g.total - g.flushed),
        ti + w.len() + e <= g.ring@.len(),
        ring@.subrange(ti, ti + w.len()) == w,
        forall|k: int| 0 <= k < ring@.len() && !(ti <= k < ti + w.len() + e) ==> #[trigger] ring@[k] == g.ring@[k],
        spec::step(b, g.view()) == Step::Next(
            St {
                phase: spec::after_data(g.mrem - w.len()),
                out: g.out@ + w,
                mrem: g.mrem - w.len(),
                pos: p as int,
                blen: seq3(g.blen).update(2, blen2 as int),
                ..g.view()
            },
        ),
    ensures
        dict_next(g, ring, Ghost(g.out@ + w), w.len() as u64, p, blen2).wf(),
        dict_next(g, ring, Ghost(g.out@ + w), w.len() as u64, p, blen2).reached(b),
        g.out@.is_prefix_of(g.out@ + w),
        crate::rank::rank_lt(b, dict_next(g, ring, Ghost(g.out@ + w), w.len() as u64, p, blen2).view(), g.view()),
{
    let n = dict_next(g, ring, Ghost(g.out@ + w), w.len() as u64, p, blen2);
    let wl = w.len() as int;
    let r = g.ring@.len() as int;
    let t = g.total as int;
    let s0 = g.view();
    crate::rank::lemma_rank1(b, g);
    lemma_ring_basic(g);
    assert(ring_ok(n.ring@, n.rbits, n.total, n.flushed, n.out@, g.ph, n.mrem, n.wbits)) by {
        reveal(ring_ok);
        assert forall|i: int|
            0 <= i < n.total && i >= n.total - r && (i >= n.total - r + 16 || i >= n.flushed || n.total <= r) implies #[trigger] n.out@[i]
            == n.ring@[i % r] by {
            if i >= t {
                lemma_mod_add(t, r, i - t);
                assert(n.ring@[ti + (i - t)] == ring@.subrange(ti, ti + wl)[i - t]);
            } else {
                if n.total <= r {
                    vstd::arithmetic::div_mod::lemma_small_mod(t as nat, r as nat);
                    vstd::arithmetic::div_mod::lemma_small_mod(i as nat, r as nat);
                } else {
                    lemma_ring_gap(i, t, r, ti, wl + e);
                }
                assert(n.ring@[i % r] == g.ring@[i % r]);
                assert(n.out@[i] == g.out@[i]);
            }
        }
    }
    lemma_ring_ph(n.ring@, n.rbits, n.total, n.flushed, n.out@, g.ph, n.ph, n.mrem, n.wbits);
    assert(cmd_ok(n.ph, n.dctx, n.dr, n.ilen, n.clen, n.mrem, n.dist, n.total, n.wbits)) by {
        reveal(cmd_ok);
    }
    assert(seq3(n.blen) =~= seq3(g.blen).update(2, blen2 as int));
    assert(spec::step(b, s0) == Step::Next(n.view()));
    lemma_run_extend(b, spec::init(), g.steps@, s0);
    lemma_wf_data(g, n);
}

/// `g` is `o` but for the ring and what a command changes.
pub open spec fn hot(g: Decoder, o: Decoder) -> bool {
    g == (Decoder {
        ring: g.ring,
        pos: g.pos,
        total: g.total,
        mrem: g.mrem,
        blen: g.blen,
        dr: g.dr,
        ilen: g.ilen,
        clen: g.clen,
        dctx: g.dctx,
        implicit: g.implicit,
        dist: g.dist,
        ph: g.ph,
        out: g.out,
        steps: g.steps,
        ..o
    })
}

/// One more step, from `g` to `g1`, after those from `o` to `g`.
pub proof fn lemma_adv(o: Decoder, g: Decoder, g1: Decoder, prog: bool, src: Seq<u8>, base: u64, b: Seq<u8>)
    requires
        moved(o, g, src, base, b),
        moved(g, g1, src, base, b),
        g.steps@ < g1.steps@,
        crate::rank::rank_lt(b, g1.view(), g.view()),
        !prog ==> g == o,
        prog ==> o.steps@ < g.steps@ && crate::rank::rank_lt(b, g.view(), o.view()),
    ensures
        moved(o, g1, src, base, b),
        o.steps@ < g1.steps@,
        crate::rank::rank_lt(b, g1.view(), o.view()),
{
    lemma_moved_trans(o, g, g1, src, base, b);
    if prog {
        crate::rank::lemma_rank_trans(b, g1.view(), g.view(), o.view());
    }
}

/// `b[i]` without the bounds check, which the precondition is.
#[inline(always)]
pub fn get64(b: &[u64], i: usize) -> (r: u64)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

/// `&b[i]` without the bounds check, which the precondition is.
#[inline(always)]
/// `f` holds the tables of `codes` side by side, each widened to `t` bits.
#[verifier::opaque]
pub open spec fn flat_ok(f: Seq<u32>, codes: Seq<HCode>, t: u64) -> bool {
    forall|i: int| 0 <= i < codes.len() ==> flat_at(f, i, t, #[trigger] codes[i])
}

/// The tables of `codes` side by side, each widened to the widest one's
/// bits, for `sym_winf`. Empty when there are no codes.
#[verifier::spinoff_prover]
pub fn mk_flat(codes: &[HCode]) -> (r: (Vec<u32>, u64))
    requires
        codes@.len() <= 256,
        forall|i: int| 0 <= i < codes@.len() ==> (#[trigger] codes@[i]).tbits <= 10 && codes@[i].table@.len() == pow2(
            codes@[i].tbits as nat,
        ),
    ensures
        r.0@.len() != 0 ==> flat_ok(r.0@, codes@, r.1),
{
    let n = codes.len();
    let mut t: u32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == codes@.len(),
            t <= 10,
            forall|k: int| 0 <= k < i ==> (#[trigger] codes@[k]).tbits <= t,
            forall|k: int| 0 <= k < codes@.len() ==> (#[trigger] codes@[k]).tbits <= 10,
        decreases n - i,
    {
        if codes[i].tbits > t {
            t = codes[i].tbits;
        }
        i = i + 1;
    }
    proof {
        verilith_core::bits::lemma_mask(t as u64);
        lemma_pow2_pos(t as nat);
        lemma_pow2_strictly_increases(t as nat, 11);
        vstd::arithmetic::power2::lemma2_to64();
    }
    let size: usize = 1usize << t;
    let ghost pf = pow2(t as nat) as int;
    assert(size == pf) by {
        assert((1usize << t) == (1u64 << (t as u64))) by (bit_vector)
            requires
                t <= 10,
        ;
    }
    assert(n * size <= 256 * 1024) by (nonlinear_arith)
        requires
            n <= 256,
            size <= 1024,
    ;
    let mut f: Vec<u32> = Vec::with_capacity(n * size);
    i = 0;
    while i < n
        invariant
            i <= n == codes@.len(),
            n <= 256,
            t <= 10,
            size == pf == pow2(t as nat),
            1 <= pf <= 1024,
            f@.len() == i * pf,
            forall|k: int| 0 <= k < codes@.len() ==> (#[trigger] codes@[k]).tbits <= t && codes@[k].table@.len() == pow2(
                codes@[k].tbits as nat,
            ),
            forall|k: int| 0 <= k < i ==> flat_at(f@, k, t as u64, #[trigger] codes@[k]),
        decreases n - i,
    {
        let h = &codes[i];
        let tb = h.tbits;
        let ghost pt = pow2(tb as nat) as int;
        let ghost pd = pow2((t - tb) as nat) as int;
        proof {
            lemma_pow2_pos(tb as nat);
            lemma_pow2_pos((t - tb) as nat);
            lemma_pow2_adds(tb as nat, (t - tb) as nat);
            lemma_pow2_strictly_increases((t - tb) as nat, 11);
            assert(pf == pt * pd);
            assert(pd <= pf) by (nonlinear_arith)
                requires
                    pf == pt * pd,
                    1 <= pt,
                    1 <= pd,
            ;
            verilith_core::bits::lemma_mask((t - tb) as u64);
        }
        let reps: usize = 1usize << (t - tb);
        assert(reps == pd) by {
            let d = (t - tb) as u32;
            assert((1usize << d) == (1u64 << (d as u64))) by (bit_vector)
                requires
                    d <= 10,
            ;
        }
        let ghost f0 = f@;
        let mut q: usize = 0;
        while q < reps
            invariant
                q <= reps == pd,
                pf == pt * pd,
                1 <= pt,
                1 <= pd <= 1024,
                pf <= 1024,
                i < n <= 256,
                h.table@.len() == pt,
                f0.len() == i * pf,
                f0.is_prefix_of(f@),
                f@.len() == i * pf + q * pt,
                forall|j: int| 0 <= j < q * pt ==> #[trigger] f@[i * pf + j] == h.table@[j % pt],
            decreases reps - q,
        {
            let ghost f1 = f@;
            f.extend_from_slice(h.table.as_slice());
            proof {
                assert(q * pt + pt == (q + 1) * pt) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < (q + 1) * pt implies #[trigger] f@[i * pf + j] == h.table@[j % pt] by {
                    if j < q * pt {
                        assert(f@[i * pf + j] == f1[i * pf + j]);
                    } else {
                        let r = j - q * pt;
                        assert(f@[i * pf + j] == h.table@[r]);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, pt, q as int, r);
                    }
                }
            }
            q = q + 1;
        }
        proof {
            assert(q * pt == pf) by (nonlinear_arith)
                requires
                    q == pd,
                    pf == pt * pd,
            ;
            assert(i * pf + pf == (i + 1) * pf) by (nonlinear_arith);
            assert((i + 1) * pf <= 256 * 1024) by (nonlinear_arith)
                requires
                    i + 1 <= 256,
                    0 <= pf <= 1024,
            ;
            assert forall|k: int| 0 <= k < i + 1 implies flat_at(f@, k, t as u64, #[trigger] codes@[k]) by {
                if k < i {
                    lemma_flat_ext(f0, f@, k, t as u64, codes@[k]);
                } else {
                    assert forall|j: int| 0 <= j < pf implies #[trigger] fget(f@, i as int, t as u64, j) == h.table@[j % pt] by {
                        assert(f@[i * pf + j] == h.table@[j % pt]);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        reveal(flat_ok);
    }
    (f, t as u64)
}

pub fn code_at(b: &[HCode], i: usize) -> (r: &HCode)
    requires
        i < b@.len(),
    ensures
        *r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { b.get_unchecked(i) }
}

impl Decoder {

    /// Appends `x` to the output.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn put(&mut self, x: u8)
        requires
            ring_ok(old(self).ring@, old(self).rbits, old(self).total, old(self).flushed, old(self).out@, old(self).ph, old(self).mrem, old(self).wbits),
            old(self).ring@.len() - (old(self).total - old(self).flushed) > 0,
            old(self).mrem >= 1,
            old(self).ph != Ph::Metadata,
        ensures
            ring_ok(final(self).ring@, final(self).rbits, final(self).total, final(self).flushed, final(self).out@, final(self).ph, (final(self).mrem - 1) as u32, final(self).wbits),
            final(self).out@ == old(self).out@.push(x),
            final(self).total == old(self).total + 1,
            final(self).ring@.len() == old(self).ring@.len(),
            *final(self) == (Decoder { ring: final(self).ring, total: final(self).total, out: final(self).out, ..*old(self) }),
    {
        proof {
            reveal(ring_ok);
            lemma_mask(self.rbits as u64);
            lemma_and_mask(self.total, self.rbits as u64);
        }
        let r = self.ring.len() as u64;
        let i = self.total & (r - 1);
        let ghost t = self.total as int;
        let ghost ring0 = self.ring@;
        verilith_core::prims::store_at(&mut self.ring, i as usize, x);
        self.total = self.total + 1;
        self.out = Ghost(self.out@.push(x));
        proof {
            let rr = r as int;
            assert forall|j: int| 0 <= j < self.total && j >= self.total - rr && (j >= self.total - rr + 16 || j >= self.flushed || self.total <= rr) implies #[trigger] self.out@[j] == self.ring@[j % rr] by {
                if j < t {
                    assert(j % rr != t % rr) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, rr);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t, rr);
                        assert(t - j < rr);
                        if j % rr == t % rr {
                            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(rr, t / rr, j / rr);
                            assert(t - j == rr * (t / rr - j / rr));
                            if t / rr - j / rr >= 1 {
                                vstd::arithmetic::mul::lemma_mul_inequality(1, t / rr - j / rr, rr);
                            } else {
                                vstd::arithmetic::mul::lemma_mul_inequality(t / rr - j / rr, 0, rr);
                            }
                        }
                    }
                    assert(self.ring@[j % rr] == ring0[j % rr]);
                }
            }
        }
    }

    /// The byte `d` back in the output.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn back(&self, d: u64) -> (r: u8)
        requires
            ring_ok(self.ring@, self.rbits, self.total, self.flushed, self.out@, self.ph, self.mrem, self.wbits),
            1 <= d <= self.total,
            d <= self.ring@.len(),
            d <= self.ring@.len() - 16 || self.total <= self.ring@.len(),
        ensures
            r == self.out@[self.total - d],
    {
        proof {
            reveal(ring_ok);
            lemma_mask(self.rbits as u64);
            lemma_and_mask((self.total - d) as u64, self.rbits as u64);
        }
        let r = self.ring.len() as u64;
        verilith_core::prims::get(self.ring.as_slice(), ((self.total - d) & (r - 1)) as usize)
    }

    /// `m` bytes of a copy in one go: neither ring range wraps, and no
    /// byte read is one the copy writes (`m <= dist`). Writes only the
    /// ring: the decoder after it is `copy_next`.
    #[verifier::spinoff_prover]
    #[inline(always)]
    pub fn copy_chunk(ring: &mut Vec<u8>, si: usize, ti: usize, m: u64, wide: bool, Ghost(g): Ghost<Decoder>, Ghost(b): Ghost<Seq<u8>>)
        requires
            wide ==> ti + 16 <= g.ring@.len() && g.ring@.len() - (g.total - g.flushed) >= 16,
            g.wf(),
            g.reached(b),
            g.ph == Ph::Copy,
            *old(ring) == g.ring,
            1 <= m <= g.clen,
            m <= g.dist,
            m <= g.ring@.len() - (g.total - g.flushed),
            g.ring@.len() > 0,
            si as int == (g.total - g.dist) as int % g.ring@.len() as int,
            ti as int == g.total as int % g.ring@.len() as int,
            si + m <= g.ring@.len(),
            ti + m <= g.ring@.len(),
        ensures
            final(ring)@.len() == old(ring)@.len(),
            copy_next(g, *final(ring), m).wf(),
            copy_next(g, *final(ring), m).reached(b),
            g.out@.is_prefix_of(copy_next(g, *final(ring), m).out@),
            crate::rank::rank_lt(b, copy_next(g, *final(ring), m).view(), g.view()),
    {
        let ghost o = g;
        let ghost s = g.view();
        proof {
            reveal(cmd_ok);
            reveal(ring_ok);
            lemma2_to64();
            lemma_pow2_le(10, g.wbits as nat);
            lemma_copy_run(b, spec::init(), g.steps@, s, m as int);
        }
        let ghost r = g.ring@.len() as int;
        let ghost d = g.dist as int;
        let ghost t = g.total as int;
        let ghost l = t - d;
        proof {
            lemma_ring_order(l, d, r);
        }
        // What is written: 16 bytes by the wide copy, whatever `m` is. The
        // bytes past `m` land on ones the ring no longer has to hold.
        let ghost w: int = if wide && m <= 16 && si + 16 <= ti { 16 } else { m as int };
        if wide && m <= 16 && si + 16 <= ti {
            copy16(ring.as_mut_slice(), si, ti);
        } else if m < 8 {
            copy_small(ring.as_mut_slice(), si, ti, m as usize);
        } else if si + (m as usize) <= ti && m < 64 {
            copy_words(ring.as_mut_slice(), si, ti, m as usize);
        } else {
            verilith_core::prims::copy_within(ring.as_mut_slice(), si, ti, m as usize);
        }
        proof {
            let n = copy_next(g, *ring, m);
            let ring0 = o.ring@;
            // The source lies within the bytes the ring still holds.
            assert(d <= r - 16 || t <= r);
            assert forall|i: int| 0 <= i < n.total && i >= n.total - r && (i >= n.total - r + 16 || i >= n.flushed || n.total <= r) implies #[trigger] n.out@[i] == n.ring@[i % r] by {
                if i >= t {
                    lemma_mod_add(t, r, i - t);
                    lemma_mod_add(l, r, i - t);
                    assert(n.out@[i] == o.out@[l + (i - t)]);
                    assert(n.ring@[i % r] == ring0[si + (i - t)]);
                    assert(o.out@[l + (i - t)] == ring0[(l + (i - t)) % r]);
                } else {
                    assert(n.out@[i] == o.out@[i]);
                    lemma_mod_add(t, r, 0);
                    // i + r = t + j with m <= j < r, so i % r lies outside the written range.
                    if n.total <= r {
                        vstd::arithmetic::div_mod::lemma_small_mod(t as nat, r as nat);
                    }
                    assert(t + w - r <= i);
                    lemma_ring_gap(i, t, r, ti as int, w);
                    assert(n.ring@[i % r] == ring0[i % r]);
                }
            }
            lemma_wf_data(o, n);
            assert(n.view() == copied(s, m as int));
            assert(o.out@.is_prefix_of(n.out@));
            reveal(cmd_ok);
            crate::rank::lemma_rank_bytes(b, o.view(), n.view());
            assert(n.wf());
        }
    }

    /// `copy_chunk` on the decoder itself.
    #[verifier::spinoff_prover]
    fn copy_bulk(&mut self, si: usize, ti: usize, m: u64, Ghost(b): Ghost<Seq<u8>>)
        requires
            old(self).wf(),
            old(self).reached(b),
            old(self).ph == Ph::Copy,
            1 <= m <= old(self).clen,
            m <= old(self).dist,
            m <= old(self).ring@.len() - (old(self).total - old(self).flushed),
            old(self).ring@.len() > 0,
            si as int == (old(self).total - old(self).dist) as int % old(self).ring@.len() as int,
            ti as int == old(self).total as int % old(self).ring@.len() as int,
            si + m <= old(self).ring@.len(),
            ti + m <= old(self).ring@.len(),
        ensures
            final(self).wf(),
            final(self).reached(b),
            final(self).flushed == old(self).flushed,
            old(self).out@.is_prefix_of(final(self).out@),
            final(self).pos == old(self).pos,
            old(self).steps@ < final(self).steps@,
            crate::rank::rank_lt(b, final(self).view(), old(self).view()),
    {
        let ghost o = *self;
        proof {
            reveal(cmd_ok);
            reveal(ring_ok);
        }
        Self::copy_chunk(&mut self.ring, si, ti, m, false, Ghost(o), Ghost(b));
        let ghost n = copy_next(o, self.ring, m);
        self.total = self.total + m;
        self.clen = self.clen - m as u32;
        self.mrem = self.mrem - m as u32;
        if self.clen == 0 {
            self.ph = after_data(self.mrem);
        }
        self.out = Ghost(n.out@);
        self.steps = Ghost(self.steps@ + m as nat);
        proof {
            assert(*self == n);
        }
    }

    /// The whole of a copy that fits the ring without wrapping, in chunks
    /// of at most the distance. Writes only the ring; returns the decoder
    /// after it.
    #[verifier::spinoff_prover]
    #[inline(always)]
    pub fn copy_all(ring: &mut Vec<u8>, si: usize, ti: usize, n: u64, d: u64, wide: bool, Ghost(g): Ghost<Decoder>, Ghost(b): Ghost<Seq<u8>>) -> (gn: Ghost<Decoder>)
        requires
            wide ==> ti + 16 <= g.ring@.len() && g.ring@.len() - (g.total - g.flushed) >= 16,
            g.wf(),
            g.reached(b),
            g.ph == Ph::Copy,
            *old(ring) == g.ring,
            n == g.clen,
            d == g.dist,
            n <= g.ring@.len() - (g.total - g.flushed),
            g.ring@.len() > 0,
            si as int == (g.total - g.dist) as int % g.ring@.len() as int,
            ti as int == g.total as int % g.ring@.len() as int,
            si + n <= g.ring@.len(),
            ti + n <= g.ring@.len(),
        ensures
            final(ring)@.len() == old(ring)@.len(),
            gn@ == copy_done(g, *final(ring), gn@.out, gn@.steps),
            gn@.wf(),
            gn@.reached(b),
            g.out@.is_prefix_of(gn@.out@),
            g.steps@ < gn@.steps@,
            crate::rank::rank_lt(b, gn@.view(), g.view()),
    {
        let ghost r = g.ring@.len() as int;
        let ghost mut cur = g;
        proof {
            reveal(cmd_ok);
            reveal(ring_ok);
            lemma2_to64();
            lemma_pow2_le(10, g.wbits as nat);
            assert(1 <= d <= g.total && d <= r);
            assert(1 <= n <= g.mrem);
            assert(g.out@.is_prefix_of(g.out@)) by {
                assert(g.out@.subrange(0, g.out@.len() as int) =~= g.out@);
            }
        }
        let rl = ring.len();
        if d >= n {
            proof {
                lemma_mod_add((g.total - g.dist) as int, r, 0);
                lemma_mod_add(g.total as int, r, 0);
            }
            Self::copy_chunk(ring, si, ti, n, wide, Ghost(g), Ghost(b));
            return Ghost(copy_next(g, *ring, n));
        }
        let mut k: u64 = 0;
        while k < n
            invariant
                k <= n,
                1 <= n <= g.mrem,
                n == g.clen,
                d == g.dist,
                1 <= d <= g.total,
                g.total + g.mrem <= MAX_OUT,
                r == g.ring@.len(),
                r > 0,
                ring@.len() == r,
                n <= r - (g.total - g.flushed),
                g.flushed <= g.total,
                si as int == (g.total - g.dist) as int % r,
                ti as int == g.total as int % r,
                si + n <= r,
                ti + n <= r,
                cur.wf(),
                cur.reached(b),
                cur == (Decoder {
                    ring: *ring,
                    total: (g.total + k) as u64,
                    clen: (g.clen - k) as u32,
                    mrem: (g.mrem - k) as u32,
                    ph: cur.ph,
                    out: cur.out,
                    steps: cur.steps,
                    ..g
                }),
                k < n ==> cur.ph == Ph::Copy,
                k == n ==> cur.ph == (if g.mrem == n { Ph::MetaDone } else { Ph::CmdBegin }),
                g.out@.is_prefix_of(cur.out@),
                g.steps@ <= cur.steps@,
                k == 0 ==> cur == g,
                k > 0 ==> g.steps@ < cur.steps@ && crate::rank::rank_lt(b, cur.view(), g.view()),
                r == rl,
            decreases n - k,
        {
            let m = if n - k < d { n - k } else { d };
            proof {
                lemma_mod_add((g.total - g.dist) as int, r, k as int);
                lemma_mod_add(g.total as int, r, k as int);
            }
            let ghost prev = cur;
            Self::copy_chunk(ring, si + k as usize, ti + k as usize, m, false, Ghost(cur), Ghost(b));
            proof {
                cur = copy_next(prev, *ring, m);
                lemma_prefix_trans(g.out@, prev.out@, cur.out@);
                if k > 0 {
                    crate::rank::lemma_rank_trans(b, cur.view(), prev.view(), g.view());
                }
            }
            k = k + m;
        }
        Ghost(cur)
    }

    /// The distance step when it names a dictionary word, for `fast_loop`:
    /// writes the word to the ring in one piece. Leaves everything as it
    /// is (`false`) for whatever is not the plain case: a bad reference, an
    /// empty word, one that does not fit the meta-block, the output room or
    /// the ring before its end. `resolve_dict` deals with those. `wv` and
    /// `mid` are scratch space for a transformed word.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    #[inline(never)]
    pub fn dict_p(
        ring: &mut Vec<u8>,
        wv: &mut Vec<u8>,
        mid: &mut Vec<u8>,
        d: u64,
        maxd: u64,
        last: bool,
        p: u64,
        blen2: u32,
        clen: u32,
        mrem: u32,
        tot: u64,
        r: u64,
        flushed: u64,
        Ghost(g): Ghost<Decoder>,
        Ghost(src): Ghost<Seq<u8>>,
        base: u64,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (res: (bool, u64, Ghost<Decoder>))
        requires
            g.wf(),
            g.reached(b),
            g.ph == Ph::Dist,
            *old(ring) == g.ring,
            g.pos <= p <= lim(src, base as int),
            blen2 <= g.blen[2],
            1 <= d < 0x8000_0000,
            spec::step(b, g.view()) == spec::resolve(
                St { pos: p as int, blen: seq3(g.blen).update(2, blen2 as int), ..g.view() },
                d as int,
                last,
            ),
            maxd == spec::max_distance(g.total as int, g.wbits as int),
            d > maxd,
            clen == g.clen,
            mrem == g.mrem,
            g.ring@.len() > 0,
            tot == g.total,
            r == g.ring@.len(),
            flushed == g.flushed,
        ensures
            final(ring)@.len() == old(ring)@.len(),
            !res.0 ==> *final(ring) == *old(ring),
            res.0 ==> {
                let n = res.2@;
                &&& 1 <= res.1 <= g.mrem
                &&& n == dict_next(g, *final(ring), n.out, res.1, p, blen2)
                &&& n.wf()
                &&& n.reached(b)
                &&& g.out@.is_prefix_of(n.out@)
                &&& crate::rank::rank_lt(b, n.view(), g.view())
            },
    {
        let ghost s0 = g.view();
        let ghost s1 = St { pos: p as int, blen: seq3(g.blen).update(2, blen2 as int), ..s0 };
        proof {
            lemma_dist_facts(g);
            lemma_ring_basic(g);
            lemma2_to64();
            lemma_resolve_dict(s1, d as int, last);
        }
        if d > 0x7FFF_FFFC || clen < 4 || clen > 24 {
            return (false, 0, Ghost(g));
        }
        let len = clen as usize;
        let addr = d - maxd - 1;
        proof {
            lemma_tables();
            assert(NDBITS[len as int] <= 11);
            lemma_pow2_le(NDBITS[len as int] as nat, 11);
            lemma_pow2_pos(NDBITS[len as int] as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, NDBITS[len as int] as u64);
        }
        let pn = 1u64 << (NDBITS[len] as u64);
        let nd = NDBITS[len] as u64;
        let idx = addr & (pn - 1);
        let tid = addr >> nd;
        proof {
            assert(idx == addr % pn && tid == addr / pn) by (bit_vector)
                requires
                    nd <= 11,
                    pn == 1u64 << nd,
                    idx == addr & ((pn - 1) as u64),
                    tid == addr >> nd,
            ;
        }
        if tid >= 121 {
            return (false, 0, Ghost(g));
        }
        proof {
            assert(DOFFSET[len as int] + pow2(NDBITS[len as int] as nat) * len <= 122784);
            assert((idx + 1) * len <= pn * len) by (nonlinear_arith)
                requires
                    idx < pn,
            ;
        }
        proof {
            reveal(ring_ok);
            lemma_mask(g.rbits as u64);
            lemma_and_mask(tot, g.rbits as u64);
        }
        let ti = (tot & (r - 1)) as usize;
        let room = r - (tot - flushed);
        let rl = ring.len();
        if room >= 17 && ti as u64 + 64 <= r {
            // The common case: straight into the ring, 8 bytes at a time.
            let lim = if (mrem as u64) < room - 16 { mrem as u64 } else { room - 16 };
            if tid == 0 {
                // The identity, the most common transform: the word alone.
                proof {
                    assert(idx * len + len == (idx + 1) * len) by (nonlinear_arith);
                }
                let off = DOFFSET[len] as usize + idx as usize * len;
                if off + 24 <= 122784 && len as u64 <= lim {
                    crate::words::put_word(ring, ti, off, len);
                    let ghost w = spec::dict_word(len as int, idx as int);
                    let ghost n = dict_next(g, *ring, Ghost(g.out@ + w), len as u64, p, blen2);
                    proof {
                        lemma_transform0(w);
                        assert(ring@.subrange(ti as int, ti + len) =~= w);
                        lemma_dict_next(g, *ring, w, p, blen2, ti as int, 16, b);
                    }
                    return (true, len as u64, Ghost(n));
                }
            }
            let wl = crate::words::transform_ring(ring, ti, len, idx as usize, tid as usize, lim);
            if wl != 0 {
                let ghost w = spec::transform(spec::dict_word(len as int, idx as int), tid as int);
                let ghost n = dict_next(g, *ring, Ghost(g.out@ + w), wl as u64, p, blen2);
                proof {
                    lemma_dict_next(g, *ring, w, p, blen2, ti as int, 16, b);
                }
                return (true, wl as u64, Ghost(n));
            }
        }
        let word = dict_word(len, idx as usize);
        // Transform 0, the identity, is the common one: no buffer for it.
        if tid != 0 {
            wv.clear();
            transform_into(wv, mid, word, tid as usize);
        }
        let w: &[u8] = if tid == 0 { word } else { wv.as_slice() };
        proof {
            if tid == 0 {
                lemma_transform0(word@);
            }
            assert(w@ =~= spec::transform(spec::dict_word(len as int, idx as int), tid as int));
        }
        let wl = w.len();
        if wl == 0 || wl as u64 > mrem as u64 || wl as u64 > room || wl > rl - ti {
            return (false, 0, Ghost(g));
        }
        let ghost ring0 = ring@;
        verilith_core::prims::copy_in(ring.as_mut_slice(), ti, w, 0, wl);
        let ghost n = dict_next(g, *ring, Ghost(g.out@ + w@), wl as u64, p, blen2);
        proof {
            assert(w@.subrange(0, wl as int) =~= w@);
            assert(ring@.subrange(ti as int, ti + wl) =~= w@);
            lemma_dict_next(g, *ring, w@, p, blen2, ti as int, 0, b);
        }
        (true, wl as u64, Ghost(n))
    }

    /// The whole copy of a command, for `fast_loop`. Does nothing (`false`)
    /// when the copy does not fit the output room or runs over the end of
    /// the ring; `st_copy` deals with those.
    #[verifier::spinoff_prover]
    #[inline(always)]
    pub fn copy_cmd(ring: &mut Vec<u8>, tot: u64, d: u64, n: u64, r: u64, flushed: u64, Ghost(g): Ghost<Decoder>, Ghost(b): Ghost<Seq<u8>>) -> (res: (bool, Ghost<Decoder>))
        requires
            g.wf(),
            g.reached(b),
            g.ph == Ph::Copy,
            *old(ring) == g.ring,
            n == g.clen,
            d == g.dist,
            tot == g.total,
            flushed == g.flushed,
            r == g.ring@.len(),
            r > 0,
        ensures
            final(ring)@.len() == old(ring)@.len(),
            !res.0 ==> *final(ring) == *old(ring),
            res.0 ==> {
                let gn = res.1@;
                &&& gn == copy_done(g, *final(ring), gn.out, gn.steps)
                &&& gn.wf()
                &&& gn.reached(b)
                &&& g.out@.is_prefix_of(gn.out@)
                &&& g.steps@ < gn.steps@
                &&& crate::rank::rank_lt(b, gn.view(), g.view())
            },
    {
        proof {
            reveal(cmd_ok);
            reveal(ring_ok);
            lemma_ring_basic(g);
            lemma2_to64();
            lemma_mask(g.rbits as u64);
            assert(1 <= d <= tot && d <= r);
            assert(1 <= n <= g.mrem);
            lemma_and_mask((tot - d) as u64, g.rbits as u64);
            lemma_and_mask(tot, g.rbits as u64);
        }
        let mask = r - 1;
        let si = ((tot - d) & mask) as usize;
        let ti = (tot & mask) as usize;
        let room = r - (tot - flushed);
        if n <= 16 && room >= 16 && ti as u64 + 16 <= r && si + 16 <= ti {
            // The common case, a short copy from at least 16 back with
            // room for 16 bytes whatever its length: these four tests
            // cover everything the general case checks.
            proof {
                lemma_ring_order(tot - d, d as int, r as int);
                assert(d >= 16);
            }
            Self::copy_chunk(ring, si, ti, n, true, Ghost(g), Ghost(b));
            let ghost gn = copy_next(g, *ring, n);
            proof {
                assert(gn == copy_done(g, *ring, gn.out, gn.steps));
            }
            return (true, Ghost(gn));
        }
        if n > room || si as u64 + n > r || ti as u64 + n > r {
            return (false, Ghost(g));
        }
        let gn = Self::copy_all(ring, si, ti, n, d, false, Ghost(g), Ghost(b));
        (true, gn)
    }

    /// Makes the ring big enough for `need` bytes of output in total, up to
    /// the window size, and at least 1024 bytes (google/brotli's
    /// `BrotliCalculateRingBufferSize`). `ph2` and `mrem2` are the phase
    /// and bytes left the ring is for.
    #[verifier::spinoff_prover]
    fn grow_ring(&mut self, need: u64, Ghost(ph2): Ghost<Ph>, Ghost(mrem2): Ghost<u32>)
        requires
            ring_ok(old(self).ring@, old(self).rbits, old(self).total, old(self).flushed, old(self).out@, Ph::MetaHeader, 0, old(self).wbits),
            10 <= old(self).wbits <= 24,
            old(self).total + mrem2 <= need <= MAX_OUT,
            ph2 != Ph::WBits,
        ensures
            ring_ok(final(self).ring@, final(self).rbits, final(self).total, final(self).flushed, final(self).out@, ph2, mrem2, final(self).wbits),
            *final(self) == (Decoder { ring: final(self).ring, rbits: final(self).rbits, ..*old(self) }),
    {
        proof {
            reveal(ring_ok);
            lemma2_to64();
            lemma_mask(self.wbits as u64);
            lemma_mask(10);
        }
        let win = 1u64 << self.wbits;
        let mut size: u64 = 1024;
        let mut bits: u32 = 10;
        proof {
            lemma_pow2_le(10, self.wbits as nat);
        }
        while size < need && size < win
            invariant
                size == pow2(bits as nat),
                10 <= bits <= self.wbits <= 24,
                size <= win,
                win == pow2(self.wbits as nat),
            decreases win - size,
        {
            proof {
                lemma_pow2_adds(bits as nat, 1);
                lemma2_to64();
                if bits + 1 > self.wbits {
                    lemma_pow2_strictly_increases(self.wbits as nat, bits as nat);
                } else {
                    lemma_pow2_le((bits + 1) as nat, self.wbits as nat);
                }
            }
            size = size * 2;
            bits = bits + 1;
        }
        let ghost win_i = win as int;
        if (self.ring.len() as u64) < size {
            // Below the window size the ring has never wrapped: byte `i` of
            // the output is at `ring[i]`.
            let ghost old_ring = self.ring@;
            let n = self.total as usize;
            let mut r = vec![0u8; size as usize];
            proof {
                assert(self.total <= old_ring.len());
            }
            verilith_core::prims::copy_in(r.as_mut_slice(), 0, self.ring.as_slice(), 0, n);
            self.ring = r;
            self.rbits = bits;
            proof {
                let rr = size as int;
                assert forall|i: int| 0 <= i < self.total && i >= self.total - rr implies #[trigger] self.out@[i] == self.ring@[i % rr] by {
                    vstd::arithmetic::div_mod::lemma_small_mod(i as nat, rr as nat);
                    assert(self.ring@[i] == (Seq::<u8>::empty() + old_ring.subrange(0, n as int)
                        + Seq::new(size as nat, |k: int| 0u8).subrange(n as int, rr))[i]);
                    assert(self.ring@[i] == old_ring[i]);
                    vstd::arithmetic::div_mod::lemma_small_mod(i as nat, old_ring.len());
                }
            }
        }
    }

    /// `spec::pc_alpha`.
    #[verifier::spinoff_prover]
    fn pc_alpha(&self) -> (r: u32)
        requires
            self.wf(),
        ensures
            r == spec::pc_alpha(self.view()),
            r <= 2328,
    {
        proof {
            reveal(maps_ok);
            reveal(reading_ok);
        }
        match self.ph {
            Ph::BTypeCode(c) => {
                proof {
                    reveal(cat_ok);
                }
                self.nbt[c as usize] + 2
            },
            Ph::BCountCode(_) => 26,
            Ph::CMap(_) => self.cm.ntrees + self.cm.rlemax,
            Ph::Trees(g) => if g == 0 {
                256
            } else if g == 1 {
                704
            } else {
                proof {
                    lemma2_to64();
                    vstd::bits::lemma_u32_shl_is_mul(48, self.npostfix);
                    lemma_pow2_le(self.npostfix as nat, 3);
                }
                16 + self.ndirect + (48u32 << self.npostfix)
            },
            _ => 0,
        }
    }
}

impl Decoder {
    /// `WBits`: the window size.
    #[verifier::spinoff_prover]
    fn st_wbits(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::WBits,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_wbits(b, s0);
        }
        match read_wbits(src, base, self.pos, Ghost(b)) {
            Res::Ok(w, p) => {
                self.wbits = w as u32;
                self.pos = p;
                self.ph = Ph::MetaHeader;
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(reading_ok);
                    reveal(cmd_ok);
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
            Res::Bad => {
                proof {
                    lemma_rejects(b, o.steps@, s0);
                }
                Some(Status::Bad)
            },
            Res::Short => Some(Status::Short),
        }
    }

    /// `MetaDone`: the padding after the last meta-block, or the next
    /// meta-block.
    #[verifier::spinoff_prover]
    fn st_metadone(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::MetaDone,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_metadone(b, s0);
            reveal(ring_ok);
            reveal(reading_ok);
            reveal(cmd_ok);
        }
        if self.last {
            match pad(src, base, self.pos, Ghost(b)) {
                Res::Ok(_, p) => {
                    self.pos = p;
                    self.ph = Ph::Done;
                    self.steps = Ghost(self.steps@ + 1);
                    proof {
                        assert(spec::step(b, s0) == Step::Next(self.view()));
                        lemma_run_extend(b, spec::init(), o.steps@, s0);
                        assert(o.out@.is_prefix_of(self.out@));
                    }
                    Some(Status::Done)
                },
                Res::Bad => {
                    proof {
                        lemma_rejects(b, o.steps@, s0);
                    }
                    Some(Status::Bad)
                },
                Res::Short => Some(Status::Short),
            }
        } else {
            self.ph = Ph::MetaHeader;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            None
        }
    }

    /// Clears the meta-block's codes and maps (`spec::begin_compressed`).
    #[verifier::spinoff_prover]
    fn reset_metablock(&mut self)
        requires
            old(self).ph == Ph::NBlockTypes(0),
        ensures
            final(self).view() == spec::begin_compressed(old(self).view()),
            final(self).btc@.len() == 3 && final(self).bcc@.len() == 3,
            final(self).btcl@.len() == 3 && final(self).bccl@.len() == 3,
            final(self).lit@.len() == 0 && final(self).cmd@.len() == 0 && final(self).dst@.len() == 0,
            final(self).litf@.len() == 0 && final(self).dstf@.len() == 0,
            final(self).ph == old(self).ph,
            final(self).ring == old(self).ring,
            final(self).rbits == old(self).rbits,
            final(self).total == old(self).total,
            final(self).flushed == old(self).flushed,
            final(self).steps == old(self).steps,
            final(self).word == old(self).word,
            final(self).pc.view() == spec::pc_init(),
            final(self).cm.view() == spec::cm_init(),
            final(self).nbt == [1u32, 1, 1] && final(self).bt == [0u32, 0, 0] && final(self).bt2 == [1u32, 1, 1]
                && final(self).blen == [BLOCK_CAP, BLOCK_CAP, BLOCK_CAP],
            *final(self) == (Decoder {
                nbt: final(self).nbt,
                btc: final(self).btc,
                bcc: final(self).bcc,
                blen: final(self).blen,
                bt: final(self).bt,
                bt2: final(self).bt2,
                cmodes: final(self).cmodes,
                cmap: final(self).cmap,
                dmap: final(self).dmap,
                lit: final(self).lit,
                litf: final(self).litf,
                dstf: final(self).dstf,
                cmd: final(self).cmd,
                dst: final(self).dst,
                pc: final(self).pc,
                cm: final(self).cm,
                btcl: final(self).btcl,
                bccl: final(self).bccl,
                litl: final(self).litl,
                cmdl: final(self).cmdl,
                dstl: final(self).dstl,
                ..*old(self)
            }),
    {
        self.nbt = [1, 1, 1];
        self.btc = vec![empty_code(), empty_code(), empty_code()];
        self.bcc = vec![empty_code(), empty_code(), empty_code()];
        self.blen = [BLOCK_CAP, BLOCK_CAP, BLOCK_CAP];
        self.bt = [0, 0, 0];
        self.bt2 = [1, 1, 1];
        self.cmodes = Vec::new();
        self.cmap = Vec::new();
        self.dmap = Vec::new();
        self.lit = Vec::new();
        self.litf = Vec::new();
        self.dstf = Vec::new();
        self.cmd = Vec::new();
        self.dst = Vec::new();
        self.pc.reset();
        self.cm = Cmx::new();
        let ghost e3: Seq<Seq<u8>> = seq![Seq::empty(), Seq::empty(), Seq::empty()];
        self.btcl = Ghost(e3);
        self.bccl = Ghost(e3);
        self.litl = Ghost(Seq::empty());
        self.cmdl = Ghost(Seq::empty());
        self.dstl = Ghost(Seq::empty());
        proof {
            assert(self.cmodes@ =~= Seq::<u8>::empty());
            assert(self.cmap@ =~= Seq::<u8>::empty());
            assert(self.dmap@ =~= Seq::<u8>::empty());
            assert(seq3(self.nbt) =~= seq![1int, 1, 1]);
            assert(seq3(self.blen) =~= seq![spec::BLOCK_CAP, spec::BLOCK_CAP, spec::BLOCK_CAP]);
            assert(seq3(self.bt) =~= seq![0int, 0, 0]);
            assert(seq3(self.bt2) =~= seq![1int, 1, 1]);
            let v = self.view();
            let w = spec::begin_compressed(old(self).view());
            assert(v.btc == w.btc);
            assert(v.bcc == w.bcc);
            assert(v.lit == w.lit);
            assert(v.cmd == w.cmd);
            assert(v.dst == w.dst);
            assert(v.pc == w.pc);
            assert(v.cm == w.cm);
            assert(v.nbt == w.nbt);
            assert(v =~= w);
        }
    }

    /// `MetaHeader`: a meta-block header.
    #[verifier::spinoff_prover]
    fn st_header(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::MetaHeader,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_header(b, s0);
            reveal(ring_ok);
            reveal(reading_ok);
            reveal(cmd_ok);
        }
        let (h, p) = match read_meta_header(src, base, self.pos, Ghost(b)) {
            Res::Bad => {
                proof {
                    lemma_rejects(b, o.steps@, s0);
                }
                return Some(Status::Bad);
            },
            Res::Short => return Some(Status::Short),
            Res::Ok(h, p) => (h, p),
        };
        let ghost sh = match spec::read_meta_header(b, o.pos as int) {
            R::Ok(sh, _) => sh,
            _ => arbitrary(),
        };
        let ghost s1 = St { pos: p as int, last: h.last, mrem: h.len as int, ..s0 };
        if h.kind == K_EMPTY_LAST {
            match pad(src, base, p, Ghost(b)) {
                Res::Ok(_, p2) => {
                    self.pos = p2;
                    self.last = true;
                    self.mrem = 0;
                    self.ph = Ph::Done;
                    self.steps = Ghost(self.steps@ + 1);
                    proof {
                        assert(sh.kind is EmptyLast);
                        assert(spec::step(b, s0) == Step::Next(self.view()));
                        lemma_run_extend(b, spec::init(), o.steps@, s0);
                        assert(o.out@.is_prefix_of(self.out@));
                    }
                    return Some(Status::Done);
                },
                Res::Bad => {
                    proof {
                        assert(sh.kind is EmptyLast);
                        lemma_rejects(b, o.steps@, s0);
                    }
                    return Some(Status::Bad);
                },
                Res::Short => {
                    proof {
                        assert(sh.kind is EmptyLast);
                    }
                    return Some(Status::Short);
                },
            }
        }
        if h.kind == K_METADATA {
            self.pos = p;
            self.last = h.last;
            self.mrem = h.len;
            self.ph = Ph::Metadata;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(sh.kind is Metadata);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            return None;
        }
        if self.total + h.len as u64 > MAX_OUT {
            return Some(Status::Limit);
        }
        let ph2 = if h.kind == K_UNCOMPRESSED { Ph::Uncompressed } else { Ph::NBlockTypes(0) };
        self.grow_ring(self.total + h.len as u64, Ghost(ph2), Ghost(h.len));
        self.pos = p;
        self.last = h.last;
        self.mrem = h.len;
        if h.kind == K_UNCOMPRESSED {
            self.ph = Ph::Uncompressed;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(sh.kind is Uncompressed);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            None
        } else {
            self.ph = Ph::NBlockTypes(0);
            self.reset_metablock();
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(sh.kind is Compressed);
                reveal(cat_ok);
                reveal(maps_ok);
                reveal(trees_ok);
                assert(self.view() == spec::begin_compressed(s1));
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
                assert(self.pc.inv(0));
            }
            None
        }
    }

    /// `Metadata`: skips metadata bytes.
    #[verifier::spinoff_prover]
    fn st_skip(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Metadata,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_metadata(b, s0);
            reveal(ring_ok);
            reveal(reading_ok);
            reveal(cmd_ok);
        }
        if self.mrem == 0 {
            self.ph = Ph::MetaDone;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            return None;
        }
        // Skip whole bytes; the position is byte-aligned here.
        let avail = (8 * (base + src.len() as u64) - self.pos) / 8;
        if avail == 0 {
            proof {
                assert(full(src@, base as int, b) ==> verilith_core::bits::nbits(b) == lim(src@, base as int));
            }
            return Some(Status::Short);
        }
        let n = if avail < self.mrem as u64 { avail } else { self.mrem as u64 };
        self.pos = self.pos + 8 * n;
        self.mrem = self.mrem - n as u32;
        self.steps = Ghost(self.steps@ + n as nat);
        proof {
            assert(verilith_core::bits::nbits(b) >= lim(src@, base as int));
            lemma_skip(b, o.steps@, s0, n as nat);
            assert(self.view() == St { pos: s0.pos + 8 * n, mrem: s0.mrem - n, ..s0 });
            assert(o.out@.is_prefix_of(self.out@));
        }
        None
    }

    /// `Uncompressed`: copies bytes of an uncompressed meta-block.
    #[verifier::loop_isolation(false)]
    #[verifier::spinoff_prover]
    fn st_raw(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Uncompressed,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_raw(b, s0);
            reveal(ring_ok);
            reveal(reading_ok);
            reveal(cmd_ok);
        }
        if self.mrem == 0 {
            self.ph = Ph::MetaDone;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            return None;
        }
        let avail = (8 * (base + src.len() as u64) - self.pos) / 8;
        if avail == 0 {
            proof {
                assert(full(src@, base as int, b) ==> verilith_core::bits::nbits(b) == lim(src@, base as int));
            }
            return Some(Status::Short);
        }
        let room = self.room();
        if room == 0 {
            proof {
                reveal(cmd_ok);
                lemma_ring_big(*self);
            }
            return Some(Status::Full);
        }
        let mut n = if avail < self.mrem as u64 { avail } else { self.mrem as u64 };
        if n > room {
            n = room;
        }
        let start = (self.pos / 8 - base) as usize;
        let mut k: usize = 0;
        while k < n as usize
            invariant
                self.wf(),
                self.reached(b),
                self.ph == Ph::Uncompressed,
                self.pos == o.pos + 8 * k,
                self.mrem == o.mrem - k,
                self.total == o.total + k,
                self.flushed == o.flushed,
                o.out@.is_prefix_of(self.out@),
                self.steps@ == o.steps@ + k,
                k <= n,
                n <= o.mrem,
                n <= avail,
                n <= room,
                room == o.ring@.len() - (o.total - o.flushed),
                self.ring@.len() == o.ring@.len(),
                self.pos % 8 == 0,
                start == o.pos / 8 - base,
                o.pos + 8 * n <= lim(src@, base as int),
            decreases n - k,
        {
            let ghost s1 = self.view();
            let ghost n1 = self.steps@;
            let x = src[start + k];
            proof {
                reveal(ring_ok);
                reveal(cmd_ok);
                verilith_core::bits::lemma_bits_byte(b, (self.pos / 8) as int);
                assert(self.pos / 8 == base + start + k);
                assert(b[(self.pos / 8) as int] == x);
                assert(8 * (self.pos / 8) == self.pos);
            }
            self.put(x);
            self.pos = self.pos + 8;
            self.mrem = self.mrem - 1;
            self.steps = Ghost(self.steps@ + 1);
            k = k + 1;
            proof {
                reveal(cmd_ok);
                lemma_step_raw(b, s1);
                assert(spec::step(b, s1) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), n1, s1);
                assert(o.out@.is_prefix_of(self.out@)) by {
                    assert(o.out@.is_prefix_of(s1.out));
                }
            }
        }
        None
    }

    /// `NBlockTypes(c)`.
    #[verifier::spinoff_prover]
    fn st_nbt(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph is NBlockTypes,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let c = match self.ph {
            Ph::NBlockTypes(c) => c,
            _ => 0,
        };
        proof {
            lemma_step_nbt(b, s0, c as int);
        }
        match varlen8(src, base, self.pos, Ghost(b)) {
            Res::Bad => Some(Status::Bad),
            Res::Short => Some(Status::Short),
            Res::Ok(v, p) => {
                self.pos = p;
                self.nbt[c as usize] = v as u32 + 1;
                if v + 1 >= 2 {
                    self.pc.reset();
                    self.ph = Ph::BTypeCode(c);
                } else {
                    self.ph = after_cat(c);
                }
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(reading_ok);
                    reveal(cmd_ok);
                    reveal(cat_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    assert(seq3(self.nbt) =~= s0.nbt.update(c as int, v + 1));
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                    assert(self.pc.inv(spec::pc_alpha(self.view())));
                }
                None
            },
        }
    }
}

impl Decoder {
    /// `BTypeCode(c)` and `BCountCode(c)`: one item of a block type or
    /// block count code.
    #[verifier::spinoff_prover]
    fn st_code(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph is BTypeCode || old(self).ph is BCountCode,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let (c, count) = match self.ph {
            Ph::BTypeCode(c) => (c, false),
            Ph::BCountCode(c) => (c, true),
            _ => (0, false),
        };
        proof {
            lemma_step_code(b, s0);
            reveal(reading_ok);
            reveal(cat_ok);
        }
        let alpha = self.pc_alpha();
        match self.pc.step(src, base, self.pos, alpha, Ghost(b)) {
            Res::Bad => {
                proof {
                    lemma_rejects(b, o.steps@, s0);
                }
                Some(Status::Bad)
            },
            Res::Short => Some(Status::Short),
            Res::Ok(PcOut::More, p) => {
                self.pos = p;
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
            Res::Ok(PcOut::Code(h, lens), p) => {
                self.pos = p;
                self.pc.reset();
                if !count {
                    self.btc.set(c as usize, h);
                    self.btcl = Ghost(self.btcl@.update(c as int, lens@));
                    self.ph = Ph::BCountCode(c);
                } else {
                    self.bcc.set(c as usize, h);
                    self.bccl = Ghost(self.bccl@.update(c as int, lens@));
                    self.ph = Ph::BCount(c);
                }
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                    assert(self.pc.inv(spec::pc_alpha(self.view())));
                }
                None
            },
        }
    }

    /// `BCount(c)`: the first block count of category `c`.
    #[verifier::spinoff_prover]
    fn st_bcount(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph is BCount,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let c = match self.ph {
            Ph::BCount(c) => c,
            _ => 0,
        };
        proof {
            lemma_step_bcount(b, s0, c as int);
            reveal(cat_ok);
        }
        match read_blen(&self.bcc[c as usize], src, base, self.pos, Ghost(self.bccl@[c as int]), Ghost(b)) {
            Res::Bad => Some(Status::Bad),
            Res::Short => Some(Status::Short),
            Res::Ok(len, p) => {
                self.pos = p;
                self.blen[c as usize] = len as u32;
                self.ph = after_cat(c);
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    reveal(reading_ok);
                    assert(seq3(self.blen) =~= s0.blen.update(c as int, len as int));
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
        }
    }

    /// `DistParams`: `NPOSTFIX` and `NDIRECT`.
    #[verifier::spinoff_prover]
    fn st_dparams(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::DistParams,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_dparams(b, s0);
        }
        match read_bits(src, base, self.pos, 6, Ghost(b)) {
            None => Some(Status::Short),
            Some(v) => {
                proof {
                    lemma2_to64();
                }
                let np = (v % 4) as u32;
                self.pos = self.pos + 6;
                self.npostfix = np;
                proof {
                    lemma_pow2_le(np as nat, 3);
                    assert(v < 64);
                    assert((v / 4) * pow2(np as nat) <= 120) by (nonlinear_arith)
                        requires
                            v / 4 <= 15,
                            pow2(np as nat) <= 8,
                    ;
                    vstd::bits::lemma_u32_shl_is_mul((v / 4) as u32, np);
                }
                self.ndirect = ((v / 4) as u32) << np;
                if self.dtab.len() == 0 || self.dnp != np || self.dnd != self.ndirect {
                    self.dtab = mk_dtab(np, self.ndirect);
                    self.dnp = np;
                    self.dnd = self.ndirect;
                }
                self.cmodes = Vec::new();
                self.ph = Ph::CModes;
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    reveal(reading_ok);
                    reveal(cat_ok);
                    assert(self.cmodes@ =~= Seq::<u8>::empty());
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
        }
    }

    /// `CModes`: one context mode.
    #[verifier::spinoff_prover]
    fn st_cmodes(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CModes,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_cmodes(b, s0);
            reveal(maps_ok);
            reveal(reading_ok);
            reveal(cat_ok);
        }
        if self.cmodes.len() as u32 >= self.nbt[0] {
            self.ph = Ph::CMap(0);
            self.steps = Ghost(self.steps@ + 1);
            proof {
                reveal(ring_ok);
                reveal(cmd_ok);
                reveal(trees_ok);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
                assert(self.cm.map@.len() == 0);
            }
            return None;
        }
        match read_bits(src, base, self.pos, 2, Ghost(b)) {
            None => Some(Status::Short),
            Some(m) => {
                proof {
                    lemma2_to64();
                }
                self.pos = self.pos + 2;
                self.cmodes.push(m as u8);
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                    assert forall|i: int| 0 <= i < self.cmodes@.len() implies #[trigger] self.cmodes@[i] < 4 by {
                        if i < o.cmodes@.len() {
                            assert(self.cmodes@[i] == o.cmodes@[i]);
                        }
                    }
                }
                None
            },
        }
    }

    /// `Trees(g)`: one item of a literal, insert-and-copy or distance code.
    #[verifier::spinoff_prover]
    fn st_trees(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph is Trees,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let g = match self.ph {
            Ph::Trees(g) => g,
            _ => 0,
        };
        proof {
            lemma_step_trees(b, s0, g as int);
            reveal(trees_ok);
            reveal(maps_ok);
            reveal(cat_ok);
            reveal(reading_ok);
        }
        let (n, total) = if g == 0 {
            (self.lit.len(), self.ntl as usize)
        } else if g == 1 {
            (self.cmd.len(), self.nbt[1] as usize)
        } else {
            (self.dst.len(), self.ntd as usize)
        };
        if n >= total {
            if g < 2 {
                self.pc.reset();
                self.ph = Ph::Trees(g + 1);
            } else {
                // Side-by-side tables pay for themselves only when the
                // meta-block is long enough: up to 4 KiB is copied per
                // tree, so ask for 4 KiB of output per tree.
                proof {
                    assert forall|i: int| 0 <= i < self.lit@.len() implies (#[trigger] self.lit@[i]).tbits <= 10
                        && self.lit@[i].table@.len() == pow2(self.lit@[i].tbits as nat) by {
                        assert(hcode_ok(self.lit@[i], self.litl@[i]));
                    }
                    assert forall|i: int| 0 <= i < self.dst@.len() implies (#[trigger] self.dst@[i]).tbits <= 10
                        && self.dst@[i].table@.len() == pow2(self.dst@[i].tbits as nat) by {
                        assert(hcode_ok(self.dst@[i], self.dstl@[i]));
                    }
                }
                let nt = self.lit.len() as u64 + self.dst.len() as u64;
                if self.lit.len() <= 256 && self.dst.len() <= 256 && nt << 12 <= self.mrem as u64 {
                    let (f, t) = mk_flat(self.lit.as_slice());
                    self.litf = f;
                    self.litt = t;
                    let (f, t) = mk_flat(self.dst.as_slice());
                    self.dstf = f;
                    self.dstt = t;
                }
                self.ph = Ph::CmdBegin;
            }
            self.steps = Ghost(self.steps@ + 1);
            proof {
                reveal(ring_ok);
                reveal(cmd_ok);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            return None;
        }
        let alpha = self.pc_alpha();
        // The lengths of one code come one per step; take them in a row.
        let mut prog = false;
        let mut budget: u32 = 4096;
        loop
            invariant
                o == *old(self),
                self.wf(),
                self.reached(b),
                at(src@, base, self.pos, b),
                self.ph == o.ph,
                o.ph == Ph::Trees(g),
                g < 3,
                self.lit == o.lit && self.cmd == o.cmd && self.dst == o.dst,
                self.litl == o.litl && self.cmdl == o.cmdl && self.dstl == o.dstl,
                self.ntl == o.ntl && self.ntd == o.ntd && self.nbt == o.nbt,
                self.npostfix == o.npostfix && self.ndirect == o.ndirect,
                self.flushed == o.flushed,
                n < total,
                n == (if g == 0 { o.lit@.len() } else if g == 1 { o.cmd@.len() } else { o.dst@.len() }),
                total == (if g == 0 { o.ntl as usize } else if g == 1 { o.nbt[1] as usize } else { o.ntd as usize }),
                alpha == spec::pc_alpha(self.view()),
                2 <= alpha <= 2328,
                self.pc.inv(alpha as int),
                !prog ==> *self == o,
                prog ==> moved(o, *self, src@, base, b) && o.steps@ < self.steps@ && crate::rank::rank_lt(
                    b,
                    self.view(),
                    o.view(),
                ),
                budget >= 1,
            decreases budget,
        {
            let ghost m = *self;
            let ghost sm = self.view();
            proof {
                crate::rank::lemma_rank1(b, m);
                lemma_step_trees(b, sm, g as int);
                reveal(trees_ok);
                reveal(maps_ok);
                reveal(cat_ok);
                reveal(reading_ok);
            }
            match self.pc.step(src, base, self.pos, alpha, Ghost(b)) {
                Res::Bad => {
                    proof {
                        lemma_rejects(b, m.steps@, sm);
                    }
                    return Some(Status::Bad);
                },
                Res::Short => {
                    proof {
                        assert(*self == m);
                    }
                    if prog {
                        return None;
                    }
                    return Some(Status::Short);
                },
                Res::Ok(PcOut::More, p) => {
                    self.pos = p;
                    self.steps = Ghost(self.steps@ + 1);
                    proof {
                        assert(spec::step(b, sm) == Step::Next(self.view()));
                        lemma_run_extend(b, spec::init(), m.steps@, sm);
                        assert(m.out@.is_prefix_of(self.out@));
                        assert(self.wf());
                        assert(moved(m, *self, src@, base, b));
                        assert(crate::rank::rank_lt(b, self.view(), sm));
                        if prog {
                            lemma_moved_trans(o, m, *self, src@, base, b);
                            crate::rank::lemma_rank_trans(b, self.view(), sm, o.view());
                        } else {
                            assert(m == o);
                        }
                        assert(moved(o, *self, src@, base, b));
                        assert(o.steps@ < self.steps@);
                        assert(crate::rank::rank_lt(b, self.view(), o.view()));
                    }
                    prog = true;
                    budget = budget - 1;
                    if budget == 0 {
                        return None;
                    }
                },
                Res::Ok(PcOut::Code(h, lens), p) => {
                    self.pos = p;
                    self.pc.reset();
                    if g == 0 {
                        self.lit.push(h);
                        self.litl = Ghost(self.litl@.push(lens@));
                    } else if g == 1 {
                        self.cmd.push(h);
                        self.cmdl = Ghost(self.cmdl@.push(lens@));
                    } else {
                        self.dst.push(h);
                        self.dstl = Ghost(self.dstl@.push(lens@));
                    }
                    self.steps = Ghost(self.steps@ + 1);
                    proof {
                        assert(spec::step(b, sm) == Step::Next(self.view()));
                        lemma_run_extend(b, spec::init(), m.steps@, sm);
                        assert(m.out@.is_prefix_of(self.out@));
                        if g == 0 {
                            lemma_codes_push(m.lit@, m.litl@, h, lens@, 256);
                        } else if g == 1 {
                            lemma_codes_push(m.cmd@, m.cmdl@, h, lens@, 704);
                        } else {
                            assert(alpha == spec::dist_alpha(self.npostfix as int, self.ndirect as int));
                            lemma_codes_push(m.dst@, m.dstl@, h, lens@, alpha as int);
                        }
                        assert(self.wf());
                        assert(moved(m, *self, src@, base, b));
                        assert(crate::rank::rank_lt(b, self.view(), sm));
                        if prog {
                            lemma_moved_trans(o, m, *self, src@, base, b);
                            crate::rank::lemma_rank_trans(b, self.view(), sm, o.view());
                        } else {
                            assert(m == o);
                        }
                        assert(moved(o, *self, src@, base, b));
                        assert(o.steps@ < self.steps@);
                        assert(crate::rank::rank_lt(b, self.view(), o.view()));
                    }
                    return None;
                },
            }
        }
    }
}

/// The phase after the block type information of category `c`.
#[verifier::spinoff_prover]
fn after_cat(c: u8) -> (r: Ph)
    requires
        c < 3,
    ensures
        phase_of(r) == spec::after_cat(c as int),
        stage(r) == 14 + 4 * c || (c == 2 && r == Ph::DistParams),
        ph_ok(r),
{
    if c < 2 {
        Ph::NBlockTypes(c + 1)
    } else {
        Ph::DistParams
    }
}

/// The phase after a meta-block's data.
#[verifier::spinoff_prover]
fn after_data(mrem: u32) -> (r: Ph)
    ensures
        phase_of(r) == spec::after_data(mrem as int),
        stage(r) == 30 || r == Ph::MetaDone,
        r == Ph::MetaDone <==> mrem == 0,
        r != Ph::Metadata && r != Ph::WBits && r != Ph::Insert && r != Ph::Copy,
        ph_ok(r),
{
    if mrem == 0 {
        Ph::MetaDone
    } else {
        Ph::CmdBegin
    }
}

/// `spec::short_delta`.
#[verifier::spinoff_prover]
fn short_delta(k: u32) -> (r: i64)
    requires
        k < 6,
    ensures
        r == spec::short_delta(k as int),
        -3 <= r <= 3,
{
    if k % 2 == 0 {
        -((k / 2 + 1) as i64)
    } else {
        (k / 2 + 1) as i64
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_tables()
    ensures
        forall|i: int| 0 <= i < 11 ==> #[trigger] CELL[i] / 8 <= 2 && CELL[i] % 4 <= 2,
        forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594,
        forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118,
        forall|i: int| 4 <= i <= 24 ==> 5 <= #[trigger] NDBITS[i] <= 11,
        forall|i: int| 4 <= i <= 24 ==> #[trigger] DOFFSET[i] + pow2(NDBITS[i] as nat) * i <= 122784,
{
    assert(forall|i: int| 0 <= i < 11 ==> #[trigger] CELL[i] / 8 <= 2 && CELL[i] % 4 <= 2) by (compute);
    assert(forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594) by (compute);
    assert(forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118) by (compute);
    assert(forall|i: int| 4 <= i <= 24 ==> 5 <= #[trigger] NDBITS[i] <= 11) by (compute);
    lemma2_to64();
    assert(forall|i: int| 4 <= i <= 24 ==> #[trigger] DOFFSET[i] + pow2(NDBITS[i] as nat) * i <= 122784) by {
        assert forall|i: int| 4 <= i <= 24 implies #[trigger] DOFFSET[i] + pow2(NDBITS[i] as nat) * i <= 122784 by {
            assert(NDBITS[i] <= 11);
            assert(4 <= i <= 24);
            if i == 4 { assert(DOFFSET[4] + pow2(NDBITS[4] as nat) * 4 <= 122784) by (compute); }
            else if i == 5 { assert(DOFFSET[5] + pow2(NDBITS[5] as nat) * 5 <= 122784) by (compute); }
            else if i == 6 { assert(DOFFSET[6] + pow2(NDBITS[6] as nat) * 6 <= 122784) by (compute); }
            else if i == 7 { assert(DOFFSET[7] + pow2(NDBITS[7] as nat) * 7 <= 122784) by (compute); }
            else if i == 8 { assert(DOFFSET[8] + pow2(NDBITS[8] as nat) * 8 <= 122784) by (compute); }
            else if i == 9 { assert(DOFFSET[9] + pow2(NDBITS[9] as nat) * 9 <= 122784) by (compute); }
            else if i == 10 { assert(DOFFSET[10] + pow2(NDBITS[10] as nat) * 10 <= 122784) by (compute); }
            else if i == 11 { assert(DOFFSET[11] + pow2(NDBITS[11] as nat) * 11 <= 122784) by (compute); }
            else if i == 12 { assert(DOFFSET[12] + pow2(NDBITS[12] as nat) * 12 <= 122784) by (compute); }
            else if i == 13 { assert(DOFFSET[13] + pow2(NDBITS[13] as nat) * 13 <= 122784) by (compute); }
            else if i == 14 { assert(DOFFSET[14] + pow2(NDBITS[14] as nat) * 14 <= 122784) by (compute); }
            else if i == 15 { assert(DOFFSET[15] + pow2(NDBITS[15] as nat) * 15 <= 122784) by (compute); }
            else if i == 16 { assert(DOFFSET[16] + pow2(NDBITS[16] as nat) * 16 <= 122784) by (compute); }
            else if i == 17 { assert(DOFFSET[17] + pow2(NDBITS[17] as nat) * 17 <= 122784) by (compute); }
            else if i == 18 { assert(DOFFSET[18] + pow2(NDBITS[18] as nat) * 18 <= 122784) by (compute); }
            else if i == 19 { assert(DOFFSET[19] + pow2(NDBITS[19] as nat) * 19 <= 122784) by (compute); }
            else if i == 20 { assert(DOFFSET[20] + pow2(NDBITS[20] as nat) * 20 <= 122784) by (compute); }
            else if i == 21 { assert(DOFFSET[21] + pow2(NDBITS[21] as nat) * 21 <= 122784) by (compute); }
            else if i == 22 { assert(DOFFSET[22] + pow2(NDBITS[22] as nat) * 22 <= 122784) by (compute); }
            else if i == 23 { assert(DOFFSET[23] + pow2(NDBITS[23] as nat) * 23 <= 122784) by (compute); }
            else { assert(DOFFSET[24] + pow2(NDBITS[24] as nat) * 24 <= 122784) by (compute); }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub proof fn lemma_lut()
    ensures
        forall|i: int| 0 <= i < 2048 ==> #[trigger] CONTEXT_LUT[i] < 64,
{
    assert(forall|i: int| 0 <= i < 2048 ==> #[trigger] CONTEXT_LUT[i] < 64) by (compute);
}


impl Decoder {
    /// A block switch of category `c` (`spec::block_switch`), the step when
    /// the block count of `c` has run out.
    #[verifier::spinoff_prover]
    fn st_switch(&mut self, src: &[u8], base: u64, c: usize, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            stage(old(self).ph) == 30,
            old(self).ph != Ph::Copy,
            c < 3,
            spec::step(b, old(self).view()) == spec::block_switch(old(self).view(), b, c as int),
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            reveal(cat_ok);
        }
        if self.nbt[c] < 2 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        let (sym, p) = match read_sym(&self.btc[c], src, base, self.pos, Ghost(self.btcl@[c as int]), Ghost(b)) {
            Res::Ok(s, p) => (s as u32, p),
            Res::Bad => return Some(Status::Bad),
            Res::Short => return Some(Status::Short),
        };
        let (len, p2) = match read_blen(&self.bcc[c], src, base, p, Ghost(self.bccl@[c as int]), Ghost(b)) {
            Res::Ok(l, p2) => (l as u32, p2),
            Res::Bad => return Some(Status::Bad),
            Res::Short => return Some(Status::Short),
        };
        let n = self.nbt[c];
        let t0 = if sym == 0 {
            self.bt2[c]
        } else if sym == 1 {
            self.bt[c] + 1
        } else {
            sym - 2
        };
        let t = if t0 >= n { t0 - n } else { t0 };
        self.pos = p2;
        self.bt2[c] = self.bt[c];
        self.bt[c] = t;
        self.blen[c] = len;
        self.steps = Ghost(self.steps@ + 1);
        proof {
            assert(seq3(self.bt) =~= s0.bt.update(c as int, t as int));
            assert(seq3(self.bt2) =~= s0.bt2.update(c as int, s0.bt[c as int]));
            assert(seq3(self.blen) =~= s0.blen.update(c as int, len as int));
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(self.out@));
            reveal(cmd_ok);
        }
        None
    }
    /// `CmdBegin`: an insert-and-copy command.
    #[verifier::spinoff_prover]
    fn st_command(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_cur_tree(o, 1);
        }
        if self.blen[1] == 0 {
            proof {
                lemma_step_sw(b, s0, 1);
            }
            return self.st_switch(src, base, 1, Ghost(b));
        }
        let (wx, c) = peek(src, base, self.pos, Ghost(b));
        self.cmd_w(src, base, wx, c, Ghost(b)).0
    }

    /// `CmdBegin` with a block count left: reads the command at `pos`
    /// from the window `wx`. Changes nothing: on `None` the decoder after
    /// the step is `cmd_next` of what it returns (insert length, copy
    /// length, distance context, implicit distance, new position), with the
    /// rest of the window.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    #[inline(always)]
    pub fn cmd_p(h: &HCode, src: &[u8], base: u64, wx: u64, c: u64, pos: u64, mrem: u32, sure: bool, Ghost(g): Ghost<Decoder>, Ghost(b): Ghost<Seq<u8>>) -> (r: (Option<Status>, u32, u32, u32, bool, u64, u64, u64))
        requires
            sure ==> c >= 15,
            g.wf(),
            g.reached(b),
            at(src@, base, g.pos, b),
            g.ph == Ph::CmdBegin,
            g.blen[1] != 0,
            win_ok(src@, base, g.pos, wx, c, b),
            pos == g.pos,
            mrem == g.mrem,
            g.bt[1] < g.cmd@.len(),
            *h == g.cmd@[g.bt[1] as int],
        ensures
            r.0 is None || r.0 == Some(Status::Bad) || r.0 == Some(Status::Short),
            r.0 is None ==> wstep_ok(g, cmd_next(g, r.1, r.2, r.3, r.4, r.5), r.0, src@, base, b, fresh(src@, base, g.pos, c)),
            r.0 is Some ==> wstep_ok(g, g, r.0, src@, base, b, fresh(src@, base, g.pos, c)),
            r.0 is None ==> win_ok(src@, base, r.5, r.6, r.7, b),
    {
        proof {
            crate::rank::lemma_rank1(b, g);
        }
        let ghost s0 = g.view();
        let ghost o = g;
        proof {
            lemma_cur_tree(o, 1);
        }
        proof {
            assert(s0.bt[1] == o.bt[1] && s0.cmd == o.cmdl@);
            lemma_cmd_short(b, s0);
        }
        let ghost t = g.bt[1] as int;
        proof {
            assert(hcode_ok(g.cmd@[t], g.cmdl@[t]));
        }
        let (sym, p) = match sym_win(h, wx, c, pos, sure, Ghost(src@), base, Ghost(g.cmdl@[t]), Ghost(b)) {
            Res::Ok(s, p) => (s as usize, p),
            Res::Bad => return (Some(Status::Bad), 0, 0, 0, false, 0, 0, 0),
            Res::Short => return (Some(Status::Short), 0, 0, 0, false, 0, 0, 0),
        };
        let used = p - pos;
        proof {
            lemma_shr_bits(b, pos as int, c as nat, wx, used);
        }
        proof {
            lemma_cmd_lut();
            lemma_tables();
            assert(lut_ok(sym as int));
        }
        let e = get64(&CMD_LUT, sym);
        let ghost ic = spec::ins_code(sym as int);
        let ghost cc = spec::cpy_code(sym as int);
        proof {
            assert((e & 0xffff) == e % 0x10000 && ((e >> 16u64) & 0xff) == (e / 0x10000) % 0x100
                && ((e >> 24u64) & 0xffff) == (e / 0x100_0000) % 0x10000 && ((e >> 40u64) & 0xff)
                == (e / 0x100_0000_0000) % 0x100) by (bit_vector);
            assert(INS_EXTRA[ic] <= 24 && CPY_EXTRA[cc] <= 24);
            let a = (e >> 16u64) & 0xff;
            let c8 = (e >> 40u64) & 0xff;
            assert(((e >> 16u64) & 0x3f) == a) by (bit_vector)
                requires
                    a == (e >> 16u64) & 0xff,
                    a <= 24,
            ;
            assert(((e >> 40u64) & 0x3f) == c8) by (bit_vector)
                requires
                    c8 == (e >> 40u64) & 0xff,
                    c8 <= 24,
            ;
        }
        let ie = (e >> 16) & 0x3f;
        let ce = (e >> 40) & 0x3f;
        let x2 = wx >> used;
        let c2 = c - used;
        proof {
            lemma2_to64();
            lemma_pow2_le(ie as nat, 24);
            lemma_pow2_le(ce as nat, 24);
        }
        let (ix, cx, wo, co) = if ie + ce <= c2 {
            // Both fields are in the window.
            let y = x2 >> ie;
            proof {
                lemma_mask(ie);
                lemma_mask(ce);
                lemma_shr_bits(b, p as int, c2 as nat, x2, ie);
                lemma_shr_bits(b, p + ie, (c2 - ie) as nat, y, ce);
                lemma_bits_bound(b, p as int, ie as nat);
                lemma_bits_bound(b, p + ie, ce as nat);
                lemma_shr_bits(b, p as int, c2 as nat, x2, (ie + ce) as u64);
                lemma_bits_bound(b, (p + ie + ce) as int, (c2 - ie - ce) as nat);
            }
            (x2 & ((1u64 << ie) - 1), y & ((1u64 << ce) - 1), x2 >> (ie + ce), c2 - ie - ce)
        } else {
            match read_two(src, base, p, ie, ce, Ghost(b)) {
                None => return (Some(Status::Short), 0, 0, 0, false, 0, 0, 0),
                Some(x) => {
                    proof {
                        assert(bits(b, (p + ie + ce) as int, 0) == 0);
                        assert(pow2(0) == 1);
                    }
                    (x.0, x.1, 0u64, 0u64)
                },
            }
        };
        let cb = ((e >> 24) & 0xffff) as u32;
        let ilen = (e & 0xffff) + ix;
        let clen = cb as u64 + cx;
        proof {
            lemma_cmd(b, s0, sym as int, p as int, ic, cc, ix as int, cx as int);
        }
        if ilen > mrem as u64 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return (Some(Status::Bad), 0, 0, 0, false, 0, 0, 0);
        }
        let dctx = if cb > 4 { 3 } else { cb - 2 };
        let implicit = sym < 128;
        let pn = p + ie + ce;
        proof {
            let n = cmd_next(g, ilen as u32, clen as u32, dctx, implicit, pn);
            assert(seq3(n.blen) =~= s0.blen.update(1, s0.blen[1] - 1));
            assert(spec::step(b, s0) == Step::Next(n.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(n.out@)) by {
                assert(o.out@.subrange(0, o.out@.len() as int) =~= o.out@);
            }
            lemma_ring_ph(n.ring@, n.rbits, n.total, n.flushed, n.out@, o.ph, n.ph, n.mrem, n.wbits);
            assert(cmd_ok(n.ph, n.dctx, n.dr, n.ilen, n.clen, n.mrem, n.dist, n.total, n.wbits)) by {
                reveal(cmd_ok);
            }
            lemma_wf_data(o, n);
            assert(n.wf());
            assert(n.reached(b));
            assert(moved(g, n, src@, base, b));
            assert(crate::rank::rank_lt(b, n.view(), g.view()));
        }
        (None, ilen as u32, clen as u32, dctx, implicit, pn, wo, co)
    }

    #[verifier::spinoff_prover]
    #[inline(always)]
    fn cmd_w(&mut self, src: &[u8], base: u64, wx: u64, c: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: (Option<Status>, u64, u64))
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
            old(self).blen[1] != 0,
            win_ok(src@, base, old(self).pos, wx, c, b),
        ensures
            wstep_ok(*old(self), *final(self), r.0, src@, base, b, fresh(src@, base, old(self).pos, c)),
            r.0 is None ==> win_ok(src@, base, final(self).pos, r.1, r.2, b),
    {
        let ghost o = *self;
        proof {
            lemma_cur_tree(o, 1);
        }
        let t = self.bt[1] as usize;
        let r = Self::cmd_p(&self.cmd[t], src, base, wx, c, self.pos, self.mrem, false, Ghost(o), Ghost(b));
        if r.0.is_some() {
            return (r.0, 0, 0);
        }
        self.pos = r.5;
        self.blen[1] = self.blen[1] - 1;
        self.ilen = r.1;
        self.clen = r.2;
        self.dctx = r.3;
        self.implicit = r.4;
        self.ph = if r.1 > 0 { Ph::Insert } else { Ph::Dist };
        self.steps = Ghost(self.steps@ + 1);
        proof {
            let n = cmd_next(o, r.1, r.2, r.3, r.4, r.5);
            assert(self.blen =~= n.blen);
            assert(*self == n);
        }
        (None, r.6, r.7)
    }
    /// Up to `n` literals of the current block in a tight loop, with the
    /// position, output count and last two bytes in locals. Writes only
    /// the ring: returns how many literals it wrote (fewer than `n` only
    /// when the window ends), the window and position after them, and the
    /// output; the decoder after them is `fast_state`.
    #[verifier::spinoff_prover]
    #[inline(always)]
    #[verifier::rlimit(40)]
    pub fn lit_p(
        ring: &mut Vec<u8>,
        lit: &[HCode],
        litf: &[u32],
        lt: u64,
        fl: bool,
        cmap: &[u8],
        src: &[u8],
        base: u64,
        mode: usize,
        row: usize,
        n: u64,
        wx0: u64,
        c0: u64,
        pos0: u64,
        tot0: u64,
        Ghost(o): Ghost<Decoder>,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (r: (u64, u64, u64, u64, Ghost<Seq<u8>>))
        requires
            o.wf(),
            o.reached(b),
            at(src@, base, o.pos, b),
            o.ph == Ph::Insert,
            1 <= n <= o.ilen,
            n <= o.blen[0],
            n <= o.ring@.len() - (o.total - o.flushed),
            win_ok(src@, base, o.pos, wx0, c0, b),
            *old(ring) == o.ring,
            lit@ == o.lit@,
            fl ==> flat_ok(litf@, lit@, lt),
            cmap@ == o.cmap@,
            o.bt[0] < o.cmodes@.len(),
            mode == o.cmodes@[o.bt[0] as int],
            row == o.bt[0] * 64,
            pos0 == o.pos,
            tot0 == o.total,
        ensures
            r.0 <= n,
            final(ring)@.len() == old(ring)@.len(),
            r.0 == 0 ==> *final(ring) == *old(ring) && r.3 == o.pos && r.4@ == o.out@ && ((fresh(src@, base, o.pos, c0) || c0 < 15)
                ==> full(src@, base as int, b) ==> spec::step(b, o.view()) is Short),
            win_ok(src@, base, r.3, r.1, r.2, b),
            r.0 > 0 ==> ({
                let f = fast_state(o, *final(ring), r.3, r.4@, r.0 as int);
                moved(o, f, src@, base, b) && o.steps@ < f.steps@ && crate::rank::rank_lt(b, f.view(), o.view())
            }),
    {
        proof {
            lemma_cur_tree(o, 0);
            lemma_ring_basic(o);
            reveal(ring_ok);
            lemma_mask(o.rbits as u64);
            assert(1 <= o.ilen <= o.mrem) by {
                reveal(cmd_ok);
            }
            lemma_fast0(o);
            reveal(fast_ok);
        }
        let ghost t = o.bt[0] as int;
        proof {
            assert(row + 64 <= 64 * o.nbt[0]) by (nonlinear_arith)
                requires
                    t < o.nbt[0],
                    row == t * 64,
            ;
        }
        let rl = ring.len();
        let r = rl as u64;
        let mask = r - 1;
        proof {
            if tot0 >= 1 {
                lemma_and_mask((tot0 - 1) as u64, o.rbits as u64);
            }
            if tot0 >= 2 {
                lemma_and_mask((tot0 - 2) as u64, o.rbits as u64);
            }
        }
        let mut p1 = if tot0 >= 1 { verilith_core::prims::get(ring.as_slice(), ((tot0 - 1) & mask) as usize) } else { 0 };
        let mut p2 = if tot0 >= 2 { verilith_core::prims::get(ring.as_slice(), ((tot0 - 2) & mask) as usize) } else { 0 };
        let mut pos = pos0;
        let mut tot = tot0;
        let ghost mut out = o.out@;
        let ghost fr_ok = fresh(src@, base, pos, c0) || c0 < 15;
        let mut wx = wx0;
        let mut c = c0;
        let ghost mut fresh = fresh(src@, base, pos, c0);
        if c < 15 {
            let (x2, c2) = peek(src, base, pos, Ghost(b));
            wx = x2;
            c = c2;
            proof {
                fresh = true;
            }
        }
        let mut k: u64 = 0;
        let mut short = false;
        while k < n && !short
            invariant
                at(src@, base, o.pos, b),
                k <= n,
                n <= o.ilen,
                o.ilen <= o.mrem,
                o.total + o.mrem <= MAX_OUT,
                n <= o.blen[0],
                n <= o.ring@.len() - (o.total - o.flushed),
                t == o.bt[0],
                t < o.cmodes@.len(),
                mode == o.cmodes@[t],
                mode < 4,
                row == t * 64,
                row + 64 <= o.cmap@.len(),
                cmap@ == o.cmap@,
                lit@ == o.lit@,
                fl ==> flat_ok(litf@, lit@, lt),
                forall|i: int| 0 <= i < o.cmap@.len() ==> #[trigger] o.cmap@[i] < o.lit@.len(),
                forall|i: int| 0 <= i < o.lit@.len() ==> #[trigger] hcode_ok(o.lit@[i], o.litl@[i]) && o.litl@[i].len() == 256,
                o.litl@.len() == o.lit@.len(),
                r == o.ring@.len(),
                r == rl,
                rl == o.ring@.len(),
                o.ph == Ph::Insert,
                o.ilen >= 1,
                o.blen[0] != 0,
                r > 0,
                mask == r - 1,
                mask == lowmask(o.rbits as u64),
                r == pow2(o.rbits as nat),
                o.rbits < 64,
                fast_ok(b, o, *ring, pos, out, k as int),
                at(src@, base, pos, b),
                o.pos <= pos,
                o.out@.is_prefix_of(out),
                out.len() == o.total + k,
                ring@.len() == r,
                tot == o.total + k,
                p1 == spec::p1(out),
                p2 == spec::p2(out),
                short && k == 0 && fr_ok ==> (full(src@, base as int, b) ==> spec::step(b, o.view()) is Short),
                k == 0 ==> *ring == o.ring && pos == o.pos && out == o.out@,
                k == 0 ==> fresh || !fr_ok,
                c <= 56,
                wx as nat == bits(b, pos as int, c as nat),
                wx < pow2(c as nat),
                pos + c <= lim(src@, base as int),
                fresh ==> (c == 56 || pos + c == lim(src@, base as int)),
            decreases n - k, (if short { 0int } else { 1int }),
        {
            if c < 15 {
                let (x2, c2) = peek(src, base, pos, Ghost(b));
                wx = x2;
                c = c2;
                proof {
                    fresh = true;
                }
            }
            let ctx = lit_ctx(mode, p1, p2);
            let tree = verilith_core::prims::get(cmap, row + ctx) as usize;
            proof {
                assert(tree as int == o.cmap@[row + ctx]);
                assert(tree < o.lit@.len());
                assert(hcode_ok(o.lit@[tree as int], o.litl@[tree as int]));
                if fl {
                    reveal(flat_ok);
                    assert(flat_at(litf@, tree as int, lt, lit@[tree as int]));
                }
                assert(o.litl@[tree as int].len() == 256);
            }
            match sym_winf(code_at(lit, tree), litf, tree, lt, fl, wx, c, pos, false, Ghost(src@), base, Ghost(o.litl@[tree as int]), Ghost(b)) {
                Res::Ok(xs, p) => {
                    let x = xs as u8;
                    proof {
                        lemma_ring_idx(tot, o.rbits, r);
                        assert((tot & mask) < r);
                        assert(r as int == ring@.len());
                        assert((tot & mask) as int == tot as int % r as int);
                    }
                    let i = (tot & mask) as usize;
                    assert(i as int == (tot & mask) as int);
                    assert(i as int == (o.total + k) % ring@.len() as int);
                    assert(xs < 256);
                    let ghost ring0 = *ring;
                    verilith_core::prims::store_at(ring, i, x);
                    proof {
                        assert(ring@ == ring0@.update((o.total + k) % ring0@.len() as int, xs as u8));
                        lemma_fast_next(b, o, ring0, *ring, pos, p, out, k as int, ctx as int, tree as int, xs);
                        lemma_prefix_trans(o.out@, out, out.push(x));
                        out = out.push(x);
                    }
                    let used = p - pos;
                    proof {
                        lemma_shr_bits(b, pos as int, c as nat, wx, used);
                        lemma_bits_bound(b, p as int, (c - used) as nat);
                    }
                    wx = wx >> used;
                    c = c - used;
                    proof {
                        fresh = false;
                    }
                    pos = p;
                    tot = tot + 1;
                    p2 = p1;
                    p1 = x;
                    k = k + 1;
                },
                _ => {
                    proof {
                        if k == 0 && fresh {
                            lemma_fast_short(b, o, ctx as int, tree as int);
                        }
                    }
                    short = true;
                },
            }
        }
        proof {
            if k > 0 {
                let fin = fast_state(o, *ring, pos, out, k as int);
                reveal(fast_ok);
                assert(verilith_core::bits::nbits(b) >= lim(src@, base as int));
                crate::rank::lemma_rank_bytes(b, o.view(), fin.view());
            }
        }
        (k, wx, c, pos, Ghost(out))
    }

    /// `lit_p` on the decoder itself.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn lit_fast(&mut self, src: &[u8], base: u64, n: u64, wx0: u64, c0: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: (u64, u64, u64))
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Insert,
            1 <= n <= old(self).ilen,
            n <= old(self).blen[0],
            n <= old(self).ring@.len() - (old(self).total - old(self).flushed),
            win_ok(src@, base, old(self).pos, wx0, c0, b),
        ensures
            r.0 <= n,
            r.0 == 0 ==> *final(self) == *old(self) && ((fresh(src@, base, old(self).pos, c0) || c0 < 15) ==> full(src@, base as int, b) ==> spec::step(b, old(self).view()) is Short),
            win_ok(src@, base, final(self).pos, r.1, r.2, b),
            r.0 > 0 ==> moved(*old(self), *final(self), src@, base, b) && old(self).steps@ < final(self).steps@
                && crate::rank::rank_lt(b, final(self).view(), old(self).view()),
    {
        let ghost o = *self;
        proof {
            lemma_cur_tree(o, 0);
            lemma_ring_basic(o);
            assert(1 <= o.ilen <= o.mrem) by {
                reveal(cmd_ok);
            }
        }
        let t = self.bt[0] as usize;
        let mode = self.cmodes[t] as usize;
        let row = t * 64;
        let r = Self::lit_p(
            &mut self.ring,
            self.lit.as_slice(),
            self.litf.as_slice(),
            self.litt,
            self.litf.len() != 0,
            self.cmap.as_slice(),
            src,
            base,
            mode,
            row,
            n,
            wx0,
            c0,
            self.pos,
            self.total,
            Ghost(o),
            Ghost(b),
        );
        let k = r.0;
        if k == 0 {
            proof {
                assert(*self == o);
            }
            return (0, r.1, r.2);
        }
        let ghost fin = fast_state(o, self.ring, r.3, r.4@, k as int);
        self.pos = r.3;
        self.total = self.total + k;
        self.blen[0] = self.blen[0] - k as u32;
        self.ilen = self.ilen - k as u32;
        self.mrem = self.mrem - k as u32;
        if self.ilen == 0 {
            self.ph = if self.mrem == 0 { Ph::MetaDone } else { Ph::Dist };
        }
        self.out = r.4;
        self.steps = Ghost(o.steps@ + k as nat);
        proof {
            assert(self.blen =~= fin.blen);
            assert(*self == fin);
        }
        (k, r.1, r.2)
    }

    /// `Insert`: one literal.
    #[verifier::spinoff_prover]
    fn st_literal(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Insert,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        if self.blen[0] == 0 {
            proof {
                lemma_step_sw(b, s0, 0);
            }
            return self.st_switch(src, base, 0, Ghost(b));
        }
        if self.room() == 0 {
            proof {
                reveal(cmd_ok);
                lemma_ring_big(*self);
            }
            return Some(Status::Full);
        }
        proof {
            lemma_ring_basic(o);
        }
        let mut n = self.ilen as u64;
        if (self.blen[0] as u64) < n {
            n = self.blen[0] as u64;
        }
        let room = self.room();
        if room < n {
            n = room;
        }
        if n >= 2 {
            let (wx, c) = peek(src, base, self.pos, Ghost(b));
            if self.lit_fast(src, base, n, wx, c, Ghost(b)).0 == 0 {
                return Some(Status::Short);
            }
            return None;
        }
        let p1 = if self.total >= 1 { self.back(1) } else { 0 };
        let p2 = if self.total >= 2 { self.back(2) } else { 0 };
        if self.lit_one(src, base, p1, p2, Ghost(b)).is_none() {
            return Some(Status::Short);
        }
        None
    }

    /// One literal.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn lit_one(&mut self, src: &[u8], base: u64, p1: u8, p2: u8, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<u8>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Insert,
            old(self).blen[0] != 0,
            old(self).ring@.len() - (old(self).total - old(self).flushed) > 0,
            p1 == spec::p1(old(self).out@),
            p2 == spec::p2(old(self).out@),
        ensures
            r matches Some(x) ==> moved(*old(self), *final(self), src@, base, b) && final(self).mrem < old(self).mrem
                && final(self).out@ == old(self).out@.push(x)
                && crate::rank::rank_lt(b, final(self).view(), old(self).view()),
            r is None ==> *final(self) == *old(self) && (full(src@, base as int, b) ==> spec::step(b, old(self).view()) is Short),
    {
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_cur_tree(o, 0);
            crate::rank::lemma_rank1(b, o);
            lemma_ring_basic(o);
            assert(1 <= o.ilen <= o.mrem) by {
                reveal(cmd_ok);
            }
        }
        let t = self.bt[0] as usize;
        let mode = self.cmodes[t] as usize;
        proof {
            assert(p1 == spec::p1(s0.out));
            assert(p2 == spec::p2(s0.out));
            assert(s0.bt[0] == t && s0.cmodes == o.cmodes@ && s0.cmap == o.cmap@ && s0.lit == o.litl@);
        }
        let ctx = lit_ctx(mode, p1, p2);
        proof {
            assert(t * 64 + ctx < 64 * o.nbt[0]) by (nonlinear_arith)
                requires
                    t < o.nbt[0],
                    ctx < 64,
            ;
        }
        let tree = verilith_core::prims::get(self.cmap.as_slice(), t * 64 + ctx) as usize;
        proof {
            assert(hcode_ok(self.lit@[tree as int], self.litl@[tree as int]));
            lemma_lit(b, s0, tree as int);
        }
        let (x, p) = match read_sym(&self.lit[tree], src, base, self.pos, Ghost(self.litl@[tree as int]), Ghost(b)) {
            Res::Ok(x, p) => (x as u8, p),
            Res::Bad => return None,
            Res::Short => return None,
        };
        self.pos = p;
        self.put(x);
        self.blen[0] = self.blen[0] - 1;
        self.ilen = self.ilen - 1;
        self.mrem = self.mrem - 1;
        if self.ilen == 0 {
            self.ph = if self.mrem == 0 { Ph::MetaDone } else { Ph::Dist };
        }
        self.steps = Ghost(self.steps@ + 1);
        proof {
            assert(seq3(self.blen) =~= s0.blen.update(0, s0.blen[0] - 1));
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(self.out@));
            lemma_ring_ph(self.ring@, self.rbits, self.total, self.flushed, self.out@, o.ph, self.ph, self.mrem, self.wbits);
            assert(cmd_ok(self.ph, self.dctx, self.dr, self.ilen, self.clen, self.mrem, self.dist, self.total, self.wbits)) by {
                reveal(cmd_ok);
            }
            lemma_wf_data(o, *self);
        }
        Some(x)
    }

    /// Whole commands in a tight loop: command, literals, distance and
    /// copy, with the bit window and everything a command changes in
    /// locals, and the tables borrowed once. It stops, with the decoder
    /// at the last step it finished, at anything out of the ordinary: a
    /// block count that ran out, the end of the window or of the
    /// meta-block, a dictionary word, a copy or literals that do not fit
    /// the ring without wrapping, or a malformed stream. `step` then takes
    /// that one. Returns whether it took any step.
    #[verifier::spinoff_prover]
    #[verifier::loop_isolation(false)]
    #[verifier::rlimit(250)]
    // Compiled twice, once for each value of `fl` (see `fast_loop` and
    // `fast_loop_f`), so that the choice of lookup costs nothing per symbol.
    #[inline(always)]
    fn fast_loop_g(&mut self, fl: bool, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (prog: bool)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
            fl ==> old(self).litf@.len() != 0 && old(self).dstf@.len() != 0,
        ensures
            moved(*old(self), *final(self), src@, base, b),
            !prog ==> *final(self) == *old(self),
            prog ==> old(self).steps@ < final(self).steps@ && crate::rank::rank_lt(b, final(self).view(), old(self).view()),
    {
        let ghost o = *self;
        proof {
            assert(o.out@.is_prefix_of(o.out@)) by {
                assert(o.out@.subrange(0, o.out@.len() as int) =~= o.out@);
            }
            lemma_cur_tree(o, 1);
            lemma_cur_tree(o, 0);
            lemma_data_facts(o);
            lemma_ring_basic(o);
            reveal(ring_ok);
            lemma2_to64();
            lemma_pow2_le(o.wbits as nat, 24);
            lemma_pow2_le(10, o.wbits as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, o.wbits as u64);
            lemma_mask(o.rbits as u64);
        }
        let rl = self.ring.len();
        if rl == 0 {
            return false;
        }
        let r = rl as u64;
        let mask = r - 1;
        let flushed = self.flushed;
        let win = (1u64 << self.wbits) - 16;
        let np = self.npostfix;
        let ghost nd = self.ndirect;
        let dtab: &[u64] = self.dtab.as_slice();
        let t0 = self.bt[0] as usize;
        let t1 = self.bt[1] as usize;
        let t2 = self.bt[2] as usize;
        let mode = self.cmodes[t0] as usize;
        let row = t0 * 64;
        let mut pos = self.pos;
        let mut tot = self.total;
        let mut mrem = self.mrem;
        let mut bl0 = self.blen[0];
        let mut bl1 = self.blen[1];
        let bl1s = bl1;
        let mut bl2 = self.blen[2];
        let mut drb = self.dr;
        let mut di: usize = 0;
        let mut ilen = self.ilen;
        let mut clen = self.clen;
        let mut dctx = self.dctx;
        let mut implicit = self.implicit;
        let mut dist = self.dist;
        let mut ph = Ph::CmdBegin;
        let (x0, c0) = peek(src, base, pos, Ghost(b));
        let mut wx = x0;
        let mut c = c0;
        let ghost mut prog = false;
        let ghost mut g = o;
        let cmd_h: &HCode = &self.cmd[t1];
        let lit: &[HCode] = self.lit.as_slice();
        let litf: &[u32] = self.litf.as_slice();
        let lt = self.litt;
        let dstf: &[u32] = self.dstf.as_slice();
        let dt = self.dstt;
        let ghost flit = fl ==> flat_ok(litf@, lit@, lt);
        let ghost fdst = fl ==> flat_ok(dstf@, self.dst@, dt);
        assert(flit && fdst);
        let dst: &[HCode] = self.dst.as_slice();
        let cmap: &[u8] = self.cmap.as_slice();
        let dmap: &[u8] = self.dmap.as_slice();
        let ring: &mut Vec<u8> = &mut self.ring;
        // Scratch space for transformed dictionary words.
        let mut sw: Vec<u8> = Vec::with_capacity(64);
        let mut sm: Vec<u8> = Vec::with_capacity(64);
        proof {
            assert(g.blen =~= [bl0, bl1, bl2]);
        }
        loop
            invariant
                g.wf(),
                g.reached(b),
                moved(o, g, src@, base, b),
                hot(g, o),
                *ring == g.ring,
                ring@.len() == rl,
                pos == g.pos,
                tot == g.total,
                mrem == g.mrem,
                g.blen[0] == bl0 && g.blen[1] == bl1 && g.blen[2] == bl2,
                dr_ring(drb, di, g.dr),
                ilen == g.ilen,
                clen == g.clen,
                dctx == g.dctx,
                implicit == g.implicit,
                dist == g.dist,
                ph == g.ph,
                win_ok(src@, base, pos, wx, c, b),
                bl1 <= bl1s,
                prog == (bl1 < bl1s),
                !prog ==> g == o,
                prog ==> o.steps@ < g.steps@ && crate::rank::rank_lt(b, g.view(), o.view()),
            decreases mrem,
        {
            match ph {
                Ph::CmdBegin => {},
                _ => {
                    break;
                },
            }
            if bl1 == 0 {
                break;
            }
            if c < 39 {
                let (x2, c2) = peek(src, base, pos, Ghost(b));
                wx = x2;
                c = c2;
                // Less than a symbol's worth: the end of the input.
                if c < 15 {
                    break;
                }
            }
            // The command.
            let rc = Self::cmd_p(cmd_h, src, base, wx, c, pos, mrem, true, Ghost(g), Ghost(b));
            if rc.0.is_some() {
                break;
            }
            proof {
                let g1 = cmd_next(g, rc.1, rc.2, rc.3, rc.4, rc.5);
                lemma_adv(o, g, g1, prog, src@, base, b);
                g = g1;
            }
            pos = rc.5;
            wx = rc.6;
            c = rc.7;
            bl1 = bl1 - 1;
            ilen = rc.1;
            clen = rc.2;
            dctx = rc.3;
            implicit = rc.4;
            proof {
                prog = true;
            }
            if ilen > 0 {
                // The literals.
                proof {
                    lemma_ring_basic(g);
                    reveal(cmd_ok);
                }
                let room = r - (tot - flushed);
                if (bl0 as u64) < ilen as u64 || room < ilen as u64 {
                    ph = Ph::Insert;
                    break;
                }
                let rl2 = Self::lit_p(ring, lit, litf, lt, fl, cmap, src, base, mode, row, ilen as u64, wx, c, pos, tot, Ghost(g), Ghost(b));
                let k = rl2.0;
                wx = rl2.1;
                c = rl2.2;
                if k > 0 {
                    proof {
                        let g1 = fast_state(g, *ring, rl2.3, rl2.4@, k as int);
                        lemma_adv(o, g, g1, prog, src@, base, b);
                        g = g1;
                    }
                    pos = rl2.3;
                    tot = tot + k;
                    bl0 = bl0 - k as u32;
                    ilen = ilen - k as u32;
                    mrem = mrem - k as u32;
                }
                if ilen > 0 {
                    ph = Ph::Insert;
                    break;
                }
                if mrem == 0 {
                    ph = Ph::MetaDone;
                    break;
                }
            }
            // The distance.
            if !implicit && bl2 == 0 {
                ph = Ph::Dist;
                break;
            }
            // A distance symbol is at most 15 bits; its extra bits are read
            // from the input when the window is short of them.
            if c < 24 && !implicit {
                let (x2, c2) = peek(src, base, pos, Ghost(b));
                wx = x2;
                c = c2;
                if c < 15 {
                    ph = Ph::Dist;
                    break;
                }
            }
            proof {
                lemma_dist_facts(g);
            }
            let rd = Self::dist_rd(dst, dstf, dt, fl, dmap, src, base, wx, c, pos, bl2, t2, dctx as usize, implicit, &drb, di, np, Ghost(nd), dtab, true, Ghost(g), Ghost(b));
            if rd.0.is_some() {
                ph = Ph::Dist;
                break;
            }
            let d = rd.1;
            let maxd = if tot < win { tot } else { win };
            proof {
                lemma_ring_basic(g);
                assert(maxd == spec::max_distance(g.total as int, g.wbits as int));
            }
            if d > maxd {
                // A dictionary word.
                let rw = Self::dict_p(ring, &mut sw, &mut sm, d, maxd, rd.2, rd.3, rd.4, clen, mrem, tot, r, flushed, Ghost(g), Ghost(src@), base, Ghost(b));
                if !rw.0 {
                    ph = Ph::Dist;
                    break;
                }
                proof {
                    let g1 = rw.2@;
                    assert(moved(g, g1, src@, base, b));
                    lemma_adv(o, g, g1, prog, src@, base, b);
                    g = g1;
                }
                pos = rd.3;
                wx = rd.5;
                c = rd.6;
                bl2 = rd.4;
                tot = tot + rw.1;
                mrem = mrem - rw.1 as u32;
                if mrem == 0 {
                    ph = Ph::MetaDone;
                    break;
                }
                continue;
            }
            if clen > mrem {
                ph = Ph::Dist;
                break;
            }
            proof {
                lemma_dist_next(g, d, rd.2, rd.3, rd.4, src@, base, b);
                let g1 = dist_next(g, d as u32, rd.2, rd.3, rd.4);
                lemma_adv(o, g, g1, prog, src@, base, b);
                g = g1;
            }
            pos = rd.3;
            wx = rd.5;
            c = rd.6;
            bl2 = rd.4;
            dist = d as u32;
            if !rd.2 {
                di = (di + 3) % 4;
                drb[di] = d as u32;
            }
            // The copy.
            let n = clen as u64;
            let rcp = Self::copy_cmd(ring, tot, d, n, r, flushed, Ghost(g), Ghost(b));
            if !rcp.0 {
                ph = Ph::Copy;
                break;
            }
            proof {
                let gn = rcp.1@;
                assert(moved(g, gn, src@, base, b));
                lemma_adv(o, g, gn, prog, src@, base, b);
                g = gn;
            }
            tot = tot + n;
            mrem = mrem - clen;
            clen = 0;
            if mrem == 0 {
                ph = Ph::MetaDone;
                break;
            }
        }
        self.pos = pos;
        self.total = tot;
        self.mrem = mrem;
        self.blen = [bl0, bl1, bl2];
        self.dr = [drb[di], drb[(di + 1) % 4], drb[(di + 2) % 4], drb[(di + 3) % 4]];
        self.ilen = ilen;
        self.clen = clen;
        self.dctx = dctx;
        self.implicit = implicit;
        self.dist = dist;
        self.ph = ph;
        self.out = Ghost(g.out@);
        self.steps = Ghost(g.steps@);
        proof {
            assert(self.blen =~= g.blen);
            assert(self.dr =~= g.dr);
            assert(*self == g);
        }
        bl1 != bl1s
    }

    /// `fast_loop_g` with each tree's own table.
    // Its own function: inlined into `run`, LLVM keeps the bit window in memory.
    #[inline(never)]
    fn fast_loop(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (prog: bool)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
        ensures
            moved(*old(self), *final(self), src@, base, b),
            !prog ==> *final(self) == *old(self),
            prog ==> old(self).steps@ < final(self).steps@ && crate::rank::rank_lt(b, final(self).view(), old(self).view()),
    {
        self.fast_loop_g(false, src, base, Ghost(b))
    }

    /// `fast_loop_g` with the side-by-side tables.
    #[inline(never)]
    fn fast_loop_f(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (prog: bool)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
            old(self).litf@.len() != 0 && old(self).dstf@.len() != 0,
        ensures
            moved(*old(self), *final(self), src@, base, b),
            !prog ==> *final(self) == *old(self),
            prog ==> old(self).steps@ < final(self).steps@ && crate::rank::rank_lt(b, final(self).view(), old(self).view()),
    {
        self.fast_loop_g(true, src, base, Ghost(b))
    }

    /// Commands: as many as `fast_loop` takes, or else one step.
    #[verifier::spinoff_prover]
    fn fast_cmds(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CmdBegin,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        let prog = if self.litf.len() != 0 && self.dstf.len() != 0 {
            self.fast_loop_f(src, base, Ghost(b))
        } else {
            self.fast_loop(src, base, Ghost(b))
        };
        if prog {
            return None;
        }
        self.step(src, base, Ghost(b))
    }

    /// `Copy`: copies bytes from `dist` back, as many as fit.
    #[verifier::spinoff_prover]
    #[verifier::loop_isolation(false)]
    #[inline(always)]
    fn st_copy(&mut self, Ghost(src): Ghost<Seq<u8>>, base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            8 * base <= old(self).pos <= lim(src, base as int),
            old(self).ph == Ph::Copy,
        ensures
            step_ok(*old(self), *final(self), r, src, base, b),
            final(self).pos == old(self).pos,
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost o = *self;
        proof {
            reveal(cmd_ok);
            reveal(ring_ok);
        }
        let room = self.room();
        if room == 0 {
            proof {
                reveal(cmd_ok);
                lemma_ring_big(*self);
            }
            return Some(Status::Full);
        }
        let mut n = self.clen as u64;
        if n > room {
            n = room;
        }
        let d = self.dist as u64;
        // Copy only as far as neither the source nor the destination wraps
        // around the ring, so the ring indices just count up.
        let r = self.ring.len() as u64;
        proof {
            lemma2_to64();
            lemma_pow2_le(10, self.wbits as nat);
            assert(1 <= d <= self.total && d <= r);
            lemma_mask(self.rbits as u64);
            lemma_and_mask((self.total - d) as u64, self.rbits as u64);
            lemma_and_mask(self.total, self.rbits as u64);
        }
        let si = ((self.total - d) & (r - 1)) as usize;
        let ti = (self.total & (r - 1)) as usize;
        if n > r - si as u64 {
            n = r - si as u64;
        }
        if n > r - ti as u64 {
            n = r - ti as u64;
        }
        let m = if n < d { n } else { d };
        if m >= 8 {
            self.copy_bulk(si, ti, m, Ghost(b));
            return None;
        }
        let mut k: u64 = 0;
        while k < n
            invariant
                si + n <= r && ti + n <= r,
                r == self.ring@.len(),
                k < n ==> (si + k) as int == (self.total - d) as int % r as int,
                k < n ==> (ti + k) as int == self.total as int % r as int,
                1 <= d <= o.total,
                d <= r,
                self.wf(),
                self.reached(b),
                k <= n,
                n <= o.clen,
                n <= room,
                room == o.ring@.len() - (o.total - o.flushed),
                self.ring@.len() == o.ring@.len(),
                self.total == o.total + k,
                self.flushed == o.flushed,
                self.pos == o.pos,
                self.clen == o.clen - k,
                self.mrem == o.mrem - k,
                self.dist == d,
                o.out@.is_prefix_of(self.out@),
                self.steps@ == o.steps@ + k,
                self.nbt == o.nbt && self.bt == o.bt && self.bt2 == o.bt2 && self.blen == o.blen,
                self.btc == o.btc && self.btcl == o.btcl && self.bcc == o.bcc && self.bccl == o.bccl,
                self.npostfix == o.npostfix && self.ndirect == o.ndirect,
                self.cmodes == o.cmodes && self.cmap == o.cmap && self.ntl == o.ntl && self.dmap == o.dmap && self.ntd == o.ntd,
                self.lit == o.lit && self.litl == o.litl && self.cmd == o.cmd && self.cmdl == o.cmdl && self.dst == o.dst && self.dstl == o.dstl,
                self.pc == o.pc && self.cm == o.cm,
                k < n ==> self.ph == Ph::Copy,
                self.ph == Ph::Copy || k == n,
                self.ph == Ph::Copy || self.ph == Ph::CmdBegin || self.ph == Ph::MetaDone,
            decreases n - k,
        {
            let ghost s1 = self.view();
            proof {
                reveal(cmd_ok);
                reveal(ring_ok);
                lemma_step_copy(b, s1);
                lemma2_to64();
                lemma_pow2_le(10, self.wbits as nat);
            }
            // Masked indices, as LLVM's vectorized version of this loop is
            // slower for the short copies that reach it.
            let x = self.back(d);
            self.put(x);
            self.clen = self.clen - 1;
            self.mrem = self.mrem - 1;
            if self.clen == 0 {
                self.ph = after_data(self.mrem);
            }
            self.steps = Ghost(self.steps@ + 1);
            k = k + 1;
            proof {
                if k < n {
                    lemma_mod_inc((self.total - 1 - d) as int, r as int);
                    lemma_mod_inc((self.total - 1) as int, r as int);
                }
                reveal(cmd_ok);
                reveal(ring_ok);
                lemma_wf_data(o, *self);
                assert(spec::step(b, s1) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), (self.steps@ - 1) as nat, s1);
                assert(o.out@.is_prefix_of(self.out@)) by {
                    assert(o.out@.is_prefix_of(s1.out));
                }
            }
        }
        proof {
            reveal(cmd_ok);
            crate::rank::lemma_rank_bytes(b, o.view(), self.view());
        }
        None
    }

    /// `Dist`: the distance of the command.
    #[verifier::spinoff_prover]
    fn st_distance(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Dist,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_dist_facts(o);
        }
        if !self.implicit {
            if self.blen[2] == 0 {
                proof {
                    lemma_step_sw(b, s0, 2);
                }
                return self.st_switch(src, base, 2, Ghost(b));
            }
        }
        let (wx, c) = peek(src, base, self.pos, Ghost(b));
        self.dist_w(src, base, wx, c, Ghost(b)).0
    }

    /// `Dist` (with a block count left unless the distance is implicit):
    /// reads the distance at `pos` from the window `wx`. Changes nothing:
    /// on `None` it returns the distance, whether it is the last distance
    /// again, the position after it, the distance block count left and the
    /// rest of the window, and the step is `spec::resolve` of those.
    #[verifier::spinoff_prover]
    #[inline(always)]
    pub fn dist_rd(
        dst: &[HCode],
        dstf: &[u32],
        dt: u64,
        fl: bool,
        dmap: &[u8],
        src: &[u8],
        base: u64,
        wx: u64,
        c: u64,
        pos: u64,
        bl2: u32,
        t: usize,
        dc: usize,
        implicit: bool,
        drb: &[u32; 4],
        di: usize,
        np: u32,
        Ghost(nd): Ghost<u32>,
        dtab: &[u64],
        sure: bool,
        Ghost(g): Ghost<Decoder>,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (r: (Option<Status>, u64, bool, u64, u32, u64, u64))
        requires
            sure ==> implicit || c >= 15,
            g.wf(),
            g.reached(b),
            at(src@, base, g.pos, b),
            g.ph == Ph::Dist,
            g.implicit || g.blen[2] != 0,
            win_ok(src@, base, g.pos, wx, c, b),
            dst@ == g.dst@,
            fl ==> flat_ok(dstf@, dst@, dt),
            dmap@ == g.dmap@,
            pos == g.pos,
            bl2 == g.blen[2],
            t == g.bt[2],
            dc == g.dctx,
            implicit == g.implicit,
            dr_ring(*drb, di, g.dr),
            np == g.npostfix,
            nd == g.ndirect,
            dtab_ok(dtab@, np, nd),
        ensures
            r.0 is None || r.0 == Some(Status::Bad) || r.0 == Some(Status::Short),
            r.0 is Some ==> wstep_ok(g, g, r.0, src@, base, b, fresh(src@, base, g.pos, c)),
            r.0 is None ==> {
                &&& 1 <= r.1 < 0x8000_0000
                &&& g.pos <= r.3 <= lim(src@, base as int)
                &&& r.4 <= g.blen[2]
                &&& spec::step(b, g.view()) == spec::resolve(
                    St { pos: r.3 as int, blen: seq3(g.blen).update(2, r.4 as int), ..g.view() },
                    r.1 as int,
                    r.2,
                )
                &&& win_ok(src@, base, r.3, r.5, r.6, b)
            },
    {
        let ghost s0 = g.view();
        let ghost o = g;
        proof {
            lemma_dist_facts(o);
        }
        if implicit {
            proof {
                lemma_dist_implicit(b, s0);
                assert(seq3(o.blen).update(2, o.blen[2] as int) =~= seq3(o.blen));
                assert(St { pos: o.pos as int, blen: seq3(o.blen).update(2, o.blen[2] as int), ..s0 } == s0);
            }
            return (None, drb[di] as u64, true, pos, bl2, wx, c);
        }
        proof {
            assert(t * 4 + dc < 4 * o.nbt[2]) by (nonlinear_arith)
                requires
                    t < o.nbt[2],
                    dc < 4,
            ;
            assert(s0.bt[2] == t && s0.dctx == dc && s0.dmap == o.dmap@ && s0.dst == o.dstl@);
        }
        let tree = verilith_core::prims::get(dmap, t * 4 + dc) as usize;
        proof {
            lemma_dist(b, s0, tree as int);
            assert(hcode_ok(g.dst@[tree as int], g.dstl@[tree as int]));
            if fl {
                reveal(flat_ok);
                assert(flat_at(dstf@, tree as int, dt, dst@[tree as int]));
            }
        }
        let (dcode, p) = match sym_winf(code_at(dst, tree), dstf, tree, dt, fl, wx, c, pos, sure, Ghost(src@), base, Ghost(g.dstl@[tree as int]), Ghost(b)) {
            Res::Ok(s, p) => (s as u32, p),
            Res::Bad => return (Some(Status::Bad), 0, false, 0, 0, 0, 0),
            Res::Short => return (Some(Status::Short), 0, false, 0, 0, 0, 0),
        };
        let used = p - pos;
        proof {
            lemma_shr_bits(b, pos as int, c as nat, wx, used);
        }
        proof {
            lemma_dist_code(b, s0, tree as int, dcode as int, p as int);
        }
        let blen2 = bl2 - 1;
        if dcode < 16 {
            let dr = [drb[di], drb[(di + 1) % 4], drb[(di + 2) % 4], drb[(di + 3) % 4]];
            proof {
                assert(dr =~= g.dr);
            }
            let d = short_dist(dcode, dr);
            if d <= 0 {
                proof {
                    lemma_rejects(b, o.steps@, s0);
                }
                return (Some(Status::Bad), 0, false, 0, 0, 0, 0);
            }
            proof {
                lemma_shr_bits(b, o.pos as int, c as nat, wx, used);
                lemma_bits_bound(b, p as int, (c - used) as nat);
            }
            return (None, d as u64, dcode == 0, p, blen2, wx >> used, c - used);
        } else {
            proof {
                reveal(dtab_ok);
            }
            let ent = get64(dtab, dcode as usize);
            proof {
                assert(ent == dt_ent(dcode as int, np as int, nd as int));
                assert(dt_fits(dcode as int, np as int, nd as int));
            }
            let nb = ent & 0xff;
            let dbase = ent >> 8;
            let x2 = wx >> used;
            let c2 = c - used;
            proof {
                lemma_dt_ent(dcode as int, np, nd, ent);
                lemma_shr_bits(b, o.pos as int, c as nat, wx, used);
                lemma_bits_bound(b, p as int, (c - used) as nat);
            }
            let (e, wo, co) = if nb <= c2 {
                // The extra bits are in the window.
                proof {
                    lemma_mask(nb);
                    lemma_shr_bits(b, p as int, c2 as nat, x2, nb);
                    lemma_bits_bound(b, p as int, nb as nat);
                    lemma_bits_bound(b, (p + nb) as int, (c2 - nb) as nat);
                }
                (x2 & ((1u64 << nb) - 1), x2 >> nb, c2 - nb)
            } else {
                match read_bits(src, base, p, nb, Ghost(b)) {
                    None => return (Some(Status::Short), 0, false, 0, 0, 0, 0),
                    Some(e) => {
                        proof {
                            assert(bits(b, (p + nb) as int, 0) == 0);
                            assert(pow2(0) == 1) by { vstd::arithmetic::power2::lemma2_to64(); }
                        }
                        (e, 0u64, 0u64)
                    },
                }
            };
            proof {
                lemma2_to64();
                lemma_pow2_le(np as nat, 3);
                lemma_pow2_le(nb as nat, 24);
                if dcode < 16 + nd {
                    assert(nb == 0 && e == 0);
                }
                assert(e < pow2(nb as nat));
                assert(e * pow2(np as nat) <= 0x100_0000 * 8) by (nonlinear_arith)
                    requires
                        e <= 0x100_0000,
                        pow2(np as nat) <= 8,
                ;
                vstd::bits::lemma_u64_shl_is_mul(e, np as u64);
                if dcode < 16 + nd {
                    assert(nb == 0 && e == 0);
                } else {
                    lemma_dist_far(b, s0, tree as int, dcode as int, p as int, e as int);
                    lemma_dist_value_lin(dcode as int, e as int, np as int, nd as int);
                }
            }
            let d = (e << np) + dbase;
            proof {
                assert(1 <= d < 0x8000_0000);
                assert(g.pos <= p + nb <= lim(src@, base as int));
                assert(blen2 <= g.blen[2]);
                assert(win_ok(src@, base, (p + nb) as u64, wo, co, b));
                assert(spec::step(b, g.view()) == spec::resolve(
                    St { pos: (p + nb) as int, blen: seq3(g.blen).update(2, blen2 as int), ..g.view() },
                    d as int,
                    false,
                ));
            }
            return (None, d, false, p + nb, blen2, wo, co);
        }
    }

    #[verifier::spinoff_prover]
    #[inline(always)]
    fn dist_w(&mut self, src: &[u8], base: u64, wx: u64, c: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: (Option<Status>, u64, u64))
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::Dist,
            old(self).implicit || old(self).blen[2] != 0,
            win_ok(src@, base, old(self).pos, wx, c, b),
        ensures
            wstep_ok(*old(self), *final(self), r.0, src@, base, b, fresh(src@, base, old(self).pos, c)),
            r.0 is None ==> win_ok(src@, base, final(self).pos, r.1, r.2, b),
    {
        let ghost o = *self;
        proof {
            lemma_dist_facts(o);
        }
        let r = Self::dist_rd(
            self.dst.as_slice(),
            self.dstf.as_slice(),
            self.dstt,
            self.dstf.len() != 0,
            self.dmap.as_slice(),
            src,
            base,
            wx,
            c,
            self.pos,
            self.blen[2],
            self.bt[2] as usize,
            self.dctx as usize,
            self.implicit,
            &self.dr,
            0,
            self.npostfix,
            Ghost(self.ndirect),
            self.dtab.as_slice(),
            false,
            Ghost(o),
            Ghost(b),
        );
        if r.0.is_some() {
            return (r.0, 0, 0);
        }
        let rr = self.resolve(r.1, r.2, r.3, r.4, Ghost(src@), base, Ghost(b));
        (rr, r.5, r.6)
    }

    /// `spec::resolve`: commits the distance `d` read, with the position
    /// after it `p` and the distance block count `blen2`: a backward copy,
    /// or a dictionary word, which goes out whole.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn resolve(
        &mut self,
        d: u64,
        last: bool,
        p: u64,
        blen2: u32,
        Ghost(src): Ghost<Seq<u8>>,
        base: u64,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            old(self).ph == Ph::Dist,
            old(self).pos <= p <= lim(src, base as int),
            blen2 <= old(self).blen[2],
            1 <= d < 0x8000_0000,
            spec::step(b, old(self).view()) == spec::resolve(
                St { pos: p as int, blen: seq3(old(self).blen).update(2, blen2 as int), ..old(self).view() },
                d as int,
                last,
            ),
        ensures
            step_ok(*old(self), *final(self), r, src, base, b),
            r is None ==> final(self).pos == p,
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let ghost s1 = St { pos: p as int, blen: seq3(o.blen).update(2, blen2 as int), ..s0 };
        proof {
            lemma_dist_facts(o);
            lemma_ring_basic(o);
            lemma2_to64();
            lemma_pow2_le(o.wbits as nat, 24);
            lemma_pow2_le(10, o.wbits as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, o.wbits as u64);
        }
        let win = (1u64 << self.wbits) - 16;
        let maxd = if self.total < win { self.total } else { win };
        proof {
            assert(maxd == spec::max_distance(s1.out.len() as int, s1.wbits));
        }
        if d <= maxd {
            self.resolve_copy(d, last, p, blen2, Ghost(src), base, Ghost(b))
        } else {
            self.resolve_dict(d, maxd, last, p, blen2, Ghost(src), base, Ghost(b))
        }
    }

    /// `resolve` within the window: a backward copy.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn resolve_copy(
        &mut self,
        d: u64,
        last: bool,
        p: u64,
        blen2: u32,
        Ghost(src): Ghost<Seq<u8>>,
        base: u64,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            old(self).ph == Ph::Dist,
            old(self).pos <= p <= lim(src, base as int),
            blen2 <= old(self).blen[2],
            1 <= d < 0x8000_0000,
            spec::step(b, old(self).view()) == spec::resolve(
                St { pos: p as int, blen: seq3(old(self).blen).update(2, blen2 as int), ..old(self).view() },
                d as int,
                last,
            ),
            d <= spec::max_distance(old(self).total as int, old(self).wbits as int),
        ensures
            step_ok(*old(self), *final(self), r, src, base, b),
            r is None ==> final(self).pos == p,
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let ghost s1 = St { pos: p as int, blen: seq3(o.blen).update(2, blen2 as int), ..s0 };
        proof {
            lemma_dist_facts(o);
            lemma_ring_basic(o);
            lemma2_to64();
        }
        proof {
            lemma_resolve_copy(s1, d as int, last);
        }
        if self.clen > self.mrem {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        self.pos = p;
        self.blen[2] = blen2;
        self.dist = d as u32;
        if !last {
            self.dr = [d as u32, self.dr[0], self.dr[1], self.dr[2]];
        }
        self.ph = Ph::Copy;
        self.steps = Ghost(self.steps@ + 1);
        proof {
            assert(seq3(self.blen) =~= s1.blen);
            if !last {
                assert(seq4(self.dr) =~= seq![d as int, s0.dr[0], s0.dr[1], s0.dr[2]]);
            }
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            lemma_ring_ph(self.ring@, self.rbits, self.total, self.flushed, self.out@, o.ph, self.ph, self.mrem, self.wbits);
            assert(cmd_ok(self.ph, self.dctx, self.dr, self.ilen, self.clen, self.mrem, self.dist, self.total, self.wbits)) by {
                reveal(cmd_ok);
            }
            lemma_wf_data(o, *self);
        }
        return None;
    }

    /// `resolve` past the window: a dictionary word.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn resolve_dict(
        &mut self,
        d: u64,
        maxd: u64,
        last: bool,
        p: u64,
        blen2: u32,
        Ghost(src): Ghost<Seq<u8>>,
        base: u64,
        Ghost(b): Ghost<Seq<u8>>,
    ) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            old(self).ph == Ph::Dist,
            old(self).pos <= p <= lim(src, base as int),
            blen2 <= old(self).blen[2],
            1 <= d < 0x8000_0000,
            spec::step(b, old(self).view()) == spec::resolve(
                St { pos: p as int, blen: seq3(old(self).blen).update(2, blen2 as int), ..old(self).view() },
                d as int,
                last,
            ),
            maxd == spec::max_distance(old(self).total as int, old(self).wbits as int),
            d > maxd,
        ensures
            step_ok(*old(self), *final(self), r, src, base, b),
            r is None ==> final(self).pos == p,
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        let ghost s1 = St { pos: p as int, blen: seq3(o.blen).update(2, blen2 as int), ..s0 };
        proof {
            lemma_dist_facts(o);
            lemma_ring_basic(o);
            lemma2_to64();
        }
        proof {
            lemma_resolve_dict(s1, d as int, last);
        }
        if d > 0x7FFF_FFFC || self.clen < 4 || self.clen > 24 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        let len = self.clen as usize;
        let addr = d - maxd - 1;
        proof {
            lemma_tables();
            assert(NDBITS[len as int] <= 11);
            lemma_pow2_le(NDBITS[len as int] as nat, 11);
            lemma_pow2_pos(NDBITS[len as int] as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, NDBITS[len as int] as u64);
        }
        let pn = 1u64 << (NDBITS[len] as u64);
        let idx = addr % pn;
        let tid = addr / pn;
        if tid >= 121 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        proof {
            assert(DOFFSET[len as int] + pow2(NDBITS[len as int] as nat) * len <= 122784);
            assert((idx + 1) * len <= pn * len) by (nonlinear_arith)
                requires
                    idx < pn,
            ;
        }
        let word = dict_word(len, idx as usize);
        // Transform 0, the identity, is the common one: no buffer for it.
        let mut wv: Vec<u8> = Vec::new();
        let mut mid: Vec<u8> = Vec::new();
        if tid != 0 {
            transform_into(&mut wv, &mut mid, word, tid as usize);
        }
        let w: &[u8] = if tid == 0 { word } else { wv.as_slice() };
        proof {
            if tid == 0 {
                lemma_transform0(word@);
            }
            assert(w@ =~= spec::transform(spec::dict_word(len as int, idx as int), tid as int));
        }
        let wl = w.len();
        if wl == 0 && d <= 120 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        if wl as u64 > self.mrem as u64 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        if wl as u64 > self.room() {
            proof {
                reveal(cmd_ok);
                lemma_ring_big(*self);
            }
            return Some(Status::Full);
        }
        let mut k: usize = 0;
        while k < wl
            invariant
                k <= wl == w@.len() <= 40,
                wl <= o.mrem,
                ring_ok(self.ring@, self.rbits, self.total, self.flushed, self.out@, self.ph, self.mrem, self.wbits),
                self.ph == Ph::Dist,
                *self == (Decoder { ring: self.ring, total: self.total, out: self.out, mrem: self.mrem, ..o }),
                self.mrem == o.mrem - k,
                self.total == o.total + k,
                self.ring@.len() == o.ring@.len(),
                self.ring@.len() - (self.total - self.flushed) >= wl - k,
                self.out@ == o.out@ + w@.subrange(0, k as int),
            decreases wl - k,
        {
            let x = w[k];
            self.put(x);
            self.mrem = self.mrem - 1;
            k = k + 1;
            proof {
                assert(w@.subrange(0, k as int) =~= w@.subrange(0, k - 1).push(x));
            }
        }
        self.pos = p;
        self.blen[2] = blen2;
        self.ph = after_data(self.mrem);
        self.steps = Ghost(self.steps@ + 1);
        proof {
            assert(w@.subrange(0, wl as int) =~= w@);
            assert(seq3(self.blen) =~= s1.blen);
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(self.out@));
            lemma_ring_ph(self.ring@, self.rbits, self.total, self.flushed, self.out@, o.ph, self.ph, self.mrem, self.wbits);
            assert(cmd_ok(self.ph, self.dctx, self.dr, self.ilen, self.clen, self.mrem, self.dist, self.total, self.wbits)) by {
                reveal(cmd_ok);
            }
            lemma_wf_data(o, *self);
        }
        None
    }

    /// The size of context map `w`.
    #[verifier::spinoff_prover]
    fn cm_size(&self, w: u8) -> (r: u32)
        requires
            self.wf(),
            self.ph == Ph::CMap(w),
        ensures
            r == cmap_size_of(self.nbt, w as int),
            r == spec::cmap_size(self.view(), w as int),
            r <= 16384,
    {
        proof {
            reveal(cat_ok);
        }
        if w == 0 {
            self.nbt[0] * 64
        } else {
            self.nbt[2] * 4
        }
    }

    /// `spec::cmap_finish`: the map is complete; on to the next map or the
    /// prefix codes.
    #[verifier::spinoff_prover]
    fn cm_finish(&mut self, w: u8, nt: u32, map: Vec<u8>, p: u64)
        requires
            old(self).wf(),
            old(self).ph == Ph::CMap(w),
            map@.len() == cmap_size_of(old(self).nbt, w as int),
            1 <= nt <= 256,
            forall|i: int| 0 <= i < map@.len() ==> #[trigger] map@[i] < nt,
            old(self).cm.stage != 1,
        ensures
            spec::cmap_finish(St { pos: p as int, ..old(self).view() }, w as int, nt as int, map@) == Step::Next(final(self).view()),
            final(self).wf(),
            final(self).out == old(self).out && final(self).flushed == old(self).flushed && final(self).steps == old(self).steps,
            final(self).pos == p,
    {
        proof {
            reveal(ring_ok);
            reveal(cmd_ok);
            reveal(maps_ok);
            reveal(trees_ok);
            reveal(cat_ok);
            reveal(reading_ok);
        }
        self.pos = p;
        if w == 0 {
            self.cmap = map;
            self.ntl = nt;
            self.cm = Cmx::new();
            self.ph = Ph::CMap(1);
        } else {
            self.dmap = map;
            self.ntd = nt;
            self.cm = Cmx::new();
            self.pc.reset();
            self.ph = Ph::Trees(0);
        }
        proof {
            assert(self.cm.map@.len() == 0);
            assert(ring_ok(self.ring@, self.rbits, self.total, self.flushed, self.out@, self.ph, self.mrem, self.wbits));
            assert(cat_ok(self.ph, 0, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@));
            assert(cat_ok(self.ph, 1, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@));
            assert(cat_ok(self.ph, 2, self.nbt, self.bt, self.bt2, self.blen, self.btc@, self.btcl@, self.bcc@, self.bccl@));
            assert(maps_ok(self.ph, self.npostfix, self.ndirect, self.nbt, self.cmodes@, self.cmap@, self.ntl, self.dmap@, self.ntd));
            assert(trees_ok(self.ph, self.nbt, self.ntl, self.ntd, self.npostfix, self.ndirect, self.lit@, self.litl@, self.cmd@, self.cmdl@, self.dst@, self.dstl@));
            assert(reading_ok(self.ph, self.nbt, self.npostfix, self.ndirect, self.pc, self.cm));
            assert(cmd_ok(self.ph, self.dctx, self.dr, self.ilen, self.clen, self.mrem, self.dist, self.total, self.wbits));
        }
    }

    /// `CMap(w)`, stage 0: `NTREES` and `RLEMAX`.
    #[verifier::spinoff_prover]
    fn st_cm0(&mut self, src: &[u8], base: u64, w: u8, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CMap(w),
            old(self).cm.stage == 0,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_cmap(b, s0, w as int);
            reveal(reading_ok);
        }
        let size = self.cm_size(w);
        match varlen8(src, base, self.pos, Ghost(b)) {
            Res::Bad => Some(Status::Bad),
            Res::Short => Some(Status::Short),
            Res::Ok(v, p) => {
                if v == 0 {
                    let mut map: Vec<u8> = Vec::with_capacity(size as usize);
                    let mut i: u32 = 0;
                    while i < size
                        invariant
                            i <= size,
                            map@ == Seq::new(i as nat, |j: int| 0u8),
                        decreases size - i,
                    {
                        map.push(0);
                        i = i + 1;
                        proof {
                            assert(map@ =~= Seq::new(i as nat, |j: int| 0u8));
                        }
                    }
                    self.cm_finish(w, 1, map, p);
                    self.steps = Ghost(self.steps@ + 1);
                    proof {
                        assert(spec::step(b, s0) == Step::Next(self.view()));
                        lemma_run_extend(b, spec::init(), o.steps@, s0);
                        assert(o.out@.is_prefix_of(self.out@));
                    }
                    return None;
                }
                let r = match read_bits(src, base, p, 1, Ghost(b)) {
                    None => return Some(Status::Short),
                    Some(r) => r,
                };
                if r == 0 {
                    self.pos = p + 1;
                    self.cm.rlemax = 0;
                } else {
                    let r4 = match read_bits(src, base, p + 1, 4, Ghost(b)) {
                        None => return Some(Status::Short),
                        Some(r4) => r4,
                    };
                    proof {
                        lemma2_to64();
                    }
                    self.pos = p + 5;
                    self.cm.rlemax = r4 as u32 + 1;
                }
                self.cm.stage = 1;
                self.cm.ntrees = v as u32 + 1;
                self.pc.reset();
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    reveal(cat_ok);
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
        }
    }

    /// `CMap(w)`, stage 1: the prefix code of the map's symbols.
    #[verifier::spinoff_prover]
    fn st_cm1(&mut self, src: &[u8], base: u64, w: u8, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CMap(w),
            old(self).cm.stage == 1,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_cmap(b, s0, w as int);
            reveal(reading_ok);
        }
        let cap = self.cm_size(w) as usize;
        let alpha = self.pc_alpha();
        match self.pc.step(src, base, self.pos, alpha, Ghost(b)) {
            Res::Bad => {
                proof {
                    lemma_rejects(b, o.steps@, s0);
                }
                Some(Status::Bad)
            },
            Res::Short => Some(Status::Short),
            Res::Ok(PcOut::More, p) => {
                self.pos = p;
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    reveal(cat_ok);
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
            Res::Ok(PcOut::Code(h, lens), p) => {
                self.pos = p;
                self.pc.reset();
                self.cm.code = h;
                self.cm.lens = Ghost(lens@);
                self.cm.map = Vec::with_capacity(cap);
                self.cm.stage = 2;
                self.steps = Ghost(self.steps@ + 1);
                proof {
                    reveal(ring_ok);
                    reveal(cmd_ok);
                    reveal(maps_ok);
                    reveal(trees_ok);
                    reveal(cat_ok);
                    assert(self.cm.map@ =~= Seq::<u8>::empty());
                    assert(spec::step(b, s0) == Step::Next(self.view()));
                    lemma_run_extend(b, spec::init(), o.steps@, s0);
                    assert(o.out@.is_prefix_of(self.out@));
                }
                None
            },
        }
    }

    /// `CMap(w)`, stage 2: one symbol of the map, or a run of zeros.
    #[verifier::spinoff_prover]
    fn st_cm2(&mut self, src: &[u8], base: u64, w: u8, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CMap(w),
            old(self).cm.stage == 2,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_cmap(b, s0, w as int);
            reveal(reading_ok);
        }
        let size = self.cm_size(w);
        if self.cm.map.len() as u32 >= size {
            self.cm.stage = 3;
            self.steps = Ghost(self.steps@ + 1);
            proof {
                reveal(ring_ok);
                reveal(cmd_ok);
                reveal(maps_ok);
                reveal(trees_ok);
                reveal(cat_ok);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
            }
            return None;
        }
        let (sym, p) = match read_sym(&self.cm.code, src, base, self.pos, Ghost(self.cm.lens@), Ghost(b)) {
            Res::Ok(s, p) => (s, p),
            Res::Bad => return Some(Status::Bad),
            Res::Short => return Some(Status::Short),
        };
        let rle = self.cm.rlemax as u64;
        let ghost m0 = self.cm.map@;
        if sym == 0 || sym > rle {
            let x: u8 = if sym == 0 { 0 } else { (sym - rle) as u8 };
            self.pos = p;
            self.cm.map.push(x);
            self.steps = Ghost(self.steps@ + 1);
            proof {
                reveal(ring_ok);
                reveal(cmd_ok);
                reveal(maps_ok);
                reveal(trees_ok);
                reveal(cat_ok);
                assert(spec::step(b, s0) == Step::Next(self.view()));
                lemma_run_extend(b, spec::init(), o.steps@, s0);
                assert(o.out@.is_prefix_of(self.out@));
                assert forall|i: int| 0 <= i < self.cm.map@.len() implies #[trigger] self.cm.map@[i] < self.cm.ntrees by {
                    if i < m0.len() {
                        assert(self.cm.map@[i] == m0[i]);
                    }
                }
            }
            return None;
        }
        let e = match read_bits(src, base, p, sym, Ghost(b)) {
            None => return Some(Status::Short),
            Some(e) => e,
        };
        proof {
            lemma2_to64();
            lemma_pow2_le(sym as nat, 16);
            vstd::bits::lemma_u64_shl_is_mul(1, sym);
        }
        let reps = (1u64 << sym) + e;
        if self.cm.map.len() as u64 + reps > size as u64 {
            proof {
                lemma_rejects(b, o.steps@, s0);
            }
            return Some(Status::Bad);
        }
        self.pos = p + sym;
        let mut k: u64 = 0;
        while k < reps
            invariant
                k <= reps,
                m0.len() + reps <= size,
                self.cm.map@ == m0 + Seq::new(k as nat, |i: int| 0u8),
                *self == (Decoder { cm: Cmx { map: self.cm.map, ..o.cm }, pos: (p + sym) as u64, ..o }),
            decreases reps - k,
        {
            self.cm.map.push(0);
            k = k + 1;
            proof {
                assert(self.cm.map@ =~= m0 + Seq::new(k as nat, |i: int| 0u8));
            }
        }
        self.steps = Ghost(self.steps@ + 1);
        proof {
            reveal(ring_ok);
            reveal(cmd_ok);
            reveal(maps_ok);
            reveal(trees_ok);
            reveal(cat_ok);
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(self.out@));
            assert forall|i: int| 0 <= i < self.cm.map@.len() implies #[trigger] self.cm.map@[i] < self.cm.ntrees by {
                if i < m0.len() {
                    assert(self.cm.map@[i] == m0[i]);
                }
            }
        }
        None
    }

    /// `CMap(w)`, stage 3: the `IMTF` bit, then the map is complete.
    #[verifier::spinoff_prover]
    fn st_cm3(&mut self, src: &[u8], base: u64, w: u8, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            old(self).ph == Ph::CMap(w),
            old(self).cm.stage == 3,
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        let ghost s0 = self.view();
        let ghost o = *self;
        proof {
            lemma_step_cmap(b, s0, w as int);
            reveal(reading_ok);
        }
        let size = self.cm_size(w);
        let x = match read_bits(src, base, self.pos, 1, Ghost(b)) {
            None => return Some(Status::Short),
            Some(x) => x,
        };
        let p = self.pos + 1;
        let mut map: Vec<u8> = Vec::new();
        core::mem::swap(&mut map, &mut self.cm.map);
        // The map is out of `cm`, which `cm_finish` resets.
        self.cm.stage = 2;
        let nt = self.cm.ntrees;
        proof {
            assert(map@ == o.cm.map@);
            assert(map@.len() == size) by {
                // Stage 3 follows stage 2 once the map is full.
                reveal(reading_ok);
            }
            reveal(ring_ok);
            reveal(cmd_ok);
            reveal(maps_ok);
            reveal(trees_ok);
            reveal(cat_ok);
            assert(self.cm.map@ =~= Seq::<u8>::empty());
        }
        if x == 1 {
            imtf(&mut map, nt);
        }
        let ghost pre = *self;
        self.cm_finish(w, nt, map, p);
        self.steps = Ghost(self.steps@ + 1);
        proof {
            assert(spec::cmap_finish(St { pos: p as int, ..pre.view() }, w as int, nt as int, map@)
                == spec::cmap_finish(St { pos: p as int, ..s0 }, w as int, nt as int, map@));
            assert(spec::step(b, s0) == Step::Next(self.view()));
            lemma_run_extend(b, spec::init(), o.steps@, s0);
            assert(o.out@.is_prefix_of(self.out@));
        }
        None
    }

    /// One step (or a run of steps of the same kind). `None`: continue.
    #[verifier::spinoff_prover]
    fn step(&mut self, src: &[u8], base: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<Status>)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
        ensures
            step_ok(*old(self), *final(self), r, src@, base, b),
    {
        proof {
            if !(self.ph is Done) {
                crate::rank::lemma_rank1(b, *self);
            }
        }
        match self.ph {
            Ph::WBits => self.st_wbits(src, base, Ghost(b)),
            Ph::MetaHeader => self.st_header(src, base, Ghost(b)),
            Ph::Metadata => self.st_skip(src, base, Ghost(b)),
            Ph::Uncompressed => self.st_raw(src, base, Ghost(b)),
            Ph::NBlockTypes(_) => self.st_nbt(src, base, Ghost(b)),
            Ph::BTypeCode(_) => self.st_code(src, base, Ghost(b)),
            Ph::BCountCode(_) => self.st_code(src, base, Ghost(b)),
            Ph::BCount(_) => self.st_bcount(src, base, Ghost(b)),
            Ph::DistParams => self.st_dparams(src, base, Ghost(b)),
            Ph::CModes => self.st_cmodes(src, base, Ghost(b)),
            Ph::CMap(w) => {
                proof {
                    reveal(reading_ok);
                }
                if self.cm.stage == 0 {
                    self.st_cm0(src, base, w, Ghost(b))
                } else if self.cm.stage == 1 {
                    self.st_cm1(src, base, w, Ghost(b))
                } else if self.cm.stage == 2 {
                    self.st_cm2(src, base, w, Ghost(b))
                } else {
                    self.st_cm3(src, base, w, Ghost(b))
                }
            },
            Ph::Trees(_) => self.st_trees(src, base, Ghost(b)),
            Ph::CmdBegin => self.st_command(src, base, Ghost(b)),
            Ph::Insert => self.st_literal(src, base, Ghost(b)),
            Ph::Dist => self.st_distance(src, base, Ghost(b)),
            Ph::Copy => self.st_copy(Ghost(src@), base, Ghost(b)),
            Ph::MetaDone => self.st_metadone(src, base, Ghost(b)),
            Ph::Done => Some(Status::Done),
        }
    }

    /// Runs steps until the input window ends (`Short`), the output ring
    /// is full (`Full`), the stream ends (`Done`) or is malformed (`Bad`),
    /// the output would pass `MAX_OUT` (`Limit`), or `budget` steps are
    /// done (`Yield`).
    #[verifier::spinoff_prover]
    pub fn run(&mut self, src: &[u8], base: u64, budget: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Status)
        requires
            old(self).wf(),
            old(self).reached(b),
            at(src@, base, old(self).pos, b),
            budget > 0,
        ensures
            run_ok(*old(self), *final(self), r, src@, base, b),
    {
        let ghost o = *self;
        let ghost b0 = budget;
        let mut budget = budget;
        proof {
            assert(o.out@.is_prefix_of(o.out@)) by {
                assert(o.out@.subrange(0, o.out@.len() as int) =~= o.out@);
            }
        }
        while budget > 0
            invariant
                o == *old(self),
                moved(o, *self, src@, base, b),
                at(src@, base, o.pos, b),
                budget <= b0,
                budget < b0 ==> o.steps@ < self.steps@ && crate::rank::rank_lt(b, self.view(), o.view()),
                budget == b0 ==> *self == o,
            decreases budget,
        {
            budget = budget - 1;
            let ghost m = *self;
            let st = if self.ph == Ph::CmdBegin { self.fast_cmds(src, base, Ghost(b)) } else { self.step(src, base, Ghost(b)) };
            match st {
                None => {
                    proof {
                        lemma_moved_trans(o, m, *self, src@, base, b);
                        if budget + 1 < b0 {
                            crate::rank::lemma_rank_trans(b, self.view(), m.view(), o.view());
                        }
                    }
                },
                Some(s) => {
                    proof {
                        if s is Done {
                            lemma_moved_trans(o, m, *self, src@, base, b);
                            if budget + 1 < b0 && m.ph != Ph::Done {
                                crate::rank::lemma_rank_trans(b, self.view(), m.view(), o.view());
                            }
                        } else if !(s is Bad) {
                            assert(*self == m);
                        }
                    }
                    return s;
                },
            }
        }
        Status::Yield
    }
}

/// Per command symbol (§5): the insert length base (bits 0..16) and extra
/// bits (16..24), the copy length base (24..40) and extra bits (40..48).
pub const CMD_LUT: [u64; 704] = [
    0x2000000, 0x3000000, 0x4000000, 0x5000000, 0x6000000, 0x7000000,
    0x8000000, 0x9000000, 0x2000001, 0x3000001, 0x4000001, 0x5000001,
    0x6000001, 0x7000001, 0x8000001, 0x9000001, 0x2000002, 0x3000002,
    0x4000002, 0x5000002, 0x6000002, 0x7000002, 0x8000002, 0x9000002,
    0x2000003, 0x3000003, 0x4000003, 0x5000003, 0x6000003, 0x7000003,
    0x8000003, 0x9000003, 0x2000004, 0x3000004, 0x4000004, 0x5000004,
    0x6000004, 0x7000004, 0x8000004, 0x9000004, 0x2000005, 0x3000005,
    0x4000005, 0x5000005, 0x6000005, 0x7000005, 0x8000005, 0x9000005,
    0x2010006, 0x3010006, 0x4010006, 0x5010006, 0x6010006, 0x7010006,
    0x8010006, 0x9010006, 0x2010008, 0x3010008, 0x4010008, 0x5010008,
    0x6010008, 0x7010008, 0x8010008, 0x9010008, 0x1000a000000, 0x1000c000000,
    0x2000e000000, 0x20012000000, 0x30016000000, 0x3001e000000, 0x40026000000, 0x40036000000,
    0x1000a000001, 0x1000c000001, 0x2000e000001, 0x20012000001, 0x30016000001, 0x3001e000001,
    0x40026000001, 0x40036000001, 0x1000a000002, 0x1000c000002, 0x2000e000002, 0x20012000002,
    0x30016000002, 0x3001e000002, 0x40026000002, 0x40036000002, 0x1000a000003, 0x1000c000003,
    0x2000e000003, 0x20012000003, 0x30016000003, 0x3001e000003, 0x40026000003, 0x40036000003,
    0x1000a000004, 0x1000c000004, 0x2000e000004, 0x20012000004, 0x30016000004, 0x3001e000004,
    0x40026000004, 0x40036000004, 0x1000a000005, 0x1000c000005, 0x2000e000005, 0x20012000005,
    0x30016000005, 0x3001e000005, 0x40026000005, 0x40036000005, 0x1000a010006, 0x1000c010006,
    0x2000e010006, 0x20012010006, 0x30016010006, 0x3001e010006, 0x40026010006, 0x40036010006,
    0x1000a010008, 0x1000c010008, 0x2000e010008, 0x20012010008, 0x30016010008, 0x3001e010008,
    0x40026010008, 0x40036010008, 0x2000000, 0x3000000, 0x4000000, 0x5000000,
    0x6000000, 0x7000000, 0x8000000, 0x9000000, 0x2000001, 0x3000001,
    0x4000001, 0x5000001, 0x6000001, 0x7000001, 0x8000001, 0x9000001,
    0x2000002, 0x3000002, 0x4000002, 0x5000002, 0x6000002, 0x7000002,
    0x8000002, 0x9000002, 0x2000003, 0x3000003, 0x4000003, 0x5000003,
    0x6000003, 0x7000003, 0x8000003, 0x9000003, 0x2000004, 0x3000004,
    0x4000004, 0x5000004, 0x6000004, 0x7000004, 0x8000004, 0x9000004,
    0x2000005, 0x3000005, 0x4000005, 0x5000005, 0x6000005, 0x7000005,
    0x8000005, 0x9000005, 0x2010006, 0x3010006, 0x4010006, 0x5010006,
    0x6010006, 0x7010006, 0x8010006, 0x9010006, 0x2010008, 0x3010008,
    0x4010008, 0x5010008, 0x6010008, 0x7010008, 0x8010008, 0x9010008,
    0x1000a000000, 0x1000c000000, 0x2000e000000, 0x20012000000, 0x30016000000, 0x3001e000000,
    0x40026000000, 0x40036000000, 0x1000a000001, 0x1000c000001, 0x2000e000001, 0x20012000001,
    0x30016000001, 0x3001e000001, 0x40026000001, 0x40036000001, 0x1000a000002, 0x1000c000002,
    0x2000e000002, 0x20012000002, 0x30016000002, 0x3001e000002, 0x40026000002, 0x40036000002,
    0x1000a000003, 0x1000c000003, 0x2000e000003, 0x20012000003, 0x30016000003, 0x3001e000003,
    0x40026000003, 0x40036000003, 0x1000a000004, 0x1000c000004, 0x2000e000004, 0x20012000004,
    0x30016000004, 0x3001e000004, 0x40026000004, 0x40036000004, 0x1000a000005, 0x1000c000005,
    0x2000e000005, 0x20012000005, 0x30016000005, 0x3001e000005, 0x40026000005, 0x40036000005,
    0x1000a010006, 0x1000c010006, 0x2000e010006, 0x20012010006, 0x30016010006, 0x3001e010006,
    0x40026010006, 0x40036010006, 0x1000a010008, 0x1000c010008, 0x2000e010008, 0x20012010008,
    0x30016010008, 0x3001e010008, 0x40026010008, 0x40036010008, 0x202000a, 0x302000a,
    0x402000a, 0x502000a, 0x602000a, 0x702000a, 0x802000a, 0x902000a,
    0x202000e, 0x302000e, 0x402000e, 0x502000e, 0x602000e, 0x702000e,
    0x802000e, 0x902000e, 0x2030012, 0x3030012, 0x4030012, 0x5030012,
    0x6030012, 0x7030012, 0x8030012, 0x9030012, 0x203001a, 0x303001a,
    0x403001a, 0x503001a, 0x603001a, 0x703001a, 0x803001a, 0x903001a,
    0x2040022, 0x3040022, 0x4040022, 0x5040022, 0x6040022, 0x7040022,
    0x8040022, 0x9040022, 0x2040032, 0x3040032, 0x4040032, 0x5040032,
    0x6040032, 0x7040032, 0x8040032, 0x9040032, 0x2050042, 0x3050042,
    0x4050042, 0x5050042, 0x6050042, 0x7050042, 0x8050042, 0x9050042,
    0x2050062, 0x3050062, 0x4050062, 0x5050062, 0x6050062, 0x7050062,
    0x8050062, 0x9050062, 0x1000a02000a, 0x1000c02000a, 0x2000e02000a, 0x2001202000a,
    0x3001602000a, 0x3001e02000a, 0x4002602000a, 0x4003602000a, 0x1000a02000e, 0x1000c02000e,
    0x2000e02000e, 0x2001202000e, 0x3001602000e, 0x3001e02000e, 0x4002602000e, 0x4003602000e,
    0x1000a030012, 0x1000c030012, 0x2000e030012, 0x20012030012, 0x30016030012, 0x3001e030012,
    0x40026030012, 0x40036030012, 0x1000a03001a, 0x1000c03001a, 0x2000e03001a, 0x2001203001a,
    0x3001603001a, 0x3001e03001a, 0x4002603001a, 0x4003603001a, 0x1000a040022, 0x1000c040022,
    0x2000e040022, 0x20012040022, 0x30016040022, 0x3001e040022, 0x40026040022, 0x40036040022,
    0x1000a040032, 0x1000c040032, 0x2000e040032, 0x20012040032, 0x30016040032, 0x3001e040032,
    0x40026040032, 0x40036040032, 0x1000a050042, 0x1000c050042, 0x2000e050042, 0x20012050042,
    0x30016050042, 0x3001e050042, 0x40026050042, 0x40036050042, 0x1000a050062, 0x1000c050062,
    0x2000e050062, 0x20012050062, 0x30016050062, 0x3001e050062, 0x40026050062, 0x40036050062,
    0x50046000000, 0x50066000000, 0x60086000000, 0x700c6000000, 0x80146000000, 0x90246000000,
    0xa0446000000, 0x180846000000, 0x50046000001, 0x50066000001, 0x60086000001, 0x700c6000001,
    0x80146000001, 0x90246000001, 0xa0446000001, 0x180846000001, 0x50046000002, 0x50066000002,
    0x60086000002, 0x700c6000002, 0x80146000002, 0x90246000002, 0xa0446000002, 0x180846000002,
    0x50046000003, 0x50066000003, 0x60086000003, 0x700c6000003, 0x80146000003, 0x90246000003,
    0xa0446000003, 0x180846000003, 0x50046000004, 0x50066000004, 0x60086000004, 0x700c6000004,
    0x80146000004, 0x90246000004, 0xa0446000004, 0x180846000004, 0x50046000005, 0x50066000005,
    0x60086000005, 0x700c6000005, 0x80146000005, 0x90246000005, 0xa0446000005, 0x180846000005,
    0x50046010006, 0x50066010006, 0x60086010006, 0x700c6010006, 0x80146010006, 0x90246010006,
    0xa0446010006, 0x180846010006, 0x50046010008, 0x50066010008, 0x60086010008, 0x700c6010008,
    0x80146010008, 0x90246010008, 0xa0446010008, 0x180846010008, 0x2060082, 0x3060082,
    0x4060082, 0x5060082, 0x6060082, 0x7060082, 0x8060082, 0x9060082,
    0x20700c2, 0x30700c2, 0x40700c2, 0x50700c2, 0x60700c2, 0x70700c2,
    0x80700c2, 0x90700c2, 0x2080142, 0x3080142, 0x4080142, 0x5080142,
    0x6080142, 0x7080142, 0x8080142, 0x9080142, 0x2090242, 0x3090242,
    0x4090242, 0x5090242, 0x6090242, 0x7090242, 0x8090242, 0x9090242,
    0x20a0442, 0x30a0442, 0x40a0442, 0x50a0442, 0x60a0442, 0x70a0442,
    0x80a0442, 0x90a0442, 0x20c0842, 0x30c0842, 0x40c0842, 0x50c0842,
    0x60c0842, 0x70c0842, 0x80c0842, 0x90c0842, 0x20e1842, 0x30e1842,
    0x40e1842, 0x50e1842, 0x60e1842, 0x70e1842, 0x80e1842, 0x90e1842,
    0x2185842, 0x3185842, 0x4185842, 0x5185842, 0x6185842, 0x7185842,
    0x8185842, 0x9185842, 0x5004602000a, 0x5006602000a, 0x6008602000a, 0x700c602000a,
    0x8014602000a, 0x9024602000a, 0xa044602000a, 0x18084602000a, 0x5004602000e, 0x5006602000e,
    0x6008602000e, 0x700c602000e, 0x8014602000e, 0x9024602000e, 0xa044602000e, 0x18084602000e,
    0x50046030012, 0x50066030012, 0x60086030012, 0x700c6030012, 0x80146030012, 0x90246030012,
    0xa0446030012, 0x180846030012, 0x5004603001a, 0x5006603001a, 0x6008603001a, 0x700c603001a,
    0x8014603001a, 0x9024603001a, 0xa044603001a, 0x18084603001a, 0x50046040022, 0x50066040022,
    0x60086040022, 0x700c6040022, 0x80146040022, 0x90246040022, 0xa0446040022, 0x180846040022,
    0x50046040032, 0x50066040032, 0x60086040032, 0x700c6040032, 0x80146040032, 0x90246040032,
    0xa0446040032, 0x180846040032, 0x50046050042, 0x50066050042, 0x60086050042, 0x700c6050042,
    0x80146050042, 0x90246050042, 0xa0446050042, 0x180846050042, 0x50046050062, 0x50066050062,
    0x60086050062, 0x700c6050062, 0x80146050062, 0x90246050062, 0xa0446050062, 0x180846050062,
    0x1000a060082, 0x1000c060082, 0x2000e060082, 0x20012060082, 0x30016060082, 0x3001e060082,
    0x40026060082, 0x40036060082, 0x1000a0700c2, 0x1000c0700c2, 0x2000e0700c2, 0x200120700c2,
    0x300160700c2, 0x3001e0700c2, 0x400260700c2, 0x400360700c2, 0x1000a080142, 0x1000c080142,
    0x2000e080142, 0x20012080142, 0x30016080142, 0x3001e080142, 0x40026080142, 0x40036080142,
    0x1000a090242, 0x1000c090242, 0x2000e090242, 0x20012090242, 0x30016090242, 0x3001e090242,
    0x40026090242, 0x40036090242, 0x1000a0a0442, 0x1000c0a0442, 0x2000e0a0442, 0x200120a0442,
    0x300160a0442, 0x3001e0a0442, 0x400260a0442, 0x400360a0442, 0x1000a0c0842, 0x1000c0c0842,
    0x2000e0c0842, 0x200120c0842, 0x300160c0842, 0x3001e0c0842, 0x400260c0842, 0x400360c0842,
    0x1000a0e1842, 0x1000c0e1842, 0x2000e0e1842, 0x200120e1842, 0x300160e1842, 0x3001e0e1842,
    0x400260e1842, 0x400360e1842, 0x1000a185842, 0x1000c185842, 0x2000e185842, 0x20012185842,
    0x30016185842, 0x3001e185842, 0x40026185842, 0x40036185842, 0x50046060082, 0x50066060082,
    0x60086060082, 0x700c6060082, 0x80146060082, 0x90246060082, 0xa0446060082, 0x180846060082,
    0x500460700c2, 0x500660700c2, 0x600860700c2, 0x700c60700c2, 0x801460700c2, 0x902460700c2,
    0xa04460700c2, 0x1808460700c2, 0x50046080142, 0x50066080142, 0x60086080142, 0x700c6080142,
    0x80146080142, 0x90246080142, 0xa0446080142, 0x180846080142, 0x50046090242, 0x50066090242,
    0x60086090242, 0x700c6090242, 0x80146090242, 0x90246090242, 0xa0446090242, 0x180846090242,
    0x500460a0442, 0x500660a0442, 0x600860a0442, 0x700c60a0442, 0x801460a0442, 0x902460a0442,
    0xa04460a0442, 0x1808460a0442, 0x500460c0842, 0x500660c0842, 0x600860c0842, 0x700c60c0842,
    0x801460c0842, 0x902460c0842, 0xa04460c0842, 0x1808460c0842, 0x500460e1842, 0x500660e1842,
    0x600860e1842, 0x700c60e1842, 0x801460e1842, 0x902460e1842, 0xa04460e1842, 0x1808460e1842,
    0x50046185842, 0x50066185842, 0x60086185842, 0x700c6185842, 0x80146185842, 0x90246185842,
    0xa0446185842, 0x180846185842,
];

/// `CMD_LUT` is the insert and copy lengths of every command symbol.
#[verifier::spinoff_prover]
pub proof fn lemma_cmd_lut()
    ensures
        forall|i: int| 0 <= i < 704 ==> #[trigger] lut_ok(i),
{
    assert(lut_all(0)) by (compute_only);
    assert forall|i: int| 0 <= i < 704 implies #[trigger] lut_ok(i) by {
        lemma_lut_all(0, i);
    }
}

/// `lut_ok` from `i` to the end, checked by evaluation.
pub open spec fn lut_all(i: int) -> bool
    decreases 704 - i,
{
    if i >= 704 || i < 0 {
        true
    } else {
        lut_ok(i) && lut_all(i + 1)
    }
}

proof fn lemma_lut_all(k: int, i: int)
    requires
        0 <= k <= i < 704,
        lut_all(k),
    ensures
        lut_ok(i),
    decreases i - k,
{
    if k < i {
        lemma_lut_all(k + 1, i);
    }
}

pub open spec fn lut_ok(i: int) -> bool {
    let e = CMD_LUT[i] as int;
    &&& 0 <= spec::ins_code(i) < 24 && 0 <= spec::cpy_code(i) < 24
    &&& e % 0x10000 == INS_BASE[spec::ins_code(i)] as int
    &&& (e / 0x10000) % 0x100 == INS_EXTRA[spec::ins_code(i)] as int
    &&& (e / 0x100_0000) % 0x10000 == CPY_BASE[spec::cpy_code(i)] as int
    &&& (e / 0x100_0000_0000) % 0x100 == CPY_EXTRA[spec::cpy_code(i)] as int
    &&& e < 0x1_0000_0000_0000
}

/// The literal context (§7.1) from the mode and the last two bytes.
#[verifier::spinoff_prover]
fn lit_ctx(mode: usize, p1: u8, p2: u8) -> (r: usize)
    requires
        mode < 4,
    ensures
        r == spec::lit_context(mode as int, p1, p2),
        r < 64,
{
    proof {
        lemma_lut();
    }
    let a = verilith_core::prims::get(&CONTEXT_LUT, mode * 512 + p1 as usize);
    let c2 = verilith_core::prims::get(&CONTEXT_LUT, mode * 512 + 256 + p2 as usize);
    assert(a | c2 < 64) by (bit_vector)
        requires
            a < 64 && c2 < 64,
    ;
    (a | c2) as usize
}

/// `spec::short_dist`.
#[verifier::spinoff_prover]
fn short_dist(dcode: u32, dr: [u32; 4]) -> (r: i64)
    requires
        dcode < 16,
        forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] dr[i] <= 0x7fff_fffc,
    ensures
        r == spec::short_dist(dcode as int, seq4(dr)),
{
    if dcode < 4 {
        dr[dcode as usize] as i64
    } else if dcode < 10 {
        dr[0] as i64 + short_delta(dcode - 4)
    } else {
        dr[1] as i64 + short_delta(dcode - 10)
    }
}

/// `spec::dist_extra`: the number of extra bits of distance code `dcode`.
#[verifier::spinoff_prover]
fn dist_nbits(dcode: u32, np: u32, nd: u32) -> (r: u64)
    requires
        np <= 3,
        nd <= 120,
        16 + nd <= dcode < spec::dist_alpha(np as int, nd as int),
    ensures
        r as nat == spec::dist_extra(dcode as int, np as int, nd as int),
        1 <= r <= 24,
{
    proof {
        lemma2_to64();
        lemma_pow2_le(np as nat, 3);
    }
    let x = dcode - nd - 16;
    let q = x >> (np + 1);
    proof {
        vstd::bits::lemma_u32_shr_is_div(x, (np + 1) as u32);
        assert(q == x as nat / pow2((np + 1) as nat));
        if np == 0 {
            assert(q == x / 2);
        } else if np == 1 {
            assert(q == x / 4);
        } else if np == 2 {
            assert(q == x / 8);
        } else {
            assert(q == x / 16);
        }
    }
    1 + q as u64
}

/// `spec::dist_value`: the distance of code `dcode` with extra bits `e`.
#[verifier::spinoff_prover]
fn dist_val(dcode: u32, e: u64, np: u32, nd: u32, nb: u64) -> (r: u64)
    requires
        np <= 3,
        nd <= 120,
        16 + nd <= dcode < spec::dist_alpha(np as int, nd as int),
        nb as nat == spec::dist_extra(dcode as int, np as int, nd as int),
        1 <= nb <= 24,
        e < pow2(nb as nat),
    ensures
        r == spec::dist_value(dcode as int, e as int, np as int, nd as int),
        1 <= r < 0x4000_0000,
{
    proof {
        lemma2_to64();
        lemma_pow2_le(np as nat, 3);
        lemma_pow2_le(nb as nat, 24);
        vstd::bits::lemma_u64_shl_is_mul(1, np as u64);
        vstd::bits::lemma_u64_shl_is_mul(1, nb);
    }
    let x = (dcode - nd - 16) as u64;
    let p = 1u64 << np;
    let pb = 1u64 << nb;
    let hcode = x / p;
    let lcode = x % p;
    let h2 = 2 + hcode % 2;
    proof {
        assert(h2 * pb <= 3 * 0x100_0000 && h2 * pb >= 4) by (nonlinear_arith)
            requires
                2 <= h2 <= 3,
                1 <= pb <= 0x100_0000,
                pb >= 2,
        ;
    }
    let offset = h2 * pb - 4;
    proof {
        assert((offset + e) * p <= (4 * 0x100_0000) * 8) by (nonlinear_arith)
            requires
                offset + e <= 4 * 0x100_0000,
                1 <= p <= 8,
        ;
    }
    (offset + e) * p + lcode + nd as u64 + 1
}

/// Moves `l[x]` to the front.
#[verifier::spinoff_prover]
fn move_to_front(l: &mut Vec<u8>, x: usize)
    requires
        old(l)@.len() == 256,
        x < 256,
    ensures
        final(l)@ == seq![old(l)@[x as int]] + old(l)@.remove(x as int),
        final(l)@.len() == 256,
        final(l)@[0] == old(l)@[x as int],
        forall|i: int| 1 <= i <= x ==> #[trigger] final(l)@[i] == old(l)@[i - 1],
        forall|i: int| x < i < 256 ==> #[trigger] final(l)@[i] == old(l)@[i],
{
    let ghost l0 = l@;
    let y = l[x];
    let mut j = x;
    while j > 0
        invariant
            j <= x < 256,
            l@.len() == 256,
            forall|i: int| j < i <= x ==> #[trigger] l@[i] == l0[i - 1],
            forall|i: int| 0 <= i < 256 && (i > x || i <= j) ==> #[trigger] l@[i] == l0[i],
        decreases j,
    {
        let t = l[j - 1];
        l.set(j, t);
        j = j - 1;
    }
    l.set(0, y);
    assert(l@ =~= seq![y] + l0.remove(x as int));
}

/// Inverse move-to-front (§7.3), in place. Values below `nt` stay below it.
#[verifier::spinoff_prover]
fn imtf(v: &mut Vec<u8>, nt: u32)
    requires
        1 <= nt <= 256,
        forall|i: int| 0 <= i < old(v)@.len() ==> #[trigger] old(v)@[i] < nt,
    ensures
        final(v)@ == spec::imtf(old(v)@),
        forall|i: int| 0 <= i < final(v)@.len() ==> #[trigger] final(v)@[i] < nt,
        final(v)@.len() == old(v)@.len(),
{
    let ghost orig = v@;
    let mut l: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 256
        invariant
            i <= 256,
            l@ == Seq::new(i as nat, |j: int| j as u8),
        decreases 256 - i,
    {
        l.push(i as u8);
        i = i + 1;
        proof {
            assert(l@ =~= Seq::new(i as nat, |j: int| j as u8));
        }
    }
    let n = v.len();
    let mut k: usize = 0;
    while k < n
        invariant
            n == v@.len() == orig.len(),
            k <= n,
            l@.len() == 256,
            forall|j: int| 0 <= j < nt ==> #[trigger] l@[j] < nt,
            forall|j: int| k <= j < n ==> #[trigger] v@[j] == orig[j],
            forall|j: int| 0 <= j < n ==> #[trigger] orig[j] < nt,
            1 <= nt <= 256,
            forall|j: int| 0 <= j < k ==> #[trigger] v@[j] < nt,
            v@.subrange(0, k as int) + spec::imtf_from(orig, k as int, l@) == spec::imtf(orig),
        decreases n - k,
    {
        let x = v[k] as usize;
        let y = l[x];
        let ghost l0 = l@;
        let ghost v0 = v@;
        move_to_front(&mut l, x);
        v.set(k, y);
        k = k + 1;
        proof {
            assert(x < nt);
            assert(spec::imtf_from(orig, k - 1, l0) == seq![y] + spec::imtf_from(orig, k as int, l@));
            assert(v@.subrange(0, k as int) =~= v0.subrange(0, k - 1).push(y));
            assert(v@.subrange(0, k as int) + spec::imtf_from(orig, k as int, l@)
                =~= v0.subrange(0, k - 1) + (seq![y] + spec::imtf_from(orig, k as int, l@)));
            assert forall|j: int| 0 <= j < nt implies #[trigger] l@[j] < nt by {
                if j == 0 {
                } else if j <= x {
                    assert(l@[j] == l0[j - 1]);
                } else {
                    assert(l@[j] == l0[j]);
                }
            }
        }
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
        assert(spec::imtf_from(orig, n as int, l@) =~= Seq::<u8>::empty());
    }
}

/// `&s[a..b]`.
fn slice_subrange<'a>(s: &'a [u8], a: usize, b: usize) -> (r: &'a [u8])
    requires
        a <= b <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    &s[a..b]
}

} // verus!
