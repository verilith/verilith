//! The block encoder: match finding, then entropy coding (`ent`). Only
//! memory safety is proven here; `compress` keeps a block only after the
//! verified decoder has decoded it back to its input.
use crate::ent::*;
use crate::opt::OptState;
use verilith_core::lz::{eq_len, load32};
use verilith_core::prims::load_u64_le;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Match finding strategies.
pub const FAST: u8 = 1;
pub const DFAST: u8 = 2;
pub const GREEDY: u8 = 3;
pub const LAZY: u8 = 4;
pub const LAZY2: u8 = 5;
/// The optimal parser on a binary tree (libzstd's btopt / btultra).
pub const OPT: u8 = 6;

/// The parameters of a level: window log, chain log, hash log, search
/// log, minimum match, strategy (libzstd's table for large inputs).
pub fn level_params(level: i32) -> (r: (u32, u32, u32, u32, u32, u8))
    ensures
        10 <= r.0 <= 27,
        6 <= r.1 <= 27,
        6 <= r.2 <= 25,
        r.3 <= 10,
        4 <= r.4 <= 7,
{
    if level <= 1 {
        (19, 12, 13, 1, 6, FAST)
    } else if level == 2 {
        (20, 15, 16, 1, 6, FAST)
    } else if level == 3 {
        (21, 16, 17, 1, 5, DFAST)
    } else if level == 4 {
        (21, 18, 18, 1, 5, DFAST)
    } else if level == 5 {
        (21, 18, 19, 3, 5, GREEDY)
    } else if level == 6 {
        (21, 18, 19, 3, 5, LAZY)
    } else if level == 7 {
        (21, 19, 20, 4, 5, LAZY)
    } else if level == 8 {
        (21, 19, 20, 4, 5, LAZY2)
    } else if level == 9 {
        (22, 20, 21, 4, 5, LAZY2)
    } else if level == 10 {
        (22, 21, 22, 5, 5, LAZY2)
    } else if level == 11 {
        (22, 21, 22, 6, 5, LAZY2)
    } else if level == 12 {
        (22, 22, 23, 6, 5, LAZY2)
    } else if level == 13 {
        (22, 22, 22, 7, 5, LAZY2)
    } else if level == 14 {
        (22, 22, 23, 7, 5, LAZY2)
    } else if level == 15 {
        (22, 23, 23, 8, 5, LAZY2)
    } else if level == 16 {
        (22, 22, 22, 5, 4, OPT)
    } else if level == 17 {
        (23, 23, 22, 5, 4, OPT)
    } else if level == 18 {
        (23, 23, 22, 6, 4, OPT)
    } else if level == 19 {
        (23, 24, 22, 7, 4, OPT)
    } else if level == 20 {
        (25, 25, 23, 7, 4, OPT)
    } else if level == 21 {
        (26, 26, 24, 7, 4, OPT)
    } else {
        (27, 27, 25, 9, 4, OPT)
    }
}

/// The optimal parser's "sufficient length": a match this long is taken
/// at once (libzstd's target length for the level).
pub fn target_len(level: i32) -> (r: usize)
    ensures
        r >= 16,
{
    if level <= 16 {
        48
    } else if level == 17 {
        64
    } else if level == 18 {
        128
    } else if level <= 20 {
        256
    } else if level == 21 {
        512
    } else {
        999
    }
}

/// The sequences of a block: literals, and per sequence its literals
/// length, match length and offset.
pub struct Store {
    pub lits: Vec<u8>,
    pub ll: Vec<u32>,
    pub ml: Vec<u32>,
    pub off: Vec<u32>,
}

impl Store {
    pub open spec fn wf(&self) -> bool {
        &&& self.ll@.len() == self.ml@.len()
        &&& self.ll@.len() == self.off@.len()
    }
}

pub struct Enc {
    pub window: usize,
    pub strat: u8,
    pub hlog: u32,
    pub clog: u32,
    pub slog: u32,
    pub mls: u32,
    /// Table entries are positions minus `base`.
    pub base: usize,
    pub t1: Vec<u32>,
    pub t2: Vec<u32>,
    /// The next position to add to the hash chains.
    pub next: usize,
    pub rep1: usize,
    pub rep2: usize,
    pub st: Store,
    pub ob: Vec<u32>,
    pub lsc: LitScratch,
    pub ssc: SeqScratch,
    /// The optimal parser's statistics and nodes.
    pub op: OptState,
}

/// The table index of the `mls` bytes at `ip`.
#[inline(always)]
pub fn hash(src: &[u8], ip: usize, mls: u32, hlog: u32) -> (h: usize)
    requires
        ip + 8 <= src@.len(),
        4 <= mls <= 8,
        1 <= hlog <= 30,
    ensures
        h < (1usize << hlog),
{
    let x = load_u64_le(src, ip);
    let ms: u64 = 64 - 8 * mls as u64;
    let y = (x << ms).wrapping_mul(0xCF1BBCDCB7A56463u64);
    let hl = hlog as u64;
    let sh: u64 = 64 - hl;
    let h = y >> sh;
    proof {
        assert(y >> sh < (1u64 << hl)) by (bit_vector)
            requires 1 <= hl <= 30, sh == 64 - hl;
        assert((1u64 << hl) <= 0x4000_0000) by (bit_vector)
            requires 1 <= hl <= 30;
        assert((1u64 << hl) as usize == (1usize << hlog)) by (bit_vector)
            requires 1 <= hlog <= 30, hl == hlog as u64;
    }
    h as usize
}

/// Do the first `mls` bytes at `a` and `b` agree?
#[inline(always)]
fn eq_mls(src: &[u8], a: usize, b: usize, mls: u32) -> bool
    requires
        a + 8 <= src@.len(),
        b + 8 <= src@.len(),
        4 <= mls <= 8,
{
    let x = load_u64_le(src, a) ^ load_u64_le(src, b);
    let ms: u64 = 64 - 8 * mls as u64;
    (x << ms) == 0
}

/// Adds a sequence: the literals `src[anchor..ip]`, then a match of `m`
/// bytes from `off` back.
#[inline(always)]
pub fn emit(st: &mut Store, src: &[u8], anchor: usize, ip: usize, off: usize, m: usize)
    requires
        anchor <= ip <= src@.len(),
        old(st).wf(),
    ensures
        final(st).wf(),
{
    st.lits.extend_from_slice(slice_subrange(src, anchor, ip));
    st.ll.push((ip - anchor) as u32);
    st.ml.push(m as u32);
    st.off.push(off as u32);
}

/// Is there room in `st` for literals up to `end` from `anchor` and a
/// sequence per 4 of those bytes? (Every match is at least 4 bytes.)
pub open spec fn room(st: &Store, anchor: usize, end: usize) -> bool {
    &&& verilith_core::spare::spare(st.lits) >= end - anchor + 8
    &&& 4 * verilith_core::spare::spare(st.ll) >= end - anchor + 4
    &&& 4 * verilith_core::spare::spare(st.ml) >= end - anchor + 4
    &&& 4 * verilith_core::spare::spare(st.off) >= end - anchor + 4
}

/// Reserves `room(st, pos, end)`.
pub fn reserve_room(st: &mut Store, pos: usize, end: usize)
    requires
        pos <= end,
        end - pos <= 0x20000,
        old(st).wf(),
    ensures
        final(st).wf(),
        final(st).lits@ == old(st).lits@,
        room(final(st), pos, end),
{
    let n = (end - pos) / 4 + 2;
    proof {
        let x = (end - pos) as int;
        assert(4 * (x / 4 + 2) >= x + 4) by (nonlinear_arith);
    }
    verilith_core::spare::reserve_spare(&mut st.lits, end - pos + 8);
    verilith_core::spare::reserve_spare(&mut st.ll, n);
    verilith_core::spare::reserve_spare(&mut st.ml, n);
    verilith_core::spare::reserve_spare(&mut st.off, n);
}

/// `emit` into reserved room: a sequence ending at `ip + m`, at least 4
/// bytes past `anchor`. No capacity checks, and short literal runs take
/// no `memcpy` call.
#[inline(always)]
pub fn emit_s(st: &mut Store, src: &[u8], anchor: usize, ip: usize, off: usize, m: usize, end: usize)
    requires
        anchor <= ip,
        ip + 8 <= src@.len(),
        ip + m <= end,
        ip + m >= anchor + 4,
        old(st).wf(),
        room(old(st), anchor, end),
    ensures
        final(st).wf(),
        room(final(st), (ip + m) as usize, end),
{
    verilith_core::spare::append_wild_spare(&mut st.lits, src, anchor, ip);
    verilith_core::spare::push_spare(&mut st.ll, (ip - anchor) as u32);
    verilith_core::spare::push_spare(&mut st.ml, m as u32);
    verilith_core::spare::push_spare(&mut st.off, off as u32);
}

/// The loop of `Enc::fast`. Returns the table, the last anchor and the
/// repeat offsets.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn fast_run(
    t1: Vec<u32>,
    st: &mut Store,
    src: &[u8],
    pos: usize,
    end: usize,
    base: usize,
    low: usize,
    hlog: u32,
    mls: u32,
    rep1: usize,
    rep2: usize,
) -> (r: (Vec<u32>, usize, usize, usize))
    requires
        pos < end <= src@.len(),
        end - pos >= 16,
        base <= pos,
        base <= low,
        end - base < 0xC002_0000,
        t1@.len() == (1usize << hlog),
        1 <= hlog <= 30,
        4 <= mls <= 8,
        old(st).wf(),
        room(old(st), pos, end),
    ensures
        r.0@.len() == t1@.len(),
        pos <= r.1 <= end,
        final(st).wf(),
{
    let mut t1 = t1;
    let ghost tl = t1@.len();
    let mut anchor = pos;
    let mut ip = if pos == 0 { 1 } else { pos };
    // Repeat offsets reach back no further than `low`.
    let mut r1 = if ip >= low && rep1 <= ip - low { rep1 } else { 0 };
    let mut r2 = if ip >= low && rep2 <= ip - low { rep2 } else { 0 };
    let ilimit = end - 8;
    while ip < ilimit
        invariant
            anchor <= ip,
            ip <= end,
            pos <= anchor,
            ilimit == end - 8,
            t1@.len() == tl,
            st.wf(),
            room(st, anchor, end),
            r1 == 0 || (ip >= low && r1 <= ip - low),
            r2 == 0 || (ip >= low && r2 <= ip - low),
        decreases end - ip,
    {
        let ghost ip0 = ip;
        let h = hash(src, ip, mls, hlog);
        let cand = base.wrapping_add(t1[h] as usize);
        t1.set(h, (ip - base) as u32);
        let ip1 = ip + 1;
        if r1 != 0 && load32(src, ip1) == load32(src, ip1 - r1) {
            let m = 4 + eq_len(src, ip1 + 4, ip1 + 4 - r1, end - (ip1 + 4));
            emit_s(st, src, anchor, ip1, r1, m, end);
            ip = ip1 + m;
            anchor = ip;
        } else if cand < ip && cand >= low && eq_mls(src, ip, cand, mls) {
            let off = ip - cand;
            let mut m = mls as usize + eq_len(src, ip + mls as usize, cand + mls as usize, end - (ip + mls as usize));
            let mut s = ip;
            let mut c = cand;
            while s > anchor && c > base && src[s - 1] == src[c - 1]
                invariant
                    anchor <= s <= ip,
                    c < s,
                    s - c == off,
                    m <= end - s,
                    s + m >= ip + 4,
                decreases s,
            {
                s = s - 1;
                c = c - 1;
                m = m + 1;
            }
            emit_s(st, src, anchor, s, off, m, end);
            r2 = r1;
            r1 = off;
            ip = s + m;
            anchor = ip;
        } else {
            let stp = (ip - anchor) / 256 + 1;
            ip = if ilimit - ip > stp { ip + stp } else { ilimit };
            continue;
        }
        if ip < ilimit && ip >= base + 2 {
            let h2 = hash(src, ip - 2, mls, hlog);
            t1.set(h2, (ip - 2 - base) as u32);
            while ip < ilimit && r2 != 0 && load32(src, ip) == load32(src, ip - r2)
                invariant
                    anchor == ip,
                    ip <= end,
                    pos <= anchor,
                    ilimit == end - 8,
                    t1@.len() == tl,
                    st.wf(),
                    room(st, anchor, end),
                    r1 == 0 || (ip >= low && r1 <= ip - low),
                    r2 == 0 || (ip >= low && r2 <= ip - low),
                    ip > ip0,
                decreases end - ip,
            {
                let q = r2;
                let m = 4 + eq_len(src, ip + 4, ip + 4 - q, end - (ip + 4));
                r2 = r1;
                r1 = q;
                emit_s(st, src, ip, ip, q, m, end);
                let h3 = hash(src, ip, mls, hlog);
                t1.set(h3, (ip - base) as u32);
                ip = ip + m;
                anchor = ip;
            }
        }
    }
    (t1, anchor, r1, r2)
}

/// The loop of `Enc::dfast`. Returns the tables, the last anchor and the
/// repeat offsets.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn dfast_run(
    t1: Vec<u32>,
    t2: Vec<u32>,
    st: &mut Store,
    src: &[u8],
    pos: usize,
    end: usize,
    base: usize,
    low: usize,
    hlog: u32,
    clog: u32,
    mls: u32,
    rep1: usize,
    rep2: usize,
) -> (r: (Vec<u32>, Vec<u32>, usize, usize, usize))
    requires
        pos < end <= src@.len(),
        end - pos >= 16,
        base <= pos,
        base <= low,
        end - base < 0xC002_0000,
        t1@.len() == (1usize << hlog),
        t2@.len() == (1usize << clog),
        1 <= hlog <= 30,
        1 <= clog <= 30,
        4 <= mls <= 8,
        old(st).wf(),
        room(old(st), pos, end),
    ensures
        r.0@.len() == t1@.len(),
        r.1@.len() == t2@.len(),
        pos <= r.2 <= end,
        final(st).wf(),
{
    let mut t1 = t1;
    let mut t2 = t2;
    let ghost tl1 = t1@.len();
    let ghost tl2 = t2@.len();
    let mut anchor = pos;
    let mut ip = if pos == 0 { 1 } else { pos };
    let mut r1 = if ip >= low && rep1 <= ip - low { rep1 } else { 0 };
    let mut r2 = if ip >= low && rep2 <= ip - low { rep2 } else { 0 };
    let ilimit = end - 8;
    while ip < ilimit
        invariant
            anchor <= ip,
            ip <= end,
            pos <= anchor,
            ilimit == end - 8,
            t1@.len() == tl1,
            t2@.len() == tl2,
            st.wf(),
            room(st, anchor, end),
            r1 == 0 || (ip >= low && r1 <= ip - low),
            r2 == 0 || (ip >= low && r2 <= ip - low),
        decreases end - ip,
    {
        let ghost ip0 = ip;
        let hl = hash(src, ip, 8, hlog);
        let hs = hash(src, ip, mls, clog);
        let cl = base.wrapping_add(t1[hl] as usize);
        let cs = base.wrapping_add(t2[hs] as usize);
        t1.set(hl, (ip - base) as u32);
        t2.set(hs, (ip - base) as u32);
        let ip1 = ip + 1;
        if r1 != 0 && load32(src, ip1) == load32(src, ip1 - r1) {
            let m = 4 + eq_len(src, ip1 + 4, ip1 + 4 - r1, end - (ip1 + 4));
            emit_s(st, src, anchor, ip1, r1, m, end);
            ip = ip1 + m;
            anchor = ip;
        } else {
            let mut start = ip;
            let mut off: usize = 0;
            let mut m: usize = 0;
            if cl < ip && cl >= low && eq_mls(src, ip, cl, 8) {
                off = ip - cl;
                m = 8 + eq_len(src, ip + 8, cl + 8, end - (ip + 8));
            } else if cs < ip && cs >= low && eq_mls(src, ip, cs, mls) {
                // A long match one byte later?
                let h3 = hash(src, ip1, 8, hlog);
                let c3 = base.wrapping_add(t1[h3] as usize);
                t1.set(h3, (ip1 - base) as u32);
                if c3 < ip1 && c3 >= low && eq_mls(src, ip1, c3, 8) {
                    off = ip1 - c3;
                    start = ip1;
                    m = 8 + eq_len(src, ip1 + 8, c3 + 8, end - (ip1 + 8));
                } else {
                    off = ip - cs;
                    m = mls as usize + eq_len(src, ip + mls as usize, cs + mls as usize, end - (ip + mls as usize));
                }
            }
            if off == 0 {
                let stp = (ip - anchor) / 256 + 1;
                ip = if ilimit - ip > stp { ip + stp } else { ilimit };
                continue;
            }
            let mut s = start;
            let mut c = start - off;
            while s > anchor && c > base && src[s - 1] == src[c - 1]
                invariant
                    anchor <= s <= start,
                    c < s,
                    s - c == off,
                    m <= end - s,
                    s + m >= ip + 4,
                decreases s,
            {
                s = s - 1;
                c = c - 1;
                m = m + 1;
            }
            emit_s(st, src, anchor, s, off, m, end);
            r2 = r1;
            r1 = off;
            ip = s + m;
            anchor = ip;
        }
        if ip < ilimit && ip >= base + 2 {
            let p = ip - 2;
            let h4 = hash(src, p, 8, hlog);
            t1.set(h4, (p - base) as u32);
            let h5 = hash(src, p, mls, clog);
            t2.set(h5, (p - base) as u32);
            while ip < ilimit && r2 != 0 && load32(src, ip) == load32(src, ip - r2)
                invariant
                    anchor == ip,
                    ip <= end,
                    pos <= anchor,
                    ilimit == end - 8,
                    t1@.len() == tl1,
                    t2@.len() == tl2,
                    st.wf(),
                    room(st, anchor, end),
                    r1 == 0 || (ip >= low && r1 <= ip - low),
                    r2 == 0 || (ip >= low && r2 <= ip - low),
                    ip > ip0,
                decreases end - ip,
            {
                let q = r2;
                let m2 = 4 + eq_len(src, ip + 4, ip + 4 - q, end - (ip + 4));
                r2 = r1;
                r1 = q;
                emit_s(st, src, ip, ip, q, m2, end);
                let h6 = hash(src, ip, 8, hlog);
                t1.set(h6, (ip - base) as u32);
                let h7 = hash(src, ip, mls, clog);
                t2.set(h7, (ip - base) as u32);
                ip = ip + m2;
                anchor = ip;
            }
        }
    }
    (t1, t2, anchor, r1, r2)
}

/// The fixed parameters of a hash-chain search over one block.
pub struct Hc {
    pub base: usize,
    /// The lowest position a match may come from.
    pub low: usize,
    pub hlog: u32,
    pub mls: u32,
    pub slog: u32,
}

impl Hc {
    pub open spec fn wf(&self, t1: Seq<u32>, t2: Seq<u32>) -> bool {
        &&& self.base <= self.low
        &&& 1 <= self.hlog <= 30
        &&& 4 <= self.mls <= 8
        &&& self.slog <= 16
        &&& t1.len() == (1usize << self.hlog)
        &&& t2.len() >= 2
    }
}

/// Adds positions `next..ip` to the hash chains; returns `ip`.
#[inline(always)]
fn hc_insert(t1: &mut Vec<u32>, t2: &mut Vec<u32>, p: &Hc, src: &[u8], next: usize, ip: usize) -> (r: usize)
    requires
        p.wf(old(t1)@, old(t2)@),
        ip + 8 <= src@.len(),
        p.base <= next,
        p.base <= ip,
        ip - p.base < 0xC002_0000,
    ensures
        final(t1)@.len() == old(t1)@.len(),
        final(t2)@.len() == old(t2)@.len(),
        r == ip,
{
    let cmask = t2.len() - 1;
    let mut q = next;
    while q < ip
        invariant
            p.wf(t1@, t2@),
            t1@.len() == old(t1)@.len(),
            t2@.len() == old(t2)@.len(),
            p.base <= q,
            ip + 8 <= src@.len(),
            ip - p.base < 0xC002_0000,
            cmask == t2@.len() - 1,
        decreases ip - q,
    {
        let h = hash(src, q, p.mls, p.hlog);
        let ci = q & cmask;
        proof {
            assert(q & cmask <= cmask) by (bit_vector);
        }
        t2.set(ci, t1[h]);
        t1.set(h, (q - p.base) as u32);
        q = q + 1;
    }
    ip
}

/// The longest match at `ip` along the hash chain, after adding the
/// positions before it: (length, offset); length 0 if none of at least
/// 4. Returns the next position to add as well.
#[inline(always)]
fn hc_find(t1: &mut Vec<u32>, t2: &mut Vec<u32>, p: &Hc, src: &[u8], next: usize, ip: usize, end: usize) -> (r: (usize, usize, usize))
    requires
        p.wf(old(t1)@, old(t2)@),
        ip + 8 <= end <= src@.len(),
        p.base <= next,
        p.base <= ip,
        ip - p.base < 0xC002_0000,
    ensures
        final(t1)@.len() == old(t1)@.len(),
        final(t2)@.len() == old(t2)@.len(),
        r.0 > 0 ==> 1 <= r.1 && p.low <= ip - r.1 && r.0 <= end - ip && r.0 >= 4,
        r.2 == ip,
{
    let nx = if next <= ip { hc_insert(t1, t2, p, src, next, ip) } else { ip };
    let cmask = t2.len() - 1;
    let h = hash(src, ip, p.mls, p.hlog);
    let mut cand = p.base.wrapping_add(t1[h] as usize);
    let mut best: usize = 3;
    let mut boff: usize = 0;
    let mut attempts: u32 = 1u32 << p.slog;
    let csize = t2.len();
    let lim = end - ip;
    // The head may be older than the chain table reaches; the links after
    // it are followed only while they are not (libzstd's `minChain`).
    while attempts > 0 && cand < ip && cand >= p.low
        invariant
            p.wf(t1@, t2@),
            cmask == t2@.len() - 1,
            3 <= best <= lim,
            lim == end - ip,
            ip + 8 <= end <= src@.len(),
            best > 3 ==> 1 <= boff && p.low <= ip - boff,
        decreases attempts,
    {
        if best < lim && src[cand + best] == src[ip + best] {
            let l = eq_len(src, ip, cand, lim);
            if l > best {
                best = l;
                boff = ip - cand;
                if l == lim {
                    break;
                }
            }
        }
        if ip - cand >= csize {
            break;
        }
        let ci = cand & cmask;
        proof {
            assert(cand & cmask <= cmask) by (bit_vector);
        }
        let nc = p.base.wrapping_add(t2[ci] as usize);
        if nc >= cand {
            break;
        }
        cand = nc;
        attempts = attempts - 1;
    }
    if best > 3 {
        (best, boff, nx)
    } else {
        (0, 0, nx)
    }
}

/// The loop of `Enc::lazy`. Returns the tables, the last anchor, the next
/// position to add to the chains and the repeat offsets.
#[verifier::loop_isolation(false)]
fn lazy_run(
    t1: Vec<u32>,
    t2: Vec<u32>,
    st: &mut Store,
    src: &[u8],
    pos: usize,
    end: usize,
    p: &Hc,
    next: usize,
    depth: u32,
    rep1: usize,
    rep2: usize,
) -> (r: (Vec<u32>, Vec<u32>, usize, usize, usize, usize))
    requires
        pos < end <= src@.len(),
        end - pos >= 16,
        p.base <= pos,
        p.base <= next,
        end - p.base < 0xC002_0000,
        p.wf(t1@, t2@),
        old(st).wf(),
        room(old(st), pos, end),
    ensures
        r.0@.len() == t1@.len(),
        r.1@.len() == t2@.len(),
        pos <= r.2 <= end,
        p.base <= r.3,
        final(st).wf(),
{
    let mut t1 = t1;
    let mut t2 = t2;
    let ghost tl1 = t1@.len();
    let ghost tl2 = t2@.len();
    let low = p.low;
    let base = p.base;
    let mut nxt = next;
    let mut anchor = pos;
    let mut ip = if pos == 0 { 1 } else { pos };
    let mut r1 = if ip >= low && rep1 <= ip - low { rep1 } else { 0 };
    let mut r2 = if ip >= low && rep2 <= ip - low { rep2 } else { 0 };
    let ilimit = end - 8;
    while ip < ilimit
        invariant
            anchor <= ip,
            ip <= end,
            pos <= anchor,
            ilimit == end - 8,
            p.base <= nxt,
            t1@.len() == tl1,
            t2@.len() == tl2,
            p.wf(t1@, t2@),
            st.wf(),
            room(st, anchor, end),
            r1 == 0 || (ip >= low && r1 <= ip - low),
            r2 == 0 || (ip >= low && r2 <= ip - low),
        decreases end - ip,
    {
        let ghost ip0 = ip;
        let mut m: usize = 0;
        let mut off: usize = 0;
        let mut start = ip + 1;
        // A repeat offset one byte ahead.
        if r1 != 0 && load32(src, ip + 1) == load32(src, ip + 1 - r1) {
            m = 4 + eq_len(src, ip + 5, ip + 5 - r1, end - (ip + 5));
            off = r1;
        }
        if depth > 0 || m == 0 {
            let (m2, o2, n2) = hc_find(&mut t1, &mut t2, p, src, nxt, ip, end);
            nxt = n2;
            if m2 > m {
                m = m2;
                off = o2;
                start = ip;
            }
        }
        if m < 4 {
            let stp = (ip - anchor) / 256 + 1;
            ip = if ilimit - ip > stp { ip + stp } else { ilimit };
            continue;
        }
        // Look ahead for something better.
        let mut d: u32 = 0;
        let mut cur = start;
        while d < depth && cur + 1 < ilimit
            invariant
                p.wf(t1@, t2@),
                t1@.len() == tl1,
                t2@.len() == tl2,
                p.base <= nxt,
                anchor <= start <= cur,
                ip <= start,
                cur <= ilimit,
                m >= 4,
                m <= end - start,
                1 <= off <= start,
                start - off >= low,
                r1 == 0 || (ip >= low && r1 <= ip - low),
            decreases depth - d,
        {
            cur = cur + 1;
            d = d + 1;
            let mut better = false;
            if r1 != 0 && load32(src, cur) == load32(src, cur - r1) {
                let mr = 4 + eq_len(src, cur + 4, cur + 4 - r1, end - (cur + 4));
                let g2 = (mr as i64).wrapping_mul(4);
                let g1 = (m as i64).wrapping_mul(4) - hbit(lo32((off + 1) as u64)) as i64 + 1;
                if g2 > g1 {
                    m = mr;
                    off = r1;
                    start = cur;
                    better = true;
                }
            }
            let (m2, o2, n2) = hc_find(&mut t1, &mut t2, p, src, nxt, cur, end);
            nxt = n2;
            if m2 >= 4 {
                let g2 = (m2 as i64).wrapping_mul(4) - hbit(lo32((o2 + 1) as u64)) as i64;
                let g1 = (m as i64).wrapping_mul(4) - hbit(lo32((off + 1) as u64)) as i64 + if d == 1 { 4 } else { 7 };
                if g2 > g1 {
                    m = m2;
                    off = o2;
                    start = cur;
                    better = true;
                }
            }
            if !better {
                break;
            }
        }
        // Extend backwards.
        let mut s = start;
        let mut c = start - off;
        while s > anchor && c > base && src[s - 1] == src[c - 1]
            invariant
                anchor <= s <= start,
                c < s,
                s - c == off,
                m <= end - s,
                s + m >= ip + 4,
                s + m >= start,
            decreases s,
        {
            s = s - 1;
            c = c - 1;
            m = m + 1;
        }
        emit_s(st, src, anchor, s, off, m, end);
        if off != r1 {
            r2 = r1;
            r1 = off;
        }
        ip = s + m;
        anchor = ip;
        while ip < ilimit && r2 != 0 && load32(src, ip) == load32(src, ip - r2)
            invariant
                anchor == ip,
                ip <= end,
                pos <= anchor,
                ilimit == end - 8,
                p.base <= nxt,
                t1@.len() == tl1,
                t2@.len() == tl2,
                p.wf(t1@, t2@),
                st.wf(),
                room(st, anchor, end),
                r1 == 0 || (ip >= low && r1 <= ip - low),
                r2 == 0 || (ip >= low && r2 <= ip - low),
                ip > ip0,
            decreases end - ip,
        {
            let q = r2;
            let m2 = 4 + eq_len(src, ip + 4, ip + 4 - q, end - (ip + 4));
            r2 = r1;
            r1 = q;
            emit_s(st, src, ip, ip, q, m2, end);
            ip = ip + m2;
            anchor = ip;
        }
    }
    (t1, t2, anchor, nxt, r1, r2)
}

impl Enc {
    pub open spec fn wf(&self) -> bool {
        &&& 1 <= self.hlog <= 30
        &&& 1 <= self.clog <= 30
        &&& 4 <= self.mls <= 8
        &&& self.slog <= 16
        &&& self.t1@.len() == (1usize << self.hlog)
        &&& self.t2@.len() == (1usize << self.clog)
        &&& self.t1@.len() >= 2
        &&& self.t2@.len() >= 2
        &&& self.st.wf()
        &&& self.lsc.cnt@.len() == 256
        &&& self.op.wf()
    }

    pub fn new(src: &[u8], window: u64, level: i32) -> (r: Enc)
        ensures
            r.wf(),
    {
        let (wlog0, clog0, hlog0, slog, mls, strat) = level_params(level);
        // Smaller tables for small inputs.
        let n = src.len();
        let mut need: u32 = 10;
        while need < 27 && (1usize << need) < n
            invariant
                10 <= need <= 27,
            decreases 27 - need,
        {
            need = need + 1;
        }
        let wlog = if wlog0 < need { wlog0 } else { need };
        let mut hlog = if hlog0 > wlog + 1 { wlog + 1 } else { hlog0 };
        let mut clog = if clog0 > wlog + 1 { wlog + 1 } else { clog0 };
        if strat == FAST {
            clog = 6;
        }
        if hlog < 6 {
            hlog = 6;
        }
        if clog < 6 {
            clog = 6;
        }
        proof {
            assert((1usize << hlog) <= 0x800_0000 && (1usize << hlog) >= 2) by (bit_vector)
                requires 1 <= hlog <= 27;
            assert((1usize << clog) <= 0x800_0000 && (1usize << clog) >= 2) by (bit_vector)
                requires 1 <= clog <= 27;
        }
        let t1: Vec<u32> = vec![0u32; 1usize << hlog];
        let t2: Vec<u32> = vec![0u32; 1usize << clog];
        let win: usize = if window > 0x8000_0000 { 0x8000_0000 } else { window as usize };
        Enc {
            window: win,
            strat,
            hlog,
            clog,
            slog,
            mls,
            base: 0,
            t1,
            t2,
            next: 0,
            rep1: 1,
            rep2: 4,
            st: Store { lits: Vec::new(), ll: Vec::new(), ml: Vec::new(), off: Vec::new() },
            ob: Vec::new(),
            lsc: LitScratch::new(),
            ssc: SeqScratch::new(),
            op: OptState::new(target_len(level)),
        }
    }

    /// Is `off` a usable offset for a match at `ip`?
    #[inline(always)]
    pub fn off_ok(&self, ip: usize, off: usize) -> (r: bool)
        ensures
            r ==> 1 <= off <= ip,
    {
        off >= 1 && off <= ip && off <= self.window && ip - off >= self.base
    }

    /// Clears the tables when positions would no longer fit 32 bits.
    pub fn rebase(&mut self, pos: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            pos - final(self).base < 0xC000_0000,
            final(self).base <= pos,
    {
        if pos >= self.base && pos - self.base < 0xC000_0000 {
            return;
        }
        let mut i: usize = 0;
        while i < self.t1.len()
            invariant
                self.wf(),
            decreases self.t1@.len() - i,
        {
            self.t1.set(i, 0);
            i = i + 1;
        }
        let mut i: usize = 0;
        while i < self.t2.len()
            invariant
                self.wf(),
            decreases self.t2@.len() - i,
        {
            self.t2.set(i, 0);
            i = i + 1;
        }
        self.base = pos;
        self.next = pos;
    }

    /// The fast strategy: one hash table of `mls`-byte hashes, the
    /// repeat offset tried one byte ahead. The loop runs on locals (the
    /// table moved out of `self`), with one `low` for the whole block and
    /// a copy per match length so the hash shifts are constants.
    #[verifier::loop_isolation(false)]
    pub fn fast(&mut self, src: &[u8], pos: usize, end: usize)
        requires
            old(self).wf(),
            pos < end <= src@.len(),
            pos >= old(self).base,
            pos - old(self).base < 0xC000_0000,
            end - pos <= 0x20000,
        ensures
            final(self).wf(),
    {
        let mut anchor = pos;
        if end - pos >= 16 {
            reserve_room(&mut self.st, anchor, end);
            let base = self.base;
            let low = if end - base > self.window { end - self.window } else { base };
            let mut t1: Vec<u32> = Vec::new();
            core::mem::swap(&mut t1, &mut self.t1);
            let hlog = self.hlog;
            let (r1, r2) = (self.rep1, self.rep2);
            let (t, a, q1, q2) = if self.mls == 4 {
                fast_run(t1, &mut self.st, src, pos, end, base, low, hlog, 4, r1, r2)
            } else if self.mls == 5 {
                fast_run(t1, &mut self.st, src, pos, end, base, low, hlog, 5, r1, r2)
            } else if self.mls == 6 {
                fast_run(t1, &mut self.st, src, pos, end, base, low, hlog, 6, r1, r2)
            } else if self.mls == 7 {
                fast_run(t1, &mut self.st, src, pos, end, base, low, hlog, 7, r1, r2)
            } else {
                fast_run(t1, &mut self.st, src, pos, end, base, low, hlog, 8, r1, r2)
            };
            self.t1 = t;
            self.rep1 = q1;
            self.rep2 = q2;
            anchor = a;
        }
        self.st.lits.extend_from_slice(slice_subrange(src, anchor, end));
    }

    /// The double-fast strategy: a table of 8-byte hashes for long
    /// matches and one of `mls`-byte hashes for short ones. Like `fast`,
    /// the loop runs on locals.
    #[verifier::loop_isolation(false)]
    pub fn dfast(&mut self, src: &[u8], pos: usize, end: usize)
        requires
            old(self).wf(),
            pos < end <= src@.len(),
            pos >= old(self).base,
            pos - old(self).base < 0xC000_0000,
            end - pos <= 0x20000,
        ensures
            final(self).wf(),
    {
        let mut anchor = pos;
        if end - pos >= 16 {
            reserve_room(&mut self.st, anchor, end);
            let base = self.base;
            let low = if end - base > self.window { end - self.window } else { base };
            let mut t1: Vec<u32> = Vec::new();
            let mut t2: Vec<u32> = Vec::new();
            core::mem::swap(&mut t1, &mut self.t1);
            core::mem::swap(&mut t2, &mut self.t2);
            let (hlog, clog) = (self.hlog, self.clog);
            let (r1, r2) = (self.rep1, self.rep2);
            let (u1, u2, a, q1, q2) = if self.mls == 4 {
                dfast_run(t1, t2, &mut self.st, src, pos, end, base, low, hlog, clog, 4, r1, r2)
            } else if self.mls == 5 {
                dfast_run(t1, t2, &mut self.st, src, pos, end, base, low, hlog, clog, 5, r1, r2)
            } else if self.mls == 6 {
                dfast_run(t1, t2, &mut self.st, src, pos, end, base, low, hlog, clog, 6, r1, r2)
            } else {
                dfast_run(t1, t2, &mut self.st, src, pos, end, base, low, hlog, clog, self.mls, r1, r2)
            };
            self.t1 = u1;
            self.t2 = u2;
            self.rep1 = q1;
            self.rep2 = q2;
            anchor = a;
        }
        self.st.lits.extend_from_slice(slice_subrange(src, anchor, end));
    }

    /// Greedy and lazy matching on hash chains (libzstd's
    /// `ZSTD_compressBlock_lazy_generic`), looking `depth` positions ahead
    /// for a better match. Like `fast`, the loop runs on locals.
    #[verifier::loop_isolation(false)]
    pub fn lazy(&mut self, src: &[u8], pos: usize, end: usize, depth: u32)
        requires
            old(self).wf(),
            pos < end <= src@.len(),
            pos >= old(self).base,
            pos - old(self).base < 0xC000_0000,
            end - pos <= 0x20000,
        ensures
            final(self).wf(),
    {
        let mut anchor = pos;
        if end - pos >= 16 {
            reserve_room(&mut self.st, anchor, end);
            let base = self.base;
            let low = if end - base > self.window { end - self.window } else { base };
            let mut t1: Vec<u32> = Vec::new();
            let mut t2: Vec<u32> = Vec::new();
            core::mem::swap(&mut t1, &mut self.t1);
            core::mem::swap(&mut t2, &mut self.t2);
            let p = Hc { base, low, hlog: self.hlog, mls: self.mls, slog: self.slog };
            let next = if self.next < base || self.next > pos { pos } else { self.next };
            let (u1, u2, a, nx, q1, q2) = lazy_run(t1, t2, &mut self.st, src, pos, end, &p, next, depth, self.rep1, self.rep2);
            self.t1 = u1;
            self.t2 = u2;
            self.next = nx;
            self.rep1 = q1;
            self.rep2 = q2;
            anchor = a;
        }
        self.st.lits.extend_from_slice(slice_subrange(src, anchor, end));
    }

    /// Appends the content of a compressed block for `src[pos..end]`, the
    /// repeat offsets at its start being `r1`, `r2`, `r3`. `false`: no
    /// block was made (what was appended is to be dropped).
    #[verifier::loop_isolation(false)]
    pub fn block(&mut self, src: &[u8], pos: usize, end: usize, r1: u64, r2: u64, r3: u64, out: &mut Vec<u8>) -> (ok: bool)
        requires
            old(self).wf(),
            pos < end <= src@.len(),
            end - pos <= 0x20000,
        ensures
            final(self).wf(),
            grew(old(out)@, final(out)@),
    {
        let ghost o0 = out@;
        proof {
            lemma_grew_refl(out@);
        }
        self.rebase(pos);
        self.st.lits.clear();
        self.st.ll.clear();
        self.st.ml.clear();
        self.st.off.clear();
        self.rep1 = if r1 <= 0x8000_0000 { r1 as usize } else { 0 };
        self.rep2 = if r2 <= 0x8000_0000 { r2 as usize } else { 0 };
        if self.strat == FAST {
            self.fast(src, pos, end);
        } else if self.strat == DFAST {
            self.dfast(src, pos, end);
        } else if self.strat == GREEDY {
            self.lazy(src, pos, end, 0);
        } else if self.strat == LAZY {
            self.lazy(src, pos, end, 1);
        } else if self.strat == LAZY2 {
            self.lazy(src, pos, end, 2);
        } else {
            self.opt(src, pos, end, r1, r2, r3);
        }
        // Offsets to offset values, with the repeat offsets as the
        // decoder keeps them.
        let n = self.st.ll.len();
        self.ob.clear();
        let mut a = r1;
        let mut b = r2;
        let mut c = r3;
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(),
                n == self.st.ll@.len(),
                self.ob@.len() == i,
                i <= n,
            decreases n - i,
        {
            let o = self.st.off[i] as u64;
            let l0 = self.st.ll[i] == 0;
            let v: u64 = if !l0 {
                if o == a {
                    1
                } else if o == b {
                    b = a;
                    a = o;
                    2
                } else if o == c {
                    c = b;
                    b = a;
                    a = o;
                    3
                } else {
                    c = b;
                    b = a;
                    a = o;
                    o + 3
                }
            } else {
                if o == b {
                    b = a;
                    a = o;
                    1
                } else if o == c {
                    c = b;
                    b = a;
                    a = o;
                    2
                } else if a > 1 && o == a - 1 {
                    c = b;
                    b = a;
                    a = o;
                    3
                } else {
                    c = b;
                    b = a;
                    a = o;
                    o + 3
                }
            };
            if v > 0xFFFF_FFFF {
                return false;
            }
            self.ob.push(v as u32);
            i = i + 1;
        }
        if self.st.lits.len() >= 0x10_0000 {
            return false;
        }
        put_lits(out, self.st.lits.as_slice(), &mut self.lsc, 11);
        let ghost o1 = out@;
        let ok = put_seqs(out, self.st.ll.as_slice(), self.st.ml.as_slice(), self.ob.as_slice(), &mut self.ssc);
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
        ok
    }
}

} // verus!
