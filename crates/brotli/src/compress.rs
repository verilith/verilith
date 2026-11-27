//! The compressor proper: an LZ77 parse (not trusted: every command it
//! makes is checked before it is written, `cwrite::check_cmds`), prefix
//! codes from the symbol counts, and the proven meta-block writers.
use crate::cwrite::put_compressed;
use crate::encoder::Enc;
use crate::mblock::*;
use crate::pcode::{make_code, make_plan};
#[cfg(verus_only)]
use crate::spec::*;
use verilith_core::lz::{eq_len, load32};
use vstd::prelude::*;

verus! {

/// What the parser finds: `ins` literals, then `clen` bytes from `dist`
/// back (no copy when `dist == 0`).
#[derive(Clone, Copy)]
pub struct Lz {
    pub ins: u32,
    pub clen: u32,
    pub dist: u32,
}

const NONE: u32 = 0xFFFF_FFFF;

/// Hash chains over the whole input.
pub struct Mf {
    pub head: Vec<u32>,
    pub prev: Vec<u32>,
    pub depth: u32,
    pub lazy: bool,
    pub wmax: usize,
    /// Four recent positions per hash of seven bytes (no chains).
    pub quick: bool,
    /// Positions per hash in quick mode: 4, 8, 16 or 32, the most recent
    /// kept in a ring (`num` counts the insertions per hash).
    pub ways: usize,
    pub num: Vec<u32>,
    /// Hash seven bytes, not four.
    pub h7: bool,
}

#[inline(always)]
fn hash7(data: &[u8], i: usize) -> (r: usize)
    requires
        i + 8 <= data@.len(),
    ensures
        r < 0x10_0000,
{
    let x = verilith_core::prims::load_u64_le(data, i);
    let y = (x << 8u64).wrapping_mul(0x1FE3_5A7B_D357_9BD3);
    assert((y >> 44u64) < 0x10_0000) by (bit_vector);
    (y >> 44u64) as usize
}

#[inline(always)]
fn hash4(data: &[u8], i: usize) -> (r: usize)
    requires
        i + 4 <= data@.len(),
    ensures
        r < 0x10_0000,
{
    let x = load32(data, i);
    let y = x.wrapping_mul(0x1E35_A7BD);
    assert((y >> 12u32) < 0x10_0000) by (bit_vector);
    (y >> 12u32) as usize
}

impl Mf {
    pub fn new(n: usize, depth: u32, lazy: bool, quick: bool, ways: usize, h7: bool, wmax: usize) -> (r: Mf)
        requires
            n < 0xFFFF_FFFF,
            ways == 4 || ways == 8 || ways == 16 || ways == 32,
        ensures
            r.wf(n as nat),
            r.wmax == wmax,
    {
        let head = vec![NONE; 0x10_0000];
        let prev = if quick { Vec::new() } else { vec![NONE; n] };
        let num = vec![0u32; 0x10_0000];
        Mf { head, prev, depth, lazy, wmax, quick, ways, num, h7 }
    }

    pub open spec fn wf(&self, n: nat) -> bool {
        &&& self.head@.len() == 0x10_0000
        &&& !self.quick ==> self.prev@.len() == n
        &&& n < 0xFFFF_FFFF
        &&& (self.ways == 4 || self.ways == 8 || self.ways == 16 || self.ways == 32)
        &&& self.num@.len() == 0x10_0000
    }

    /// Room in the chains for an input of `n` bytes.
    pub fn grow(&mut self, n: usize)
        requires
            old(self).wf((n - 1) as nat),
            n >= 1,
            n < 0xFFFF_FFFF,
        ensures
            final(self).wf(n as nat),
            final(self).wmax == old(self).wmax,
    {
        if !self.quick {
            self.prev.push(NONE);
        }
    }

    #[inline(always)]
    fn insert(&mut self, data: &[u8], i: usize)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            final(self).wmax == old(self).wmax,
    {
        if self.quick {
            if i < data.len() && data.len() - i >= 8 {
                let w = self.ways;
                let h = if self.h7 { hash7(data, i) } else { hash4(data, i) };
                let kx = h / w;
                assert(kx * w <= 0x10_0000 * 32) by (nonlinear_arith) requires kx <= 0x10_0000, w <= 32;
                let c = self.num[kx];
                let idx = kx * w + (c as usize) % w;
                if idx < self.head.len() {
                    self.head.set(idx, i as u32);
                }
                self.num.set(kx, c.wrapping_add(1));
            }
        } else if i < data.len() && data.len() - i >= 4 {
            let h = hash4(data, i);
            self.prev.set(i, self.head[h]);
            self.head.set(h, i as u32);
        }
    }

    /// The best match for `i`, at most `max` long, as (length, distance,
    /// score). The score is google/brotli's: bytes covered against the
    /// bits of the distance.
    fn find(&self, data: &[u8], i: usize, max: usize, last: usize) -> (r: (usize, usize, u64))
        requires
            self.wf(data@.len()),
            i + max <= data@.len(),
            max <= 0xFFFF,
        ensures
            r.0 <= max,
            r.0 > 0 ==> 1 <= r.1 <= i,
            r.2 < 0x1_0000_0000,
    {
        let mut best: usize = 0;
        let mut bd: usize = 0;
        let mut bs: u64 = MIN_SCORE;
        // The last distance first: it is cheap to write.
        if last >= 1 && last <= i && last <= self.wmax && max >= 2 {
            let k = eq_len(data, i - last, i, max);
            if k >= 3 {
                best = k;
                bd = last;
                bs = 1935 + 135 * k as u64;
            }
        }
        if max < 4 {
            return (best, bd, bs);
        }
        if self.quick {
            if data.len() - i < 8 {
                return (best, bd, bs);
            }
            let w = self.ways;
            let h = if self.h7 { hash7(data, i) } else { hash4(data, i) };
            let kx = h / w;
            assert(kx * w <= 0x10_0000 * 32) by (nonlinear_arith) requires kx <= 0x10_0000, w <= 32;
            let key = kx * w;
            if key + w > self.head.len() {
                return (best, bd, bs);
            }
            let top = self.num[kx] as usize;
            let mut j: usize = 0;
            while j < w
                invariant
                    self.wf(data@.len()),
                    i + max <= data@.len(),
                    max <= 0xFFFF,
                    best <= max,
                    best > 0 ==> 1 <= bd <= i,
                    bs < 0x1_0000_0000,
                    w == self.ways,
                    w <= 32,
                    key + w <= 0x10_0000,
                decreases w - j,
            {
                let c = self.head[key + (top % w + w - 1 - j) % w];
                j = j + 1;
                if c == NONE || c as usize >= i {
                    continue;
                }
                let cu = c as usize;
                let dist = i - cu;
                if dist > self.wmax || best >= max || data[cu + best] != data[i + best] {
                    continue;
                }
                let k = eq_len(data, cu, i, max);
                if k >= 4 {
                    let sc = 1920 + 135 * k as u64 - 30 * log2_floor(dist as u32) as u64;
                    if sc > bs {
                        best = k;
                        bd = dist;
                        bs = sc;
                    }
                }
            }
            return (best, bd, bs);
        }
        let h = hash4(data, i);
        let mut c = self.head[h];
        let mut d: u32 = 0;
        while d < self.depth && c != NONE && (c as usize) < i
            invariant
                self.wf(data@.len()),
                i + max <= data@.len(),
                max <= 0xFFFF,
                best <= max,
                best > 0 ==> 1 <= bd <= i,
                bs < 0x1_0000_0000,
                !self.quick,
            decreases self.depth - d,
        {
            let cu = c as usize;
            let dist = i - cu;
            if dist > self.wmax {
                break;
            }
            if best < max && data[cu + best] == data[i + best] {
                let k = eq_len(data, cu, i, max);
                if k >= 4 {
                    let sc = 1920 + 135 * k as u64 - 30 * log2_floor(dist as u32) as u64;
                    if sc > bs {
                        best = k;
                        bd = dist;
                        bs = sc;
                        if k == max {
                            break;
                        }
                    }
                }
            }
            c = self.prev[cu];
            d = d + 1;
        }
        (best, bd, bs)
    }
}

const MIN_SCORE: u64 = 2020;

#[inline(always)]
fn log2_floor(x: u32) -> (r: u32)
    ensures
        r <= 31,
{
    if x == 0 {
        return 0;
    }
    let b = crate::pcode::bitlen_exec(x);
    proof {
        crate::pcode::lemma_bitlen_bound(x as nat);
    }
    if b == 0 { 0 } else if b > 32 { 31 } else { b - 1 }
}

/// The parse of `data[start..end]`.
pub fn parse(mf: &mut Mf, data: &[u8], start: usize, end: usize, last0: usize) -> (r: Vec<Lz>)
    requires
        old(mf).wf(data@.len()),
        start <= end <= data@.len(),
    ensures
        final(mf).wf(data@.len()),
        final(mf).wmax == old(mf).wmax,
{
    let mut out: Vec<Lz> = Vec::new();
    let mut i = start;
    let mut lit = start;
    let mut last = last0;
    while i < end
        invariant
            mf.wf(data@.len()),
            mf.wmax == old(mf).wmax,
            start <= lit <= i <= end <= data@.len(),
        decreases end - i,
    {
        let max = if end - i > 0xFFFF { 0xFFFF } else { end - i };
        let (mut len, mut dist, mut sc) = mf.find(data, i, max, last);
        if len >= 3 && sc > MIN_SCORE {
            // Lazy matching: a later start that scores clearly better wins.
            let mut tries: u32 = 0;
            let ghost i0 = i;
            while mf.lazy && tries < 4 && i + 1 < end && len < 256
                invariant
                    mf.wf(data@.len()),
                    mf.wmax == old(mf).wmax,
                    start <= lit <= i < end <= data@.len(),
                    len <= end - i,
                    len >= 3,
                    1 <= dist <= i,
                    i >= i0,
                    sc < 0x1_0000_0000,
                decreases 4 - tries,
            {
                let max1 = if end - i - 1 > 0xFFFF { 0xFFFF } else { end - i - 1 };
                let (l1, d1, s1) = mf.find(data, i + 1, max1, last);
                if l1 >= 3 && s1 >= sc + 175 {
                    mf.insert(data, i);
                    i = i + 1;
                    len = l1;
                    dist = d1;
                    sc = s1;
                    tries = tries + 1;
                } else {
                    break;
                }
            }
            let ins = (i - lit) as u32;
            out.push(Lz { ins, clen: len as u32, dist: dist as u32 });
            let stop = i + len;
            while i < stop
                invariant
                    mf.wf(data@.len()),
                    mf.wmax == old(mf).wmax,
                    i <= stop <= end <= data@.len(),
                decreases stop - i,
            {
                mf.insert(data, i);
                i = i + 1;
            }
            lit = i;
            last = dist;
        } else {
            mf.insert(data, i);
            i = i + 1;
            // Long runs of literals: probably incompressible, look less
            // (google/brotli's "random heuristics").
            if i - lit > 128 && i < end {
                let step = if i - lit > 512 { 4 } else { 2 };
                let mut j: usize = 1;
                let ghost i1 = i;
                while j < step && i < end
                    invariant
                        mf.wf(data@.len()),
                        mf.wmax == old(mf).wmax,
                        start <= lit <= i <= end <= data@.len(),
                        i >= i1,
                    decreases step - j,
                {
                    i = i + 1;
                    j = j + 1;
                }
            }
        }
    }
    if lit < end {
        out.push(Lz { ins: (end - lit) as u32, clen: 0, dist: 0 });
    }
    out
}

#[inline(always)]
fn bump(f: &mut Vec<u32>, i: usize)
    requires
        i < old(f)@.len(),
    ensures
        final(f)@.len() == old(f)@.len(),
{
    let v = f[i];
    if v < 0xFFFF_FFFF {
        f.set(i, v + 1);
    }
}

/// Symbols and counts for the parse `lz` of `data[start..]`, with last
/// distances `dr`. `None` if a length or distance has no code.
pub fn symbols(lz: &[Lz], data: &[u8], start: usize, dr0: [u32; 4], lf: &mut Vec<u32>, cf: &mut Vec<u32>, df: &mut Vec<u32>) -> (r: Option<Vec<Cmd>>)
    requires
        old(lf)@.len() == 256,
        old(cf)@.len() == 704,
        old(df)@.len() == 64,
    ensures
        final(lf)@.len() == 256,
        final(cf)@.len() == 704,
        final(df)@.len() == 64,
{
    let mut out: Vec<Cmd> = Vec::with_capacity(lz.len());
    let mut dr = dr0;
    let mut q = start;
    let mut i: usize = 0;
    while i < lz.len()
        invariant
            lf@.len() == 256,
            cf@.len() == 704,
            df@.len() == 64,
        decreases lz.len() - i,
    {
        let x = lz[i];
        let ic = match ins_code_of(x.ins) {
            Some(c) => c,
            None => return None,
        };
        // The literals.
        let ins = x.ins as usize;
        if ins > data.len() || q > data.len() - ins {
            return None;
        }
        let mut k = q;
        let qe = q + ins;
        while k < qe
            invariant
                lf@.len() == 256,
                qe <= data@.len(),
            decreases qe - k,
        {
            bump(lf, data[k] as usize);
            k = k + 1;
        }
        q = q + ins;
        if x.dist == 0 {
            let sym = cmd_sym(ic, 0, ic < 8);
            bump(cf, sym as usize);
            out.push(Cmd { ins: x.ins, clen: 2, dist: 0, sym, dcode: 0, extra: 0 });
        } else {
            let cc = match cpy_code_of(x.clen) {
                Some(c) => c,
                None => return None,
            };
            let d = x.dist;
            if d >= 0x100_0000 {
                return None;
            }
            let (sym, dcode, extra) = if d == dr[0] && ic < 8 && cc < 16 {
                (cmd_sym(ic, cc, true), 0u8, 0u32)
            } else {
                let s = cmd_sym(ic, cc, false);
                if d == dr[0] {
                    (s, 0, 0)
                } else if d == dr[1] {
                    (s, 1, 0)
                } else if d == dr[2] {
                    (s, 2, 0)
                } else if d == dr[3] {
                    (s, 3, 0)
                } else {
                    let (dc, ex, _nb) = dist_code(d);
                    (s, dc, ex)
                }
            };
            bump(cf, sym as usize);
            if sym >= 128 {
                bump(df, dcode as usize);
                if dcode != 0 {
                    dr = [d, dr[0], dr[1], dr[2]];
                }
            }
            out.push(Cmd { ins: x.ins, clen: x.clen, dist: d, sym, dcode, extra });
            let cl = x.clen as usize;
            if cl > data.len() || q > data.len() - cl {
                return None;
            }
            q = q + cl;
        }
        i = i + 1;
    }
    Some(out)
}

/// Bits to write symbols with counts `f` and lengths `l`.
fn cost(f: &[u32], l: &[u8]) -> (r: u64)
    ensures
        r < 0x2000_0000_0000_0000,
{
    let mut s: u64 = 0;
    let mut i: usize = 0;
    while i < f.len() && i < l.len()
        invariant
            s < 0x2000_0000_0000_0000,
        decreases f.len() - i,
    {
        let a = f[i] as u64;
        let b = l[i] as u64;
        assert(a * b < 0x100_0000_0000) by (nonlinear_arith) requires a < 0x1_0000_0000, b < 256;
        let x = a * b;
        if s < 0x1000_0000_0000_0000 {
            s = s + x;
        }
        i = i + 1;
    }
    s
}

/// Settings per quality level.
pub struct Params {
    pub depth: u32,
    pub lazy: bool,
    pub quick: bool,
    pub ways: usize,
    pub h7: bool,
    pub block: usize,
}

pub fn params(quality: u32) -> (r: Params)
    ensures
        1 <= r.block <= 0x100_0000,
        r.ways == 4 || r.ways == 8 || r.ways == 16 || r.ways == 32,
{
    if quality <= 2 {
        Params { depth: 1, lazy: false, quick: true, ways: 4, h7: true, block: 0x1_0000 }
    } else if quality <= 4 {
        Params { depth: 8, lazy: true, quick: true, ways: 4, h7: true, block: 0x20_0000 }
    } else if quality <= 6 {
        Params { depth: 32, lazy: true, quick: true, ways: 32, h7: false, block: 0x10_0000 }
    } else if quality <= 9 {
        Params { depth: 64, lazy: true, quick: false, ways: 4, h7: true, block: 0x4_0000 }
    } else {
        Params { depth: 256, lazy: true, quick: false, ways: 4, h7: true, block: 0x4_0000 }
    }
}

/// The window: the smallest `2^wb - 16` that holds the input, from 16 to 24
/// (as google/brotli picks it, `lgwin` at most 24).
pub fn window_bits(n: usize, lgwin: u32) -> (r: u32)
    ensures
        16 <= r <= 24,
{
    let max = if lgwin < 16 { 16 } else if lgwin > 24 { 24 } else { lgwin };
    let mut wb: u32 = 16;
    proof {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, 16);
        crate::elemmas::lemma_pow2_small();
    }
    while wb < max && (shl1(wb) - 16) < n as u64
        invariant
            16 <= wb <= 24,
            max <= 24,
            vstd::arithmetic::power2::pow2(wb as nat) >= 16,
        decreases 24 - wb,
    {
        proof {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(wb as nat, wb as nat + 1);
        }
        wb = wb + 1;
    }
    wb
}

/// One meta-block, compressed if the commands check out and it is smaller,
/// stored otherwise.
pub fn put_block(e: &mut Enc, dr: &mut [u32; 4], wb: u32, data: &[u8], start: usize, end: usize, lz: &[Lz])
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
        final(e).st@.out == data@.subrange(0, end as int),
{
    let mut lf = vec![0u32; 256];
    let mut cf = vec![0u32; 704];
    let mut df = vec![0u32; 64];
    if let Some(cmds) = symbols(lz, data, start, *dr, &mut lf, &mut cf, &mut df) {
        // Every tree needs a symbol.
        if lf[0] == 0 { lf.set(0, 1); }
        if df[0] == 0 { df.set(0, 1); }
        let ll = crate::ehuff::huff_lens(&lf, 15);
        let cl = crate::ehuff::huff_lens(&cf, 15);
        let dl = crate::ehuff::huff_lens(&df, 15);
        // Header estimate: a few bytes per tree plus the lengths.
        let mut bits = cost(&lf, &ll) / 4 + cost(&cf, &cl) / 4 + cost(&df, &dl) / 4;
        bits = bits * 4 + 400;
        let mut k: usize = 0;
        while k < cmds.len()
            decreases cmds.len() - k,
        {
            let c = &cmds[k];
            let (ic, cc) = crate::cwrite::sym_codes_safe(c.sym);
            let ne = if c.sym >= 128 && c.dcode >= 16 { 1 + (c.dcode as u64 - 16) / 2 } else { 0 };
            if bits < 0x1000_0000_0000_0000 {
                bits = bits + crate::spec::INS_EXTRA[ic] as u64 + crate::spec::CPY_EXTRA[cc] as u64 + ne;
            }
            k = k + 1;
        }
        if bits / 8 < (end - start) as u64 {
            let lh = make_code(ll.clone());
            let ch = make_code(cl.clone());
            let dh = make_code(dl.clone());
            let lp = make_plan(&ll);
            let cp = make_plan(&cl);
            let dp = make_plan(&dl);
            if let (Some(lh), Some(ch), Some(dh), Some(lp), Some(cp), Some(dp)) = (lh, ch, dh, lp, cp, dp) {
                if put_compressed(e, dr, wb, data, start, end, &cmds, &lh, &lp, &ch, &cp, &dh, &dp) {
                    return;
                }
            }
        }
    }
    let piece = vstd::slice::slice_subrange(data, start, end);
    e.put_stored(piece);
    proof {
        assert(data@.subrange(0, start as int) + data@.subrange(start as int, end as int) =~= data@.subrange(0, end as int));
    }
}

/// `data` compressed at `quality` (0 to 11) with window `2^lgwin`.
pub fn compress(data: &[u8], quality: u32, lgwin: u32) -> (r: Vec<u8>)
    ensures
        decodes(r@, data@, r@.len() as int),
{
    let n = data.len();
    if n >= 0xFFFF_FFFF {
        return crate::encoder::compress_stored(data);
    }
    let wb = window_bits(n, lgwin);
    let cap = if n <= 0x4000_0000 { n + n / 8 + 1024 } else { n };
    let mut e = Enc::new(wb, cap);
    let mut dr: [u32; 4] = [4, 11, 15, 16];
    let p = params(quality);
    proof {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, wb as nat);
        crate::elemmas::lemma_pow2_small();
    }
    let wmax = (shl1(wb) - 16) as usize;
    let mut mf = Mf::new(n, p.depth, p.lazy, p.quick, p.ways, p.h7, wmax);
    let mut i: usize = 0;
    let mut last: usize = 4;
    proof {
        assert(drs(dr) =~= seq![4int, 11, 15, 16]);
    }
    while i < n
        invariant
            e.ok(),
            e.st@.phase is MetaHeader,
            e.bw.sent() == Seq::<u8>::empty(),
            e.st@.wbits == wb,
            e.st@.dr == drs(dr),
            16 <= wb <= 24,
            i <= n,
            n == data@.len(),
            e.st@.out == data@.subrange(0, i as int),
            mf.wf(n as nat),
            1 <= p.block <= 0x100_0000,
        decreases n - i,
    {
        let k = if n - i > p.block { p.block } else { n - i };
        let lz = parse(&mut mf, data, i, i + k, last);
        put_block(&mut e, &mut dr, wb, data, i, i + k, &lz);
        last = dr[0] as usize;
        i = i + k;
    }
    proof {
        assert(data@.subrange(0, n as int) =~= data@);
    }
    let r = e.finish();
    proof {
        assert(Seq::<u8>::empty() + r@ =~= r@);
    }
    r
}

} // verus!
