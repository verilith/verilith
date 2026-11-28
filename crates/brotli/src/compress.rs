//! The compressor proper: an LZ77 parse (not trusted: every command it
//! makes is checked as it is written, `mbw::put_mb`), a plan for the
//! meta-block (`cplan`, not trusted either), and the proven writers.
use crate::encoder::Enc;
use crate::mblock::*;
#[cfg(verus_only)]
use crate::spec::*;
use verilith_core::lz::{eq_len, load32};
use verilith_core::prims::{get, get32, store_at};
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
    /// Bytes hashed in quick mode: 4, 5 or 7.
    pub hlen: u32,
    /// Binary trees instead of chains (`prev` holds the left children,
    /// `right` the right ones), for optimal parsing.
    pub bt: bool,
    pub right: Vec<u32>,
    /// Static dictionary words by the hash of their first four bytes
    /// (`dict_table`), or empty when the dictionary is not searched.
    pub dict: Vec<u32>,
}

/// Slots per bucket of the dictionary table, and buckets.
pub const DSLOTS: usize = 4;
pub const DBUCKETS: usize = 0x8000;

/// The static dictionary's words, untransformed, by the hash of their first
/// four bytes: `DSLOTS` entries per bucket, each `len << 16 | index` (0 for
/// none), the longest words kept.
pub fn dict_table() -> (r: Vec<u32>)
    ensures
        r@.len() == DSLOTS * DBUCKETS,
{
    let mut t: Vec<u32> = vec![0u32; DSLOTS * DBUCKETS];
    let mut len: usize = 4;
    while len <= 24
        invariant
            4 <= len <= 25,
            t@.len() == DSLOTS * DBUCKETS,
        decreases 25 - len,
    {
        let nb = crate::spec::NDBITS[len] as u32;
        proof {
            assert(forall|k: int| 0 <= k < 25 ==> #[trigger] crate::spec::NDBITS[k] <= 24) by (compute);
            assert(forall|k: int| 0 <= k < 25 ==> #[trigger] crate::spec::DOFFSET[k] <= 122784) by (compute);
            crate::mblock::lemma_shl1_24();
        }
        let n = shl1(nb) as usize;
        let mut idx: usize = 0;
        while idx < n
            invariant
                4 <= len <= 24,
                n <= 0x100_0000,
                t@.len() == DSLOTS * DBUCKETS,
                forall|k: int| 0 <= k < 25 ==> #[trigger] crate::spec::DOFFSET[k] <= 122784,
            decreases n - idx,
        {
            if idx > 0xFFFF {
                break;
            }
            proof {
                assert((idx + 1) * len <= 0x10000 * 24) by (nonlinear_arith) requires idx <= 0xFFFF, len <= 24;
            }
            if (crate::spec::DOFFSET[len] as usize) + (idx + 1) * len > 122784 {
                break;
            }
            let w = crate::words::dict_word(len, idx);
            let h = hash4(w, 0) >> 5;
            let key = h * DSLOTS;
            let e = ((len as u32) << 16) | idx as u32;
            // An empty slot, else the shortest word if this one is longer.
            let mut best: usize = DSLOTS;
            let mut bl: u32 = 0xFFFF_FFFF;
            let mut j: usize = 0;
            while j < DSLOTS
                invariant
                    j <= DSLOTS,
                    key + DSLOTS <= t@.len(),
                    best <= DSLOTS,
                decreases DSLOTS - j,
            {
                let v = t[key + j];
                let vl = v >> 16;
                if v == 0 {
                    if bl != 0 {
                        best = j;
                        bl = 0;
                    }
                } else if vl < bl {
                    best = j;
                    bl = vl;
                }
                j = j + 1;
            }
            if best < DSLOTS && bl < len as u32 {
                t.set(key + best, e);
            }
            idx = idx + 1;
        }
        len = len + 1;
    }
    t
}

/// A hash of the `len` (5 or 7) bytes at `i`.
#[inline(always)]
fn hash_n(data: &[u8], i: usize, len: u64) -> (r: usize)
    requires
        i + 8 <= data@.len(),
        len == 5 || len == 7,
    ensures
        r < 0x10_0000,
{
    let x = verilith_core::prims::load_u64_le(data, i);
    let y = (x << (64 - 8 * len)).wrapping_mul(0x1FE3_5A7B_D357_9BD3);
    assert((y >> 44u64) < 0x10_0000) by (bit_vector);
    (y >> 44u64) as usize
}

#[inline(always)]
pub fn hash4(data: &[u8], i: usize) -> (r: usize)
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
    pub fn new(n: usize, depth: u32, lazy: bool, quick: bool, ways: usize, hlen: u32, wmax: usize, bt: bool, dict: bool) -> (r: Mf)
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
        let bt = bt && !quick;
        let right = if bt { vec![NONE; n] } else { Vec::new() };
        let dict = if dict && !bt { dict_table() } else { Vec::new() };
        Mf { head, prev, depth, lazy, wmax, quick, ways, num, hlen, bt, right, dict }
    }

    pub open spec fn wf(&self, n: nat) -> bool {
        &&& self.head@.len() == 0x10_0000
        &&& !self.quick ==> self.prev@.len() == n
        &&& n < 0xFFFF_FFFF
        &&& (self.ways == 4 || self.ways == 8 || self.ways == 16 || self.ways == 32)
        &&& self.num@.len() == 0x10_0000
        &&& self.bt ==> !self.quick && self.right@.len() == n
        &&& self.dict@.len() == 0 || self.dict@.len() == DSLOTS * DBUCKETS
    }

    #[inline(always)]
    fn hash(&self, data: &[u8], i: usize) -> (r: usize)
        requires
            i + 8 <= data@.len(),
        ensures
            r < 0x10_0000,
    {
        if self.hlen == 5 {
            hash_n(data, i, 5)
        } else if self.hlen == 7 {
            hash_n(data, i, 7)
        } else {
            hash4(data, i)
        }
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
        if self.bt {
            self.right.push(NONE);
        }
    }

    #[inline(always)]
    pub fn insert(&mut self, data: &[u8], i: usize)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            final(self).wmax == old(self).wmax,
    {
        if self.quick {
            if i < data.len() && data.len() - i >= 8 {
                let m = self.ways - 1;
                let h = self.hash(data, i);
                let key = h & !m;
                assert(h & !m < 0x10_0000) by (bit_vector) requires h < 0x10_0000;
                let c = get32(self.num.as_slice(), key);
                let cu = c as usize;
                let idx = key | (cu & m);
                assert((h & !m) | (cu & m) < 0x10_0000) by (bit_vector)
                    requires
                        h < 0x10_0000,
                        m < 32,
                ;
                store_at(&mut self.head, idx, i as u32);
                store_at(&mut self.num, key, c.wrapping_add(1));
            }
        } else if i < data.len() && data.len() - i >= 4 {
            let h = hash4(data, i);
            let hd = get32(self.head.as_slice(), h);
            store_at(&mut self.prev, i, hd);
            store_at(&mut self.head, h, i as u32);
        }
    }

    /// The best match for `i`, at most `max` long, as (length, distance,
    /// score). The score is google/brotli's: bytes covered against the
    /// bits of the distance.
    fn find(&self, data: &[u8], i: usize, max: usize, last: usize, usedict: bool) -> (r: (usize, usize, u64))
        requires
            self.wf(data@.len()),
            i + max <= data@.len(),
            max <= 0xFFFF,
        ensures
            r.0 <= max,
            r.0 > 0 ==> 1 <= r.1,
            r.2 < 0x1_0000_0000,
    {
        let (best, bd, bs) = self.find_lz(data, i, max, last);
        if best > 0 || !usedict || self.dict.len() == 0 || max < 4 || data.len() - i < 4 {
            return (best, bd, bs);
        }
        // A static dictionary word, when no long match was found.
        let maxd = if i < self.wmax { i } else { self.wmax };
        let key = (hash4(data, i) >> 5) * DSLOTS;
        let mut best = best;
        let mut bd = bd;
        let mut bs = bs;
        let mut j: usize = 0;
        while j < DSLOTS
            invariant
                self.wf(data@.len()),
                self.dict@.len() == DSLOTS * DBUCKETS,
                key + DSLOTS <= self.dict@.len(),
                i + max <= data@.len(),
                max <= 0xFFFF,
                best <= max,
                best > 0 ==> 1 <= bd,
                bs < 0x1_0000_0000,
            decreases DSLOTS - j,
        {
            let e = self.dict[key + j];
            j = j + 1;
            let len = (e >> 16) as usize;
            let idx = (e & 0xFFFF) as usize;
            if e == 0 || len < 4 || len > 24 || len > max || len <= best {
                continue;
            }
            proof {
                assert(forall|k: int| 0 <= k < 25 ==> #[trigger] crate::spec::DOFFSET[k] <= 122784) by (compute);
                assert((idx + 1) * len <= 0x10000 * 24) by (nonlinear_arith) requires idx <= 0xFFFF, len <= 24;
            }
            if (crate::spec::DOFFSET[len] as usize) + (idx + 1) * len > 122784 {
                continue;
            }
            let w = crate::words::dict_word(len, idx);
            let mut k: usize = 0;
            while k < len && get(data, i + k) == get(w, k)
                invariant
                    k <= len,
                    len <= max,
                    i + max <= data@.len(),
                    w@.len() == len,
                decreases len - k,
            {
                k = k + 1;
            }
            if k < len || maxd >= 0x100_0000 - 0x10000 {
                continue;
            }
            let d = maxd + 1 + idx;
            let sc = 1920 + 135 * len as u64 - 30 * log2_floor(d as u32) as u64;
            if sc > bs {
                best = len;
                bd = d;
                bs = sc;
            }
        }
        (best, bd, bs)
    }

    /// The best backward match, as `find`.
    fn find_lz(&self, data: &[u8], i: usize, max: usize, last: usize) -> (r: (usize, usize, u64))
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
            let m = w - 1;
            let h = self.hash(data, i);
            let key = h & !m;
            assert(h & !m < 0x10_0000) by (bit_vector) requires h < 0x10_0000;
            let top = get32(self.num.as_slice(), key) as usize;
            let x4 = load32(data, i);
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
                    m == w - 1,
                    key == h & !m,
                    h < 0x10_0000,
                decreases w - j,
            {
                let t = top.wrapping_sub(1 + j);
                let slot = key | (t & m);
                assert(key | (t & m) < 0x10_0000) by (bit_vector)
                    requires
                        key == h & !m,
                        h < 0x10_0000,
                        m < 32,
                ;
                let c = get32(self.head.as_slice(), slot);
                j = j + 1;
                if c == NONE || c as usize >= i {
                    continue;
                }
                let cu = c as usize;
                let dist = i - cu;
                // Matches shorter than four bytes are not taken: four
                // bytes at once rule out most candidates.
                if dist > self.wmax || best >= max || load32(data, cu) != x4 || get(data, cu + best) != get(data, i + best) {
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
        let x4 = load32(data, i);
        let mut c = get32(self.head.as_slice(), h);
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
            if best < max && load32(data, cu) == x4 && get(data, cu + best) == get(data, i + best) {
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
            c = get32(self.prev.as_slice(), cu);
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
    let z = x.leading_zeros();
    if z >= 31 { 0 } else { 31 - z }
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
    // Past `rh` with no match, look less often (google/brotli's "random
    // heuristics": that data is probably not compressible).
    let mut rh = if start < usize::MAX - 64 { start + 64 } else { start };
    let mut looks: u32 = 0;
    let mut hits: u32 = 0;
    while i < end
        invariant
            mf.wf(data@.len()),
            mf.wmax == old(mf).wmax,
            start <= lit <= i <= end <= data@.len(),
        decreases end - i,
    {
        let max = if end - i > 0xFFFF { 0xFFFF } else { end - i };
        // The dictionary is searched while it finds words (google/brotli
        // stops below one hit in 128 lookups, after the first 1024).
        let usedict = looks < 1024 || hits >= looks / 128;
        let (mut len, mut dist, mut sc) = mf.find(data, i, max, last, usedict);
        if usedict && mf.dict.len() > 0 {
            if looks < 0xFFFF_FFFF {
                looks = looks + 1;
            }
            let maxd = if i < mf.wmax { i } else { mf.wmax };
            if len > 0 && dist > maxd && hits < 0xFFFF_FFFF {
                hits = hits + 1;
            }
        }
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
                    1 <= dist,
                    i >= i0,
                    sc < 0x1_0000_0000,
                decreases 4 - tries,
            {
                let max1 = if end - i - 1 > 0xFFFF { 0xFFFF } else { end - i - 1 };
                let (l1, d1, s1) = mf.find(data, i + 1, max1, last, usedict);
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
            rh = if len <= usize::MAX - 64 && stop <= usize::MAX - len - 64 { stop + len + 64 } else { stop };
            mf.insert(data, i);
            // A long copy from close by: only its end is worth hashing.
            let mut k = i + 1;
            if dist < len / 4 && stop - k > 4 * dist {
                k = stop - 4 * dist;
            }
            while k < stop
                invariant
                    mf.wf(data@.len()),
                    mf.wmax == old(mf).wmax,
                    k <= stop <= end <= data@.len(),
                decreases stop - k,
            {
                mf.insert(data, k);
                k = k + 1;
            }
            // A dictionary word leaves the last distance as it was.
            let maxd = if i < mf.wmax { i } else { mf.wmax };
            i = stop;
            lit = i;
            if dist <= maxd {
                last = dist;
            }
        } else {
            mf.insert(data, i);
            i = i + 1;
            if i > rh {
                let far = rh < usize::MAX - 256 && i > rh + 256;
                let (span, every): (usize, usize) = if far { (16, 4) } else { (8, 2) };
                let jump = if end - i > span + 8 { i + span } else { i };
                let ghost i1 = i;
                while i < jump
                    invariant
                        mf.wf(data@.len()),
                        mf.wmax == old(mf).wmax,
                        start <= lit <= i <= jump <= end <= data@.len(),
                        i >= i1,
                        every >= 2,
                    decreases jump - i,
                {
                    mf.insert(data, i);
                    i = if jump - i > every { i + every } else { jump };
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
pub fn symbols(lz: &[Lz], data: &[u8], start: usize, dr0: [u32; 4], wmax: usize, lf: &mut Vec<u32>, cf: &mut Vec<u32>, df: &mut Vec<u32>) -> (r: Option<Vec<Cmd>>)
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
            // Past the window: a dictionary word, with an explicit code.
            let p = q;
            let maxd = if p < wmax { p } else { wmax };
            let dict = d as usize > maxd;
            let (sym, dcode, extra) = if dict {
                let (dc, ex, _nb) = dist_code(d);
                (cmd_sym(ic, cc, false), dc, ex)
            } else if d == dr[0] && ic < 8 && cc < 16 {
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
                if dcode != 0 && !dict {
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
#[derive(Clone)]
pub struct Params {
    pub depth: u32,
    pub lazy: bool,
    pub quick: bool,
    pub ways: usize,
    pub hlen: u32,
    pub block: usize,
    /// Optimal parsing (`optparse`).
    pub opt: bool,
    /// Search the static dictionary.
    pub dict: bool,
    /// The meta-block planner's settings (`cplan`); no context modes to
    /// try means one block type and one tree per category.
    pub k: crate::cplan::Knobs,
}

pub fn params(quality: u32) -> (r: Params)
    ensures
        1 <= r.block <= 0x100_0000,
        r.ways == 4 || r.ways == 8 || r.ways == 16 || r.ways == 32,
{
    if quality <= 2 {
        Params { depth: 1, lazy: false, quick: true, ways: 4, hlen: 7, block: 0x1_0000, opt: false, dict: true, k: crate::cplan::Knobs { modes: 0, maxt: 1, maxb: 1, maxch: 1, minch: 128 } }
    } else if quality <= 4 {
        Params { depth: 8, lazy: true, quick: true, ways: 4, hlen: 7, block: 0x20_0000, opt: false, dict: true, k: crate::cplan::Knobs { modes: 0, maxt: 1, maxb: 1, maxch: 1, minch: 128 } }
    } else if quality <= 6 {
        Params { depth: 32, lazy: true, quick: true, ways: if quality == 5 { 16 } else { 32 }, hlen: 5, block: 0x10_0000, opt: false, dict: true, k: crate::cplan::Knobs { modes: 15, maxt: 64, maxb: 8, maxch: 64, minch: 128 } }
    } else if quality <= 9 {
        Params { depth: 64, lazy: true, quick: false, ways: 4, hlen: 7, block: 0x4_0000, opt: false, dict: true, k: crate::cplan::Knobs { modes: 15, maxt: 64, maxb: 8, maxch: 64, minch: 128 } }
    } else {
        Params { depth: if quality == 10 { 32 } else { 64 }, lazy: true, quick: false, ways: 4, hlen: 7, block: 0x4_0000, opt: true, dict: false, k: crate::cplan::Knobs { modes: 15, maxt: 64, maxb: 16, maxch: 128, minch: 128 } }
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
pub fn put_block(e: &mut Enc, dr: &mut [u32; 4], wb: u32, data: &[u8], start: usize, end: usize, lz: &[Lz], kn: &crate::cplan::Knobs)
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
    proof {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, wb as nat);
    }
    let wmax = (shl1(wb) - 16) as usize;
    if let Some(cmds) = symbols(lz, data, start, *dr, wmax, &mut lf, &mut cf, &mut df) {
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
            let plan = if kn.modes != 0 {
                crate::cplan::plan_full(data, start, end, &cmds, kn)
            } else {
                crate::cplan::plan_single(&lf, &cf, &df)
            };
            if crate::mbw::put_mb(e, dr, wb, data, start, end, &cmds, &plan) {
                return;
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
    let p = params(quality);
    compress_with(data, p, lgwin)
}

/// `data` compressed with the settings `p`.
pub fn compress_with(data: &[u8], p: Params, lgwin: u32) -> (r: Vec<u8>)
    requires
        1 <= p.block <= 0x100_0000,
        p.ways == 4 || p.ways == 8 || p.ways == 16 || p.ways == 32,
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
    proof {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, wb as nat);
        crate::elemmas::lemma_pow2_small();
    }
    let wmax = (shl1(wb) - 16) as usize;
    let mut mf = Mf::new(n, p.depth, p.lazy, p.quick, p.ways, p.hlen, wmax, p.opt, p.dict);
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
        let lz = if p.opt { crate::optparse::parse_opt(&mut mf, data, i, i + k, dr) } else { parse(&mut mf, data, i, i + k, last) };
        put_block(&mut e, &mut dr, wb, data, i, i + k, &lz, &p.k);
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
