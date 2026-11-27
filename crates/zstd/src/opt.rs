//! The optimal parser (libzstd's btopt and btultra): matches from a
//! binary tree, then the cheapest way through each stretch of the input
//! by the bit prices of literals and sequences, from statistics carried
//! from block to block.
//!
//! As for the other match finders, only memory safety and termination are
//! proven here: every block it makes is decoded by the proven decoder and
//! compared with the input before it is kept (`compress::comp_block`).
use crate::enc::*;
use crate::ent::*;
use verilith_core::lz::eq_len;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The nodes of one stretch (libzstd's `ZSTD_OPT_NUM`).
pub const NODES: usize = 4096;
/// The price of a node not reached yet.
pub const INF: u32 = 0x3FFF_FFFF;

pub struct OptState {
    /// Frequencies: literals, literals length codes, match length codes,
    /// offset codes.
    pub lit_f: Vec<u32>,
    pub ll_f: Vec<u32>,
    pub ml_f: Vec<u32>,
    pub of_f: Vec<u32>,
    /// Their prices, in 1/256 bits.
    pub lit_p: Vec<u32>,
    pub ll_p: Vec<u32>,
    pub ml_p: Vec<u32>,
    pub of_p: Vec<u32>,
    /// Per node: price so far (literals since the last match not yet
    /// charged their length code), the match that ends here (0: a
    /// literal), its offset, the literals since the last match, and the
    /// repeat offsets after it.
    pub price: Vec<u32>,
    pub mlen: Vec<u32>,
    pub moff: Vec<u32>,
    pub litlen: Vec<u32>,
    pub ra: Vec<u32>,
    pub rb: Vec<u32>,
    pub rc: Vec<u32>,
    /// The matches at one position, longer and longer.
    pub ml: Vec<u32>,
    pub mo: Vec<u32>,
    /// The path found, backwards: start node, length, offset.
    pub ps: Vec<u32>,
    pub pl: Vec<u32>,
    pub po: Vec<u32>,
    /// A match at least this long is taken at once.
    pub tlen: usize,
    /// Statistics have been gathered (from an earlier block).
    pub started: bool,
    /// Bytes coded since the prices were last worked out.
    pub since: usize,
}

const BASE_LL: [u32; 36] = [4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
const BASE_OF: [u32; 32] = [6, 2, 1, 1, 2, 3, 4, 4, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

impl OptState {
    pub open spec fn wf(&self) -> bool {
        &&& self.lit_f@.len() == 256
        &&& self.ll_f@.len() == 36
        &&& self.ml_f@.len() == 53
        &&& self.of_f@.len() == 32
        &&& self.lit_p@.len() == 256
        &&& self.ll_p@.len() == 36
        &&& self.ml_p@.len() == 53
        &&& self.of_p@.len() == 32
        &&& self.price@.len() == NODES + 1
        &&& self.mlen@.len() == NODES + 1
        &&& self.moff@.len() == NODES + 1
        &&& self.litlen@.len() == NODES + 1
        &&& self.ra@.len() == NODES + 1
        &&& self.rb@.len() == NODES + 1
        &&& self.rc@.len() == NODES + 1
        &&& self.ml@.len() == self.mo@.len()
    }

    pub fn new(tlen: usize) -> (r: OptState)
        ensures
            r.wf(),
    {
        OptState {
            lit_f: vec![1u32; 256],
            ll_f: vec![1u32; 36],
            ml_f: vec![1u32; 53],
            of_f: vec![1u32; 32],
            lit_p: vec![0u32; 256],
            ll_p: vec![0u32; 36],
            ml_p: vec![0u32; 53],
            of_p: vec![0u32; 32],
            price: vec![0u32; NODES + 1],
            mlen: vec![0u32; NODES + 1],
            moff: vec![0u32; NODES + 1],
            litlen: vec![0u32; NODES + 1],
            ra: vec![0u32; NODES + 1],
            rb: vec![0u32; NODES + 1],
            rc: vec![0u32; NODES + 1],
            ml: Vec::new(),
            mo: Vec::new(),
            ps: Vec::new(),
            pl: Vec::new(),
            po: Vec::new(),
            tlen,
            started: false,
            since: 0,
        }
    }
}

/// Prices from frequencies: `log2(sum / f)` in 1/256 bits.
fn prices(f: &Vec<u32>, p: &mut Vec<u32>)
    requires
        f@.len() == old(p)@.len(),
        f@.len() <= 256,
    ensures
        final(p)@.len() == old(p)@.len(),
{
    let n = f.len();
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == f@.len(),
            n <= 256,
            sum <= i * 0x1_0000_0000,
        decreases n - i,
    {
        sum = sum + f[i] as u64;
        i = i + 1;
    }
    let ls = log2_256(if sum > 0xFFFF_FFFF { 0xFFFF_FFFF } else { sum as u32 });
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == f@.len(),
            p@.len() == n,
        decreases n - i,
    {
        let l = log2_256(f[i]);
        // A symbol costs at least an eighth of a bit.
        p.set(i, if ls > l + 32 { ls - l } else { 32 });
        i = i + 1;
    }
}

/// Rescales frequencies to sum near `2^11`, each at least 1.
fn rescale(f: &mut Vec<u32>)
    requires
        old(f)@.len() <= 256,
    ensures
        final(f)@.len() == old(f)@.len(),
{
    let n = f.len();
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == f@.len(),
            n <= 256,
            sum <= i * 0x1_0000_0000,
        decreases n - i,
    {
        sum = sum + f[i] as u64;
        i = i + 1;
    }
    let mut sh: u32 = 0;
    while sh < 31 && (sum >> sh) > 2048
        invariant
            sh <= 31,
        decreases 31 - sh,
    {
        sh = sh + 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == f@.len(),
            sh <= 31,
        decreases n - i,
    {
        let v = f[i] >> sh;
        f.set(i, if v < 0xFFFF_FFFF { v + 1 } else { v });
        i = i + 1;
    }
}

/// Adds `k` to a frequency, saturating.
#[inline(always)]
fn bump(f: &mut Vec<u32>, i: usize, k: u32)
    requires
        i < old(f)@.len(),
        k <= 16,
    ensures
        final(f)@.len() == old(f)@.len(),
{
    let v = f[i];
    if v < 0x1000_0000 {
        f.set(i, v + k);
    }
}

/// The offset value of a match `o` back, and the repeat offsets after
/// it, from repeat offsets `a`, `b`, `c` (with `ll0`: no literals before
/// it), as the decoder keeps them (RFC 8878 3.1.2.5).
#[inline(always)]
pub fn rep_step(o: u32, ll0: bool, a: u32, b: u32, c: u32) -> (r: (u64, u32, u32, u32))
    ensures
        1 <= r.0 <= o as u64 + 3,
{
    if !ll0 {
        if o == a {
            (1, a, b, c)
        } else if o == b {
            (2, b, a, c)
        } else if o == c {
            (3, c, a, b)
        } else {
            (o as u64 + 3, o, a, b)
        }
    } else {
        if o == b {
            (1, b, a, c)
        } else if o == c {
            (2, c, a, b)
        } else if a > 1 && o == a - 1 {
            (3, o, a, b)
        } else {
            (o as u64 + 3, o, a, b)
        }
    }
}

#[inline(always)]
fn add_p(a: u32, b: u32) -> (r: u32)
    ensures
        r <= INF,
{
    let s = a as u64 + b as u64;
    if s >= INF as u64 {
        INF
    } else {
        s as u32
    }
}

impl Enc {
    /// The price of `l` literals' length code.
    #[inline(always)]
    fn ll_price(&self, l: u32) -> (r: u32)
        requires
            self.wf(),
    {
        let c = ll_code(l) as usize;
        add_p(LL_BITS[c] as u32 * 256, self.op.ll_p[c])
    }

    /// The price of a sequence's offset value `ob` and match length `m`.
    #[inline(always)]
    fn match_price(&self, ob: u64, m: u32) -> (r: u32)
        requires
            self.wf(),
    {
        let oc = hbit(if ob > 0xFFFF_FFFF { 0xFFFF_FFFF } else { ob as u32 }) as usize;
        let mc = ml_code(m) as usize;
        add_p(add_p(oc as u32 * 256, self.op.of_p[oc]), add_p(ML_BITS[mc] as u32 * 256, self.op.ml_p[mc]))
    }

    fn refresh(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
    {
        prices(&self.op.lit_f, &mut self.op.lit_p);
        prices(&self.op.ll_f, &mut self.op.ll_p);
        prices(&self.op.ml_f, &mut self.op.ml_p);
        prices(&self.op.of_f, &mut self.op.of_p);
        self.op.since = 0;
    }

    /// Statistics for a new block: the first from its bytes and
    /// libzstd's starting distributions, later ones scaled down.
    fn stats_start(&mut self, src: &[u8], pos: usize, end: usize)
        requires
            old(self).wf(),
            pos <= end <= src@.len(),
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
    {
        if !self.op.started {
            let mut i: usize = 0;
            while i < 256
                invariant
                    i <= 256,
                    self.wf(),
                decreases 256 - i,
            {
                self.op.lit_f.set(i, 0);
                i = i + 1;
            }
            let mut p = pos;
            while p < end
                invariant
                    pos <= p <= end,
                    end <= src@.len(),
                    self.wf(),
                decreases end - p,
            {
                let b = src[p] as usize;
                bump(&mut self.op.lit_f, b, 1);
                p = p + 1;
            }
            let mut i: usize = 0;
            while i < 256
                invariant
                    i <= 256,
                    self.wf(),
                decreases 256 - i,
            {
                let v = self.op.lit_f[i];
                self.op.lit_f.set(i, v / 16 + 1);
                i = i + 1;
            }
            let mut i: usize = 0;
            while i < 36
                invariant
                    i <= 36,
                    self.wf(),
                decreases 36 - i,
            {
                self.op.ll_f.set(i, BASE_LL[i]);
                i = i + 1;
            }
            let mut i: usize = 0;
            while i < 53
                invariant
                    i <= 53,
                    self.wf(),
                decreases 53 - i,
            {
                self.op.ml_f.set(i, 1);
                i = i + 1;
            }
            let mut i: usize = 0;
            while i < 32
                invariant
                    i <= 32,
                    self.wf(),
                decreases 32 - i,
            {
                self.op.of_f.set(i, BASE_OF[i]);
                i = i + 1;
            }
            self.op.started = true;
        } else {
            rescale(&mut self.op.lit_f);
            rescale(&mut self.op.ll_f);
            rescale(&mut self.op.ml_f);
            rescale(&mut self.op.of_f);
        }
        self.refresh();
    }

    /// Counts a sequence into the statistics: `ll` literals from `lit`,
    /// then a match of `m` with offset value `ob`.
    fn count_seq(&mut self, src: &[u8], lit: usize, s: usize, m: usize, ob: u64)
        requires
            old(self).wf(),
            lit <= s <= src@.len(),
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
            final(self).op.ps@ == old(self).op.ps@,
            final(self).op.pl@ == old(self).op.pl@,
            final(self).op.po@ == old(self).op.po@,
    {
        let ll = s - lit;
        let mut i: usize = lit;
        while i < s
            invariant
                lit <= i <= s,
                s <= src@.len(),
                self.wf(),
                self.base == old(self).base,
                self.op.ps@ == old(self).op.ps@,
                self.op.pl@ == old(self).op.pl@,
                self.op.po@ == old(self).op.po@,
            decreases s - i,
        {
            let b = src[i] as usize;
            bump(&mut self.op.lit_f, b, 2);
            i = i + 1;
        }
        let lc = ll_code(if ll > 0x20000 { 0x20000 } else { ll as u32 }) as usize;
        bump(&mut self.op.ll_f, lc, 1);
        let mc = ml_code(if m > 0x20000 { 0x20000 } else { m as u32 }) as usize;
        bump(&mut self.op.ml_f, mc, 1);
        let oc = hbit(if ob > 0xFFFF_FFFF { 0xFFFF_FFFF } else { ob as u32 }) as usize;
        bump(&mut self.op.of_f, oc, 1);
        self.op.since = if self.op.since < 0x1000_0000 && ll < 0x1000_0000 { self.op.since + ll + 1 } else { self.op.since };
    }

    /// Inserts `ip` into the binary tree and, with `collect`, adds the
    /// matches longer than `best` to `op.ml`/`op.mo` (libzstd's
    /// `ZSTD_insertBtAndGetAllMatches`). Tree entries are positions minus
    /// `base` plus 1; 0 is none. The longest length found.
    #[verifier::loop_isolation(false)]
    fn bt(&mut self, src: &[u8], ip: usize, end: usize, best0: usize, collect: bool) -> (r: usize)
        requires
            old(self).wf(),
            ip + 8 <= end <= src@.len(),
            old(self).base <= ip,
            ip - old(self).base < 0xC002_0000,
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
    {
        let h = hash(src, ip, self.mls, self.hlog);
        let cur: usize = ip - self.base + 1;
        let mut m = self.t1[h] as usize;
        self.t1.set(h, cur as u32);
        let nodes = self.t2.len() / 2;
        if nodes == 0 {
            return 0;
        }
        let bmask = nodes - 1;
        let ci = cur & bmask;
        proof {
            assert(cur & bmask <= bmask) by (bit_vector);
        }
        // Where the smaller and larger subtrees are to be linked; `none`
        // once a side is closed.
        let none = self.t2.len();
        let mut sp: usize = 2 * ci;
        let mut lp: usize = 2 * ci + 1;
        let mut cls: usize = 0;
        let mut cll: usize = 0;
        let btlow: usize = if cur > bmask { cur - bmask } else { 0 };
        let wlow: usize = if cur > self.window { cur - self.window } else { 0 };
        let lim = end - ip;
        let mut best = best0;
        let mut n: u32 = 1u32 << self.slog;
        while n > 0 && m > wlow && m > btlow && m < cur
            invariant
                self.wf(),
                sp <= none,
                lp <= none,
                none == self.t2@.len(),
                cls <= lim,
                cll <= lim,
                lim == end - ip,
                cur == ip - self.base + 1,
                bmask == nodes - 1,
                2 * nodes <= none,
            decreases n,
        {
            n = n - 1;
            let mpos = self.base + m - 1;
            let mi = m & bmask;
            proof {
                assert(m & bmask <= bmask) by (bit_vector);
            }
            let ni = 2 * mi;
            let mut l = if cls < cll { cls } else { cll };
            l = l + eq_len(src, ip + l, mpos + l, lim - l);
            if l > best {
                best = l;
                if collect {
                    self.op.ml.push(l as u32);
                    self.op.mo.push((ip - mpos) as u32);
                }
                if l == lim || l > NODES {
                    // The tree cannot be kept ordered past the end.
                    break;
                }
            }
            if l == lim {
                break;
            }
            if src[mpos + l] < src[ip + l] {
                if sp < none {
                    self.t2.set(sp, m as u32);
                }
                cls = l;
                if m <= btlow {
                    sp = none;
                    break;
                }
                sp = ni + 1;
                m = self.t2[ni + 1] as usize;
            } else {
                if lp < none {
                    self.t2.set(lp, m as u32);
                }
                cll = l;
                if m <= btlow {
                    lp = none;
                    break;
                }
                lp = ni;
                m = self.t2[ni] as usize;
            }
        }
        if sp < none {
            self.t2.set(sp, 0);
        }
        if lp < none {
            self.t2.set(lp, 0);
        }
        best
    }

    /// Inserts the positions from `next` up to `ip` (exclusive) into the
    /// tree, skipping ahead inside long matches as libzstd does.
    #[verifier::loop_isolation(false)]
    fn bt_update(&mut self, src: &[u8], ip: usize, end: usize)
        requires
            old(self).wf(),
            ip + 8 <= end <= src@.len(),
            old(self).base <= ip,
            ip - old(self).base < 0xC002_0000,
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
    {
        if self.next < self.base || self.next > ip {
            self.next = ip;
        }
        let mut p = self.next;
        while p < ip
            invariant
                self.wf(),
                self.base <= p,
                ip + 8 <= end <= src@.len(),
                self.base == old(self).base,
            decreases ip - p,
        {
            let b = self.bt(src, p, end, 0, false);
            let skip = if b > 384 {
                if b - 384 < 192 { b - 384 } else { 192 }
            } else {
                1
            };
            p = if ip - p > skip { p + skip } else { ip };
        }
        self.next = ip;
    }

    /// The matches at `ip` into `op.ml`/`op.mo`, longer and longer: the
    /// repeat offsets (`a`, `b`, `c`, with `ll0`), then the tree's.
    /// The longest length.
    #[verifier::loop_isolation(false)]
    fn matches(&mut self, src: &[u8], ip: usize, end: usize, ll0: bool, a: u32, b: u32, c: u32) -> (r: usize)
        requires
            old(self).wf(),
            ip + 8 <= end <= src@.len(),
            old(self).base <= ip,
            ip - old(self).base < 0xC002_0000,
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
    {
        self.op.ml.clear();
        self.op.mo.clear();
        let lim = end - ip;
        let mut best: usize = 2;
        let mut k: u32 = 0;
        while k < 3
            invariant
                self.wf(),
                self.base == old(self).base,
                lim == end - ip,
            decreases 3 - k,
        {
            let o: u32 = if !ll0 {
                if k == 0 { a } else if k == 1 { b } else { c }
            } else {
                if k == 0 { b } else if k == 1 { c } else if a > 1 { a - 1 } else { 0 }
            };
            let ou = o as usize;
            if self.off_ok(ip, ou) {
                let l = eq_len(src, ip, ip - ou, lim);
                if l > best {
                    best = l;
                    self.op.ml.push(l as u32);
                    self.op.mo.push(o);
                }
            }
            k = k + 1;
        }
        if best >= self.op.tlen || best == lim {
            return best;
        }
        // Positions already in the tree are not searched again.
        if ip < self.next && self.next >= self.base {
            return if self.op.ml.len() > 0 { best } else { 0 };
        }
        self.bt_update(src, ip, end);
        let b2 = self.bt(src, ip, end, best, true);
        self.next = ip + 1;
        if self.op.ml.len() > 0 {
            if b2 > best { b2 } else { best }
        } else {
            0
        }
    }

    /// Relaxes the nodes reached from node `cur` (at `ip + cur`) by the
    /// matches in `op.ml`/`op.mo`. `last`: the furthest node set.
    #[verifier::loop_isolation(false)]
    fn relax(&mut self, cur: usize, last: usize, end_room: usize) -> (r: usize)
        requires
            old(self).wf(),
            cur <= last <= NODES,
        ensures
            final(self).wf(),
            final(self).base == old(self).base,
            cur <= r <= NODES,
            r >= last,
    {
        let ghost last0 = last;
        let mut last = last;
        let base_p = add_p(self.op.price[cur], self.ll_price(self.op.litlen[cur]));
        let ll0 = self.op.litlen[cur] == 0;
        let ra = self.op.ra[cur];
        let rb = self.op.rb[cur];
        let rc = self.op.rc[cur];
        let nm = self.op.ml.len();
        let mut prev: usize = 2;
        let mut j: usize = 0;
        while j < nm
            invariant
                self.wf(),
                self.base == old(self).base,
                nm == self.op.ml@.len(),
                cur <= last <= NODES,
                last >= last0,
                j <= nm,
                2 <= prev <= 0x1000_0000,
            decreases nm - j,
        {
            let len = self.op.ml[j] as usize;
            let o = self.op.mo[j];
            let (ob, na, nb, nc) = rep_step(o, ll0, ra, rb, rc);
            let mut m = prev + 1;
            let top = if len < end_room { len } else { end_room };
            while m <= top && m <= NODES - cur
                invariant
                    self.wf(),
                    self.base == old(self).base,
                    cur <= last <= NODES,
                    last >= last0,
                    m >= 3,
                decreases top + 1 - m,
            {
                let p = cur + m;
                while last < p
                    invariant
                        self.wf(),
                        self.base == old(self).base,
                        cur <= last <= NODES,
                        last >= last0,
                        p <= NODES,
                    decreases p - last,
                {
                    last = last + 1;
                    self.op.price.set(last, INF);
                }
                let np = add_p(base_p, self.match_price(ob, m as u32));
                let old_cost = add_p(self.op.price[p], self.ll_price(self.op.litlen[p]));
                let new_cost = add_p(np, self.ll_price(0));
                if new_cost < old_cost {
                    self.op.price.set(p, np);
                    self.op.mlen.set(p, m as u32);
                    self.op.moff.set(p, o);
                    self.op.litlen.set(p, 0);
                    self.op.ra.set(p, na);
                    self.op.rb.set(p, nb);
                    self.op.rc.set(p, nc);
                }
                m = m + 1;
            }
            if len > prev && len <= 0x1000_0000 {
                prev = len;
            }
            j = j + 1;
        }
        last
    }

    /// The optimal parser over `src[pos..end]`, the repeat offsets at its
    /// start being `r1`, `r2`, `r3`.
    #[verifier::loop_isolation(false)]
    pub fn opt(&mut self, src: &[u8], pos: usize, end: usize, r1: u64, r2: u64, r3: u64)
        requires
            old(self).wf(),
            pos < end <= src@.len(),
            pos >= old(self).base,
            pos - old(self).base < 0xC000_0000,
            end - pos <= 0x20000,
        ensures
            final(self).wf(),
    {
        let base0 = self.base;
        self.stats_start(src, pos, end);
        let mut a: u32 = if r1 <= 0x8000_0000 { r1 as u32 } else { 0 };
        let mut b: u32 = if r2 <= 0x8000_0000 { r2 as u32 } else { 0 };
        let mut c: u32 = if r3 <= 0x8000_0000 { r3 as u32 } else { 0 };
        let mut anchor = pos;
        let mut ip = if pos == 0 { 1 } else { pos };
        if end - pos >= 16 {
            let ilimit = end - 8;
            while ip < ilimit
                invariant
                    self.wf(),
                    self.base == base0,
                    anchor <= ip,
                    ip <= end,
                    pos <= anchor,
                    ilimit == end - 8,
                    end <= src@.len(),
                    self.base <= pos,
                    end - self.base < 0xC002_0000,
                decreases end - ip,
            {
                let lb = self.matches(src, ip, end, ip == anchor, a, b, c);
                let nm = self.op.ml.len();
                if nm == 0 {
                    ip = ip + 1;
                    continue;
                }
                // A match taken at once: from node `tcur`, `tml` long.
                let mut tail = false;
                let mut tcur: usize = 0;
                let mut tml: usize = 0;
                let mut toff: u32 = 0;
                let mut last: usize = 0;
                self.op.price.set(0, 0);
                self.op.mlen.set(0, 0);
                self.op.litlen.set(0, (ip - anchor) as u32);
                self.op.ra.set(0, a);
                self.op.rb.set(0, b);
                self.op.rc.set(0, c);
                if lb >= self.op.tlen || lb > NODES {
                    tail = true;
                    tml = self.op.ml[nm - 1] as usize;
                    toff = self.op.mo[nm - 1];
                } else {
                    last = self.relax(0, 0, end - ip);
                    let mut cur: usize = 1;
                    while cur <= last
                        invariant
                            self.wf(),
                            self.base == base0,
                            1 <= cur <= NODES,
                            last <= NODES,
                            tcur <= NODES,
                            anchor <= ip < ilimit,
                            ilimit == end - 8,
                            end <= src@.len(),
                            self.base <= pos <= ip,
                            end - self.base < 0xC002_0000,
                        decreases NODES + 1 - cur,
                    {
                        // A literal from the node before.
                        if cur - 1 < end - ip {
                            let lit = src[ip + cur - 1] as usize;
                            let pl = self.op.litlen[cur - 1];
                            let nl = if pl < 0x10_0000 { pl + 1 } else { pl };
                            let np = add_p(self.op.price[cur - 1], self.op.lit_p[lit]);
                            let new_cost = add_p(np, self.ll_price(nl));
                            let old_cost = add_p(self.op.price[cur], self.ll_price(self.op.litlen[cur]));
                            if new_cost < old_cost {
                                let (pa, pb, pc) = (self.op.ra[cur - 1], self.op.rb[cur - 1], self.op.rc[cur - 1]);
                                self.op.price.set(cur, np);
                                self.op.mlen.set(cur, 0);
                                self.op.litlen.set(cur, nl);
                                self.op.ra.set(cur, pa);
                                self.op.rb.set(cur, pb);
                                self.op.rc.set(cur, pc);
                            }
                        }
                        if cur == last {
                            break;
                        }
                        if cur < ilimit - ip && self.op.price[cur] < INF {
                            let p = ip + cur;
                            let l0 = self.op.litlen[cur] == 0;
                            let (na, nb, nc) = (self.op.ra[cur], self.op.rb[cur], self.op.rc[cur]);
                            let lb2 = self.matches(src, p, end, l0, na, nb, nc);
                            let n2 = self.op.ml.len();
                            if n2 > 0 {
                                if lb2 >= self.op.tlen || lb2 > NODES - cur {
                                    tail = true;
                                    tcur = cur;
                                    tml = self.op.ml[n2 - 1] as usize;
                                    toff = self.op.mo[n2 - 1];
                                    break;
                                }
                                last = self.relax(cur, last, end - p);
                            }
                        }
                        cur = cur + 1;
                    }
                }
                // The path: back from the last match's end.
                let mut endp: usize = if tail {
                    tcur
                } else {
                    let ll = self.op.litlen[last] as usize;
                    if ll <= last { last - ll } else { 0 }
                };
                self.op.ps.clear();
                self.op.pl.clear();
                self.op.po.clear();
                while endp > 0
                    invariant
                        self.wf(),
                        self.base == base0,
                        endp <= NODES,
                        self.op.ps@.len() == self.op.pl@.len(),
                        self.op.ps@.len() == self.op.po@.len(),
                    decreases endp,
                {
                    let m = self.op.mlen[endp] as usize;
                    if m > 0 && m <= endp {
                        self.op.ps.push((endp - m) as u32);
                        self.op.pl.push(m as u32);
                        self.op.po.push(self.op.moff[endp]);
                        endp = endp - m;
                    } else {
                        endp = endp - 1;
                    }
                }
                // The sequences, in order.
                let mut k = self.op.ps.len();
                while k > 0
                    invariant
                        self.wf(),
                        self.base == base0,
                        anchor <= end,
                        ip <= end,
                        ip < ilimit,
                        pos <= anchor,
                        end <= src@.len(),
                        k <= self.op.ps@.len(),
                        self.op.ps@.len() == self.op.pl@.len(),
                        self.op.ps@.len() == self.op.po@.len(),
                    decreases k,
                {
                    k = k - 1;
                    let q = self.op.ps[k] as usize;
                    if q > end - ip {
                        break;
                    }
                    let s = ip + q;
                    let m = self.op.pl[k] as usize;
                    let o = self.op.po[k];
                    if s < anchor || s > end || m > end - s || m < 3 {
                        break;
                    }
                    let (ob, na, nb, nc) = rep_step(o, s == anchor, a, b, c);
                    self.count_seq(src, anchor, s, m, ob);
                    emit(&mut self.st, src, anchor, s, o as usize, m);
                    a = na;
                    b = nb;
                    c = nc;
                    anchor = s + m;
                }
                if tail && tcur <= end - ip {
                    let s = ip + tcur;
                    if s >= anchor && s <= end && tml <= end - s && tml >= 3 {
                        let (ob, na, nb, nc) = rep_step(toff, s == anchor, a, b, c);
                        self.count_seq(src, anchor, s, tml, ob);
                        emit(&mut self.st, src, anchor, s, toff as usize, tml);
                        a = na;
                        b = nb;
                        c = nc;
                        anchor = s + tml;
                    }
                }
                if self.op.since >= 2048 {
                    self.refresh();
                }
                ip = if anchor > ip { anchor } else { ip + 1 };
            }
        }
        self.st.lits.extend_from_slice(slice_subrange(src, anchor, end));
    }
}

} // verus!
