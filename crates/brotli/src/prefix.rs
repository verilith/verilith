//! Reading a prefix code (RFC 7932 §3.4, §3.5), one item at a time:
//! `Pcx::step` computes `spec::pc_step`.
use crate::bitread::*;
use crate::huffman::*;
use crate::items::*;
use crate::spec::CL_ORDER;
use crate::work::*;
#[cfg(verus_only)]
use crate::codes::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// The decoder's state for reading one prefix code (`spec::Pc`).
pub struct Pcx {
    pub started: bool,
    /// Code length code lengths, and their code.
    pub cl: Vec<u8>,
    pub clh: HCode,
    /// Code lengths read so far.
    pub lens: Ghost<Seq<u8>>,
    /// How many there are, which of them are not zero, and how many have
    /// each length.
    pub n: usize,
    pub used: Vec<(u16, u8)>,
    pub cnts: [u16; 16],
    pub prev: u32,
    pub rep: u32,
    pub replen: u32,
    pub space: i64,
}

pub fn empty_code() -> (h: HCode) {
    HCode { table: Vec::new(), tbits: 0, count: [0u16; 16], first: [0u32; 16], offs: [0u16; 16], sorted: Vec::new() }
}

/// What one step of reading a prefix code gives.
pub enum PcOut {
    /// More to read.
    More,
    /// The code: its table and its lengths.
    Code(HCode, Ghost<Seq<u8>>),
}

/// `prepend(pre, r)`: `r` with `pre` in front of the symbols it read.
pub open spec fn prepend(pre: Seq<int>, r: R<Seq<int>>) -> R<Seq<int>> {
    match r {
        R::Ok(rest, q) => R::Ok(pre + rest, q),
        R::Bad => R::Bad,
        R::Short => R::Short,
    }
}

/// The step's result agrees with the spec's.
pub open spec fn pc_agrees(r: Res<PcOut>, s: PcRes, after: Pc, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    match r {
        Res::Ok(PcOut::More, p) => s == PcRes::Cont(after, p as int) && p <= lim(src, base as int),
        Res::Ok(PcOut::Code(h, lens), p) => s == PcRes::Fin(lens@, p as int) && hcode_ok(h, lens@) && p
            <= lim(src, base as int),
        Res::Bad => s is Bad,
        Res::Short => full(src, base as int, b) ==> s is Short,
    }
}

impl Pcx {
    pub open spec fn view(&self) -> Pc {
        Pc {
            started: self.started,
            cl: self.cl@,
            lens: self.lens@,
            prev: self.prev as int,
            rep: self.rep as int,
            replen: self.replen as int,
            space: self.space as int,
        }
    }

    /// What the state always satisfies, reading a code over `alpha`
    /// symbols.
    pub open spec fn inv(&self, alpha: int) -> bool {
        if !self.started {
            self.view() == pc_init()
        } else {
            &&& self.cl@.len() == 18
            &&& short(self.cl@)
            &&& hcode_ok(self.clh, self.cl@)
            &&& short(self.lens@)
            &&& self.lens@.len() < alpha
            &&& self.n == self.lens@.len()
            &&& sparse_inv(self.lens@, self.used@, self.cnts)
            &&& self.space == 32768 - kraft(self.lens@)
            &&& 1 <= self.prev <= 15
            &&& self.replen <= 15
            &&& (self.rep == 0 || 3 <= self.rep <= self.lens@.len())
        }
    }

    pub fn new() -> (r: Pcx)
        ensures
            r.view() == pc_init(),
    {
        Pcx {
            started: false,
            cl: Vec::new(),
            clh: empty_code(),
            lens: Ghost(Seq::empty()),
            n: 0,
            used: Vec::with_capacity(64),
            cnts: [0u16; 16],
            prev: 8,
            rep: 0,
            replen: 0,
            space: 0,
        }
    }

    pub fn reset(&mut self)
        ensures
            final(self).view() == pc_init(),
    {
        self.started = false;
        self.cl = Vec::new();
        self.clh = empty_code();
        self.lens = Ghost(Seq::empty());
        self.n = 0;
        self.used.clear();
        self.cnts = [0u16; 16];
        self.prev = 8;
        self.rep = 0;
        self.replen = 0;
        self.space = 0;
        assert(self.cl@ =~= Seq::<u8>::empty());
        assert(self.lens@ =~= Seq::<u8>::empty());
    }

    /// One step of `spec::pc_step` for an alphabet of `alpha` symbols. On
    /// `Short` the state is unchanged.
    #[verifier::rlimit(30)]
    #[inline(always)]
    pub fn step(&mut self, src: &[u8], base: u64, pos: u64, alpha: u32, Ghost(b): Ghost<Seq<u8>>, Tracked(m): Tracked<&mut Meter>) -> (r: Res<PcOut>)
        requires
            old(self).inv(alpha as int),
            at(src@, base, pos, b),
            2 <= alpha <= 2328,
        ensures
            pc_agrees(r, pc_step(b, pos as int, old(self).view(), alpha as int), final(self).view(), src@, base, b),
            r is Short ==> *final(self) == *old(self) && final(m).n == old(m).n,
            r matches Res::Ok(PcOut::More, p) ==> if old(self).started {
                final(m).n + old(self).n + 1 <= old(m).n + final(self).n + kbit() * (p - pos) && old(self).n < final(self).n
            } else {
                final(m).n <= old(m).n + clb() && pos + 2 <= p && final(self).n == 0
            },
            r matches Res::Ok(PcOut::Code(_, _), p) ==> if old(self).started {
                final(m).n + old(self).n + 1 <= old(m).n + alpha + pcb(alpha as int) + kbit() * (p - pos) && old(self).n < alpha
            } else {
                final(m).n <= old(m).n + pcb(alpha as int) && pos + 2 <= p
            },
            final(m).n <= old(m).n + clb() + alpha + pcb(alpha as int),
            r matches Res::Ok(PcOut::More, p) ==> final(self).inv(alpha as int) && pos <= p,
            r matches Res::Ok(PcOut::Code(_, lens), p) ==> lens@.len() == alpha && pos <= p,
    {
        proof {
            lemma2_to64();
        }
        if !self.started {
            let hskip = match read_bits(src, base, pos, 2, Ghost(b)) {
                None => return Res::Short,
                Some(x) => x,
            };
            if hskip == 1 {
                return read_simple(src, base, pos + 2, alpha, Ghost(b), Tracked(m));
            }
            return self.start_complex(src, base, pos, hskip, alpha, Ghost(b), Tracked(m));
        }
        let ghost pc = self.view();
        let (c, p) = match read_sym(&self.clh, src, base, pos, Ghost(self.cl@), Ghost(b)) {
            Res::Ok(c, p) => (c, p),
            Res::Bad => return Res::Bad,
            Res::Short => return Res::Short,
        };
        let mut p = p;
        let ghost old_lens = self.lens@;
        if c < 16 {
            if c != 0 {
                sparse_push(Ghost(old_lens), self.n, &mut self.used, &mut self.cnts, c as u8);
            } else {
                proof {
                    lemma_sparse_zeros(old_lens, self.used@, self.cnts, 1);
                    assert(old_lens + Seq::new(1, |i: int| 0u8) =~= old_lens.push(0u8));
                }
            }
            self.lens = Ghost(old_lens.push(c as u8));
            self.n = self.n + 1;
            self.rep = 0;
            proof {
                lemma_kraft_push(old_lens, c as u8);
                lemma_mask((15 - c) as u64);
                lemma_kraft_bound(old_lens);
                lemma_pow2_strictly_increases((15 - c) as nat, 16);
            }
            if c != 0 {
                self.prev = c as u32;
                self.space = self.space - (1u64 << (15 - c)) as i64;
            }
            assert(self.view() == Pc {
                lens: pc.lens.push(c as u8),
                rep: 0,
                prev: if c != 0 { c as int } else { pc.prev },
                space: if c != 0 { pc.space - pow2((15 - c) as nat) } else { pc.space },
                ..pc
            });
        } else {
            let x: u64 = if c == 16 { 2 } else { 3 };
            let delta = match read_bits(src, base, p, x, Ghost(b)) {
                None => return Res::Short,
                Some(d) => d as u32,
            };
            let newlen: u32 = if c == 16 { self.prev } else { 0 };
            let rep0: u32 = if self.replen != newlen { 0 } else { self.rep };
            let mul: u32 = if c == 16 { 4 } else { 8 };
            assert(mul == pow2(x as nat));
            let rep1: u32 = (if rep0 > 0 { (rep0 - 2) * mul } else { 0 }) + delta + 3;
            let d = rep1 - rep0;
            proof {
                lemma_kraft_bound(old_lens);
            }
            if self.n as u64 + d as u64 > alpha as u64 {
                return Res::Bad;
            }
            if newlen == 0 {
                proof {
                    lemma_sparse_zeros(old_lens, self.used@, self.cnts, d as nat);
                }
                self.lens = Ghost(old_lens + Seq::new(d as nat, |i: int| 0u8));
                self.n = self.n + d as usize;
            } else {
                let ghost m0 = m.n;
                let mut k: u32 = 0;
                while k < d
                    invariant
                        m.n == m0 + k,
                        k <= d,
                        self.lens@ == old_lens + Seq::new(k as nat, |i: int| newlen as u8),
                        self.n == self.lens@.len(),
                        old_lens.len() + d <= alpha,
                        alpha <= 2328,
                        1 <= newlen <= 15,
                        sparse_inv(self.lens@, self.used@, self.cnts),
                    decreases d - k,
                {
                    let ghost cur = self.lens@;
                    sparse_push(Ghost(cur), self.n, &mut self.used, &mut self.cnts, newlen as u8);
                    self.lens = Ghost(cur.push(newlen as u8));
                    self.n = self.n + 1;
                    proof {
                        m.n = m.n + 1;
                    }
                    k = k + 1;
                    assert(self.lens@ =~= old_lens + Seq::new(k as nat, |i: int| newlen as u8));
                }
            }
            self.rep = rep1;
            self.replen = newlen;
            proof {
                lemma_kraft_rep(old_lens, newlen as u8, d as nat);
                lemma_mask((15 - newlen) as u64);
                lemma_term_bound(newlen as u8);
                assert(d * term(newlen as u8) <= 2328 * 16384) by (nonlinear_arith)
                    requires d <= 2328, term(newlen as u8) <= 16384;
                assert forall|i: int| 0 <= i < self.lens@.len() implies #[trigger] self.lens@[i] <= 15 by {
                    if i < old_lens.len() {
                        assert(self.lens@[i] == old_lens[i]);
                    }
                }
            }
            if newlen != 0 {
                self.space = self.space - (d as i64) * ((1u64 << (15 - newlen) as u64) as i64);
            }
            p = p + x;
        }
        assert(short(self.lens@)) by {
            assert forall|i: int| 0 <= i < self.lens@.len() implies #[trigger] self.lens@[i] <= 15 by {
                if i < old_lens.len() {
                    assert(self.lens@[i] == old_lens[i]);
                }
            }
        }
        if (self.n as u64) < alpha as u64 && self.space != 0 {
            return Res::Ok(PcOut::More, p);
        }
        if self.space != 0 {
            return Res::Bad;
        }
        let ghost done = self.lens@;
        let ghost lens = pad_lens(done, alpha as int);
        proof {
            assert(lens =~= done + Seq::new((alpha - done.len()) as nat, |i: int| 0u8));
            lemma_kraft_zeros(done, (alpha - done.len()) as nat);
            lemma_sparse_zeros(done, self.used@, self.cnts, (alpha - done.len()) as nat);
            assert forall|i: int| 0 <= i < lens.len() implies #[trigger] lens[i] <= 15 by {
                if i < done.len() {
                    assert(lens[i] == done[i]);
                }
            }
            lemma_kraft_valid(lens);
        }
        let (h, Ghost(bw)) = build_sparse(Ghost(lens), alpha as usize, self.used.as_slice(), &self.cnts, MAX_ROOT);
        proof {
            lemma2_to64();
            m.n = m.n + bw;
        }
        match h {
            Some(h) => Res::Ok(PcOut::Code(h, Ghost(lens)), p),
            None => Res::Bad,
        }
    }

    /// The start of a complex code: the code length code lengths.
    fn start_complex(&mut self, src: &[u8], base: u64, pos: u64, hskip: u64, alpha: u32, Ghost(b): Ghost<Seq<u8>>, Tracked(m): Tracked<&mut Meter>) -> (r: Res<PcOut>)
        requires
            old(self).view() == pc_init(),
            at(src@, base, pos, b),
            rd(b, pos as int, 2) == Some(hskip as int),
            pos + 2 <= lim(src@, base as int),
            hskip < 4,
            hskip != 1,
            2 <= alpha <= 2328,
        ensures
            pc_agrees(r, pc_step(b, pos as int, pc_init(), alpha as int), final(self).view(), src@, base, b),
            r is Short ==> *final(self) == *old(self) && final(m).n == old(m).n,
            r matches Res::Ok(PcOut::More, p) ==> final(self).inv(alpha as int) && pos + 2 <= p && final(self).n == 0,
            !(r is Ok && r->Ok_0 is Code),
            final(m).n <= old(m).n + clb(),
    {
        proof {
            lemma2_to64();
            lemma_zeros(18);
        }
        let ghost zeros = Seq::new(18, |i: int| 0u8);
        let ghost target = read_cl(b, pos + 2, hskip as int, zeros, 0, 32);
        assert(target is Short ==> pc_step(b, pos as int, pc_init(), alpha as int) is Short);
        assert(forall|cl: Seq<u8>, num: int, space: int, q: int| target == R::Ok((cl, num, space), q) ==>
            pc_step(b, pos as int, pc_init(), alpha as int) == if num == 1 || space == 0 {
                PcRes::Cont(Pc { started: true, cl, lens: Seq::empty(), prev: 8, rep: 0, replen: 0, space: 32768 }, q)
            } else {
                PcRes::Bad
            });
        let mut cl: Vec<u8> = vec![0u8; 18];
        assert(cl@ =~= zeros);
        let mut num: u32 = 0;
        let mut space: i32 = 32;
        let mut i = hskip as usize;
        let mut p = pos + 2;
        let mut stop = false;
        assert(forall|j: int, k: int| 0 <= j < k < 18 ==> CL_ORDER[j] != CL_ORDER[k]) by (compute);
        assert(forall|j: int| 0 <= j < 18 ==> CL_ORDER[j] < 18) by (compute);
        while i < 18 && !stop
            invariant
                at(src@, base, p, b),
                pos + 2 <= p,
                i <= 18,
                cl@.len() == 18,
                num <= i,
                -32 <= space <= 32,
                !stop ==> space > 0,
                short(cl@),
                forall|j: int| 0 <= j < cl@.len() ==> #[trigger] cl@[j] <= 5,
                forall|j: int| i <= j < 18 ==> cl@[#[trigger] CL_ORDER[j] as int] == 0,
                forall|j: int, k: int| 0 <= j < k < 18 ==> CL_ORDER[j] != CL_ORDER[k],
                forall|j: int| 0 <= j < 18 ==> CL_ORDER[j] < 18,
                used(cl@) == num,
                kraft(cl@) + 1024 * space == 32768,
                target is Short ==> pc_step(b, pos as int, pc_init(), alpha as int) is Short,
                target == if stop {
                    R::Ok((cl@, num as int, space as int), p as int)
                } else {
                    read_cl(b, p as int, i as int, cl@, num as int, space as int)
                },
            decreases 18 - i,
        {
            let (v, p2) = match read_clcl(src, base, p, Ghost(b)) {
                Res::Ok(v, p2) => (v, p2),
                Res::Bad => return Res::Bad,
                Res::Short => {
                    assert(full(src@, base as int, b) ==> target is Short);
                    assert(full(src@, base as int, b) ==> pc_step(b, pos as int, pc_init(), alpha as int) is Short);
                    return Res::Short;
                },
            };
            let ghost cl0 = cl@;
            let j = CL_ORDER[i] as usize;
            cl.set(j, v as u8);
            proof {
                lemma_used_update(cl0, j as int, v as u8);
                lemma_kraft_update(cl0, j as int, v as u8);
                assert forall|k: int| 0 <= k < cl@.len() implies #[trigger] cl@[k] <= 5 by {
                    if k != j {
                        assert(cl@[k] == cl0[k]);
                    }
                }
                assert forall|k: int| 0 <= k < cl@.len() implies #[trigger] cl@[k] <= 15 by {
                    assert(cl@[k] <= 5);
                }
                assert forall|k: int| i + 1 <= k < 18 implies cl@[#[trigger] CL_ORDER[k] as int] == 0 by {
                    assert(CL_ORDER[k] != CL_ORDER[i as int]);
                }
            }
            p = p2;
            if v != 0 {
                proof {
                    lemma_mask((5 - v) as u64);
                    lemma_pow2_strictly_increases((5 - v) as nat, 5);
                    lemma_pow2_adds(10, (5 - v) as nat);
                    assert(term(v as u8) == pow2((15 - v) as nat));
                    assert((10 + (5 - v)) as nat == (15 - v) as nat);
                }
                proof {
                    lemma2_to64();
                }
                let dv = 1u64 << (5 - v);
                assert(dv == pow2((5 - v) as nat) && dv < 32);
                space = space - dv as i32;
                num = num + 1;
                if space <= 0 {
                    stop = true;
                }
            }
            i = i + 1;
        }
        assert(target == R::Ok((cl@, num as int, space as int), p as int));
        if !(num == 1 || space == 0) {
            return Res::Bad;
        }
        proof {
            if num == 1 {
                lemma_single_valid(cl@);
            } else {
                lemma_kraft_valid(cl@);
            }
        }
        let (h, Ghost(bw)) = build(cl.as_slice(), 5);
        proof {
            lemma2_to64();
            m.n = m.n + bw;
        }
        let clh = match h {
            Some(h) => h,
            None => return Res::Bad,
        };
        self.started = true;
        self.cl = cl;
        self.clh = clh;
        self.lens = Ghost(Seq::empty());
        self.n = 0;
        self.used.clear();
        self.cnts = [0u16; 16];
        self.prev = 8;
        self.rep = 0;
        self.replen = 0;
        self.space = 32768;
        proof {
            assert(self.lens@ =~= Seq::<u8>::empty());
            assert(self.used@ =~= Seq::<(u16, u8)>::empty());
            lemma_sparse_empty(self.cnts);
            assert(kraft(self.lens@) == 0);
        }
        Res::Ok(PcOut::More, p)
    }
}

/// `spec::read_clcl`: a code length code length, with the static code.
pub fn read_clcl(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        at(src@, base, pos, b),
    ensures
        agrees(r, crate::spec::read_clcl(b, pos as int), src@, base, b),
        r matches Res::Ok(v, p) ==> v <= 5 && pos + 2 <= p <= pos + 4,
        !(r is Bad),
{
    match read_bits(src, base, pos, 2, Ghost(b)) {
        None => Res::Short,
        Some(a) => if a == 0 {
            Res::Ok(0, pos + 2)
        } else if a == 1 {
            Res::Ok(4, pos + 2)
        } else if a == 2 {
            Res::Ok(3, pos + 2)
        } else {
            match read_bits(src, base, pos + 2, 1, Ghost(b)) {
                None => Res::Short,
                Some(c) => if c == 0 {
                    Res::Ok(2, pos + 3)
                } else {
                    match read_bits(src, base, pos + 3, 1, Ghost(b)) {
                        None => Res::Short,
                        Some(d) => if d == 0 {
                            Res::Ok(1, pos + 4)
                        } else {
                            Res::Ok(5, pos + 4)
                        },
                    }
                },
            }
        },
    }
}

/// `bitlen(x)` is at most `k` for `x < 2^k`.
proof fn lemma_bitlen_bound(x: nat, k: nat)
    requires
        x < pow2(k),
    ensures
        bitlen(x) <= k,
    decreases k,
{
    if x > 0 {
        if k == 0 {
            assert(pow2(0) == 1) by {
                lemma2_to64();
            }
        } else {
            lemma_pow2_adds(1, (k - 1) as nat);
            lemma2_to64();
            lemma_bitlen_bound(x / 2, (k - 1) as nat);
        }
    }
}

/// The lengths of a simple code, from all zeros, symbol by symbol.
proof fn lemma_simple_lens(alpha: int, syms: Seq<int>, ls: Seq<u8>)
    requires
        syms.len() == ls.len(),
        distinct(syms),
        forall|i: int| 0 <= i < syms.len() ==> 0 <= #[trigger] syms[i] < alpha,
        forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 15,
        alpha >= 0,
    ensures
        simple_lens(alpha, syms, ls).len() == alpha,
        forall|j: int| 0 <= j < alpha && !syms.contains(j) ==> simple_lens(alpha, syms, ls)[j] == 0,
        short(simple_lens(alpha, syms, ls)),
        used(simple_lens(alpha, syms, ls)) == syms.len(),
        kraft(simple_lens(alpha, syms, ls)) == ksum(ls),
    decreases syms.len(),
{
    let s = simple_lens(alpha, syms, ls);
    if syms.len() == 0 {
        lemma_zeros(alpha as nat);
        assert(s =~= Seq::new(alpha as nat, |i: int| 0u8));
    } else {
        let sd = syms.drop_last();
        let ld = ls.drop_last();
        assert(distinct(sd));
        lemma_simple_lens(alpha, sd, ld);
        let t = simple_lens(alpha, sd, ld);
        let k = syms.last();
        assert(!sd.contains(k)) by {
            if sd.contains(k) {
                let i = choose|i: int| 0 <= i < sd.len() && sd[i] == k;
                assert(syms[i] == syms[syms.len() - 1]);
            }
        }
        assert(t[k] == 0);
        lemma_used_update(t, k, ls.last());
        lemma_kraft_update(t, k, ls.last());
        assert forall|j: int| 0 <= j < alpha && !syms.contains(j) implies s[j] == 0 by {
            if sd.contains(j) {
                let i = choose|i: int| 0 <= i < sd.len() && sd[i] == j;
                assert(syms[i] == j);
            }
            assert(j != k) by {
                assert(syms[syms.len() - 1] == k);
            }
        }
        assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] <= 15 by {
            if i != k {
                assert(s[i] == t[i]);
            }
        }
        assert(term(0u8) == 0);
    }
}

/// The code space of a list of lengths.
pub open spec fn ksum(ls: Seq<u8>) -> nat
    decreases ls.len(),
{
    if ls.len() == 0 {
        0
    } else {
        ksum(ls.drop_last()) + term(ls.last())
    }
}

/// A symbol of a simple code has the length given with it.
proof fn lemma_simple_at(alpha: int, syms: Seq<int>, ls: Seq<u8>, k: int)
    requires
        syms.len() == ls.len(),
        distinct(syms),
        forall|i: int| 0 <= i < syms.len() ==> 0 <= #[trigger] syms[i] < alpha,
        0 <= k < syms.len(),
        alpha >= 0,
    ensures
        simple_lens(alpha, syms, ls).len() == alpha,
        simple_lens(alpha, syms, ls)[syms[k]] == ls[k],
    decreases syms.len(),
{
    let sd = syms.drop_last();
    let ld = ls.drop_last();
    assert(distinct(sd));
    if sd.len() == 0 {
        assert(simple_lens(alpha, sd, ld).len() == alpha);
    } else if k < sd.len() {
        lemma_simple_at(alpha, sd, ld, k);
        assert(syms[k] != syms[syms.len() - 1]);
    } else {
        lemma_simple_at(alpha, sd, ld, 0);
    }
}

/// The table of a simple code, from its 1 to 4 symbols alone: they are
/// sorted and handed to `build_sparse`, so that nothing is in proportion
/// to the alphabet.
#[verifier::spinoff_prover]
fn build_simple(alpha: u32, syms: &Vec<u32>, ls: &[u8; 4], Ghost(gs): Ghost<Seq<int>>, Tracked(m): Tracked<&mut Meter>) -> (h: Option<HCode>)
    requires
        2 <= alpha <= 2328,
        1 <= syms@.len() <= 4,
        gs.len() == syms@.len(),
        forall|k: int| 0 <= k < gs.len() ==> #[trigger] gs[k] == syms@[k] as int,
        forall|k: int| 0 <= k < gs.len() ==> 0 <= #[trigger] gs[k] < alpha,
        distinct(gs),
        forall|k: int| 0 <= k < gs.len() ==> 1 <= #[trigger] ls@[k] <= 15,
    ensures
        ({
            let lens = simple_lens(alpha as int, gs, ls@.take(gs.len() as int));
            &&& h is Some == valid_code(lens)
            &&& h matches Some(x) ==> hcode_ok(x, lens) && x.tbits <= MAX_ROOT
        }),
        final(m).n <= old(m).n + pcb(alpha as int),
{
    let n = syms.len();
    let ghost lq = ls@.take(n as int);
    let ghost full = simple_lens(alpha as int, gs, lq);
    proof {
        assert forall|k: int| 0 <= k < lq.len() implies 1 <= #[trigger] lq[k] <= 15 by {
            assert(lq[k] == ls@[k]);
        }
        lemma_simple_lens(alpha as int, gs, lq);
        lemma_simple_at(alpha as int, gs, lq, 0);
        if n > 1 {
            lemma_simple_at(alpha as int, gs, lq, 1);
        }
        if n > 2 {
            lemma_simple_at(alpha as int, gs, lq, 2);
        }
        if n > 3 {
            lemma_simple_at(alpha as int, gs, lq, 3);
        }
        assert(gs[0] == syms@[0] as int);
        assert(lq[0] == ls@[0]);
    }
    // Symbols past the last one sort after every real symbol.
    let mut a0: u32 = syms[0];
    let mut b0: u8 = ls[0];
    let mut a1: u32 = if n > 1 { syms[1] } else { 0xFFFF_FF01 };
    let mut b1: u8 = if n > 1 { ls[1] } else { 0 };
    let mut a2: u32 = if n > 2 { syms[2] } else { 0xFFFF_FF02 };
    let mut b2: u8 = if n > 2 { ls[2] } else { 0 };
    let mut a3: u32 = if n > 3 { syms[3] } else { 0xFFFF_FF03 };
    let mut b3: u8 = if n > 3 { ls[3] } else { 0 };
    let ghost (o0, o1, o2, o3) = (a0, a1, a2, a3);
    proof {
        if n > 1 {
            assert(gs[1] == syms@[1] as int && lq[1] == ls@[1]);
            assert(gs[0] != gs[1]);
        }
        if n > 2 {
            assert(gs[2] == syms@[2] as int && lq[2] == ls@[2]);
            assert(gs[0] != gs[2] && gs[1] != gs[2]);
        }
        if n > 3 {
            assert(gs[3] == syms@[3] as int && lq[3] == ls@[3]);
            assert(gs[0] != gs[3] && gs[1] != gs[3] && gs[2] != gs[3]);
        }
    }
    if a0 > a1 {
        let (t, u) = (a0, b0);
        a0 = a1;
        b0 = b1;
        a1 = t;
        b1 = u;
    }
    if a2 > a3 {
        let (t, u) = (a2, b2);
        a2 = a3;
        b2 = b3;
        a3 = t;
        b3 = u;
    }
    if a0 > a2 {
        let (t, u) = (a0, b0);
        a0 = a2;
        b0 = b2;
        a2 = t;
        b2 = u;
    }
    if a1 > a3 {
        let (t, u) = (a1, b1);
        a1 = a3;
        b1 = b3;
        a3 = t;
        b3 = u;
    }
    if a1 > a2 {
        let (t, u) = (a1, b1);
        a1 = a2;
        b1 = b2;
        a2 = t;
        b2 = u;
    }
    assert(a0 < a1 < a2 < a3);
    assert(o0 == a0 || o0 == a1 || o0 == a2 || o0 == a3);
    assert(o1 == a0 || o1 == a1 || o1 == a2 || o1 == a3);
    assert(o2 == a0 || o2 == a1 || o2 == a2 || o2 == a3);
    assert(o3 == a0 || o3 == a1 || o3 == a2 || o3 == a3);
    assert forall|x: int| 0 <= x < alpha && x != a0 && x != a1 && x != a2 && x != a3 implies #[trigger] full[x] == 0 by {
        if gs.contains(x) {
            let k = choose|k: int| 0 <= k < gs.len() && gs[k] == x;
            assert(gs[k] == syms@[k] as int);
            assert(x == o0 || x == o1 || x == o2 || x == o3);
        }
    }
    assert(a0 < alpha && full[a0 as int] == b0 && 1 <= b0 <= 15);
    assert(n > 1 ==> a1 < alpha && full[a1 as int] == b1 && 1 <= b1 <= 15);
    assert(n > 2 ==> a2 < alpha && full[a2 as int] == b2 && 1 <= b2 <= 15);
    assert(n > 3 ==> a3 < alpha && full[a3 as int] == b3 && 1 <= b3 <= 15);
    let sa: [u32; 4] = [a0, a1, a2, a3];
    let sb: [u8; 4] = [b0, b1, b2, b3];
    let mut used: Vec<(u16, u8)> = Vec::with_capacity(4);
    let mut cnts = [0u16; 16];
    let ghost mut cur: Seq<u8> = Seq::empty();
    let mut mm: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(full.take(0) =~= cur);
        lemma_sparse_empty(cnts);
        assert(used@ =~= Seq::<(u16, u8)>::empty());
    }
    while j < n
        invariant
            1 <= n <= 4,
            j <= n,
            2 <= alpha <= 2328,
            full.len() == alpha,
            sa@.len() == 4 && sb@.len() == 4,
            sa@[0] < sa@[1] < sa@[2] < sa@[3],
            forall|k: int| 0 <= k < n ==> (#[trigger] sa@[k]) < alpha && full[sa@[k] as int] == sb@[k] && 1 <= sb@[k] <= 15,
            forall|x: int| 0 <= x < alpha && x != sa@[0] && x != sa@[1] && x != sa@[2] && x != sa@[3] ==> #[trigger] full[x] == 0,
            mm == cur.len(),
            mm <= alpha,
            j == 0 ==> mm == 0,
            j > 0 ==> mm == sa@[j - 1] + 1,
            cur == full.take(mm as int),
            sparse_inv(cur, used@, cnts),
        decreases n - j,
    {
        let sym = sa[j] as usize;
        let d = sym - mm;
        proof {
            lemma_sparse_zeros(cur, used@, cnts, d as nat);
            let c2 = cur + Seq::new(d as nat, |i: int| 0u8);
            assert(c2 =~= full.take(sym as int)) by {
                assert forall|x: int| mm <= x < sym implies full[x] == 0 by {
                    assert(x != sa@[0] && x != sa@[1] && x != sa@[2] && x != sa@[3]);
                }
            }
            cur = c2;
        }
        sparse_push(Ghost(cur), sym, &mut used, &mut cnts, sb[j]);
        proof {
            assert(cur.push(sb@[j as int]) =~= full.take(sym + 1));
            cur = cur.push(sb@[j as int]);
        }
        mm = sym + 1;
        j = j + 1;
    }
    proof {
        let d = (alpha - mm) as nat;
        lemma_sparse_zeros(cur, used@, cnts, d);
        let c2 = cur + Seq::new(d, |i: int| 0u8);
        assert(c2 =~= full) by {
            assert forall|x: int| mm <= x < alpha implies full[x] == 0 by {
                assert(x != sa@[0] && x != sa@[1] && x != sa@[2] && x != sa@[3]);
            }
        }
        assert(short(full));
    }
    let (h, Ghost(bw)) = build_sparse(Ghost(full), alpha as usize, used.as_slice(), &cnts, MAX_ROOT);
    proof {
        lemma2_to64();
        m.n = m.n + bw;
    }
    h
}

/// `spec::read_simple`: a simple prefix code.
fn read_simple(src: &[u8], base: u64, pos: u64, alpha: u32, Ghost(b): Ghost<Seq<u8>>, Tracked(m): Tracked<&mut Meter>) -> (r: Res<PcOut>)
    requires
        at(src@, base, pos, b),
        2 <= alpha <= 2328,
    ensures
        r is Short ==> final(m).n == old(m).n,
        final(m).n <= old(m).n + pcb(alpha as int),
        forall|after: Pc| pc_agrees(r, crate::spec::read_simple(b, pos as int, alpha as int), after, src@, base, b),
        !(r is Ok && r->Ok_0 is More),
        r matches Res::Ok(PcOut::Code(_, lens), p) ==> lens@.len() == alpha && pos <= p,
{
    proof {
        lemma2_to64();
    }
    let nm1 = match read_bits(src, base, pos, 2, Ghost(b)) {
        None => return Res::Short,
        Some(x) => x,
    };
    let nsym = nm1 + 1;
    let mut w: u64 = 0;
    let mut a = alpha - 1;
    proof {
        lemma_bitlen_bound((alpha - 1) as nat, 12);
    }
    while a > 0
        invariant
            w + bitlen(a as nat) == bitlen((alpha - 1) as nat),
            bitlen((alpha - 1) as nat) <= 12,
        decreases a,
    {
        w = w + 1;
        a = a / 2;
    }
    let ghost wn = bitlen((alpha - 1) as nat);
    let ghost target = read_simple_syms(b, pos + 2, nsym as int, wn, alpha as int);
    assert(rd(b, pos as int, 2) == Some(nm1 as int));
    assert(target is Short ==> crate::spec::read_simple(b, pos as int, alpha as int) is Short);
    assert(target is Bad ==> crate::spec::read_simple(b, pos as int, alpha as int) is Bad);
    let mut syms: Vec<u32> = Vec::new();
    let ghost mut gs: Seq<int> = Seq::empty();
    let mut p = pos + 2;
    let mut i: u64 = 0;
    while i < nsym
        invariant
            at(src@, base, p, b),
            pos + 2 <= p,
            i <= nsym <= 4,
            w == wn,
            w <= 12,
            gs.len() == i,
            syms@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] gs[k] == syms@[k] as int,
            forall|k: int| 0 <= k < i ==> 0 <= #[trigger] gs[k] < alpha,
            target == prepend(gs, read_simple_syms(b, p as int, nsym - i, wn, alpha as int)),
            target is Short ==> crate::spec::read_simple(b, pos as int, alpha as int) is Short,
            target is Bad ==> crate::spec::read_simple(b, pos as int, alpha as int) is Bad,
        decreases nsym - i,
    {
        let v = match read_bits(src, base, p, w, Ghost(b)) {
            None => {
                assert(full(src@, base as int, b) ==> read_simple_syms(b, p as int, nsym - i, wn, alpha as int) is Short);
                assert(full(src@, base as int, b) ==> target is Short);
                assert(full(src@, base as int, b) ==> crate::spec::read_simple(b, pos as int, alpha as int) is Short);
                return Res::Short;
            },
            Some(v) => v,
        };
        if v >= alpha as u64 {
            assert(read_simple_syms(b, p as int, nsym - i, wn, alpha as int) is Bad);
            assert(target is Bad);
            assert(crate::spec::read_simple(b, pos as int, alpha as int) is Bad);
            return Res::Bad;
        }
        proof {
            let rest = read_simple_syms(b, p + w, nsym - i - 1, wn, alpha as int);
            assert(read_simple_syms(b, p as int, nsym - i, wn, alpha as int) == prepend(seq![v as int], rest));
            match rest {
                R::Ok(r2, q) => {
                    assert(gs + (seq![v as int] + r2) =~= gs.push(v as int) + r2);
                },
                _ => {},
            }
        }
        syms.push(v as u32);
        proof {
            gs = gs.push(v as int);
        }
        p = p + w;
        i = i + 1;
    }
    assert(target == R::Ok(gs, p as int)) by {
        assert(gs + Seq::<int>::empty() =~= gs);
    }
    let mut i: usize = 0;
    let mut dup = false;
    while i < syms.len()
        invariant
            syms@.len() == gs.len() <= 4,
            forall|k: int| 0 <= k < gs.len() ==> #[trigger] gs[k] == syms@[k] as int,
            dup ==> !distinct(gs),
            !dup ==> forall|x: int, y: int| 0 <= x < y < gs.len() && x < i ==> gs[x] != gs[y],
        decreases syms@.len() - i,
    {
        let mut j = i + 1;
        while j < syms.len()
            invariant
                syms@.len() == gs.len() <= 4,
                i < syms@.len(),
                i + 1 <= j <= syms@.len(),
                forall|k: int| 0 <= k < gs.len() ==> #[trigger] gs[k] == syms@[k] as int,
                dup ==> !distinct(gs),
                !dup ==> forall|x: int, y: int| 0 <= x < y < gs.len() && x < i ==> gs[x] != gs[y],
                !dup ==> forall|y: int| i < y < j ==> gs[i as int] != #[trigger] gs[y],
            decreases syms@.len() - j,
        {
            if syms[i] == syms[j] {
                dup = true;
                assert(gs[i as int] == gs[j as int]);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    if dup {
        return Res::Bad;
    }
    assert(distinct(gs));
    let ls: [u8; 4] = if nsym == 1 {
        [1, 0, 0, 0]
    } else if nsym == 2 {
        [1, 1, 0, 0]
    } else if nsym == 3 {
        [1, 2, 2, 0]
    } else {
        let t = match read_bits(src, base, p, 1, Ghost(b)) {
            None => return Res::Short,
            Some(t) => t,
        };
        p = p + 1;
        if t == 0 {
            [2, 2, 2, 2]
        } else {
            [1, 2, 3, 3]
        }
    };
    let ghost lq = ls@.take(nsym as int);
    proof {
        lemma_pow2_adds(14, 1);
        lemma_pow2_adds(13, 1);
        lemma_pow2_adds(12, 1);
        assert(seq![1u8].drop_last() =~= Seq::<u8>::empty());
        assert(seq![2u8].drop_last() =~= Seq::<u8>::empty());
        assert(seq![1u8, 1u8].drop_last() =~= seq![1u8]);
        assert(seq![1u8, 2u8].drop_last() =~= seq![1u8]);
        assert(seq![2u8, 2u8].drop_last() =~= seq![2u8]);
        assert(seq![1u8, 2u8, 2u8].drop_last() =~= seq![1u8, 2u8]);
        assert(seq![1u8, 2u8, 3u8].drop_last() =~= seq![1u8, 2u8]);
        assert(seq![2u8, 2u8, 2u8].drop_last() =~= seq![2u8, 2u8]);
        assert(seq![1u8, 2u8, 3u8, 3u8].drop_last() =~= seq![1u8, 2u8, 3u8]);
        assert(seq![2u8, 2u8, 2u8, 2u8].drop_last() =~= seq![2u8, 2u8, 2u8]);
        assert(term(1u8) == 16384 && term(2u8) == 8192 && term(3u8) == 4096);
        assert(ksum(Seq::<u8>::empty()) == 0);
        assert(ksum(seq![1u8]) == 16384);
        assert(ksum(seq![2u8]) == 8192);
        assert(ksum(seq![1u8, 1u8]) == 32768);
        assert(ksum(seq![1u8, 2u8]) == 24576);
        assert(ksum(seq![2u8, 2u8]) == 16384);
        assert(ksum(seq![1u8, 2u8, 2u8]) == 32768);
        assert(ksum(seq![1u8, 2u8, 3u8]) == 28672);
        assert(ksum(seq![2u8, 2u8, 2u8]) == 24576);
        assert(ksum(seq![1u8, 2u8, 3u8, 3u8]) == 32768);
        assert(ksum(seq![2u8, 2u8, 2u8, 2u8]) == 32768);
        if nsym == 1 {
            assert(lq =~= seq![1u8]);
        } else if nsym == 2 {
            assert(lq =~= seq![1u8, 1u8]);
        } else if nsym == 3 {
            assert(lq =~= seq![1u8, 2u8, 2u8]);
        } else if ls[0] == 2 {
            assert(lq =~= seq![2u8, 2u8, 2u8, 2u8]);
        } else {
            assert(lq =~= seq![1u8, 2u8, 3u8, 3u8]);
        }
    }
    let ghost lens = simple_lens(alpha as int, gs, lq);
    proof {
        assert forall|k: int| 0 <= k < lq.len() implies 1 <= #[trigger] lq[k] <= 15 by {
            assert(lq[k] == ls@[k]);
        }
        lemma_simple_lens(alpha as int, gs, lq);
        if nsym == 1 {
            lemma_single_valid(lens);
        } else {
            lemma_kraft_valid(lens);
        }
    }
    let h = build_simple(alpha, &syms, &ls, Ghost(gs), Tracked(m));
    match h {
        Some(h) => Res::Ok(PcOut::Code(h, Ghost(lens)), p),
        None => Res::Bad,
    }
}

} // verus!
