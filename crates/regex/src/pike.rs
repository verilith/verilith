//! The matcher: a Pike VM. All threads advance over the text together, one
//! character at a time, in priority order, at most one thread per
//! instruction.
use crate::dfa::*;
use crate::memo::*;
use crate::need::*;
use crate::prog::*;
use crate::sem::*;
use crate::spec::*;
use crate::vmspec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;
use verilith_text::utf::spec::*;

verus! {

/// An unset capture slot.
pub const NONE: usize = usize::MAX;

pub const INVALID: u32 = u32::MAX;

/// The character at `i`: its code point and length, or `(INVALID, 1)` if
/// no well-formed UTF-8 sequence starts there.
pub fn decode(s: &[u8], i: usize) -> (r: (u32, usize))
    requires
        i < s@.len(),
    ensures
        match dec(s@, i as int) {
            Some((c, l)) => r.0 == c && r.1 == l && c != INVALID && 1 <= l <= 4 && i + l <= s@.len(),
            None => r.0 == INVALID && r.1 == 1,
        },
{
    let n = s.len();
    let b = s[i];
    if b < 0x80 {
        return (b as u32, 1);
    }
    if 0xC2 <= b && b <= 0xDF {
        if n - i > 1 && 0x80 <= s[i + 1] && s[i + 1] <= 0xBF {
            let b1 = s[i + 1];
            assert(((((b & 0x1F) as u32) << 6u32) | ((b1 & 0x3F) as u32)) < 0x800) by (bit_vector);
            return ((((b & 0x1F) as u32) << 6u32) | ((b1 & 0x3F) as u32), 2);
        }
        return (INVALID, 1);
    }
    if 0xE0 <= b && b <= 0xEF {
        let lo: u8 = if b == 0xE0 {
            0xA0
        } else {
            0x80
        };
        let hi: u8 = if b == 0xED {
            0x9F
        } else {
            0xBF
        };
        if n - i > 2 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF {
            let b1 = s[i + 1];
            let b2 = s[i + 2];
            assert(((((b & 0x0F) as u32) << 12u32) | (((b1 & 0x3F) as u32) << 6u32) | ((b2 & 0x3F) as u32))
                < 0x10000) by (bit_vector);
            return ((((b & 0x0F) as u32) << 12u32) | (((b1 & 0x3F) as u32) << 6u32) | ((b2 & 0x3F) as u32), 3);
        }
        return (INVALID, 1);
    }
    if 0xF0 <= b && b <= 0xF4 {
        let lo: u8 = if b == 0xF0 {
            0x90
        } else {
            0x80
        };
        let hi: u8 = if b == 0xF4 {
            0x8F
        } else {
            0xBF
        };
        if n - i > 3 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF && 0x80 <= s[i + 3]
            && s[i + 3] <= 0xBF {
            let b1 = s[i + 1];
            let b2 = s[i + 2];
            let b3 = s[i + 3];
            assert(((((b & 0x07) as u32) << 18u32) | (((b1 & 0x3F) as u32) << 12u32) | (((b2 & 0x3F) as u32)
                << 6u32) | ((b3 & 0x3F) as u32)) < 0x200000) by (bit_vector);
            return (
                (((b & 0x07) as u32) << 18u32) | (((b1 & 0x3F) as u32) << 12u32) | (((b2 & 0x3F) as u32) << 6u32) | ((b3
                    & 0x3F) as u32),
                4,
            );
        }
        return (INVALID, 1);
    }
    (INVALID, 1)
}

/// No character starts strictly inside a well-formed sequence.
pub proof fn lemma_mid(s: Seq<u8>, p: int, l: int, q: int)
    requires
        0 <= p < s.len(),
        utf8_len(s, p) == Some(l),
        p < q < p + l,
    ensures
        dec(s, q) is None,
{
}

pub fn word_byte(b: u8) -> (r: bool)
    ensures
        r == is_word(b),
{
    (0x61 <= b && b <= 0x7A) || (0x41 <= b && b <= 0x5A) || (0x30 <= b && b <= 0x39) || b == 0x5F
}

pub fn look(k: Look, s: &[u8], p: usize) -> (r: bool)
    requires
        p <= s@.len(),
    ensures
        r == look_holds(k, s@, p as int),
{
    match k {
        Look::Start => p == 0,
        Look::End => p == s.len(),
        Look::StartLine => p == 0 || s[p - 1] == 0x0A,
        Look::EndLine => p == s.len() || s[p] == 0x0A,
        Look::Word => {
            let a = p > 0 && word_byte(s[p - 1]);
            let b = p < s.len() && word_byte(s[p]);
            a != b
        },
        Look::NotWord => {
            let a = p > 0 && word_byte(s[p - 1]);
            let b = p < s.len() && word_byte(s[p]);
            a == b
        },
    }
}

// ---------------------------------------------------------------------------
// Thread lists
// ---------------------------------------------------------------------------

/// A capture slot as the spec sees it.
pub open spec fn cv(x: usize) -> int {
    if x == NONE {
        -1
    } else {
        x as int
    }
}

pub open spec fn capv(v: Seq<usize>) -> Seq<int> {
    Seq::new(v.len(), |k: int| cv(v[k]))
}

pub open spec fn idx(k: int, ns: int, j: int) -> int {
    k * ns + j
}

pub proof fn lemma_idx(k: int, n: int, ns: int, j: int)
    requires
        0 <= k < n,
        0 <= j < ns,
    ensures
        0 <= k * ns <= idx(k, ns, j) < n * ns,
        (k + 1) * ns == k * ns + ns,
        (k + 1) * ns <= n * ns,
{
    assert((k + 1) * ns <= n * ns) by (nonlinear_arith)
        requires
            k + 1 <= n,
            ns >= 0,
    ;
    assert((k + 1) * ns == k * ns + ns) by (nonlinear_arith);
    assert(0 <= k * ns) by (nonlinear_arith)
        requires
            0 <= k,
            0 <= ns,
    ;
}

/// Threads in priority order; thread `k` has its capture slots at
/// `caps[k * ns..]`.
pub struct List {
    pub pcs: Vec<u32>,
    pub caps: Vec<usize>,
}

impl List {
    pub open spec fn wf(&self, ns: nat) -> bool {
        self.caps@.len() == self.pcs@.len() * ns
    }

    pub open spec fn v(&self, ns: nat) -> Seq<T> {
        Seq::new(
            self.pcs@.len(),
            |k: int|
                T { pc: self.pcs@[k] as int, caps: Seq::new(ns, |j: int| cv(self.caps@[idx(k, ns as int, j)])) },
        )
    }

    pub fn new() -> (r: List)
        ensures
            forall|ns: nat| r.wf(ns) && #[trigger] r.v(ns) =~= Seq::<T>::empty(),
    {
        let r = List { pcs: Vec::new(), caps: Vec::new() };
        assert forall|ns: nat| r.wf(ns) && #[trigger] r.v(ns) =~= Seq::<T>::empty() by {
            assert(0 * ns == 0) by (nonlinear_arith);
        }
        r
    }

    pub fn clear(&mut self, Ghost(ns): Ghost<nat>)
        ensures
            final(self).wf(ns),
            final(self).v(ns) =~= Seq::<T>::empty(),
    {
        self.pcs.clear();
        self.caps.clear();
        assert(0 * ns == 0) by (nonlinear_arith);
    }

    /// Appends a thread at `pc` with capture slots `cur`.
    pub fn push(&mut self, pc: u32, cur: &Vec<usize>) -> (cost: Ghost<nat>)
        requires
            old(self).wf(cur@.len()),
        ensures
            cost@ == cur@.len(),
            final(self).pcs@.len() == old(self).pcs@.len() + 1,
            final(self).wf(cur@.len()),
            final(self).v(cur@.len()) == old(self).v(cur@.len()).push(T { pc: pc as int, caps: capv(cur@) }),
    {
        let ns = cur.len();
        let ghost n0 = self.pcs@.len() as int;
        let ghost c0 = self.caps@;
        let ghost v0 = self.v(ns as nat);
        self.pcs.push(pc);
        let mut k = 0;
        while k < ns
            invariant
                k <= ns,
                ns == cur@.len(),
                self.caps@ == c0 + cur@.subrange(0, k as int),
                self.pcs@ == old(self).pcs@.push(pc),
            decreases ns - k,
        {
            self.caps.push(cur[k]);
            assert(cur@.subrange(0, k + 1) =~= cur@.subrange(0, k as int).push(cur@[k as int]));
            k += 1;
        }
        proof {
            assert((n0 + 1) * ns == n0 * ns + ns) by (nonlinear_arith);
            let t = T { pc: pc as int, caps: capv(cur@) };
            let a = self.v(ns as nat);
            let b = v0.push(t);
            assert(a.len() == b.len());
            assert forall|kk: int| 0 <= kk < a.len() implies a[kk] == b[kk] by {
                assert forall|j: int| 0 <= j < ns implies a[kk].caps[j] == b[kk].caps[j] by {
                    if kk < n0 {
                        lemma_idx(kk, n0, ns as int, j);
                    } else {
                        assert(idx(kk, ns as int, j) == n0 * ns + j);
                    }
                }
                assert(a[kk].caps =~= b[kk].caps);
            }
            assert(a =~= b);
        }
        Ghost(ns as nat)
    }

    /// Copies the capture slots of thread `i` to `dst`.
    pub fn load(&self, i: usize, dst: &mut Vec<usize>) -> (cost: Ghost<nat>)
        requires
            self.wf(old(dst)@.len()),
            i < self.pcs@.len(),
        ensures
            cost@ == old(dst)@.len(),
            final(dst)@.len() == old(dst)@.len(),
            capv(final(dst)@) == self.v(old(dst)@.len())[i as int].caps,
    {
        let ns = dst.len();
        if ns == 0 {
            assert(capv(dst@) =~= self.v(0)[i as int].caps);
            return Ghost(0);
        }
        proof {
            lemma_idx(i as int, self.pcs@.len() as int, ns as int, 0);
        }
        let cl = self.caps.len();
        assert(0 <= i * ns && i * ns + ns <= cl);
        let base = i * ns;
        let mut k = 0;
        while k < ns
            invariant
                k <= ns,
                ns == dst@.len(),
                base == i * ns,
                base + ns <= cl,
                cl == self.caps@.len(),
                forall|j: int| 0 <= j < k ==> dst@[j] == self.caps@[base + j],
            decreases ns - k,
        {
            dst[k] = self.caps[base + k];
            k += 1;
        }
        assert(capv(dst@) =~= self.v(ns as nat)[i as int].caps);
        Ghost(ns as nat)
    }
}

/// Sets every slot to unset.
pub fn fill_none(cur: &mut Vec<usize>) -> (cost: Ghost<nat>)
    ensures
        cost@ == old(cur)@.len(),
        final(cur)@.len() == old(cur)@.len(),
        capv(final(cur)@) == unset(old(cur)@.len()),
{
    let ns = cur.len();
    let mut k = 0;
    while k < ns
        invariant
            k <= ns,
            ns == cur@.len(),
            forall|j: int| 0 <= j < k ==> cur@[j] == NONE,
        decreases ns - k,
    {
        cur[k] = NONE;
        k += 1;
    }
    assert(capv(cur@) =~= unset(ns as nat));
    Ghost(ns as nat)
}

// ---------------------------------------------------------------------------
// The marking search
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum Frame {
    Explore(u32),
    Restore(u32, usize),
}

pub open spec fn fv(f: Frame) -> F {
    match f {
        Frame::Explore(pc) => F::Ex(pc as int),
        Frame::Restore(slot, old) => F::Re(slot as int, cv(old)),
    }
}

pub open spec fn sv(st: Seq<Frame>) -> Seq<F> {
    Seq::new(st.len(), |k: int| fv(st[k]))
}

/// `seen` is the set of instructions marked with generation `gen`.
pub open spec fn marks(mark: Seq<u64>, gen: u64, seen: Set<int>) -> bool {
    forall|pc: int| #[trigger] seen.contains(pc) <==> (0 <= pc < mark.len() && mark[pc] == gen)
}

pub proof fn lemma_seen_len(seen: Set<int>, n: int)
    requires
        0 <= n,
        forall|pc: int| seen.contains(pc) ==> 0 <= pc < n,
    ensures
        seen.len() <= n,
{
    vstd::set_lib::lemma_int_range(0, n);
    vstd::set_lib::lemma_len_subset(seen, vstd::set_lib::set_int_range(0, n));
}

/// Appends to `list` the threads reached from `pc0` at byte `p` without
/// consuming, in priority order, skipping instructions already marked.
pub fn add(
    prog: &Prog,
    s: &[u8],
    p: usize,
    pc0: u32,
    mark: &mut Vec<u64>,
    gen: u64,
    stack: &mut Vec<Frame>,
    cur: &mut Vec<usize>,
    list: &mut List,
    Ghost(seen): Ghost<Set<int>>,
) -> (r: (Ghost<Set<int>>, Ghost<nat>))
    requires
        prog.wf(),
        forall|v: int| seen.contains(v) ==> 0 <= v < prog.insts@.len(),
        p <= s@.len() < usize::MAX,
        pc0 < prog.insts@.len(),
        old(mark)@.len() == prog.insts@.len(),
        old(cur)@.len() == prog.nslots,
        old(list).wf(prog.nslots as nat),
        old(stack)@.len() == 0,
        marks(old(mark)@, gen, seen),
    ensures
        ({
            let e = ecd(prog.sp(), s@, p as int, pc0 as int, capv(old(cur)@), seen);
            &&& final(list).v(prog.nslots as nat) == old(list).v(prog.nslots as nat) + e.0
            &&& r.0@ == e.1
        }),
        // Work and memory: in proportion to the instructions newly marked.
        r.0@.len() >= seen.len(),
        r.1@ <= (prog.nslots + 3) * (r.0@.len() - seen.len()) + 1,
        final(list).pcs@.len() - old(list).pcs@.len() <= r.0@.len() - seen.len(),
        final(list).wf(prog.nslots as nat),
        marks(final(mark)@, gen, r.0@),
        final(mark)@.len() == old(mark)@.len(),
        final(cur)@.len() == old(cur)@.len(),
        final(stack)@.len() == 0,
        forall|k: int| 0 <= k < old(mark)@.len() ==> final(mark)@[k] == old(mark)@[k] || final(mark)@[k] == gen,
{
    let ghost sp = prog.sp();
    let ghost ns = prog.nslots as nat;
    let ghost n = prog.insts@.len() as int;
    let ghost goal = ecd(sp, s@, p as int, pc0 as int, capv(cur@), seen);
    let ghost l0 = list.v(ns);
    let ghost mut sn = seen;
    let ghost mut cost: nat = 0;
    let ghost kk = ns as int + 3;
    let ghost mut kd: int = 0;
    let ghost l0n = list.pcs@.len() as int;
    stack.push(Frame::Explore(pc0));
    proof {
        lemma_wk_ex(sp, s@, p as int, Seq::<F>::empty(), pc0 as int, capv(cur@), seen);
        assert(sv(stack@) =~= Seq::<F>::empty().push(F::Ex(pc0 as int)));
        lemma_seen_len(sn, n);
    }
    while stack.len() > 0
        invariant
            prog.wf(),
            sp == prog.sp(),
            ns == prog.nslots,
            n == prog.insts@.len(),
            p <= s@.len() < usize::MAX,
            mark@.len() == n,
            cur@.len() == ns,
            list.wf(ns),
            marks(mark@, gen, sn),
            sn.len() <= n,
            kk == ns + 3,
            kd == kk * (sn.len() - seen.len()),
            sn.len() >= seen.len(),
            cost + stack@.len() <= kd + 1,
            stack@.len() <= sn.len() - seen.len() + 1,
            list.pcs@.len() - l0n <= sn.len() - seen.len(),
            forall|k: int| 0 <= k < n ==> mark@[k] == old(mark)@[k] || mark@[k] == gen,
            forall|k: int|
                0 <= k < stack@.len() ==> match #[trigger] stack@[k] {
                    Frame::Explore(pc) => pc < n,
                    Frame::Restore(slot, old) => slot < ns,
                },
            ({
                let w = wk(sp, s@, p as int, sv(stack@), capv(cur@), sn);
                &&& list.v(ns) + w.0 == l0 + goal.0
                &&& w.1 == goal.1
            }),
        decreases 3 * (n - sn.len()) + stack@.len(),
    {
        let ghost st0 = stack@;
        let ghost c = capv(cur@);
        let ghost lv = list.v(ns);
        let f = stack.pop().unwrap();
        proof {
            cost = cost + 1;
        }
        let ghost rest = sv(stack@);
        assert(sv(st0) =~= rest.push(fv(f)));
        match f {
            Frame::Restore(slot, old) => {
                proof {
                    lemma_wk_re(sp, s@, p as int, rest, slot as int, cv(old), c, sn);
                }
                cur[slot as usize] = old;
                assert(capv(cur@) =~= c.update(slot as int, cv(old)));
            },
            Frame::Explore(pc) => {
                proof {
                    lemma_wk_ex(sp, s@, p as int, rest, pc as int, c, sn);
                }
                if mark[pc as usize] == gen {
                    assert(sn.contains(pc as int));
                    assert(lv + Seq::<T>::empty() =~= lv);
                    let ghost w2 = wk(sp, s@, p as int, rest, c, sn);
                    assert(Seq::<T>::empty() + w2.0 =~= w2.0);
                } else {
                    assert(!sn.contains(pc as int));
                    let ghost sn0 = sn;
                    mark[pc as usize] = gen;
                    proof {
                        sn = sn0.insert(pc as int);
                        vstd::set::lemma_set_insert_len(sn0, pc as int);
                        lemma_seen_len(sn, n);
                        assert(fwd_at(sp, pc as int));
                        assert(kk * (sn.len() - seen.len()) == kd + kk) by (nonlinear_arith)
                            requires
                                kd == kk * (sn0.len() - seen.len()),
                                sn.len() == sn0.len() + 1,
                        ;
                        kd = kd + kk;
                    }
                    let ghost e = ecd(sp, s@, p as int, pc as int, c, sn0);
                    let inst = prog.insts[pc as usize];
                    assert(sp[pc as int] == iv(inst, prog.classes@));
                    match inst {
                        Inst::Char { cls, next } => {
                            let pcost = list.push(pc, cur);
                            proof {
                                cost = cost + pcost@;
                                let t = T { pc: pc as int, caps: c };
                                let w2 = wk(sp, s@, p as int, rest, c, sn);
                                assert(e.0 == seq![t]);
                                assert(lv.push(t) + w2.0 =~= lv + (seq![t] + w2.0));
                            }
                        },
                        Inst::Match => {
                            let pcost = list.push(pc, cur);
                            proof {
                                cost = cost + pcost@;
                                let t = T { pc: pc as int, caps: c };
                                let w2 = wk(sp, s@, p as int, rest, c, sn);
                                assert(e.0 == seq![t]);
                                assert(lv.push(t) + w2.0 =~= lv + (seq![t] + w2.0));
                            }
                        },
                        Inst::Fail => {
                            let ghost w2 = wk(sp, s@, p as int, rest, c, sn);
                            assert(Seq::<T>::empty() + w2.0 =~= w2.0);
                        },
                        Inst::Split { a, b } => {
                            stack.push(Frame::Explore(b));
                            stack.push(Frame::Explore(a));
                            proof {
                                let rb = rest.push(F::Ex(b as int));
                                assert(sv(stack@) =~= rb.push(F::Ex(a as int)));
                                lemma_wk_ex(sp, s@, p as int, rb, a as int, c, sn);
                                let r1 = ecd(sp, s@, p as int, a as int, c, sn);
                                lemma_wk_ex(sp, s@, p as int, rest, b as int, c, r1.1);
                                let r2 = ecd(sp, s@, p as int, b as int, c, r1.1);
                                let w3 = wk(sp, s@, p as int, rest, c, r2.1);
                                assert(e.0 == r1.0 + r2.0);
                                assert(lv + (r1.0 + (r2.0 + w3.0)) =~= lv + ((r1.0 + r2.0) + w3.0));
                            }
                        },
                        Inst::Save { slot, next } => {
                            let old = cur[slot as usize];
                            stack.push(Frame::Restore(slot, old));
                            cur[slot as usize] = p;
                            stack.push(Frame::Explore(next));
                            proof {
                                let c2 = c.update(slot as int, p as int);
                                assert(capv(cur@) =~= c2);
                                let rr = rest.push(F::Re(slot as int, cv(old)));
                                assert(sv(stack@) =~= rr.push(F::Ex(next as int)));
                                lemma_wk_ex(sp, s@, p as int, rr, next as int, c2, sn);
                                let r1 = ecd(sp, s@, p as int, next as int, c2, sn);
                                lemma_wk_re(sp, s@, p as int, rest, slot as int, cv(old), c2, r1.1);
                                assert(c2.update(slot as int, cv(old)) =~= c);
                            }
                        },
                        Inst::Look { k, next } => {
                            if look(k, s, p) {
                                stack.push(Frame::Explore(next));
                                assert(sv(stack@) =~= rest.push(F::Ex(next as int)));
                                proof {
                                    lemma_wk_ex(sp, s@, p as int, rest, next as int, c, sn);
                                }
                            } else {
                                let ghost w2 = wk(sp, s@, p as int, rest, c, sn);
                                assert(Seq::<T>::empty() + w2.0 =~= w2.0);
                            }
                        },
                    }
                }
            },
        }
    }
    proof {
        assert(sv(stack@) =~= Seq::<F>::empty());
        assert(list.v(ns) + Seq::<T>::empty() =~= list.v(ns));
    }
    (Ghost(sn), Ghost(cost))
}


// ---------------------------------------------------------------------------
// The search
// ---------------------------------------------------------------------------

/// The matcher's working memory, sized for one program.
pub struct Scratch {
    pub mark: Vec<u64>,
    pub gen: u64,
    pub tmark: Vec<u64>,
    pub tgen: u64,
    pub stack: Vec<Frame>,
    pub cur: Vec<usize>,
    pub a: List,
    pub b: List,
    pub t: List,
    pub dfa: Dfa,
    pub memo: Memo,
    pub ta: Vec<Th>,
    pub tb: Vec<Th>,
    /// How little DFA passes have skipped lately, and a count of the
    /// passes left out since. Only a choice of when to try.
    pub dq: u8,
    pub dt: u8,
}

impl Scratch {
    pub open spec fn wf(&self, prog: &Prog) -> bool {
        &&& self.mark@.len() == prog.insts@.len()
        &&& self.tmark@.len() == prog.insts@.len()
        &&& forall|k: int| 0 <= k < self.mark@.len() ==> #[trigger] self.mark@[k] <= self.gen
        &&& forall|k: int| 0 <= k < self.tmark@.len() ==> #[trigger] self.tmark@[k] <= self.tgen
        &&& self.stack@.len() == 0
        &&& self.cur@.len() == prog.nslots
        &&& self.dfa.wf(prog)
        &&& self.memo.wf(prog)
    }

    pub fn new(prog: &Prog) -> (r: Scratch)
        requires
            prog.wf(),
        ensures
            r.wf(prog),
    {
        let n = prog.insts.len();
        let mut mark: Vec<u64> = Vec::new();
        let mut tmark: Vec<u64> = Vec::new();
        let mut k = 0;
        while k < n
            invariant
                k <= n,
                mark@.len() == k,
                tmark@.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] mark@[j] == 0,
                forall|j: int| 0 <= j < k ==> #[trigger] tmark@[j] == 0,
            decreases n - k,
        {
            mark.push(0);
            tmark.push(0);
            k += 1;
        }
        let mut cur: Vec<usize> = Vec::new();
        let mut k = 0;
        while k < prog.nslots
            invariant
                k <= prog.nslots,
                cur@.len() == k,
            decreases prog.nslots - k,
        {
            cur.push(NONE);
            k += 1;
        }
        Scratch {
            mark: mark,
            gen: 0,
            tmark: tmark,
            tgen: 0,
            stack: Vec::new(),
            cur: cur,
            a: List::new(),
            b: List::new(),
            t: List::new(),
            dfa: Dfa::new(prog),
            memo: Memo::new(prog),
            ta: Vec::new(),
            tb: Vec::new(),
            dq: 0,
            dt: 0,
        }
    }
}

/// A generation no mark carries.
pub fn bump(mark: &mut Vec<u64>, gen: u64) -> (r: (u64, Ghost<nat>))
    requires
        forall|k: int| 0 <= k < old(mark)@.len() ==> #[trigger] old(mark)@[k] <= gen,
    ensures
        final(mark)@.len() == old(mark)@.len(),
        forall|k: int| 0 <= k < final(mark)@.len() ==> #[trigger] final(mark)@[k] < r.0,
        r.1@ <= old(mark)@.len(),
{
    if gen == u64::MAX {
        let n = mark.len();
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == mark@.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] mark@[k] == 0,
            decreases n - i,
        {
            mark[i] = 0;
            i += 1;
        }
        (1, Ghost(n as nat))
    } else {
        (gen + 1, Ghost(0))
    }
}

proof fn lemma_fr_cons(p: Seq<SInst>, s: Seq<u8>, l: Seq<T>, i: int, at: int)
    requires
        0 <= i < l.len(),
    ensures
        fr(p, s, l.subrange(i, l.len() as int), at) == or(
            first(pmt(p, s, l[i], at)),
            fr(p, s, l.subrange(i + 1, l.len() as int), at),
        ),
{
    let a = seq![l[i]];
    let b = l.subrange(i + 1, l.len() as int);
    assert(l.subrange(i, l.len() as int) =~= a + b);
    lemma_fr_app(p, s, a, b, at);
    lemma_res_one(p, s, l[i], at);
}

pub proof fn lemma_fr_empty(p: Seq<SInst>, s: Seq<u8>, l: Seq<T>, at: int)
    requires
        l.len() == 0,
    ensures
        fr(p, s, l, at) is None,
{
}

proof fn lemma_inv_empty(p: Seq<SInst>, s: Seq<u8>, i: int, l: Seq<T>)
    requires
        l.len() == 0,
    ensures
        inv_list(p, s, i, Set::<int>::empty(), l),
{
}

pub proof fn lemma_mul_le(a: int, b: int, c: int)
    requires
        a <= b,
        0 <= c,
    ensures
        c * a <= c * b,
        a * c <= b * c,
{
    assert(c * a <= c * b) by (nonlinear_arith)
        requires
            a <= b,
            0 <= c,
    ;
    assert(a * c <= b * c) by (nonlinear_arith)
        requires
            a <= b,
            0 <= c,
    ;
}

pub proof fn lemma_mul_add(c: int, a: int, b: int)
    ensures
        c * (a + b) == c * a + c * b,
        (a + b) * c == a * c + b * c,
        c * (a - b) == c * a - c * b,
{
    assert(c * (a + b) == c * a + c * b) by (nonlinear_arith);
    assert((a + b) * c == a * c + b * c) by (nonlinear_arith);
    assert(c * (a - b) == c * a - c * b) by (nonlinear_arith);
}

/// The most loop iterations the matcher spends on one byte of the text,
/// for a program of `np` instructions and `ns` capture slots.
pub open spec fn pike_cost(np: int, ns: int) -> int {
    5 * ((ns + 3) * np) + (ns + 67) * np + (ns + 67) + 7 * np + 7 * ns + 12
}

/// Loop iterations per byte the DFA takes, at most: one lookup, and one
/// transition to compute if it is not known yet.
pub open spec fn dfa_cost(np: int) -> int {
    trans_cost(np) + np + 2
}

/// Loop iterations per byte of text, at most, for a program of `np`
/// instructions and `ns` capture slots.
pub open spec fn step_cost(np: int, ns: int) -> int {
    pike_cost(np, ns) + dfa_cost(np) + memo_cost(np, ns) + 2
}

/// The Pike VM's and the DFA's iterations together are within the bound.
proof fn lemma_total(x: int, d: int, k: int, h: int, sc: int, dc: int)
    requires
        x <= k * sc,
        d <= h * dc,
        h <= k,
        0 <= dc,
    ensures
        x + d <= k * (sc + dc),
{
    assert(h * dc <= k * dc) by (nonlinear_arith)
        requires
            h <= k,
            0 <= dc,
    ;
    assert(k * (sc + dc) == k * sc + k * dc) by (nonlinear_arith);
}

/// What `run` reports: the end of the match and its capture slots.
pub open spec fn reported(m: Option<M>, r: Option<usize>, out: Seq<usize>) -> bool {
    match m {
        Some(m) => r == Some(m.end as usize) && 0 <= m.end <= usize::MAX && capv(out) == m.caps,
        None => r is None,
    }
}

/// With no thread alive: passes over bytes at which no match can start,
/// from `p`, which is such a byte.
#[inline(never)]
fn skip_ahead(prog: &Prog, s: &[u8], p: usize, sc: &mut Scratch) -> (r: (usize, Ghost<int>))
    requires
        prog.wf(),
        prog.skip@.len() == 256,
        p < s@.len(),
        !prog.skip@[s@[p as int] as int],
        old(sc).wf(prog),
    ensures
        final(sc).wf(prog),
        final(sc).a == old(sc).a,
        final(sc).b == old(sc).b,
        marks(final(sc).mark@, final(sc).gen, Set::<int>::empty()),
        p < r.0 <= s@.len(),
        r.1@ <= 3 * (r.0 - p) + prog.insts@.len(),
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    let (q, kc) = skip_run(prog, s, p);
    let (g, bc) = bump(&mut sc.mark, sc.gen);
    sc.gen = g;
    (q, Ghost(kc@ + bc@))
}

/// With no thread alive at `p`: lets the DFA find how far the search may
/// jump. Gives `(q, e)`: the search may resume at `q`; the DFA read up
/// to `e`.
#[inline(never)]
fn dfa_skip(prog: &Prog, s: &[u8], p: usize, sc: &mut Scratch, nst: &mut NeedSt) -> (r: (
    usize,
    usize,
    Ghost<int>,
    Ghost<int>,
))
    requires
        prog.wf(),
        p <= s@.len(),
        old(sc).wf(prog),
        prog.need matches Some(x) ==> old(nst).inv(s@, x) && (old(nst).have ==> old(nst).lo <= p),
        !old(nst).have ==> old(nst).h <= p,
    ensures
        final(sc).wf(prog),
        prog.need matches Some(x) ==> final(nst).inv(s@, x) && (final(nst).have ==> final(nst).lo <= r.0),
        prog.need is None ==> *final(nst) == *old(nst),
        old(nst).have ==> final(nst).have,
        old(nst).h <= final(nst).h,
        !final(nst).have ==> final(nst).h == old(nst).h,
        0 <= r.3@ <= 2 * (final(nst).h - old(nst).h) + if old(nst).have || !final(nst).have {
            0int
        } else {
            1int
        },
        final(sc).a == old(sc).a,
        final(sc).b == old(sc).b,
        r.0 > p ==> marks(final(sc).mark@, final(sc).gen, Set::<int>::empty()),
        r.0 == p ==> final(sc).mark == old(sc).mark && final(sc).gen == old(sc).gen,
        p <= r.0 <= r.1 <= s@.len(),
        r.2@ <= (r.1 - p + 1) * dfa_cost(prog.insts@.len() as int),
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
{
    let ghost np = prog.insts@.len() as int;
    let (q, e, dc, nc) = dfa_ahead(prog, s, p, &mut sc.dfa, nst);
    proof {
        assert((e - p + 1) * dfa_cost(np) == (e - p + 1) * (trans_cost(np) + 2) + (e - p + 1) * np) by (nonlinear_arith)
            requires
                dfa_cost(np) == trans_cost(np) + 2 + np,
        ;
        assert((e - p + 1) * np >= np) by (nonlinear_arith)
            requires
                e - p + 1 >= 1,
                np >= 0,
        ;
    }
    if q > p {
        let (g, bc) = bump(&mut sc.mark, sc.gen);
        sc.gen = g;
        (q, e, Ghost(dc@ + bc@), nc)
    } else {
        (q, e, dc, nc)
    }
}

/// The leftmost match starting at or after `from`, by priority: where it
/// ends, with its capture slots in `out`.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub fn run(prog: &Prog, s: &[u8], from: usize, sc: &mut Scratch, out: &mut Vec<usize>) -> (r: (
    Option<usize>,
    Ghost<int>,
))
    requires
        prog.wf(),
        from <= s@.len() < usize::MAX,
        old(sc).wf(prog),
        old(out)@.len() == prog.nslots,
    ensures
        final(sc).wf(prog),
        final(out)@.len() == prog.nslots,
        reported(search_p(prog.sp(), s@, prog.start as int, from as int, prog.nslots as nat), r.0, final(out)@),
        // Loop iterations: linear in the text, for a fixed program.
        r.1@ <= (s@.len() - from + 2) * step_cost(prog.insts@.len() as int, prog.nslots as int),
        // Memory: no thread list is ever longer than the program (and the
        // stack never deeper than that plus one: see `add`).
        final(sc).a.pcs@.len() <= prog.insts@.len(),
        final(sc).b.pcs@.len() <= prog.insts@.len(),
{
    let ghost np = prog.insts@.len() as int;
    let ghost kk = prog.nslots as int + 3;
    let ghost ww = prog.nslots as int + 67;
    let ghost kn = kk * np;
    let ghost wn = ww * np;
    let ghost scost = pike_cost(np, prog.nslots as int);
    let ghost dcost = dfa_cost(np);
    let ghost mcost = memo_step(np, prog.nslots as int);
    let ghost mut drys: int = 0;
    let mut dh = from;
    let ghost mut nsteps: int = 0;
    let mut nst = NeedSt::new(from);
    let ghost mut dsteps: int = 0;
    let ghost mut msteps: int = 0;
    let mut hz = from;
    let ghost qq = kn + 2 * np + 2 * prog.nslots as int + 3;
    let ghost mut steps: int = 0;
    proof {
        lemma_mul_le(0, np, kk);
        lemma_mul_le(0, np, ww);
        assert(scost == 5 * kn + wn + ww + 7 * np + 7 * prog.nslots + 12);
        assert(0 * scost == 0) by (nonlinear_arith);
        assert(0 * dcost == 0) by (nonlinear_arith);
        assert(0 * mcost == 0) by (nonlinear_arith);
        assert(np * (prog.nslots as int + 2) >= 0) by (nonlinear_arith)
            requires
                np >= 0,
        ;
    }
    let ghost sp = prog.sp();
    let ghost ns = prog.nslots as nat;
    let ghost st = prog.start as int;
    let ghost ans = search_p(sp, s@, st, from as int, ns);
    let n = s.len();
    let start = prog.start as u32;
    let mut matched = false;
    let mut mend: usize = 0;
    let ghost mut mv = M { end: 0, caps: seq![] };
    let mut p = from;
    sc.a.clear(Ghost(ns));
    sc.b.clear(Ghost(ns));
    let (g, bc0) = bump(&mut sc.mark, sc.gen);
    sc.gen = g;
    let ghost mut seen = Set::<int>::empty();
    proof {
        steps = bc0@ as int;
        lemma_inv_empty(sp, s@, p as int, sc.a.v(ns));
        lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
    }
    loop
        invariant
            prog.wf(),
            sp == prog.sp(),
            ns == prog.nslots,
            st == prog.start,
            start == prog.start,
            n == s@.len(),
            n < usize::MAX,
            ans == search_p(sp, s@, st, from as int, ns),
            from <= p <= n,
            np == prog.insts@.len(),
            kk == ns + 3,
            ww == ns + 67,
            kn == kk * np,
            wn == ww * np,
            0 <= kn,
            0 <= wn,
            scost == 5 * kn + wn + ww + 7 * np + 7 * ns + 12,
            scost == pike_cost(np, ns as int),
            dcost == dfa_cost(np),
            0 <= dcost,
            from <= hz <= n + 1,
            dsteps <= (hz - from) * dcost,
            mcost == memo_step(np, ns as int),
            from <= dh <= n,
            0 <= drys <= dh - from,
            prog.need matches Some(x) ==> nst.inv(s@, x) && (nst.have ==> nst.lo <= p),
            from <= nst.h <= n,
            !nst.have ==> nst.h == from,
            0 <= nsteps <= 2 * (nst.h - from) + if nst.have {
                1int
            } else {
                0int
            },
            0 <= mcost,
            msteps <= (p - from) * mcost,
            qq == kn + 2 * np + 2 * ns + 3,
            steps <= (p - from) * scost + np,
            sc.a.pcs@.len() <= seen.len(),
            sc.b.pcs@.len() <= np,
            sc.wf(prog),
            sc.a.wf(ns),
            out@.len() == ns,
            marks(sc.mark@, sc.gen, seen),
            inv_list(sp, s@, p as int, seen, sc.a.v(ns)),
            ans == or(
                fr(sp, s@, sc.a.v(ns), p as int),
                if matched {
                    Some(mv)
                } else {
                    search_p(sp, s@, st, p as int, ns)
                },
            ),
            matched ==> mv.end == mend && capv(out@) == mv.caps,
        decreases n - p,
    {
        let ghost ph = p;
        if !matched && sc.a.pcs.len() == 0 && prog.skip.len() == 256 && p < n && !prog.skip[s[p] as usize] {
            let ghost p0 = p;
            proof {
                lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
            }
            let (q, sk) = skip_ahead(prog, s, p, sc);
            p = q;
            proof {
                let k = p - p0;
                seen = Set::<int>::empty();
                lemma_inv_empty(sp, s@, p as int, sc.a.v(ns));
                lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
                lemma_mul_add(scost, p0 - from, k);
                assert(3 * k + np <= k * scost) by (nonlinear_arith)
                    requires
                        k >= 1,
                        scost >= np + 3,
                        np >= 0,
                ;
                steps = steps + sk@;
            }
        }
        // Where most starts the skip finds go on to match, the DFA pass
        // only repeats work. A pass that skips nothing scores one, a
        // pass that skips takes three off, and from eight up the pass
        // runs one time in eight.
        let mut dgo = !matched && sc.a.pcs.len() == 0 && p >= hz && p < n;
        if dgo && sc.dq >= 8 {
            if sc.dt < 7 {
                sc.dt = sc.dt + 1;
                dgo = false;
            } else {
                sc.dt = 0;
            }
        }
        if dgo {
            let ghost p0 = p;
            let ghost hz0 = hz;
            proof {
                lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
            }
            let (q, e, dc, nc) = dfa_skip(prog, s, p, sc, &mut nst);
            proof {
                nsteps = nsteps + nc@;
            }
            hz = e + 1;
            if q > p {
                sc.dq = if sc.dq >= 3 {
                    sc.dq - 3
                } else {
                    0
                };
            } else if sc.dq < 16 {
                sc.dq = sc.dq + 1;
            }
            if q > p {
                p = q;
                proof {
                    seen = Set::<int>::empty();
                    lemma_inv_empty(sp, s@, p as int, sc.a.v(ns));
                    lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
                    lemma_mul_le(p0 - from, p - from, scost);
                }
            }
            proof {
                lemma_mul_le(e - p0 + 1, hz - hz0, dcost);
                lemma_mul_add(dcost, hz0 - from, hz - hz0);
                dsteps = dsteps + dc@;
            }
        }
        let ghost steps0 = steps;
        let ghost mut c1: int = 1;
        proof {
            lemma_seen_len(seen, np);
            lemma_mul_add(scost, p - from, 1);
            lemma_mul_le(p - from + 1, n - from + 1, scost);
            lemma_mul_add(scost, n - from + 1, 1);
        }
        if !matched {
            let fc = fill_none(&mut sc.cur);
            let ghost l0 = sc.a.v(ns);
            proof {
                lemma_add_ecd(sp, s@, p as int, st, unset(ns), seen, l0);
            }
            let gs = add(prog, s, p, start, &mut sc.mark, sc.gen, &mut sc.stack, &mut sc.cur, &mut sc.a, Ghost(seen));
            proof {
                lemma_seen_len(gs.0@, np);
                lemma_mul_le(gs.0@.len() - seen.len(), np, kk);
                c1 = c1 + fc@ + gs.1@;
                seen = gs.0@;
            }
        }
        assert(c1 <= ns + kn + 2);
        assert(sc.a.pcs@.len() <= np);
        assert(ans == or(
            fr(sp, s@, sc.a.v(ns), p as int),
            if matched {
                Some(mv)
            } else {
                search_p(sp, s@, st, p + 1, ns)
            },
        ));
        let ghost pb = p;
        let ghost dh0 = dh;
        let fr_ = fast_run(
            prog,
            s,
            p,
            &mut sc.memo,
            &mut sc.a,
            &mut sc.b,
            &mut sc.ta,
            &mut sc.tb,
            out, matched, mend, Ghost(mv), Ghost(ans), dh);
        proof {
            drys = drys + (fr_.5 - dh);
        }
        dh = fr_.5;
        p = fr_.0;
        matched = fr_.1;
        mend = fr_.2;
        proof {
            mv = fr_.3@;
            assert((pb - from) * mcost + (p - pb + 1) * mcost == (p - from + 1) * mcost) by (nonlinear_arith);
            let ghost m0 = msteps;
            lemma_mul_le(ph - from, pb - from, mcost);
            assert(m0 <= (pb - from) * mcost);
            assert(fr_.4@ - (fr_.5 - dh0) <= (p - pb + 1) * mcost);
            msteps = msteps + fr_.4@ - (fr_.5 - dh0);
            assert(msteps <= (p - from + 1) * mcost);
            lemma_mul_le(pb - from, p - from, scost);
            lemma_mul_add(scost, p - from, 1);
            lemma_mul_le(p - from + 1, n - from + 1, scost);
            lemma_mul_le(p - from + 1, n - from + 1, mcost);
        }
        assert(msteps <= (p - from + 1) * mcost);
        let ghost tail = if matched {
            Some(mv)
        } else {
            search_p(sp, s@, st, p + 1, ns)
        };
        assert(ans == or(fr(sp, s@, sc.a.v(ns), p as int), tail));
        if sc.a.pcs.len() == 0 && matched {
            proof {
                lemma_fr_empty(sp, s@, sc.a.v(ns), p as int);
            }
            proof {
                assert(steps0 + c1 <= (n - from + 2) * scost);
                lemma_mul_le(hz - from, n + 1 - from, dcost);
                lemma_total(steps0 + c1, dsteps, n - from + 2, n + 1 - from, scost, dcost);
                    lemma_total(steps0 + c1 + dsteps, msteps, n - from + 2, n + 1 - from, scost + dcost, mcost);
                    lemma_total(steps0 + c1 + dsteps + msteps, drys, n - from + 2, n - from, scost + dcost + mcost, 1);
                    lemma_total(steps0 + c1 + dsteps + msteps + drys, nsteps, n - from + 2, n - from + 1, scost + dcost + mcost + 1, 2);
            }
            return (Some(mend), Ghost(steps0 + c1 + dsteps + msteps + drys + nsteps));
        }
        let (cp, l) = if p < n {
            decode(s, p)
        } else {
            (INVALID, 1)
        };
        let ghost p2 = p + l;
        let (g, bc) = bump(&mut sc.mark, sc.gen);
        sc.gen = g;
        let ghost mut seen2 = Set::<int>::empty();
        let ghost mut c2: int = 0;
        let ghost mut wi: int = 0;
        let ghost mut ks: int = 0;
        proof {
            assert(ww * 0 == 0) by (nonlinear_arith);
            assert(kk * 0 == 0) by (nonlinear_arith);
        }
        sc.b.clear(Ghost(ns));
        proof {
            lemma_inv_empty(sp, s@, p2, sc.b.v(ns));
        }
        let ghost al = sc.a.v(ns);
        let alen = sc.a.pcs.len();
        let mut i = 0;
        let mut cut = false;
        proof {
            assert(al.subrange(0, alen as int) =~= al);
            lemma_fr_empty(sp, s@, sc.b.v(ns), p2);
        }
        while i < alen && !cut
            invariant
                prog.wf(),
                sp == prog.sp(),
                ns == prog.nslots,
                st == prog.start,
                n == s@.len(),
                n < usize::MAX,
                p <= n,
                p2 == p + l,
                p < n ==> match dec(s@, p as int) {
                    Some((c, ll)) => cp == c && l == ll && c != INVALID && 1 <= ll <= 4 && p + ll <= n,
                    None => cp == INVALID && l == 1,
                },
                p >= n ==> cp == INVALID,
                sc.wf(prog),
                sc.a.wf(ns),
                sc.b.wf(ns),
                al == sc.a.v(ns),
                alen == sc.a.pcs@.len(),
                alen == al.len(),
                i <= alen,
                alen <= np,
                np == prog.insts@.len(),
                kk == ns + 3,
                ww == ns + 67,
                wi == ww * i,
                ks == kk * seen2.len(),
                c2 <= wi + ks + (if cut { ww } else { 0 }),
                sc.b.pcs@.len() <= seen2.len(),
                out@.len() == ns,
                marks(sc.mark@, sc.gen, seen2),
                inv_list(sp, s@, p2, seen2, sc.b.v(ns)),
                p >= n ==> sc.b.v(ns).len() == 0,
                ans == or(
                    fr(sp, s@, sc.b.v(ns), p2),
                    if cut {
                        Some(mv)
                    } else {
                        or(fr(sp, s@, al.subrange(i as int, alen as int), p as int), tail)
                    },
                ),
                cut ==> matched,
                !cut ==> tail == (if matched {
                    Some(mv)
                } else {
                    search_p(sp, s@, st, p + 1, ns)
                }),
                matched ==> mv.end == mend && capv(out@) == mv.caps,
            decreases alen - i + (if cut { 0int } else { 1 }),
        {
            let pc = sc.a.pcs[i];
            let ghost t = al[i as int];
            proof {
                lemma_fr_cons(sp, s@, al, i as int, p as int);
            }
            assert(t.pc == pc);
            let ghost c20 = c2;
            proof {
                c2 = c2 + 1;
                lemma_mul_add(ww, i as int, 1);
            }
            if (pc as usize) < prog.insts.len() {
                let inst = prog.insts[pc as usize];
                assert(sp[pc as int] == iv(inst, prog.classes@));
                match inst {
                    Inst::Match => {
                        let lc = sc.a.load(i, out);
                        proof {
                            c2 = c2 + lc@;
                        }
                        matched = true;
                        mend = p;
                        cut = true;
                        proof {
                            mv = M { end: p as int, caps: t.caps };
                            assert(pmt(sp, s@, t, p as int) == seq![mv]);
                        }
                    },
                    Inst::Char { cls, next } => {
                        let (inc, cc) = if cp != INVALID {
                            prog.classes[cls as usize].contains_c(cp)
                        } else {
                            (false, Ghost(0nat))
                        };
                        proof {
                            c2 = c2 + cc@;
                        }
                        if inc {
                            let lc = sc.a.load(i, &mut sc.cur);
                            let ghost b0 = sc.b.v(ns);
                            proof {
                                assert(fwd_at(sp, pc as int));
                                lemma_add_ecd(sp, s@, p2, next as int, t.caps, seen2, b0);
                                assert(pmt(sp, s@, t, p as int) == pm(sp, s@, next as int, p2, t.caps));
                            }
                            let gs = add(
                                prog,
                                s,
                                p + l,
                                next,
                                &mut sc.mark,
                                sc.gen,
                                &mut sc.stack,
                                &mut sc.cur,
                                &mut sc.b,
                                Ghost(seen2),
                            );
                            proof {
                                lemma_mul_add(kk, seen2.len() as int, gs.0@.len() - seen2.len());
                                c2 = c2 + lc@ + gs.1@;
                                ks = kk * gs.0@.len();
                                seen2 = gs.0@;
                            }
                        } else {
                            assert(pmt(sp, s@, t, p as int).len() == 0);
                        }
                    },
                    _ => {
                        assert(pmt(sp, s@, t, p as int).len() == 0);
                    },
                }
            } else {
                assert(pmt(sp, s@, t, p as int).len() == 0);
            }
            if !cut {
                i += 1;
                proof {
                    wi = wi + ww;
                }
            }
        }
        proof {
            lemma_seen_len(seen2, np);
            lemma_mul_le(seen2.len() as int, np, kk);
            lemma_mul_le(i as int, np, ww);
        }
        assert(c2 <= wn + kn + ww);
        assert(sc.b.pcs@.len() <= np);
        proof {
            if !cut {
                lemma_fr_empty(sp, s@, al.subrange(i as int, alen as int), p as int);
            }
        }
        assert(ans == or(
            fr(sp, s@, sc.b.v(ns), p2),
            if matched {
                Some(mv)
            } else {
                search_p(sp, s@, st, p + 1, ns)
            },
        ));
        if p >= n {
            proof {
                lemma_fr_empty(sp, s@, sc.b.v(ns), p2);
            }
            if matched {
                proof {
                    assert(steps0 + c1 + bc@ + c2 <= (n - from + 2) * scost);
                    lemma_mul_le(hz - from, n + 1 - from, dcost);
                    lemma_total(steps0 + c1 + bc@ + c2, dsteps, n - from + 2, n + 1 - from, scost, dcost);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps, msteps, n - from + 2, n + 1 - from, scost + dcost, mcost);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps + msteps, drys, n - from + 2, n - from, scost + dcost + mcost, 1);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps + msteps + drys, nsteps, n - from + 2, n - from + 1, scost + dcost + mcost + 1, 2);
                }
                return (Some(mend), Ghost(steps0 + c1 + bc@ + c2 + dsteps + msteps + drys + nsteps));
            } else {
                proof {
                    assert(steps0 + c1 + bc@ + c2 <= (n - from + 2) * scost);
                    lemma_mul_le(hz - from, n + 1 - from, dcost);
                    lemma_total(steps0 + c1 + bc@ + c2, dsteps, n - from + 2, n + 1 - from, scost, dcost);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps, msteps, n - from + 2, n + 1 - from, scost + dcost, mcost);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps + msteps, drys, n - from + 2, n - from, scost + dcost + mcost, 1);
                    lemma_total(steps0 + c1 + bc@ + c2 + dsteps + msteps + drys, nsteps, n - from + 2, n - from + 1, scost + dcost + mcost + 1, 2);
                }
                return (None, Ghost(steps0 + c1 + bc@ + c2 + dsteps + msteps + drys + nsteps));
            }
        }
        // Starts strictly inside a multi-byte character can only match empty.
        let mut q = p + 1;
        let ghost mut c3: int = 0;
        let ghost mut mi: int = 0;
        proof {
            assert(0 * qq == 0) by (nonlinear_arith);
        }
        while q < p + l && !matched
            invariant
                prog.wf(),
                sp == prog.sp(),
                ns == prog.nslots,
                st == prog.start,
                start == prog.start,
                n == s@.len(),
                n < usize::MAX,
                p < n,
                p2 == p + l,
                p2 <= n,
                1 <= l <= 4,
                l > 1 ==> dec(s@, p as int) == Some((cp, l as int)),
                p < q <= p + l,
                np == prog.insts@.len(),
                kk == ns + 3,
                kn == kk * np,
                qq == kn + 2 * np + 2 * ns + 3,
                0 <= mi <= q - p - 1 + (if matched { 1int } else { 0 }),
                matched ==> q < p + l || mi <= q - p - 1,
                c3 <= mi * qq,
                sc.b.pcs@.len() <= np,
                sc.wf(prog),
                sc.a.wf(ns),
                sc.b.wf(ns),
                out@.len() == ns,
                marks(sc.mark@, sc.gen, seen2),
                inv_list(sp, s@, p2, seen2, sc.b.v(ns)),
                ans == or(
                    fr(sp, s@, sc.b.v(ns), p2),
                    if matched {
                        Some(mv)
                    } else {
                        search_p(sp, s@, st, q as int, ns)
                    },
                ),
                matched ==> mv.end == mend && capv(out@) == mv.caps,
            decreases p + l - q + (if matched { 0int } else { 1 }),
        {
            let (tg, tbc) = bump(&mut sc.tmark, sc.tgen);
            sc.tgen = tg;
            sc.t.clear(Ghost(ns));
            let fc = fill_none(&mut sc.cur);
            proof {
                lemma_inv_empty(sp, s@, q as int, sc.t.v(ns));
                lemma_add_ecd(sp, s@, q as int, st, unset(ns), Set::<int>::empty(), sc.t.v(ns));
                lemma_fr_empty(sp, s@, sc.t.v(ns), q as int);
                lemma_mid(s@, p as int, l as int, q as int);
            }
            let ghost e = ecd(sp, s@, q as int, st, unset(ns), Set::<int>::empty());
            let ghost t0 = sc.t.v(ns);
            let tgs = add(
                prog,
                s,
                q,
                start,
                &mut sc.tmark,
                sc.tgen,
                &mut sc.stack,
                &mut sc.cur,
                &mut sc.t,
                Ghost(Set::<int>::empty()),
            );
            let ghost tl = sc.t.v(ns);
            let ghost mut c4: int = 0;
            proof {
                lemma_seen_len(tgs.0@, np);
                lemma_mul_le(tgs.0@.len() as int, np, kk);
            }
            assert(tl =~= t0 + e.0);
            assert(fr(sp, s@, tl, q as int) == first(pm(sp, s@, st, q as int, unset(ns))));
            let tlen = sc.t.pcs.len();
            let mut j = 0;
            let mut found = false;
            assert(tl.subrange(0, tlen as int) =~= tl);
            while j < tlen && !found
                invariant
                    prog.wf(),
                    sp == prog.sp(),
                    ns == prog.nslots,
                    n == s@.len(),
                    q <= n,
                    dec(s@, q as int) is None,
                    sc.t.wf(ns),
                    tl == sc.t.v(ns),
                    tlen == sc.t.pcs@.len(),
                    tlen == tl.len(),
                    j <= tlen,
                    c4 <= j + (if found { ns + 1 } else { 0 }),
                    out@.len() == ns,
                    !found ==> fr(sp, s@, tl, q as int) == fr(sp, s@, tl.subrange(j as int, tlen as int), q as int),
                    found ==> fr(sp, s@, tl, q as int) == Some(mv) && mv.end == q && capv(out@) == mv.caps,
                decreases tlen - j + (if found { 0int } else { 1 }),
            {
                let pc = sc.t.pcs[j];
                let ghost t = tl[j as int];
                proof {
                    lemma_fr_cons(sp, s@, tl, j as int, q as int);
                }
                assert(t.pc == pc);
                let mut is_match = false;
                if (pc as usize) < prog.insts.len() {
                    let inst = prog.insts[pc as usize];
                    assert(sp[pc as int] == iv(inst, prog.classes@));
                    match inst {
                        Inst::Match => {
                            is_match = true;
                        },
                        _ => {},
                    }
                }
                proof {
                    c4 = c4 + 1;
                }
                if is_match {
                    let lc = sc.t.load(j, out);
                    proof {
                        c4 = c4 + lc@;
                    }
                    found = true;
                    proof {
                        mv = M { end: q as int, caps: t.caps };
                        assert(pmt(sp, s@, t, q as int) == seq![mv]);
                    }
                } else {
                    assert(pmt(sp, s@, t, q as int).len() == 0);
                    j += 1;
                }
            }
            proof {
                if !found {
                    lemma_fr_empty(sp, s@, tl.subrange(j as int, tlen as int), q as int);
                }
            }
            proof {
                lemma_mul_add(qq, mi, 1);
                assert(1 + tbc@ + fc@ + tgs.1@ + c4 <= qq);
                c3 = c3 + 1 + tbc@ + fc@ + tgs.1@ + c4;
                mi = mi + 1;
            }
            if found {
                matched = true;
                mend = q;
            } else {
                q += 1;
            }
        }
        proof {
            assert(mi <= 3);
            lemma_mul_le(mi, 3, qq);
            assert(0 <= qq);
            steps = steps0 + c1 + bc@ + c2 + c3;
            lemma_mul_add(scost, p - from, l as int);
            lemma_mul_le(1, l as int, scost);
            lemma_mul_le(p - from + 1, p + l - from, mcost);
        }
        core::mem::swap(&mut sc.a, &mut sc.b);
        p += l;
        proof {
            seen = seen2;
        }
    }
}

} // verus!
