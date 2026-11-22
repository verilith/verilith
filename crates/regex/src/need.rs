//! A byte every match must contain.
//!
//! Some patterns cannot match without consuming one particular ASCII
//! byte: `@` in an e-mail address, `=` in `(\w+)=(\w*)`. If every path
//! from the start of the program to `Match` passes an instruction that
//! consumes that byte and nothing else, then no match ends before the
//! next occurrence of the byte, and since a match is made only of bytes
//! the program can consume at all (its alphabet), no match starts before
//! the run of alphabet bytes that leads up to that occurrence. A search
//! with no thread alive may jump to the start of that run.
use crate::class::Class;
use crate::compile::*;
use crate::data::*;
use crate::prog::*;
use crate::sem::*;
use crate::skip::*;
use crate::spec::*;
use crate::vmspec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;
use verilith_text::utf::spec::*;

verus! {

/// `g` flags only instructions that consume the byte `x` and nothing
/// else.
pub open spec fn gates(p: Seq<SInst>, x: u8, g: Seq<bool>) -> bool {
    &&& g.len() == p.len()
    &&& x < 0x80
    &&& forall|pc: int, cp: u32| 0 <= pc < p.len() && g[pc] && #[trigger] chr_has(p, pc, cp) ==> cp == x as u32
}

/// `w` flags a set of instructions closed under every move except the
/// move past a flagged instruction of `g`, and `Match` is not in it.
pub open spec fn wclosed(p: Seq<SInst>, g: Seq<bool>, w: Seq<bool>) -> bool {
    &&& w.len() == p.len()
    &&& g.len() == p.len()
    &&& forall|q: int|
        0 <= q < p.len() && #[trigger] w[q] ==> match p[q] {
            SInst::Split { a, b } => (q < a < p.len() ==> w[a]) && (q < b < p.len() ==> w[b]),
            SInst::Save { slot, next } => q < next < p.len() ==> w[next],
            SInst::Look { k, next } => q < next < p.len() ==> w[next],
            SInst::Char { cls, next } => !g[q] && 0 <= next < p.len() ==> w[next],
            SInst::Match => false,
            SInst::Fail => true,
        }
}

/// What a program's required byte promises: `Match` cannot be reached
/// from the start without passing an instruction that consumes exactly
/// `x`.
pub open spec fn need_ok(p: Seq<SInst>, start: int, x: u8, g: Seq<bool>, w: Seq<bool>) -> bool {
    &&& gates(p, x, g)
    &&& wclosed(p, g, w)
    &&& 0 <= start < p.len()
    &&& w[start]
}

/// `al` marks every ASCII byte some instruction consumes, and every
/// byte that is not ASCII.
pub open spec fn al_ok(p: Seq<SInst>, al: Seq<bool>) -> bool {
    &&& al.len() == 256
    &&& forall|b: int| 0x80 <= b < 256 ==> #[trigger] al[b]
    &&& forall|pc: int, cp: u32| cp < 0x80 && #[trigger] chr_has(p, pc, cp) ==> al[cp as int]
}

/// Bytes `a..b` of `s` are all marked.
pub open spec fn inal(s: Seq<u8>, al: Seq<bool>, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> al[#[trigger] s[j] as int]
}

/// A match ends no earlier than it starts and inside the text.
pub proof fn lemma_pm_span(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c: Seq<int>)
    ensures
        forall|k: int| 0 <= k < pm(p, s, pc, i, c).len() ==> i <= (#[trigger] pm(p, s, pc, i, c)[k]).end <= s.len(),
    decreases s.len() - i + 1, p.len() - pc,
{
    if pc < 0 || pc >= p.len() || i < 0 || i > s.len() {
    } else {
        match p[pc] {
            SInst::Char { cls, next } => {
                match dec(s, i) {
                    Some((cp, l)) => {
                        if cls.contains(cp) && l >= 1 {
                            lemma_pm_span(p, s, next, i + l, c);
                            assert(pm(p, s, pc, i, c) == pm(p, s, next, i + l, c));
                        } else {
                            assert(pm(p, s, pc, i, c).len() == 0);
                        }
                    },
                    None => {
                        assert(pm(p, s, pc, i, c).len() == 0);
                    },
                }
            },
            SInst::Split { a, b } => {
                let x = if pc < a < p.len() {
                    pm(p, s, a, i, c)
                } else {
                    seq![]
                };
                let y = if pc < b < p.len() {
                    pm(p, s, b, i, c)
                } else {
                    seq![]
                };
                if pc < a < p.len() {
                    lemma_pm_span(p, s, a, i, c);
                }
                if pc < b < p.len() {
                    lemma_pm_span(p, s, b, i, c);
                }
                assert(pm(p, s, pc, i, c) == x + y);
                assert forall|k: int| 0 <= k < (x + y).len() implies i <= (#[trigger] (x + y)[k]).end <= s.len() by {
                    if k < x.len() {
                        assert((x + y)[k] == x[k]);
                    } else {
                        assert((x + y)[k] == y[k - x.len()]);
                    }
                }
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_pm_span(p, s, next, i, c.update(slot, i));
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c.update(slot, i)));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_pm_span(p, s, next, i, c);
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            SInst::Match => {
                assert(pm(p, s, pc, i, c) == seq![M { end: i, caps: c }]);
            },
            SInst::Fail => {
                assert(pm(p, s, pc, i, c).len() == 0);
            },
        }
    }
}

/// From an instruction of `w`, with no `x` in bytes `i..e`, every match
/// ends after byte `e`: it has consumed an `x` at or after `e`.
pub proof fn lemma_need_pm(
    p: Seq<SInst>,
    s: Seq<u8>,
    pc: int,
    i: int,
    c: Seq<int>,
    x: u8,
    g: Seq<bool>,
    w: Seq<bool>,
    e: int,
)
    requires
        gates(p, x, g),
        wclosed(p, g, w),
        0 <= pc < p.len(),
        w[pc],
        forall|j: int| i <= j < e ==> #[trigger] s[j] != x,
    ensures
        forall|k: int| 0 <= k < pm(p, s, pc, i, c).len() ==> (#[trigger] pm(p, s, pc, i, c)[k]).end > e,
    decreases s.len() - i + 1, p.len() - pc,
{
    if i < 0 || i > s.len() {
    } else {
        match p[pc] {
            SInst::Char { cls, next } => {
                match dec(s, i) {
                    Some((cp, l)) => {
                        if cls.contains(cp) && l >= 1 {
                            lemma_dec8_roundtrip(s, i);
                            lemma_pm_span(p, s, next, i + l, c);
                            assert(pm(p, s, pc, i, c) == pm(p, s, next, i + l, c));
                            if g[pc] {
                                assert(chr_has(p, pc, cp));
                                assert(utf8_encode(cp).len() == 1);
                                assert(s.subrange(i, i + l).len() == l);
                                assert(s.subrange(i, i + 1)[0] == s[i]);
                                assert(s[i] == x);
                            } else if 0 <= next < p.len() {
                                lemma_need_pm(p, s, next, i + l, c, x, g, w, e);
                            }
                        }
                    },
                    None => {},
                }
            },
            SInst::Split { a, b } => {
                let xa = if pc < a < p.len() {
                    pm(p, s, a, i, c)
                } else {
                    seq![]
                };
                let xb = if pc < b < p.len() {
                    pm(p, s, b, i, c)
                } else {
                    seq![]
                };
                if pc < a < p.len() {
                    lemma_need_pm(p, s, a, i, c, x, g, w, e);
                }
                if pc < b < p.len() {
                    lemma_need_pm(p, s, b, i, c, x, g, w, e);
                }
                assert(pm(p, s, pc, i, c) == xa + xb);
                assert forall|k: int| 0 <= k < (xa + xb).len() implies (#[trigger] (xa + xb)[k]).end > e by {
                    if k < xa.len() {
                        assert((xa + xb)[k] == xa[k]);
                    } else {
                        assert((xa + xb)[k] == xb[k - xa.len()]);
                    }
                }
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_need_pm(p, s, next, i, c.update(slot, i), x, g, w, e);
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c.update(slot, i)));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_need_pm(p, s, next, i, c, x, g, w, e);
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            _ => {},
        }
    }
}

/// Every byte of a match is in the alphabet.
pub proof fn lemma_al_pm(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c: Seq<int>, al: Seq<bool>)
    requires
        al_ok(p, al),
    ensures
        forall|k: int| 0 <= k < pm(p, s, pc, i, c).len() ==> inal(s, al, i, (#[trigger] pm(p, s, pc, i, c)[k]).end),
    decreases s.len() - i + 1, p.len() - pc,
{
    if pc < 0 || pc >= p.len() || i < 0 || i > s.len() {
    } else {
        match p[pc] {
            SInst::Char { cls, next } => {
                match dec(s, i) {
                    Some((cp, l)) => {
                        if cls.contains(cp) && l >= 1 {
                            lemma_dec8_roundtrip(s, i);
                            lemma_al_pm(p, s, next, i + l, c, al);
                            assert(inal(s, al, i, i + l)) by {
                                if l == 1 {
                                    assert(cp == s[i] as u32);
                                    assert(chr_has(p, pc, cp));
                                } else {
                                    assert forall|j: int| i <= j < i + l implies al[#[trigger] s[j] as int] by {
                                        assert(s[j] >= 0x80);
                                    }
                                }
                            }
                            let r = pm(p, s, next, i + l, c);
                            assert(pm(p, s, pc, i, c) == r);
                            assert forall|k: int| 0 <= k < r.len() implies inal(s, al, i, (#[trigger] r[k]).end) by {
                                assert(inal(s, al, i + l, r[k].end));
                            }
                        }
                    },
                    None => {},
                }
            },
            SInst::Split { a, b } => {
                let xa = if pc < a < p.len() {
                    pm(p, s, a, i, c)
                } else {
                    seq![]
                };
                let xb = if pc < b < p.len() {
                    pm(p, s, b, i, c)
                } else {
                    seq![]
                };
                if pc < a < p.len() {
                    lemma_al_pm(p, s, a, i, c, al);
                }
                if pc < b < p.len() {
                    lemma_al_pm(p, s, b, i, c, al);
                }
                assert(pm(p, s, pc, i, c) == xa + xb);
                assert forall|k: int| 0 <= k < (xa + xb).len() implies inal(s, al, i, (#[trigger] (xa + xb)[k]).end) by {
                    if k < xa.len() {
                        assert((xa + xb)[k] == xa[k]);
                    } else {
                        assert((xa + xb)[k] == xb[k - xa.len()]);
                    }
                }
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_al_pm(p, s, next, i, c.update(slot, i), al);
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c.update(slot, i)));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_al_pm(p, s, next, i, c, al);
                    assert(pm(p, s, pc, i, c) == pm(p, s, next, i, c));
                } else {
                    assert(pm(p, s, pc, i, c).len() == 0);
                }
            },
            _ => {},
        }
    }
}

/// No match starts at `i` if the next `x` is at `k` (or there is none
/// and `k` is the end) and some byte from `i` up to `k` is outside the
/// alphabet.
pub proof fn lemma_need_at(
    p: Seq<SInst>,
    s: Seq<u8>,
    start: int,
    i: int,
    c: Seq<int>,
    x: u8,
    g: Seq<bool>,
    w: Seq<bool>,
    al: Seq<bool>,
    k: int,
    j: int,
)
    requires
        need_ok(p, start, x, g, w),
        al_ok(p, al),
        0 <= i <= j < k <= s.len(),
        forall|t: int| i <= t < k ==> #[trigger] s[t] != x,
        !al[s[j] as int],
    ensures
        pm(p, s, start, i, c).len() == 0,
{
    let r = pm(p, s, start, i, c);
    if r.len() > 0 {
        lemma_need_pm(p, s, start, i, c, x, g, w, k);
        lemma_al_pm(p, s, start, i, c, al);
        assert(r[0].end > k);
        assert(inal(s, al, i, r[0].end));
        assert(al[s[j] as int]);
    }
}

/// No match starts at `i` if there is no `x` from `i` on.
pub proof fn lemma_need_none(
    p: Seq<SInst>,
    s: Seq<u8>,
    start: int,
    i: int,
    c: Seq<int>,
    x: u8,
    g: Seq<bool>,
    w: Seq<bool>,
)
    requires
        need_ok(p, start, x, g, w),
        forall|t: int| i <= t < s.len() ==> #[trigger] s[t] != x,
    ensures
        pm(p, s, start, i, c).len() == 0,
{
    let r = pm(p, s, start, i, c);
    if r.len() > 0 {
        lemma_need_pm(p, s, start, i, c, x, g, w, s.len() as int);
        lemma_pm_span(p, s, start, i, c);
        assert(r[0].end > s.len());
    }
}

/// A search may pass over positions where no match starts.
pub proof fn lemma_search_jump(p: Seq<SInst>, s: Seq<u8>, start: int, a: int, b: int, ns: nat)
    requires
        0 <= a <= b <= s.len(),
        forall|i: int| a <= i < b ==> (#[trigger] pm(p, s, start, i, unset(ns))).len() == 0,
    ensures
        search_p(p, s, start, a, ns) == search_p(p, s, start, b, ns),
    decreases b - a,
{
    if a < b {
        assert(pm(p, s, start, a, unset(ns)).len() == 0);
        lemma_search_jump(p, s, start, a + 1, b, ns);
    }
}

/// With the next `x` at `k` (or none, and `k` the end) and byte `j - 1`
/// outside the alphabet, a search at `a` may jump to `j`.
pub proof fn lemma_need_jump(
    p: Seq<SInst>,
    s: Seq<u8>,
    start: int,
    ns: nat,
    x: u8,
    g: Seq<bool>,
    w: Seq<bool>,
    al: Seq<bool>,
    a: int,
    j: int,
    k: int,
)
    requires
        need_ok(p, start, x, g, w),
        al_ok(p, al),
        0 <= a < j <= k <= s.len(),
        forall|t: int| a <= t < k ==> #[trigger] s[t] != x,
        !al[s[j - 1] as int],
    ensures
        search_p(p, s, start, a, ns) == search_p(p, s, start, j, ns),
{
    assert forall|i: int| a <= i < j implies (#[trigger] pm(p, s, start, i, unset(ns))).len() == 0 by {
        lemma_need_at(p, s, start, i, unset(ns), x, g, w, al, k, j - 1);
    }
    lemma_search_jump(p, s, start, a, j, ns);
}

/// With no `x` from `a` on, a search at `a` finds what a search at the
/// end finds.
pub proof fn lemma_need_end(p: Seq<SInst>, s: Seq<u8>, start: int, ns: nat, x: u8, g: Seq<bool>, w: Seq<bool>, a: int)
    requires
        need_ok(p, start, x, g, w),
        0 <= a <= s.len(),
        forall|t: int| a <= t < s.len() ==> #[trigger] s[t] != x,
    ensures
        search_p(p, s, start, a, ns) == search_p(p, s, start, s.len() as int, ns),
{
    assert forall|i: int| a <= i < s.len() implies (#[trigger] pm(p, s, start, i, unset(ns))).len() == 0 by {
        lemma_need_none(p, s, start, i, unset(ns), x, g, w);
    }
    lemma_search_jump(p, s, start, a, s.len() as int, ns);
}

// ---------------------------------------------------------------------------
// Finding the byte
// ---------------------------------------------------------------------------

/// The program's alphabet.
pub fn al_table(insts: &Vec<Inst>, classes: &Vec<Class>) -> (t: Vec<bool>)
    requires
        forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
        forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < classes@.len(),
                _ => true,
            },
    ensures
        al_ok(pv(insts@, classes@), t@),
{
    let ghost sp = pv(insts@, classes@);
    let mut t = no_flags(256);
    mark(&mut t, 0x80, 0xFF);
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            t@.len() == 256,
            sp == pv(insts@, classes@),
            forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
            forall|pc: int|
                0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                    Inst::Char { cls, next } => cls < classes@.len(),
                    _ => true,
                },
            forall|b: int| 0x80 <= b < 256 ==> #[trigger] t@[b],
            forall|q: int, cp: u32| q < pc && cp < 0x80 && #[trigger] chr_has(sp, q, cp) ==> t@[cp as int],
        decreases n - pc,
    {
        assert(sp[pc as int] == iv(insts@[pc as int], classes@));
        match insts[pc] {
            Inst::Char { cls, next } => {
                let c = &classes[cls as usize];
                let m = c.r.len();
                let mut j = 0;
                while j < m
                    invariant
                        j <= m,
                        m == c.r@.len(),
                        c.wf(),
                        t@.len() == 256,
                        forall|b: int| 0x80 <= b < 256 ==> #[trigger] t@[b],
                        forall|q: int, cp: u32| q < pc && cp < 0x80 && #[trigger] chr_has(sp, q, cp) ==> t@[cp as int],
                        forall|k: int, cp: u32|
                            0 <= k < j && cp < 0x80 && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1 ==> #[trigger] t@[cp as int],
                    decreases m - j,
                {
                    let (lo, hi) = c.r[j];
                    let ghost t0 = t@;
                    if lo < 0x80 {
                        let z: u8 = if hi < 0x80 {
                            hi as u8
                        } else {
                            0x7F
                        };
                        mark(&mut t, lo as u8, z);
                    }
                    assert forall|k: int, cp: u32|
                        0 <= k < j + 1 && cp < 0x80 && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1 implies #[trigger] t@[cp as int] by {
                        if k < j {
                            assert(t0[cp as int]);
                        }
                    }
                    j += 1;
                }
            },
            _ => {},
        }
        assert forall|q: int, cp: u32| q < pc + 1 && cp < 0x80 && #[trigger] chr_has(sp, q, cp) implies t@[cp as int] by {
            if q == pc {
                let c = classes@[insts@[pc as int]->Char_cls as int];
                let k = choose|k: int| 0 <= k < c.r@.len() && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1;
                assert(c.r@[k].0 <= cp <= c.r@[k].1);
            }
        }
        pc += 1;
    }
    t
}

/// Flags the instructions that consume `x` and nothing else.
fn gate_table(insts: &Vec<Inst>, classes: &Vec<Class>, x: u8) -> (g: Vec<bool>)
    requires
        x < 0x80,
        forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < classes@.len(),
                _ => true,
            },
    ensures
        gates(pv(insts@, classes@), x, g@),
{
    let ghost sp = pv(insts@, classes@);
    let mut g: Vec<bool> = Vec::new();
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            g@.len() == pc,
            sp == pv(insts@, classes@),
            forall|pc: int|
                0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                    Inst::Char { cls, next } => cls < classes@.len(),
                    _ => true,
                },
            forall|q: int, cp: u32| 0 <= q < pc && g@[q] && #[trigger] chr_has(sp, q, cp) ==> cp == x as u32,
        decreases n - pc,
    {
        assert(sp[pc as int] == iv(insts@[pc as int], classes@));
        let f = match insts[pc] {
            Inst::Char { cls, next } => {
                let c = &classes[cls as usize];
                c.r.len() == 1 && c.r[0].0 == x as u32 && c.r[0].1 == x as u32
            },
            _ => false,
        };
        let ghost g0 = g@;
        g.push(f);
        assert forall|q: int, cp: u32| 0 <= q < pc + 1 && g@[q] && #[trigger] chr_has(sp, q, cp) implies cp == x as u32 by {
            if q == pc {
                let c = classes@[insts@[pc as int]->Char_cls as int];
                let k = choose|k: int| 0 <= k < c.r@.len() && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1;
                assert(c.r@[k].0 <= cp <= c.r@[k].1);
            } else {
                assert(g0[q]);
            }
        }
        pc += 1;
    }
    g
}

/// What `start` reaches without moving past a flagged instruction, as
/// far as a bounded number of sweeps finds. `need_check` decides whether
/// the result will do.
fn reach_wo(insts: &Vec<Inst>, g: &Vec<bool>, start: usize) -> (w: Vec<bool>)
    requires
        g@.len() == insts@.len(),
        start < insts@.len(),
    ensures
        w@.len() == insts@.len(),
{
    let n = insts.len();
    let mut w = no_flags(n);
    w[start] = true;
    let mut round: usize = 0;
    let mut changed = true;
    while changed && round < 64
        invariant
            n == insts@.len(),
            w@.len() == n,
            g@.len() == n,
            round <= 64,
        decreases 64 - round,
    {
        changed = false;
        let mut pc = 0;
        while pc < n
            invariant
                pc <= n,
                n == insts@.len(),
                w@.len() == n,
                g@.len() == n,
            decreases n - pc,
        {
            if w[pc] {
                match insts[pc] {
                    Inst::Split { a, b } => {
                        if (a as usize) < n && !w[a as usize] {
                            w[a as usize] = true;
                            changed = true;
                        }
                        if (b as usize) < n && !w[b as usize] {
                            w[b as usize] = true;
                            changed = true;
                        }
                    },
                    Inst::Save { slot, next } => {
                        if (next as usize) < n && !w[next as usize] {
                            w[next as usize] = true;
                            changed = true;
                        }
                    },
                    Inst::Look { k, next } => {
                        if (next as usize) < n && !w[next as usize] {
                            w[next as usize] = true;
                            changed = true;
                        }
                    },
                    Inst::Char { cls, next } => {
                        if !g[pc] && (next as usize) < n && !w[next as usize] {
                            w[next as usize] = true;
                            changed = true;
                        }
                    },
                    _ => {},
                }
            }
            pc += 1;
        }
        round += 1;
    }
    w
}

/// Whether `w` is closed and free of `Match`.
fn need_check(insts: &Vec<Inst>, Ghost(cl): Ghost<Seq<Class>>, g: &Vec<bool>, w: &Vec<bool>, start: usize) -> (ok: bool)
    requires
        g@.len() == insts@.len(),
        w@.len() == insts@.len(),
    ensures
        ok ==> wclosed(pv(insts@, cl), g@, w@) && start < insts@.len() && w@[start as int],
{
    let ghost sp = pv(insts@, cl);
    let n = insts.len();
    if start >= n || !w[start] {
        return false;
    }
    let mut q = 0;
    while q < n
        invariant
            q <= n,
            n == insts@.len(),
            w@.len() == n,
            g@.len() == n,
            sp == pv(insts@, cl),
            forall|r: int|
                0 <= r < q && #[trigger] w@[r] ==> match sp[r] {
                    SInst::Split { a, b } => (r < a < sp.len() ==> w@[a]) && (r < b < sp.len() ==> w@[b]),
                    SInst::Save { slot, next } => r < next < sp.len() ==> w@[next],
                    SInst::Look { k, next } => r < next < sp.len() ==> w@[next],
                    SInst::Char { cls, next } => !g@[r] && 0 <= next < sp.len() ==> w@[next],
                    SInst::Match => false,
                    SInst::Fail => true,
                },
        decreases n - q,
    {
        assert(sp[q as int] == iv(insts@[q as int], cl));
        if w[q] {
            let ok = match insts[q] {
                Inst::Split { a, b } => {
                    let a = a as usize;
                    let b = b as usize;
                    (!(q < a && a < n) || w[a]) && (!(q < b && b < n) || w[b])
                },
                Inst::Save { slot, next } => {
                    let x = next as usize;
                    !(q < x && x < n) || w[x]
                },
                Inst::Look { k, next } => {
                    let x = next as usize;
                    !(q < x && x < n) || w[x]
                },
                Inst::Char { cls, next } => {
                    let x = next as usize;
                    g[q] || !(x < n) || w[x]
                },
                Inst::Match => false,
                Inst::Fail => true,
            };
            if !ok {
                return false;
            }
        }
        q += 1;
    }
    true
}

/// How common a byte is in text, roughly: 0 for punctuation and control
/// bytes, 1 for digits and capitals, 2 for the rarer small letters, 3
/// for the rest. Only guides the choice below.
fn rank(b: u8) -> u8 {
    if b == 0x20 || b == 0x0A || b == 0x2E || b == 0x2C {
        3
    } else if 0x61 <= b && b <= 0x7A {
        if b == 0x65 || b == 0x74 || b == 0x61 || b == 0x6F || b == 0x69 || b == 0x6E || b == 0x73 || b == 0x68 || b
            == 0x72 || b == 0x6C || b == 0x64 || b == 0x75 {
            3
        } else {
            2
        }
    } else if (0x41 <= b && b <= 0x5A) || (0x30 <= b && b <= 0x39) {
        1
    } else {
        0
    }
}

/// A byte every match must contain, if one is found among the rarer
/// bytes the program consumes on their own, with the sets that show it.
pub fn find_need(insts: &Vec<Inst>, classes: &Vec<Class>, start: usize) -> (r: (
    Option<u8>,
    Ghost<Seq<bool>>,
    Ghost<Seq<bool>>,
))
    requires
        start < insts@.len(),
        forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < classes@.len(),
                _ => true,
            },
    ensures
        r.0 matches Some(x) ==> need_ok(pv(insts@, classes@), start as int, x, r.1@, r.2@),
{
    // The candidates: bytes some instruction consumes alone.
    let mut cand = no_flags(128);
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            cand@.len() == 128,
            forall|pc: int|
                0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                    Inst::Char { cls, next } => cls < classes@.len(),
                    _ => true,
                },
        decreases n - pc,
    {
        match insts[pc] {
            Inst::Char { cls, next } => {
                let c = &classes[cls as usize];
                if c.r.len() == 1 && c.r[0].0 == c.r[0].1 && c.r[0].0 < 0x80 {
                    cand[c.r[0].0 as usize] = true;
                }
            },
            _ => {},
        }
        pc += 1;
    }
    let mut tries: usize = 0;
    let mut rk: u8 = 0;
    while rk < 3
        invariant
            rk <= 3,
            tries <= 8,
            n == insts@.len(),
            start < n,
            cand@.len() == 128,
            forall|pc: int|
                0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                    Inst::Char { cls, next } => cls < classes@.len(),
                    _ => true,
                },
        decreases 3 - rk,
    {
        let mut b: usize = 0;
        while b < 128
            invariant
                b <= 128,
                tries <= 8,
                n == insts@.len(),
                start < n,
                cand@.len() == 128,
                forall|pc: int|
                    0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                        Inst::Char { cls, next } => cls < classes@.len(),
                        _ => true,
                    },
            decreases 128 - b,
        {
            if cand[b] && rank(b as u8) == rk && tries < 8 {
                tries += 1;
                let x = b as u8;
                let g = gate_table(insts, classes, x);
                let w = reach_wo(insts, &g, start);
                if need_check(insts, Ghost(classes@), &g, &w, start) {
                    return (Some(x), Ghost(g@), Ghost(w@));
                }
            }
            b += 1;
        }
        rk += 1;
    }
    (None, Ghost(Seq::empty()), Ghost(Seq::empty()))
}


// ---------------------------------------------------------------------------
// Using the byte
// ---------------------------------------------------------------------------

/// What one search knows about where the required byte is: nothing, or
/// that its first occurrence at or after `lo` is at `k` (the end of the
/// text if there is none). `h` is how far the text has been scanned for
/// it.
pub struct NeedSt {
    pub have: bool,
    pub lo: usize,
    pub k: usize,
    pub h: usize,
}

impl NeedSt {
    pub open spec fn inv(&self, s: Seq<u8>, x: u8) -> bool {
        &&& self.h <= s.len()
        &&& self.have ==> self.lo <= self.k && self.h == self.k && crate::find::first_at(
            s,
            self.lo as int,
            x,
            self.k as int,
        )
    }

    pub fn new(from: usize) -> (r: NeedSt)
        ensures
            !r.have,
            r.h == from,
    {
        NeedSt { have: false, lo: from, k: from, h: from }
    }
}


} // verus!
