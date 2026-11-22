//! Skipping positions where no match can start.
//!
//! `first_table` marks every byte that can be the first byte of a
//! character some instruction of the program accepts. A search with no
//! thread alive may pass over a byte that is not marked, provided the
//! program cannot match the empty string: `lemma_skip` proves that no
//! match starts there.
use crate::class::*;
use crate::compile::*;
use crate::data::*;
use crate::prog::*;
use crate::sem::*;
use crate::spec::*;
use crate::vmspec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;
use verilith_text::utf::spec::*;

verus! {

/// The first byte of the UTF-8 encoding of `cp`.
pub open spec fn lead(cp: u32) -> u8 {
    utf8_encode(cp)[0]
}

/// Whether `Match` can be reached from `pc` without consuming anything,
/// if every assertion on the way holds.
pub open spec fn eps_match(p: Seq<SInst>, pc: int) -> bool
    decreases p.len() - pc,
{
    if pc < 0 || pc >= p.len() {
        false
    } else {
        match p[pc] {
            SInst::Match => true,
            SInst::Fail => false,
            SInst::Char { cls, next } => false,
            SInst::Split { a, b } => (pc < a < p.len() && eps_match(p, a)) || (pc < b < p.len() && eps_match(p, b)),
            SInst::Save { slot, next } => pc < next < p.len() && eps_match(p, next),
            SInst::Look { k, next } => pc < next < p.len() && eps_match(p, next),
        }
    }
}

/// Instruction `pc` consumes the character `cp`.
pub open spec fn chr_has(p: Seq<SInst>, pc: int, cp: u32) -> bool {
    0 <= pc < p.len() && (p[pc] matches SInst::Char { cls, next } && cls.contains(cp))
}

/// `r` flags a set of instructions closed under moves that consume
/// nothing.
pub open spec fn closed(p: Seq<SInst>, r: Seq<bool>) -> bool {
    &&& r.len() == p.len()
    &&& forall|q: int|
        0 <= q < p.len() && #[trigger] r[q] ==> match p[q] {
            SInst::Split { a, b } => (q < a < p.len() ==> r[a]) && (q < b < p.len() ==> r[b]),
            SInst::Save { slot, next } => q < next < p.len() ==> r[next],
            SInst::Look { k, next } => q < next < p.len() ==> r[next],
            _ => true,
        }
}

/// `t` marks the first byte of every character a flagged instruction
/// consumes.
pub open spec fn tbl_ok(p: Seq<SInst>, r: Seq<bool>, t: Seq<bool>) -> bool {
    &&& t.len() == 256
    &&& r.len() == p.len()
    &&& forall|pc: int, cp: u32| cp <= MAXCP && r[pc] && #[trigger] chr_has(p, pc, cp) ==> t[lead(cp) as int]
}

/// What a program's skip table promises: the flagged instructions are
/// all that the start reaches without consuming, the table marks what
/// they consume, and the program cannot match without consuming.
pub open spec fn skip_ok(p: Seq<SInst>, start: int, r: Seq<bool>, t: Seq<bool>) -> bool {
    &&& closed(p, r)
    &&& tbl_ok(p, r, t)
    &&& 0 <= start < p.len()
    &&& r[start]
    &&& !eps_match(p, start)
}

/// From an unmarked byte, the program matches nothing, unless it can
/// match without consuming.
pub proof fn lemma_skip_pm(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c: Seq<int>, r: Seq<bool>, t: Seq<bool>)
    requires
        closed(p, r),
        tbl_ok(p, r, t),
        0 <= i < s.len(),
        !t[s[i] as int],
        0 <= pc < p.len(),
        r[pc],
        !eps_match(p, pc),
    ensures
        pm(p, s, pc, i, c).len() == 0,
    decreases p.len() - pc,
{
    match p[pc] {
        SInst::Char { cls, next } => {
            match dec(s, i) {
                Some((cp, l)) => {
                    lemma_dec8_roundtrip(s, i);
                    assert(utf8_encode(cp)[0] == s.subrange(i, i + l)[0]);
                    if cls.contains(cp) {
                        assert(chr_has(p, pc, cp));
                    }
                },
                None => {},
            }
        },
        SInst::Split { a, b } => {
            if pc < a < p.len() {
                lemma_skip_pm(p, s, a, i, c, r, t);
            }
            if pc < b < p.len() {
                lemma_skip_pm(p, s, b, i, c, r, t);
            }
        },
        SInst::Save { slot, next } => {
            if pc < next < p.len() {
                lemma_skip_pm(p, s, next, i, c.update(slot, i), r, t);
            }
        },
        SInst::Look { k, next } => {
            if pc < next < p.len() {
                lemma_skip_pm(p, s, next, i, c, r, t);
            }
        },
        _ => {},
    }
}

/// A search may pass over an unmarked byte.
pub proof fn lemma_skip(p: Seq<SInst>, s: Seq<u8>, start: int, i: int, ns: nat, r: Seq<bool>, t: Seq<bool>)
    requires
        skip_ok(p, start, r, t),
        0 <= i < s.len(),
        !t[s[i] as int],
    ensures
        search_p(p, s, start, i, ns) == search_p(p, s, start, i + 1, ns),
{
    lemma_skip_pm(p, s, start, i, unset(ns), r, t);
}

/// Adds to the flagged instructions everything they reach without
/// consuming, if every assertion on the way holds.
pub fn eps_close(insts: &Vec<Inst>, r: &mut Vec<bool>, Ghost(cl): Ghost<Seq<Class>>)
    requires
        fwd(pv(insts@, cl)),
        old(r)@.len() == insts@.len(),
    ensures
        closed(pv(insts@, cl), final(r)@),
        forall|q: int| 0 <= q < insts@.len() && old(r)@[q] ==> final(r)@[q],
{
    let ghost sp = pv(insts@, cl);
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            r@.len() == n,
            sp == pv(insts@, cl),
            fwd(sp),
            forall|q: int| 0 <= q < n && old(r)@[q] ==> r@[q],
            forall|q: int|
                0 <= q < pc && #[trigger] r@[q] ==> match sp[q] {
                    SInst::Split { a, b } => (q < a < n ==> r@[a]) && (q < b < n ==> r@[b]),
                    SInst::Save { slot, next } => q < next < n ==> r@[next],
                    SInst::Look { k, next } => q < next < n ==> r@[next],
                    _ => true,
                },
        decreases n - pc,
    {
        assert(fwd_at(sp, pc as int));
        assert(sp[pc as int] == iv(insts@[pc as int], cl));
        if r[pc] {
            match insts[pc] {
                Inst::Split { a, b } => {
                    r[a as usize] = true;
                    r[b as usize] = true;
                },
                Inst::Save { slot, next } => {
                    r[next as usize] = true;
                },
                Inst::Look { k, next } => {
                    r[next as usize] = true;
                },
                _ => {},
            }
        }
        pc += 1;
    }
}

/// `n` flags, none set.
pub fn no_flags(n: usize) -> (r: Vec<bool>)
    ensures
        r@.len() == n,
        forall|q: int| 0 <= q < n ==> !#[trigger] r@[q],
{
    let mut r: Vec<bool> = Vec::new();
    let mut k = 0;
    while k < n
        invariant
            k <= n,
            r@.len() == k,
            forall|q: int| 0 <= q < k ==> !#[trigger] r@[q],
        decreases n - k,
    {
        r.push(false);
        k += 1;
    }
    r
}

/// The instructions `start` reaches without consuming, if every
/// assertion on the way holds.
pub fn reach(insts: &Vec<Inst>, start: usize, Ghost(cl): Ghost<Seq<Class>>) -> (r: Vec<bool>)
    requires
        fwd(pv(insts@, cl)),
        start < insts@.len(),
    ensures
        closed(pv(insts@, cl), r@),
        r@[start as int],
{
    let mut r = no_flags(insts.len());
    r[start] = true;
    eps_close(insts, &mut r, Ghost(cl));
    r
}

fn lead_x(cp: u32) -> (r: u8)
    requires
        cp <= MAXCP,
    ensures
        r == lead(cp),
{
    if cp < 0x80 {
        cp as u8
    } else if cp < 0x800 {
        (0xC0 + cp / 64) as u8
    } else if cp < 0x10000 {
        (0xE0 + cp / 4096) as u8
    } else {
        (0xF0 + cp / 262144) as u8
    }
}

/// Marks bytes `a..=z`.
pub fn mark(t: &mut Vec<bool>, a: u8, z: u8)
    requires
        old(t)@.len() == 256,
        a <= z,
    ensures
        final(t)@.len() == 256,
        forall|x: int| 0 <= x < 256 && old(t)@[x] ==> final(t)@[x],
        forall|x: int| a <= x <= z ==> final(t)@[x],
{
    let mut b = a as usize;
    while b <= z as usize
        invariant
            a <= b <= z + 1,
            t@.len() == 256,
            forall|x: int| 0 <= x < 256 && old(t)@[x] ==> t@[x],
            forall|x: int| a <= x < b ==> t@[x],
        decreases z + 1 - b,
    {
        t[b] = true;
        b += 1;
    }
}

proof fn lemma_lead_mono(a: u32, b: u32)
    requires
        a <= b <= MAXCP,
    ensures
        lead(a) <= lead(b),
{
}

/// Whether the program can match from `start` without consuming.
pub fn eps_start(insts: &Vec<Inst>, start: usize, Ghost(cl): Ghost<Seq<Class>>) -> (r: bool)
    requires
        fwd(pv(insts@, cl)),
        start < insts@.len(),
    ensures
        r == eps_match(pv(insts@, cl), start as int),
{
    let ghost sp = pv(insts@, cl);
    let n = insts.len();
    let mut e: Vec<bool> = Vec::new();
    let mut k = 0;
    while k < n
        invariant
            k <= n,
            e@.len() == k,
        decreases n - k,
    {
        e.push(false);
        k += 1;
    }
    let mut pc = n;
    while pc > 0
        invariant
            pc <= n,
            n == insts@.len(),
            e@.len() == n,
            sp == pv(insts@, cl),
            fwd(sp),
            forall|q: int| pc <= q < n ==> #[trigger] e@[q] == eps_match(sp, q),
        decreases pc,
    {
        pc -= 1;
        assert(fwd_at(sp, pc as int));
        assert(sp[pc as int] == iv(insts@[pc as int], cl));
        let v = match insts[pc] {
            Inst::Match => true,
            Inst::Fail => false,
            Inst::Char { cls, next } => false,
            Inst::Split { a, b } => e[a as usize] || e[b as usize],
            Inst::Save { slot, next } => e[next as usize],
            Inst::Look { k, next } => e[next as usize],
        };
        e[pc] = v;
    }
    e[start]
}

/// The first bytes of the characters the program's instructions consume.
pub fn first_table(insts: &Vec<Inst>, classes: &Vec<Class>, r: &Vec<bool>) -> (t: Vec<bool>)
    requires
        r@.len() == insts@.len(),
        forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
        forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < classes@.len(),
                _ => true,
            },
    ensures
        tbl_ok(pv(insts@, classes@), r@, t@),
{
    let ghost sp = pv(insts@, classes@);
    let mut t: Vec<bool> = Vec::new();
    let mut k = 0;
    while k < 256
        invariant
            k <= 256,
            t@.len() == k,
        decreases 256 - k,
    {
        t.push(false);
        k += 1;
    }
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            t@.len() == 256,
            r@.len() == n,
            sp == pv(insts@, classes@),
            forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
            forall|pc: int|
                0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                    Inst::Char { cls, next } => cls < classes@.len(),
                    _ => true,
                },
            forall|q: int, cp: u32|
                q < pc && cp <= MAXCP && r@[q] && #[trigger] chr_has(sp, q, cp) ==> t@[lead(cp) as int],
        decreases n - pc,
    {
        assert(sp[pc as int] == iv(insts@[pc as int], classes@));
        let ghost t1 = t@;
        match insts[pc] {
            Inst::Char { cls, next } => if r[pc] {
                let c = &classes[cls as usize];
                let m = c.r.len();
                let mut j = 0;
                while j < m
                    invariant
                        j <= m,
                        m == c.r@.len(),
                        c.wf(),
                        t@.len() == 256,
                        forall|q: int, cp: u32|
                            q < pc && cp <= MAXCP && r@[q] && #[trigger] chr_has(sp, q, cp) ==> t@[lead(cp) as int],
                        forall|k: int, cp: u32|
                            0 <= k < j && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1 ==> #[trigger] t@[lead(cp) as int],
                    decreases m - j,
                {
                    let (lo, hi) = c.r[j];
                    let a = lead_x(lo);
                    let z = lead_x(hi);
                    proof {
                        lemma_lead_mono(lo, hi);
                    }
                    let ghost t0 = t@;
                    mark(&mut t, a, z);
                    assert forall|k: int, cp: u32|
                        0 <= k < j + 1 && (#[trigger] c.r@[k]).0 <= cp <= c.r@[k].1 implies #[trigger] t@[lead(
                        cp,
                    ) as int] by {
                        if k == j {
                            lemma_lead_mono(lo, cp);
                            lemma_lead_mono(cp, hi);
                        } else {
                            assert(t0[lead(cp) as int]);
                        }
                    }
                    j += 1;
                }
            },
            _ => {},
        }
        assert forall|q: int, cp: u32| q < pc + 1 && cp <= MAXCP && r@[q] && #[trigger] chr_has(sp, q, cp) implies t@[lead(
            cp,
        ) as int] by {
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

/// `l`, if given, is the only byte the table `t` lets a match start with.
pub open spec fn only(t: Seq<bool>, l: Option<u8>) -> bool {
    l matches Some(b) ==> t.len() == 256 && forall|x: int| 0 <= x < 256 && x != b ==> !#[trigger] t[x]
}

/// The one byte flagged in `t`, if exactly one is.
pub fn only_byte(t: &Vec<bool>) -> (l: Option<u8>)
    ensures
        only(t@, l),
{
    if t.len() != 256 {
        return None;
    }
    let mut found: Option<u8> = None;
    let mut x: usize = 0;
    while x < 256
        invariant
            x <= 256,
            t@.len() == 256,
            found is None ==> forall|y: int| 0 <= y < x ==> !#[trigger] t@[y],
            found matches Some(b) ==> b < x && forall|y: int| 0 <= y < x && y != b ==> !#[trigger] t@[y],
        decreases 256 - x,
    {
        if t[x] {
            if found.is_some() {
                return None;
            }
            found = Some(x as u8);
        }
        x += 1;
    }
    found
}

/// No match starts anywhere in a run of bytes the table rules out.
pub proof fn lemma_skip_range(p: Seq<SInst>, s: Seq<u8>, start: int, a: int, b: int, ns: nat, r: Seq<bool>, t: Seq<bool>)
    requires
        skip_ok(p, start, r, t),
        0 <= a <= b <= s.len(),
        forall|j: int| a <= j < b ==> !#[trigger] t[s[j] as int],
    ensures
        search_p(p, s, start, a, ns) == search_p(p, s, start, b, ns),
    decreases b - a,
{
    if a < b {
        lemma_skip(p, s, start, a, ns, r, t);
        lemma_skip_range(p, s, start, a + 1, b, ns, r, t);
    }
}

// ---------------------------------------------------------------------------
// The second byte
// ---------------------------------------------------------------------------

/// `r2` flags every instruction that an instruction of `r` continues at
/// after consuming a character.
pub open spec fn after(p: Seq<SInst>, r: Seq<bool>, r2: Seq<bool>) -> bool {
    &&& r2.len() == p.len()
    &&& forall|pc: int|
        0 <= pc < p.len() && #[trigger] r[pc] ==> (p[pc] matches SInst::Char { cls, next } ==> 0 <= next < p.len()
            && r2[next])
}

/// No flagged instruction reaches `Match` without consuming.
pub open spec fn no_eps(p: Seq<SInst>, r2: Seq<bool>) -> bool {
    forall|pc: int| 0 <= pc < p.len() && #[trigger] r2[pc] ==> !eps_match(p, pc)
}

/// What a program's second-byte table promises: `r2` is where the
/// program can be after its first character, `t2` marks the first bytes
/// of what it consumes from there, and it cannot match there without
/// consuming.
pub open spec fn pair_ok(p: Seq<SInst>, r: Seq<bool>, r2: Seq<bool>, t2: Seq<bool>) -> bool {
    &&& closed(p, r2)
    &&& after(p, r, r2)
    &&& tbl_ok(p, r2, t2)
    &&& no_eps(p, r2)
}

/// At the end of the text the program matches nothing, unless it can
/// match without consuming.
pub proof fn lemma_end_pm(p: Seq<SInst>, s: Seq<u8>, pc: int, c: Seq<int>)
    requires
        0 <= pc < p.len(),
        !eps_match(p, pc),
    ensures
        pm(p, s, pc, s.len() as int, c).len() == 0,
    decreases p.len() - pc,
{
    let i = s.len() as int;
    match p[pc] {
        SInst::Char { cls, next } => {
            assert(dec(s, i) is None);
        },
        SInst::Split { a, b } => {
            if pc < a < p.len() {
                lemma_end_pm(p, s, a, c);
            }
            if pc < b < p.len() {
                lemma_end_pm(p, s, b, c);
            }
        },
        SInst::Save { slot, next } => {
            if pc < next < p.len() {
                lemma_end_pm(p, s, next, c.update(slot, i));
            }
        },
        SInst::Look { k, next } => {
            if pc < next < p.len() {
                lemma_end_pm(p, s, next, c);
            }
        },
        _ => {},
    }
}

/// From an ASCII byte whose next byte is unmarked or missing, the
/// program matches nothing.
pub proof fn lemma_pair_pm(
    p: Seq<SInst>,
    s: Seq<u8>,
    pc: int,
    i: int,
    c: Seq<int>,
    r: Seq<bool>,
    r2: Seq<bool>,
    t2: Seq<bool>,
)
    requires
        closed(p, r),
        pair_ok(p, r, r2, t2),
        0 <= i < s.len(),
        s[i] < 0x80,
        !(i + 1 < s.len() && t2[s[i + 1] as int]),
        0 <= pc < p.len(),
        r[pc],
        !eps_match(p, pc),
    ensures
        pm(p, s, pc, i, c).len() == 0,
    decreases p.len() - pc,
{
    match p[pc] {
        SInst::Char { cls, next } => {
            assert(dec(s, i) == Some((s[i] as u32, 1int)));
            if cls.contains(s[i] as u32) {
                assert(r2[next]);
                if i + 1 < s.len() {
                    lemma_skip_pm(p, s, next, i + 1, c, r2, t2);
                } else {
                    lemma_end_pm(p, s, next, c);
                }
            }
        },
        SInst::Split { a, b } => {
            if pc < a < p.len() {
                lemma_pair_pm(p, s, a, i, c, r, r2, t2);
            }
            if pc < b < p.len() {
                lemma_pair_pm(p, s, b, i, c, r, r2, t2);
            }
        },
        SInst::Save { slot, next } => {
            if pc < next < p.len() {
                lemma_pair_pm(p, s, next, i, c.update(slot, i), r, r2, t2);
            }
        },
        SInst::Look { k, next } => {
            if pc < next < p.len() {
                lemma_pair_pm(p, s, next, i, c, r, r2, t2);
            }
        },
        _ => {},
    }
}

/// A search may pass over an ASCII byte whose next byte is unmarked or
/// missing.
pub proof fn lemma_pair(
    p: Seq<SInst>,
    s: Seq<u8>,
    start: int,
    i: int,
    ns: nat,
    r: Seq<bool>,
    t: Seq<bool>,
    r2: Seq<bool>,
    t2: Seq<bool>,
)
    requires
        skip_ok(p, start, r, t),
        pair_ok(p, r, r2, t2),
        0 <= i < s.len(),
        s[i] < 0x80,
        !(i + 1 < s.len() && t2[s[i + 1] as int]),
    ensures
        pm(p, s, start, i, unset(ns)).len() == 0,
        search_p(p, s, start, i, ns) == search_p(p, s, start, i + 1, ns),
{
    lemma_pair_pm(p, s, start, i, unset(ns), r, r2, t2);
}

/// For every instruction, whether it reaches `Match` without consuming.
pub fn eps_table(insts: &Vec<Inst>, Ghost(cl): Ghost<Seq<Class>>) -> (e: Vec<bool>)
    requires
        fwd(pv(insts@, cl)),
    ensures
        e@.len() == insts@.len(),
        forall|q: int| 0 <= q < insts@.len() ==> #[trigger] e@[q] == eps_match(pv(insts@, cl), q),
{
    let ghost sp = pv(insts@, cl);
    let n = insts.len();
    let mut e = no_flags(n);
    let mut pc = n;
    while pc > 0
        invariant
            pc <= n,
            n == insts@.len(),
            e@.len() == n,
            sp == pv(insts@, cl),
            fwd(sp),
            forall|q: int| pc <= q < n ==> #[trigger] e@[q] == eps_match(sp, q),
        decreases pc,
    {
        pc -= 1;
        assert(fwd_at(sp, pc as int));
        assert(sp[pc as int] == iv(insts@[pc as int], cl));
        let v = match insts[pc] {
            Inst::Match => true,
            Inst::Fail => false,
            Inst::Char { cls, next } => false,
            Inst::Split { a, b } => e[a as usize] || e[b as usize],
            Inst::Save { slot, next } => e[next as usize],
            Inst::Look { k, next } => e[next as usize],
        };
        e[pc] = v;
    }
    e
}

/// The second-byte table for the instructions `r`, or nothing if the
/// program can match after one character. The ghost result is where the
/// program can be after its first character.
pub fn second_table(insts: &Vec<Inst>, classes: &Vec<Class>, r: &Vec<bool>) -> (res: (Vec<bool>, Ghost<Seq<bool>>))
    requires
        fwd(pv(insts@, classes@)),
        r@.len() == insts@.len(),
        forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
        forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < classes@.len(),
                _ => true,
            },
    ensures
        res.0@.len() == 0 || pair_ok(pv(insts@, classes@), r@, res.1@, res.0@),
{
    let ghost sp = pv(insts@, classes@);
    let n = insts.len();
    let mut r2 = no_flags(n);
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            r@.len() == n,
            r2@.len() == n,
            sp == pv(insts@, classes@),
            fwd(sp),
            forall|q: int|
                0 <= q < pc && #[trigger] r@[q] ==> (sp[q] matches SInst::Char { cls, next } ==> 0 <= next < n
                    && r2@[next]),
        decreases n - pc,
    {
        assert(fwd_at(sp, pc as int));
        assert(sp[pc as int] == iv(insts@[pc as int], classes@));
        if r[pc] {
            match insts[pc] {
                Inst::Char { cls, next } => {
                    r2[next as usize] = true;
                },
                _ => {},
            }
        }
        pc += 1;
    }
    eps_close(insts, &mut r2, Ghost(classes@));
    let e = eps_table(insts, Ghost(classes@));
    let mut q = 0;
    while q < n
        invariant
            q <= n,
            n == insts@.len(),
            r2@.len() == n,
            e@.len() == n,
            forall|j: int| 0 <= j < n ==> #[trigger] e@[j] == eps_match(sp, j),
            forall|j: int| 0 <= j < q && #[trigger] r2@[j] ==> !eps_match(sp, j),
        decreases n - q,
    {
        if r2[q] && e[q] {
            return (Vec::new(), Ghost(r2@));
        }
        q += 1;
    }
    let t2 = first_table(insts, classes, &r2);
    (t2, Ghost(r2@))
}

/// `l`, if given, holds every byte the table `t` flags.
pub open spec fn only2(t: Seq<bool>, l: Option<(u8, u8)>) -> bool {
    l matches Some(ab) ==> t.len() == 256 && forall|x: int|
        0 <= x < 256 && x != ab.0 && x != ab.1 ==> !#[trigger] t[x]
}

/// The bytes flagged in `t`, if there are one or two (one is given
/// twice).
pub fn only_two(t: &Vec<bool>) -> (l: Option<(u8, u8)>)
    ensures
        only2(t@, l),
{
    if t.len() != 256 {
        return None;
    }
    let mut a: Option<u8> = None;
    let mut b: Option<u8> = None;
    let mut x: usize = 0;
    while x < 256
        invariant
            x <= 256,
            t@.len() == 256,
            a is None ==> b is None,
            forall|y: int|
                0 <= y < x && #[trigger] t@[y] ==> (a matches Some(u) && u == y) || (b matches Some(v) && v == y),
        decreases 256 - x,
    {
        if t[x] {
            if a.is_none() {
                a = Some(x as u8);
            } else if b.is_none() {
                b = Some(x as u8);
            } else {
                return None;
            }
        }
        x += 1;
    }
    match (a, b) {
        (Some(u), Some(v)) => Some((u, v)),
        (Some(u), None) => Some((u, u)),
        _ => None,
    }
}

/// Up to three ranges that cover the flagged bytes of `skip`, split at
/// the two widest gaps, if they are worth scanning for: at most 64
/// bytes, none of them a space or a lower-case letter. Only the last
/// loop matters to the proof: it checks that the ranges cover the flags.
pub fn rng_of(skip: &Vec<bool>) -> (r: Option<(u8, u8, u8, u8, u8, u8)>)
    ensures
        r matches Some(x) ==> skip@.len() == 256 && forall|b: int|
            0 <= b < 256 ==> (#[trigger] skip@[b] ==> crate::find::inr(b as u8, x)),
{
    if skip.len() != 256 {
        return None;
    }
    // The runs of flagged bytes.
    let mut lo: Vec<u8> = Vec::new();
    let mut hi: Vec<u8> = Vec::new();
    let mut open = false;
    let mut b: usize = 0;
    while b < 256
        invariant
            b <= 256,
            skip@.len() == 256,
            lo@.len() == hi@.len() + if open {
                1int
            } else {
                0int
            },
            lo@.len() <= b,
            open ==> b >= 1,
        decreases 256 - b,
    {
        if skip[b] {
            if !open {
                lo.push(b as u8);
                open = true;
            }
        } else if open {
            hi.push((b - 1) as u8);
            open = false;
        }
        b += 1;
    }
    if open {
        hi.push(255);
    }
    let n = lo.len();
    if n == 0 {
        return None;
    }
    // The two widest gaps between runs.
    let mut g1: usize = n;
    let mut w1: u8 = 0;
    let mut g2: usize = n;
    let mut w2: u8 = 0;
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == lo@.len(),
            n == hi@.len(),
            n <= 256,
            i < n,
            g1 == n || g1 + 1 < n,
            g2 == n || g2 + 1 < n,
        decreases n - i,
    {
        let a = hi[i];
        let c = lo[i + 1];
        let w = if c > a {
            c - a
        } else {
            0
        };
        if w > w1 {
            g2 = g1;
            w2 = w1;
            g1 = i;
            w1 = w;
        } else if w > w2 {
            g2 = i;
            w2 = w;
        }
        i += 1;
    }
    let (a, c) = if g1 <= g2 {
        (g1, g2)
    } else {
        (g2, g1)
    };
    let x = if n == 1 || a == n {
        (lo[0], hi[n - 1], lo[0], hi[n - 1], lo[0], hi[n - 1])
    } else if c == n || c == a {
        (lo[0], hi[a], lo[a + 1], hi[n - 1], lo[0], hi[a])
    } else {
        (lo[0], hi[a], lo[a + 1], hi[c], lo[c + 1], hi[n - 1])
    };
    // Worth it only if such bytes are rare in text.
    if crate::find::in_rng(0x20, x) {
        return None;
    }
    let mut count: usize = 0;
    let mut b: usize = 0;
    while b < 256
        invariant
            b <= 256,
            count <= b,
            skip@.len() == 256,
            forall|j: int| 0 <= j < b ==> (#[trigger] skip@[j] ==> crate::find::inr(j as u8, x)),
        decreases 256 - b,
    {
        let y = crate::find::in_rng(b as u8, x);
        if skip[b] && !y {
            return None;
        }
        if y {
            if b >= 0x61 && b <= 0x7A {
                return None;
            }
            count += 1;
        }
        b += 1;
    }
    if count > 64 {
        return None;
    }
    Some(x)
}

} // verus!
