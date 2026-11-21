//! A cache of the Pike VM's steps.
//!
//! One step of the Pike VM turns the thread list at one byte into the
//! thread list at the next. Which instructions the new threads are at,
//! which old thread each one copies its capture slots from, and which
//! slots it sets to the new position depend only on the instructions of
//! the old list, the byte, and what the assertions see: not on the slot
//! values, and not on the position. So the step can be computed once per
//! (list, byte) without slot values (`sfull`), stored, and replayed by
//! copying (`isa`). This file proves that the replay gives exactly the
//! list the Pike VM's own step gives (`cfull`), and that this step keeps
//! the matcher's invariant.
#[allow(unused_imports)]
use crate::pike::*;
#[allow(unused_imports)]
use crate::prog::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use crate::vmspec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Slot masks
// ---------------------------------------------------------------------------

/// Slot `j` is in the mask `m`.
pub open spec fn mbit(m: u64, j: int) -> bool {
    0 <= j < 64 && (m >> (j as u64)) & 1u64 == 1u64
}

/// `m` with slot `slot`.
pub open spec fn setb(m: u64, slot: int) -> u64 {
    if 0 <= slot < 64 {
        m | (1u64 << (slot as u64))
    } else {
        m
    }
}

pub proof fn lemma_setb(m: u64, slot: int, j: int)
    requires
        0 <= slot < 64,
    ensures
        mbit(setb(m, slot), j) == (mbit(m, j) || j == slot),
{
    if 0 <= j < 64 {
        let jj = j as u64;
        let ss = slot as u64;
        assert(jj < 64 && ss < 64 ==> ((((m | (1u64 << ss)) >> jj) & 1u64 == 1u64) == (((m >> jj) & 1u64 == 1u64) || jj
            == ss))) by (bit_vector);
    }
}

pub proof fn lemma_mbit0(j: int)
    ensures
        !mbit(0, j),
{
    if 0 <= j < 64 {
        let jj = j as u64;
        assert(jj < 64 ==> (0u64 >> jj) & 1u64 == 0u64) by (bit_vector);
    }
}

/// The slots `c` with those in `m` set to `pos`.
pub open spec fn icap(c: Seq<int>, m: u64, pos: int) -> Seq<int> {
    Seq::new(c.len(), |j: int| if mbit(m, j) { pos } else { c[j] })
}

pub proof fn lemma_icap0(c: Seq<int>, pos: int)
    ensures
        icap(c, 0, pos) == c,
{
    assert forall|j: int| 0 <= j < c.len() implies icap(c, 0, pos)[j] == c[j] by {
        lemma_mbit0(j);
    }
    assert(icap(c, 0, pos) =~= c);
}

// ---------------------------------------------------------------------------
// What the assertions see
// ---------------------------------------------------------------------------

/// The kind of byte at `j`: 0 a word byte, 1 a newline, 2 any other, 3
/// the end of the text.
pub open spec fn lac(s: Seq<u8>, j: int) -> int {
    if j >= s.len() {
        3
    } else if is_word(s[j]) {
        0
    } else if s[j] == 0x0A {
        1
    } else {
        2
    }
}

/// Whether assertion `k` holds just after the byte `prev`, before a byte
/// of kind `la`.
pub open spec fn lkv(k: Look, prev: u8, la: int) -> bool {
    match k {
        Look::Start => false,
        Look::End => la == 3,
        Look::StartLine => prev == 0x0A,
        Look::EndLine => la == 3 || la == 1,
        Look::Word => is_word(prev) != (la == 0),
        Look::NotWord => is_word(prev) == (la == 0),
    }
}

pub proof fn lemma_lkv(k: Look, s: Seq<u8>, j: int)
    requires
        1 <= j <= s.len(),
    ensures
        look_holds(k, s, j) == lkv(k, s[j - 1], lac(s, j)),
{
}

// ---------------------------------------------------------------------------
// The marking search without slot values
// ---------------------------------------------------------------------------

/// A thread without slot values: its instruction and the slots set on
/// the way to it.
pub ghost struct SE {
    pub pc: int,
    pub mask: u64,
}

/// `ecd` without slot values.
pub open spec fn secd(p: Seq<SInst>, prev: u8, la: int, pc: int, m: u64, seen: Set<int>) -> (Seq<SE>, Set<int>)
    decreases p.len() - pc,
{
    if pc < 0 || pc >= p.len() || seen.contains(pc) {
        (seq![], seen)
    } else {
        let sn = seen.insert(pc);
        match p[pc] {
            SInst::Match => (seq![SE { pc: pc, mask: m }], sn),
            SInst::Char { cls, next } => (seq![SE { pc: pc, mask: m }], sn),
            SInst::Fail => (seq![], sn),
            SInst::Split { a, b } => {
                let r1 = if pc < a < p.len() {
                    secd(p, prev, la, a, m, sn)
                } else {
                    (seq![], sn)
                };
                let r2 = if pc < b < p.len() {
                    secd(p, prev, la, b, m, r1.1)
                } else {
                    (seq![], r1.1)
                };
                (r1.0 + r2.0, r2.1)
            },
            SInst::Save { slot, next } => if pc < next < p.len() {
                secd(p, prev, la, next, setb(m, slot), sn)
            } else {
                (seq![], sn)
            },
            SInst::Look { k, next } => if pc < next < p.len() && lkv(k, prev, la) {
                secd(p, prev, la, next, m, sn)
            } else {
                (seq![], sn)
            },
        }
    }
}

/// The threads `e` with slot values: `c`, and `pos` where set.
pub open spec fn ise(e: Seq<SE>, c: Seq<int>, pos: int) -> Seq<T> {
    Seq::new(e.len(), |k: int| T { pc: e[k].pc, caps: icap(c, e[k].mask, pos) })
}

/// Every slot the program saves is below 64 and below `ns`.
pub open spec fn slots_ok(p: Seq<SInst>, ns: int) -> bool {
    forall|q: int|
        0 <= q < p.len() ==> match #[trigger] p[q] {
            SInst::Save { slot, next } => 0 <= slot < 64 && slot < ns,
            _ => true,
        }
}

/// `secd` is `ecd` without slot values.
pub proof fn lemma_secd(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>, m: u64, seen: Set<int>)
    requires
        1 <= i <= s.len(),
        slots_ok(p, c.len() as int),
    ensures
        ({
            let r = secd(p, s[i - 1], lac(s, i), pc, m, seen);
            ecd(p, s, i, pc, icap(c, m, i), seen) == (ise(r.0, c, i), r.1)
        }),
    decreases p.len() - pc,
{
    let prev = s[i - 1];
    let la = lac(s, i);
    let r = secd(p, prev, la, pc, m, seen);
    let cc = icap(c, m, i);
    if pc < 0 || pc >= p.len() || seen.contains(pc) {
        assert(ise(r.0, c, i) =~= Seq::<T>::empty());
    } else {
        let sn = seen.insert(pc);
        match p[pc] {
            SInst::Match => {
                assert(ise(r.0, c, i) =~= seq![T { pc: pc, caps: cc }]);
            },
            SInst::Char { cls, next } => {
                assert(ise(r.0, c, i) =~= seq![T { pc: pc, caps: cc }]);
            },
            SInst::Fail => {
                assert(ise(r.0, c, i) =~= Seq::<T>::empty());
            },
            SInst::Split { a, b } => {
                let r1 = if pc < a < p.len() {
                    secd(p, prev, la, a, m, sn)
                } else {
                    (seq![], sn)
                };
                let r2 = if pc < b < p.len() {
                    secd(p, prev, la, b, m, r1.1)
                } else {
                    (seq![], r1.1)
                };
                if pc < a < p.len() {
                    lemma_secd(p, s, i, a, c, m, sn);
                }
                if pc < b < p.len() {
                    lemma_secd(p, s, i, b, c, m, r1.1);
                }
                assert(ise(r1.0, c, i) =~= Seq::<T>::empty() || pc < a < p.len());
                assert(ise(r2.0, c, i) =~= Seq::<T>::empty() || pc < b < p.len());
                assert(ise(r1.0 + r2.0, c, i) =~= ise(r1.0, c, i) + ise(r2.0, c, i));
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_secd(p, s, i, next, c, setb(m, slot), sn);
                    assert forall|j: int| 0 <= j < c.len() implies cc.update(slot, i)[j] == icap(c, setb(m, slot), i)[j] by {
                        lemma_setb(m, slot, j);
                    }
                    assert(cc.update(slot, i) =~= icap(c, setb(m, slot), i));
                } else {
                    assert(ise(r.0, c, i) =~= Seq::<T>::empty());
                }
            },
            SInst::Look { k, next } => {
                lemma_lkv(k, s, i);
                if pc < next < p.len() && lkv(k, prev, la) {
                    lemma_secd(p, s, i, next, c, m, sn);
                } else {
                    assert(ise(r.0, c, i) =~= Seq::<T>::empty());
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// One step of the Pike VM over an ASCII byte, as a function on lists
// ---------------------------------------------------------------------------

/// The threads of `l` from the `k`th on, stepped over the byte at `i`:
/// what they add to the next list `acc`, what gets marked, and the match
/// if a thread is at `Match` (the threads after it are dropped).
pub open spec fn cstep(p: Seq<SInst>, s: Seq<u8>, i: int, l: Seq<T>, k: int, acc: Seq<T>, seen: Set<int>) -> (
    Seq<T>,
    Set<int>,
    Option<M>,
)
    decreases l.len() - k,
{
    if k < 0 || k >= l.len() {
        (acc, seen, None)
    } else {
        let t = l[k];
        if t.pc < 0 || t.pc >= p.len() {
            cstep(p, s, i, l, k + 1, acc, seen)
        } else {
            match p[t.pc] {
                SInst::Match => (acc, seen, Some(M { end: i, caps: t.caps })),
                SInst::Char { cls, next } => if 0 <= i < s.len() && cls.contains(s[i] as u32) {
                    let r = ecd(p, s, i + 1, next, t.caps, seen);
                    cstep(p, s, i, l, k + 1, acc + r.0, r.1)
                } else {
                    cstep(p, s, i, l, k + 1, acc, seen)
                },
                _ => cstep(p, s, i, l, k + 1, acc, seen),
            }
        }
    }
}

/// A whole step: the list at `i + 1`, with the threads of a match
/// starting there added last unless a match is known, and the match
/// found at `i` if any.
pub open spec fn cfull(p: Seq<SInst>, s: Seq<u8>, st: int, ns: nat, i: int, l: Seq<T>, matched: bool) -> (
    Seq<T>,
    Option<M>,
) {
    let r = cstep(p, s, i, l, 0, seq![], Set::<int>::empty());
    if matched || r.2 is Some {
        (r.0, r.2)
    } else {
        (r.0 + ecd(p, s, i + 1, st, unset(ns), r.1).0, None)
    }
}

pub proof fn lemma_dec_ascii(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        s[i] < 0x80,
    ensures
        dec(s, i) == Some((s[i] as u32, 1int)),
{
}

pub open spec fn orm(a: Option<M>, b: Option<M>) -> Option<M> {
    match a {
        Some(_) => a,
        None => b,
    }
}

/// `cstep` keeps the matcher's invariant.
pub proof fn lemma_cstep(
    p: Seq<SInst>,
    s: Seq<u8>,
    i: int,
    l: Seq<T>,
    k: int,
    acc: Seq<T>,
    seen: Set<int>,
    tail: Option<M>,
)
    requires
        fwd(p),
        0 <= i < s.len(),
        s[i] < 0x80,
        0 <= k <= l.len(),
        inv_list(p, s, i + 1, seen, acc),
    ensures
        ({
            let r = cstep(p, s, i, l, k, acc, seen);
            &&& inv_list(p, s, i + 1, r.1, r.0)
            &&& or(fr(p, s, r.0, i + 1), orm(r.2, tail)) == or(
                fr(p, s, acc, i + 1),
                or(fr(p, s, l.subrange(k, l.len() as int), i), tail),
            )
        }),
    decreases l.len() - k,
{
    if k >= l.len() {
        assert(l.subrange(k, l.len() as int) =~= Seq::<T>::empty());
    } else {
        let t = l[k];
        lemma_fr_cons2(p, s, l, k, i);
        lemma_dec_ascii(s, i);
        if t.pc < 0 || t.pc >= p.len() {
            lemma_cstep(p, s, i, l, k + 1, acc, seen, tail);
        } else {
            match p[t.pc] {
                SInst::Match => {
                    assert(pmt(p, s, t, i) == seq![M { end: i, caps: t.caps }]);
                },
                SInst::Char { cls, next } => {
                    if cls.contains(s[i] as u32) {
                        assert(fwd_at(p, t.pc));
                        let r = ecd(p, s, i + 1, next, t.caps, seen);
                        lemma_add_ecd(p, s, i + 1, next, t.caps, seen, acc);
                        assert(pmt(p, s, t, i) == pm(p, s, next, i + 1, t.caps));
                        lemma_cstep(p, s, i, l, k + 1, acc + r.0, r.1, tail);
                    } else {
                        assert(pmt(p, s, t, i).len() == 0);
                        lemma_cstep(p, s, i, l, k + 1, acc, seen, tail);
                    }
                },
                _ => {
                    assert(pmt(p, s, t, i).len() == 0);
                    lemma_cstep(p, s, i, l, k + 1, acc, seen, tail);
                },
            }
        }
    }
}

pub proof fn lemma_fr_cons2(p: Seq<SInst>, s: Seq<u8>, l: Seq<T>, i: int, at: int)
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

/// A whole step keeps the matcher's invariant: if the answer is the best
/// match of the list at `i`, or else the known match, or else the result
/// of searching from `i + 1`, the same holds one byte on.
pub proof fn lemma_cfull(
    p: Seq<SInst>,
    s: Seq<u8>,
    st: int,
    ns: nat,
    i: int,
    l: Seq<T>,
    matched: bool,
    mv: M,
    ans: Option<M>,
)
    requires
        fwd(p),
        0 <= i < s.len(),
        s[i] < 0x80,
        0 <= st < p.len(),
        ans == or(
            fr(p, s, l, i),
            if matched {
                Some(mv)
            } else {
                search_p(p, s, st, i + 1, ns)
            },
        ),
    ensures
        ({
            let r = cfull(p, s, st, ns, i, l, matched);
            ans == or(
                fr(p, s, r.0, i + 1),
                match r.1 {
                    Some(m) => Some(m),
                    None => if matched {
                        Some(mv)
                    } else {
                        search_p(p, s, st, i + 2, ns)
                    },
                },
            )
        }),
{
    let tail = if matched {
        Some(mv)
    } else {
        search_p(p, s, st, i + 1, ns)
    };
    let e = Seq::<T>::empty();
    let r = cstep(p, s, i, l, 0, e, Set::<int>::empty());
    lemma_cstep(p, s, i, l, 0, e, Set::<int>::empty(), tail);
    assert(l.subrange(0, l.len() as int) =~= l);
    assert(fr(p, s, e, i + 1) is None);
    if !(matched || r.2 is Some) {
        lemma_add_ecd(p, s, i + 1, st, unset(ns), r.1, r.0);
    }
}

// ---------------------------------------------------------------------------
// The same step without slot values
// ---------------------------------------------------------------------------

/// A thread of the next list without slot values: its instruction, the
/// thread of the old list it copies its slots from (or -1 for none: all
/// unset), and the slots it sets to the new position.
pub ghost struct SA {
    pub src: int,
    pub pc: int,
    pub mask: u64,
}

pub open spec fn tag(e: Seq<SE>, src: int) -> Seq<SA> {
    Seq::new(e.len(), |k: int| SA { src: src, pc: e[k].pc, mask: e[k].mask })
}

/// `cstep` without slot values, for a list at the instructions `pcs`,
/// the byte `b`, and a next byte of kind `la`. A match is reported as
/// the index of the thread at `Match`.
pub open spec fn sstep(p: Seq<SInst>, b: u8, la: int, pcs: Seq<int>, k: int, acc: Seq<SA>, seen: Set<int>) -> (
    Seq<SA>,
    Set<int>,
    Option<int>,
)
    decreases pcs.len() - k,
{
    if k < 0 || k >= pcs.len() {
        (acc, seen, None)
    } else {
        let pc = pcs[k];
        if pc < 0 || pc >= p.len() {
            sstep(p, b, la, pcs, k + 1, acc, seen)
        } else {
            match p[pc] {
                SInst::Match => (acc, seen, Some(k)),
                SInst::Char { cls, next } => if cls.contains(b as u32) {
                    let r = secd(p, b, la, next, 0, seen);
                    sstep(p, b, la, pcs, k + 1, acc + tag(r.0, k), r.1)
                } else {
                    sstep(p, b, la, pcs, k + 1, acc, seen)
                },
                _ => sstep(p, b, la, pcs, k + 1, acc, seen),
            }
        }
    }
}

/// `cfull` without slot values.
pub open spec fn sfull(p: Seq<SInst>, st: int, b: u8, la: int, pcs: Seq<int>, matched: bool) -> (Seq<SA>, Option<int>) {
    let r = sstep(p, b, la, pcs, 0, seq![], Set::<int>::empty());
    if matched || r.2 is Some {
        (r.0, r.2)
    } else {
        (r.0 + tag(secd(p, b, la, st, 0, r.1).0, -1), None)
    }
}

/// The slot values thread `a` gets from the list `l` at position `pos`.
pub open spec fn acap(a: SA, l: Seq<T>, ns: nat, pos: int) -> Seq<int> {
    icap(
        if 0 <= a.src < l.len() {
            l[a.src].caps
        } else {
            unset(ns)
        },
        a.mask,
        pos,
    )
}

/// The threads `a` with slot values from the list `l`.
pub open spec fn isa(a: Seq<SA>, l: Seq<T>, ns: nat, pos: int) -> Seq<T> {
    Seq::new(a.len(), |k: int| T { pc: a[k].pc, caps: acap(a[k], l, ns, pos) })
}

/// Every thread of `l` has `ns` slots.
pub open spec fn caps_ok(l: Seq<T>, ns: nat) -> bool {
    forall|k: int| 0 <= k < l.len() ==> (#[trigger] l[k]).caps.len() == ns
}

pub open spec fn mat(l: Seq<T>, i: int, j: Option<int>) -> Option<M> {
    match j {
        Some(j) => Some(M { end: i, caps: l[j].caps }),
        None => None,
    }
}

/// `sstep` is `cstep` without slot values.
pub proof fn lemma_sstep(
    p: Seq<SInst>,
    s: Seq<u8>,
    ns: nat,
    i: int,
    l: Seq<T>,
    k: int,
    sacc: Seq<SA>,
    seen: Set<int>,
)
    requires
        0 <= i < s.len(),
        slots_ok(p, ns as int),
        caps_ok(l, ns),
        0 <= k <= l.len(),
    ensures
        ({
            let c = cstep(p, s, i, l, k, isa(sacc, l, ns, i + 1), seen);
            let r = sstep(p, s[i], lac(s, i + 1), pcs_of(l), k, sacc, seen);
            &&& c.0 == isa(r.0, l, ns, i + 1)
            &&& c.1 == r.1
            &&& c.2 == mat(l, i, r.2)
            &&& (r.2 matches Some(j) ==> k <= j < l.len())
        }),
    decreases l.len() - k,
{
    let b = s[i];
    let la = lac(s, i + 1);
    let pcs = pcs_of(l);
    let acc = isa(sacc, l, ns, i + 1);
    if k < l.len() {
        let t = l[k];
        assert(pcs[k] == t.pc);
        if t.pc < 0 || t.pc >= p.len() {
            lemma_sstep(p, s, ns, i, l, k + 1, sacc, seen);
        } else {
            match p[t.pc] {
                SInst::Match => {},
                SInst::Char { cls, next } => {
                    if cls.contains(b as u32) {
                        let r = secd(p, b, la, next, 0, seen);
                        lemma_secd(p, s, i + 1, next, t.caps, 0, seen);
                        lemma_icap0(t.caps, i + 1);
                        let sacc2 = sacc + tag(r.0, k);
                        assert(acc + ise(r.0, t.caps, i + 1) =~= isa(sacc2, l, ns, i + 1));
                        lemma_sstep(p, s, ns, i, l, k + 1, sacc2, r.1);
                    } else {
                        lemma_sstep(p, s, ns, i, l, k + 1, sacc, seen);
                    }
                },
                _ => {
                    lemma_sstep(p, s, ns, i, l, k + 1, sacc, seen);
                },
            }
        }
    }
}

/// `sfull` is `cfull` without slot values.
pub proof fn lemma_sfull(p: Seq<SInst>, s: Seq<u8>, st: int, ns: nat, i: int, l: Seq<T>, matched: bool)
    requires
        0 <= i < s.len(),
        slots_ok(p, ns as int),
        caps_ok(l, ns),
    ensures
        ({
            let c = cfull(p, s, st, ns, i, l, matched);
            let r = sfull(p, st, s[i], lac(s, i + 1), pcs_of(l), matched);
            &&& c.0 == isa(r.0, l, ns, i + 1)
            &&& c.1 == mat(l, i, r.1)
            &&& (r.1 matches Some(j) ==> 0 <= j < l.len())
        }),
{
    let b = s[i];
    let la = lac(s, i + 1);
    let e = Seq::<SA>::empty();
    assert(isa(e, l, ns, i + 1) =~= Seq::<T>::empty());
    lemma_sstep(p, s, ns, i, l, 0, e, Set::<int>::empty());
    let r = sstep(p, b, la, pcs_of(l), 0, e, Set::<int>::empty());
    if !(matched || r.2 is Some) {
        let x = secd(p, b, la, st, 0, r.1);
        lemma_secd(p, s, i + 1, st, unset(ns), 0, r.1);
        lemma_icap0(unset(ns), i + 1);
        assert(isa(r.0, l, ns, i + 1) + ise(x.0, unset(ns), i + 1) =~= isa(r.0 + tag(x.0, -1), l, ns, i + 1));
    }
}

pub open spec fn pos_ok(a: Seq<SA>) -> bool {
    forall|k: int| 0 <= k < a.len() ==> (#[trigger] a[k]).src >= 0
}

/// The threads `sstep` adds each have a thread of the old list as source.
pub proof fn lemma_sstep_pos(p: Seq<SInst>, b: u8, la: int, pcs: Seq<int>, k: int, acc: Seq<SA>, seen: Set<int>)
    requires
        pos_ok(acc),
        0 <= k,
    ensures
        pos_ok(sstep(p, b, la, pcs, k, acc, seen).0),
    decreases pcs.len() - k,
{
    if k < pcs.len() {
        let pc = pcs[k];
        if pc < 0 || pc >= p.len() {
            lemma_sstep_pos(p, b, la, pcs, k + 1, acc, seen);
        } else {
            match p[pc] {
                SInst::Match => {},
                SInst::Char { cls, next } => {
                    if cls.contains(b as u32) {
                        let r = secd(p, b, la, next, 0, seen);
                        let acc2 = acc + tag(r.0, k);
                        assert forall|j: int| 0 <= j < acc2.len() implies (#[trigger] acc2[j]).src >= 0 by {
                            if j < acc.len() {
                                assert(acc2[j] == acc[j]);
                            } else {
                                assert(acc2[j] == tag(r.0, k)[j - acc.len()]);
                            }
                        }
                        assert(pos_ok(acc2));
                        lemma_sstep_pos(p, b, la, pcs, k + 1, acc2, r.1);
                    } else {
                        lemma_sstep_pos(p, b, la, pcs, k + 1, acc, seen);
                    }
                },
                _ => {
                    lemma_sstep_pos(p, b, la, pcs, k + 1, acc, seen);
                },
            }
        }
    }
}

/// If a step from the list `l` leaves no thread with a source and finds
/// no match, no thread of `l` leads to a match: the answer is that of a
/// search from the next byte on.
pub proof fn lemma_idle(p: Seq<SInst>, s: Seq<u8>, st: int, ns: nat, i: int, l: Seq<T>, ans: Option<M>)
    requires
        fwd(p),
        0 <= i < s.len(),
        s[i] < 0x80,
        0 <= st < p.len(),
        slots_ok(p, ns as int),
        caps_ok(l, ns),
        ans == or(fr(p, s, l, i), search_p(p, s, st, i + 1, ns)),
        ({
            let f = sfull(p, st, s[i], lac(s, i + 1), pcs_of(l), false);
            &&& f.1 is None
            &&& forall|k: int| 0 <= k < f.0.len() ==> (#[trigger] f.0[k]).src == -1
        }),
    ensures
        ans == search_p(p, s, st, i + 1, ns),
{
    let b = s[i];
    let la = lac(s, i + 1);
    let e = Seq::<SA>::empty();
    let et = Seq::<T>::empty();
    let f = sfull(p, st, b, la, pcs_of(l), false);
    let r = sstep(p, b, la, pcs_of(l), 0, e, Set::<int>::empty());
    lemma_sstep_pos(p, b, la, pcs_of(l), 0, e, Set::<int>::empty());
    assert(pos_ok(r.0));
    assert(r.2 is None);
    if r.0.len() > 0 {
        assert(f.0[0] == r.0[0]);
        assert(false);
    }
    assert(isa(e, l, ns, i + 1) =~= et);
    lemma_sstep(p, s, ns, i, l, 0, e, Set::<int>::empty());
    let c = cstep(p, s, i, l, 0, et, Set::<int>::empty());
    assert(c.0 =~= et);
    assert(c.2 is None);
    let tail = search_p(p, s, st, i + 1, ns);
    lemma_cstep(p, s, i, l, 0, et, Set::<int>::empty(), tail);
    assert(l.subrange(0, l.len() as int) =~= l);
    assert(fr(p, s, et, i + 1) is None);
}

// ---------------------------------------------------------------------------
// Computing a step without slot values
// ---------------------------------------------------------------------------

/// A thread of a stored step: where its slots come from (`NOSRC`: all
/// unset), its instruction, and the slots it sets to the new position.
#[derive(Clone, Copy)]
pub struct Act {
    pub src: u32,
    pub pc: u32,
    pub mask: u64,
}

pub const NOSRC: u32 = u32::MAX;

pub open spec fn srcv(src: u32) -> int {
    if src == NOSRC {
        -1
    } else {
        src as int
    }
}

pub open spec fn av(a: Act) -> SA {
    SA { src: srcv(a.src), pc: a.pc as int, mask: a.mask }
}

pub open spec fn avs(v: Seq<Act>) -> Seq<SA> {
    Seq::new(v.len(), |k: int| av(v[k]))
}

/// A frame of the search's stack: an instruction to explore, or a mask
/// to put back.
#[derive(Clone, Copy)]
pub enum SFrame {
    Explore(u32),
    Restore(u64),
}

pub ghost enum SF {
    Ex(int),
    Re(u64),
}

pub open spec fn sfv(f: SFrame) -> SF {
    match f {
        SFrame::Explore(pc) => SF::Ex(pc as int),
        SFrame::Restore(m) => SF::Re(m),
    }
}

pub open spec fn ssv(st: Seq<SFrame>) -> Seq<SF> {
    Seq::new(st.len(), |k: int| sfv(st[k]))
}

/// What the stack still has to produce, top (last) first.
pub open spec fn swk(p: Seq<SInst>, b: u8, la: int, st: Seq<SF>, m: u64, seen: Set<int>) -> (Seq<SE>, Set<int>)
    decreases st.len(),
{
    if st.len() == 0 {
        (seq![], seen)
    } else {
        match st.last() {
            SF::Re(old) => swk(p, b, la, st.drop_last(), old, seen),
            SF::Ex(pc) => {
                let r1 = secd(p, b, la, pc, m, seen);
                let r2 = swk(p, b, la, st.drop_last(), m, r1.1);
                (r1.0 + r2.0, r2.1)
            },
        }
    }
}

pub proof fn lemma_swk_ex(p: Seq<SInst>, b: u8, la: int, st: Seq<SF>, pc: int, m: u64, seen: Set<int>)
    ensures
        swk(p, b, la, st.push(SF::Ex(pc)), m, seen) == ({
            let r1 = secd(p, b, la, pc, m, seen);
            let r2 = swk(p, b, la, st, m, r1.1);
            (r1.0 + r2.0, r2.1)
        }),
{
    assert(st.push(SF::Ex(pc)).drop_last() =~= st);
}

pub proof fn lemma_swk_re(p: Seq<SInst>, b: u8, la: int, st: Seq<SF>, old: u64, m: u64, seen: Set<int>)
    ensures
        swk(p, b, la, st.push(SF::Re(old)), m, seen) == swk(p, b, la, st, old, seen),
{
    assert(st.push(SF::Re(old)).drop_last() =~= st);
}

/// `lkv`, computed.
pub fn lkx(k: Look, b: u8, la: u8) -> (r: bool)
    ensures
        r == lkv(k, b, la as int),
{
    match k {
        Look::Start => false,
        Look::End => la == 3,
        Look::StartLine => b == 0x0A,
        Look::EndLine => la == 3 || la == 1,
        Look::Word => word_byte(b) != (la == 0),
        Look::NotWord => word_byte(b) == (la == 0),
    }
}

/// The marking search without slot values, from `pc0`: appends the
/// threads it reaches to `acts`, each copying from `src`. Stops and
/// gives false if it runs out of `fuel`, one unit per loop iteration.
pub fn sadd(
    prog: &Prog,
    b: u8,
    la: u8,
    pc0: u32,
    src: u32,
    mark: &mut Vec<u64>,
    gen: u64,
    stack: &mut Vec<SFrame>,
    acts: &mut Vec<Act>,
    fuel: &mut u64, it: &mut Ghost<int>,
    Ghost(seen): Ghost<Set<int>>,
) -> (r: (bool, Ghost<Set<int>>))
    requires
        prog.wf(),
        prog.nslots <= 64,
        pc0 < prog.insts@.len(),
        old(mark)@.len() == prog.insts@.len(),
        old(stack)@.len() == 0,
        marks(old(mark)@, gen, seen),
        forall|v: int| seen.contains(v) ==> 0 <= v < prog.insts@.len(),
    ensures
        final(mark)@.len() == old(mark)@.len(),
        final(stack)@.len() == 0,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
        forall|k: int| 0 <= k < old(mark)@.len() ==> final(mark)@[k] == old(mark)@[k] || final(mark)@[k] == gen,
        r.0 ==> ({
            let e = secd(prog.sp(), b, la as int, pc0 as int, 0, seen);
            &&& avs(final(acts)@) == avs(old(acts)@) + tag(e.0, srcv(src))
            &&& r.1@ == e.1
            &&& marks(final(mark)@, gen, r.1@)
            &&& forall|v: int| r.1@.contains(v) ==> 0 <= v < prog.insts@.len()
        }),
{
    let ghost sp = prog.sp();
    let ghost n = prog.insts@.len() as int;
    let ghost lai = la as int;
    let ghost si = srcv(src);
    let ghost goal = secd(sp, b, lai, pc0 as int, 0, seen);
    let ghost a0 = avs(acts@);
    let ghost mut sn = seen;
    let ghost mut out = Seq::<SE>::empty();
    let mut m: u64 = 0;
    stack.push(SFrame::Explore(pc0));
    proof {
        lemma_swk_ex(sp, b, lai, Seq::<SF>::empty(), pc0 as int, 0, seen);
        assert(ssv(stack@) =~= Seq::<SF>::empty().push(SF::Ex(pc0 as int)));
        assert(a0 + tag(out, si) =~= a0);
        let g = secd(sp, b, lai, pc0 as int, 0, seen);
        assert(g.0 + Seq::<SE>::empty() =~= g.0);
    }
    while stack.len() > 0
        invariant
            prog.wf(),
            prog.nslots <= 64,
            sp == prog.sp(),
            n == prog.insts@.len(),
            lai == la as int,
            si == srcv(src),
            mark@.len() == n,
            old(mark)@.len() == n,
            marks(mark@, gen, sn),
            forall|v: int| sn.contains(v) ==> 0 <= v < n,
            forall|k: int| 0 <= k < n ==> mark@[k] == old(mark)@[k] || mark@[k] == gen,
            forall|k: int|
                0 <= k < stack@.len() ==> match #[trigger] stack@[k] {
                    SFrame::Explore(pc) => pc < n,
                    SFrame::Restore(old) => true,
                },
            avs(acts@) == a0 + tag(out, si),
            ({
                let w = swk(sp, b, lai, ssv(stack@), m, sn);
                &&& out + w.0 == goal.0
                &&& w.1 == goal.1
            }),
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
        decreases *fuel,
    {
        if *fuel == 0 {
            stack.clear();
            return (false, Ghost(sn));
        }
        *fuel -= 1;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        let ghost st0 = stack@;
        let f = stack.pop().unwrap();
        let ghost rest = ssv(stack@);
        assert(ssv(st0) =~= rest.push(sfv(f)));
        match f {
            SFrame::Restore(old) => {
                proof {
                    lemma_swk_re(sp, b, lai, rest, old, m, sn);
                }
                m = old;
            },
            SFrame::Explore(pc) => {
                proof {
                    lemma_swk_ex(sp, b, lai, rest, pc as int, m, sn);
                }
                if mark[pc as usize] == gen {
                    assert(sn.contains(pc as int));
                    let ghost w2 = swk(sp, b, lai, rest, m, sn);
                    assert(Seq::<SE>::empty() + w2.0 =~= w2.0);
                } else {
                    assert(!sn.contains(pc as int));
                    let ghost sn0 = sn;
                    mark.set(pc as usize, gen);
                    proof {
                        sn = sn0.insert(pc as int);
                        assert(fwd_at(sp, pc as int));
                    }
                    let ghost e = secd(sp, b, lai, pc as int, m, sn0);
                    let inst = prog.insts[pc as usize];
                    assert(sp[pc as int] == iv(inst, prog.classes@));
                    match inst {
                        Inst::Char { cls, next } => {
                            let ghost av0 = acts@;
                            let x = Act { src: src, pc: pc, mask: m };
                            acts.push(x);
                            proof {
                                let t = SE { pc: pc as int, mask: m };
                                let w2 = swk(sp, b, lai, rest, m, sn);
                                assert(e.0 == seq![t]);
                                let out2 = out.push(t);
                                assert(acts@ == av0.push(x));
                                assert(avs(acts@) =~= avs(av0).push(av(x)));
                                assert(tag(out2, si) =~= tag(out, si).push(av(x)));
                                assert(avs(acts@) =~= a0 + tag(out2, si));
                                assert(out2 + w2.0 =~= out + (seq![t] + w2.0));
                                out = out2;
                            }
                        },
                        Inst::Match => {
                            let ghost av0 = acts@;
                            let x = Act { src: src, pc: pc, mask: m };
                            acts.push(x);
                            proof {
                                let t = SE { pc: pc as int, mask: m };
                                let w2 = swk(sp, b, lai, rest, m, sn);
                                assert(e.0 == seq![t]);
                                let out2 = out.push(t);
                                assert(acts@ == av0.push(x));
                                assert(avs(acts@) =~= avs(av0).push(av(x)));
                                assert(tag(out2, si) =~= tag(out, si).push(av(x)));
                                assert(avs(acts@) =~= a0 + tag(out2, si));
                                assert(out2 + w2.0 =~= out + (seq![t] + w2.0));
                                out = out2;
                            }
                        },
                        Inst::Fail => {
                            let ghost w2 = swk(sp, b, lai, rest, m, sn);
                            assert(Seq::<SE>::empty() + w2.0 =~= w2.0);
                        },
                        Inst::Split { a, b: bb } => {
                            stack.push(SFrame::Explore(bb));
                            stack.push(SFrame::Explore(a));
                            proof {
                                let rb = rest.push(SF::Ex(bb as int));
                                assert(ssv(stack@) =~= rb.push(SF::Ex(a as int)));
                                lemma_swk_ex(sp, b, lai, rb, a as int, m, sn);
                                let r1 = secd(sp, b, lai, a as int, m, sn);
                                lemma_swk_ex(sp, b, lai, rest, bb as int, m, r1.1);
                                let r2 = secd(sp, b, lai, bb as int, m, r1.1);
                                let w3 = swk(sp, b, lai, rest, m, r2.1);
                                assert(e.0 == r1.0 + r2.0);
                                assert(out + (r1.0 + (r2.0 + w3.0)) =~= out + ((r1.0 + r2.0) + w3.0));
                            }
                        },
                        Inst::Save { slot, next } => {
                            let old = m;
                            stack.push(SFrame::Restore(old));
                            assert(slot < 64);
                            m = m | (1u64 << (slot as u64));
                            stack.push(SFrame::Explore(next));
                            proof {
                                assert(m == setb(old, slot as int));
                                let rr = rest.push(SF::Re(old));
                                assert(ssv(stack@) =~= rr.push(SF::Ex(next as int)));
                                lemma_swk_ex(sp, b, lai, rr, next as int, m, sn);
                                let r1 = secd(sp, b, lai, next as int, m, sn);
                                lemma_swk_re(sp, b, lai, rest, old, m, r1.1);
                            }
                        },
                        Inst::Look { k, next } => {
                            if lkx(k, b, la) {
                                stack.push(SFrame::Explore(next));
                                assert(ssv(stack@) =~= rest.push(SF::Ex(next as int)));
                                proof {
                                    lemma_swk_ex(sp, b, lai, rest, next as int, m, sn);
                                }
                            } else {
                                let ghost w2 = swk(sp, b, lai, rest, m, sn);
                                assert(Seq::<SE>::empty() + w2.0 =~= w2.0);
                            }
                        },
                    }
                }
            },
        }
    }
    proof {
        assert(ssv(stack@) =~= Seq::<SF>::empty());
        assert(out + Seq::<SE>::empty() =~= out);
    }
    (true, Ghost(sn))
}

pub const NOCUT: u32 = u32::MAX;

pub open spec fn pcsv(v: Seq<u32>) -> Seq<int> {
    Seq::new(v.len(), |k: int| v[k] as int)
}

pub open spec fn cutv(c: u32) -> Option<int> {
    if c == NOCUT {
        None
    } else {
        Some(c as int)
    }
}

/// Every thread of `a` copies from a thread below `n`, or from none.
pub open spec fn srcs_ok(a: Seq<SA>, n: int) -> bool {
    forall|k: int| 0 <= k < a.len() ==> -1 <= (#[trigger] a[k]).src < n
}

pub proof fn lemma_sstep_src(p: Seq<SInst>, b: u8, la: int, pcs: Seq<int>, k: int, acc: Seq<SA>, seen: Set<int>)
    requires
        srcs_ok(acc, pcs.len() as int),
        0 <= k,
    ensures
        srcs_ok(sstep(p, b, la, pcs, k, acc, seen).0, pcs.len() as int),
    decreases pcs.len() - k,
{
    if k < pcs.len() {
        let pc = pcs[k];
        if pc < 0 || pc >= p.len() {
            lemma_sstep_src(p, b, la, pcs, k + 1, acc, seen);
        } else {
            match p[pc] {
                SInst::Match => {},
                SInst::Char { cls, next } => {
                    if cls.contains(b as u32) {
                        let r = secd(p, b, la, next, 0, seen);
                        lemma_sstep_src(p, b, la, pcs, k + 1, acc + tag(r.0, k), r.1);
                    } else {
                        lemma_sstep_src(p, b, la, pcs, k + 1, acc, seen);
                    }
                },
                _ => {
                    lemma_sstep_src(p, b, la, pcs, k + 1, acc, seen);
                },
            }
        }
    }
}

pub proof fn lemma_sfull_src(p: Seq<SInst>, st: int, b: u8, la: int, pcs: Seq<int>, matched: bool)
    ensures
        srcs_ok(sfull(p, st, b, la, pcs, matched).0, pcs.len() as int),
{
    lemma_sstep_src(p, b, la, pcs, 0, seq![], Set::<int>::empty());
}

/// Computes `sfull` for the list at `pcs`: the threads of the next list
/// into `acts`, and the index of the thread at `Match` or `NOCUT`. Gives
/// false if it runs out of `fuel`.
pub fn sbuild(
    prog: &Prog,
    pcs: &Vec<u32>,
    matched: bool,
    b: u8,
    la: u8,
    mark: &mut Vec<u64>,
    gen: u64,
    stack: &mut Vec<SFrame>,
    acts: &mut Vec<Act>,
    fuel: &mut u64, it: &mut Ghost<int>,
) -> (r: (bool, u32))
    requires
        prog.wf(),
        prog.nslots <= 64,
        pcs@.len() <= prog.insts@.len(),
        old(mark)@.len() == prog.insts@.len(),
        old(stack)@.len() == 0,
        old(acts)@.len() == 0,
        marks(old(mark)@, gen, Set::<int>::empty()),
    ensures
        final(mark)@.len() == old(mark)@.len(),
        final(stack)@.len() == 0,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
        forall|k: int| 0 <= k < old(mark)@.len() ==> final(mark)@[k] == old(mark)@[k] || final(mark)@[k] == gen,
        r.0 ==> ({
            let f = sfull(prog.sp(), prog.start as int, b, la as int, pcsv(pcs@), matched);
            &&& avs(final(acts)@) == f.0
            &&& cutv(r.1) == f.1
            &&& (r.1 != NOCUT ==> r.1 < pcs@.len())
        }),
{
    let ghost sp = prog.sp();
    let ghost np = prog.insts@.len() as int;
    let ghost lai = la as int;
    let ghost pv = pcsv(pcs@);
    let ghost e0 = Seq::<SA>::empty();
    let ghost goal = sstep(sp, b, lai, pv, 0, e0, Set::<int>::empty());
    let n = pcs.len();
    let mut k: usize = 0;
    let mut cut: u32 = NOCUT;
    let ghost mut seen = Set::<int>::empty();
    assert(avs(acts@) =~= e0);
    while k < n && cut == NOCUT
        invariant
            prog.wf(),
            prog.nslots <= 64,
            sp == prog.sp(),
            np == prog.insts@.len(),
            lai == la as int,
            pv == pcsv(pcs@),
            n == pcs@.len(),
            n <= np,
            k <= n,
            mark@.len() == np,
            old(mark)@.len() == np,
            stack@.len() == 0,
            marks(mark@, gen, seen),
            forall|v: int| seen.contains(v) ==> 0 <= v < np,
            forall|j: int| 0 <= j < np ==> mark@[j] == old(mark)@[j] || mark@[j] == gen,
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
            cut == NOCUT ==> goal == sstep(sp, b, lai, pv, k as int, avs(acts@), seen),
            cut != NOCUT ==> goal == (avs(acts@), seen, Some(cut as int)) && cut < n,
        decreases *fuel,
    {
        if *fuel < 66 {
            return (false, NOCUT);
        }
        *fuel -= 66;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        let pc = pcs[k];
        assert(pv[k as int] == pc as int);
        if (pc as usize) < prog.insts.len() {
            let inst = prog.insts[pc as usize];
            assert(sp[pc as int] == iv(inst, prog.classes@));
            match inst {
                Inst::Match => {
                    cut = k as u32;
                },
                Inst::Char { cls, next } => {
                    let (inc, cc) = prog.classes[cls as usize].contains_c(b as u32);
                    proof {
                        *it.borrow_mut() = it@ + cc@;
                    }
                    if inc {
                        assert(fwd_at(sp, pc as int));
                        let ghost a0 = avs(acts@);
                        let (ok, gs) = sadd(prog, b, la, next, k as u32, mark, gen, stack, acts, fuel, it, Ghost(seen));
                        if !ok {
                            return (false, NOCUT);
                        }
                        proof {
                            assert(srcv(k as u32) == k as int);
                            seen = gs@;
                        }
                    }
                },
                _ => {},
            }
        }
        if cut == NOCUT {
            k += 1;
        }
    }
    if !matched && cut == NOCUT {
        let (ok, gs) = sadd(prog, b, la, prog.start as u32, NOSRC, mark, gen, stack, acts, fuel, it, Ghost(seen));
        if !ok {
            return (false, NOCUT);
        }
    }
    (true, cut)
}

// ---------------------------------------------------------------------------
// The table of stored steps
// ---------------------------------------------------------------------------

/// The most lists the table holds.
pub const MEMO_STATES: usize = 256;

/// The most threads all stored steps hold together.
pub const MEMO_ACTS: usize = 0x4_0000;

/// A step not computed yet.
pub const MUNK: u32 = 0xFFFF_FFFF;

/// A step the table will not hold.
pub const MNO: u32 = 0xFFFF_FFFE;

/// A list the table knows: its instructions, and whether a match is
/// already known when the Pike VM is at it.
pub struct MState {
    pub pcs: Vec<u32>,
    pub matched: bool,
}

/// A stored step.
pub struct Ent {
    /// The threads of the next list.
    pub acts: Vec<Act>,
    /// The thread at `Match`, or `NOCUT`.
    pub cut: u32,
    /// The next list.
    pub next: u32,
    /// The next list holds only threads of a match starting there.
    pub idle: bool,
    /// The one thread every thread of `acts` that has a source takes its
    /// slots from (`NOSRC`: none has a source), or `UMIX`.
    pub us: u32,
    /// Threads of `acts`, among the first 64, that have a source and set
    /// no slot.
    pub zb: u64,
}

pub const UMIX: u32 = 0xFFFF_FFFE;

pub open spec fn zb_ok(acts: Seq<Act>, zb: u64) -> bool {
    forall|j: int| #[trigger] mbit(zb, j) ==> j < acts.len() && acts[j].src != NOSRC && acts[j].mask == 0
}

/// Beside a stored step, what following it takes when the list is kept
/// as one row (`useq`): the step's own `next`, `cut`, `us` and `zb`.
/// `ok` only for a step with one source, numbered below 64, that is not
/// `idle` and leaves threads. Not `ok` and `us` 64: a step that is not
/// `idle` and leaves no thread.
#[derive(Clone, Copy)]
pub struct Un {
    pub zb: u64,
    pub cut: u32,
    pub next: u16,
    pub us: u8,
    pub ok: bool,
}

pub open spec fn un_ok(ents: Seq<Ent>, t: u32, u: Un) -> bool {
    (u.ok || u.us == 64) ==> t != MUNK && t != MNO && t < ents.len() && {
        let e = ents[t as int];
        &&& u.next as u32 == e.next
        &&& u.cut == e.cut
        &&& u.ok ==> u.us < 64 && u.us as u32 == e.us && e.acts@.len() > 0
        &&& !u.ok ==> e.acts@.len() == 0
        &&& u.zb == e.zb
        &&& !e.idle
    }
}

pub open spec fn us_ok(acts: Seq<Act>, us: u32) -> bool {
    us == UMIX || forall|k: int| 0 <= k < acts.len() ==> (#[trigger] acts[k]).src == NOSRC || acts[k].src == us
}

/// The threads a step with one source gives, without a list: thread `k`
/// has row `ux` (no row if it has no source) and sets its own slots at
/// `upos`.
pub open spec fn useq(acts: Seq<Act>, ux: u32, upos: usize) -> Seq<Th> {
    Seq::new(
        acts.len(),
        |k: int|
            Th {
                row: if acts[k].src == NOSRC {
                    NOROW
                } else {
                    ux
                },
                mask: acts[k].mask,
                pos: upos,
            },
    )
}

pub struct Memo {
    /// Capture slots fit a mask.
    pub on: bool,
    pub states: Vec<MState>,
    /// For each list, kind of next byte and ASCII byte: a stored step,
    /// `MUNK` or `MNO`.
    pub trans: Vec<u32>,
    /// Beside `trans`, for following steps without their threads: four
    /// times the next list, plus one if `idle`, plus two if the next
    /// list is empty, for a stored step that reaches no match; `DSTOP`
    /// for anything else.
    pub dn: Vec<u32>,
    /// Beside `trans`, for following steps on a list kept as one row.
    pub un: Vec<Un>,
    /// The kind of each byte as a next byte.
    pub lat: Vec<u8>,
    /// How well dry runs have paid lately, and a count of the runs
    /// skipped since they stopped paying. Only a choice of when to try.
    pub credit: u8,
    pub tick: u8,
    pub ents: Vec<Ent>,
    pub nacts: usize,
    pub mark: Vec<u64>,
    pub gen: u64,
    pub stack: Vec<SFrame>,
}

pub const DSTOP: u32 = 0xFFFF_FFFF;

pub open spec fn dn_ok(ents: Seq<Ent>, t: u32, d: u32) -> bool {
    d == DSTOP || (t != MUNK && t != MNO && t < ents.len() && ents[t as int].cut == NOCUT && d as int / 4
        == ents[t as int].next && (d as int % 2 == 1) == ents[t as int].idle)
}

/// The kind of byte `b` as a next byte.
pub open spec fn lab(b: u8) -> int {
    if is_word(b) {
        0
    } else if b == 0x0A {
        1
    } else {
        2
    }
}

pub open spec fn tidx(sid: int, la: int, b: int) -> int {
    (sid * 4 + la) * 128 + b
}

pub open spec fn apcs(a: Seq<SA>) -> Seq<int> {
    Seq::new(a.len(), |k: int| a[k].pc)
}

/// The stored step `e` is the step from list `sid` over byte `b` before
/// a byte of kind `la`.
pub open spec fn ent_ok(p: Seq<SInst>, st: int, states: Seq<MState>, sid: int, la: int, b: u8, e: Ent) -> bool {
    let f = sfull(p, st, b, la, pcsv(states[sid].pcs@), states[sid].matched);
    &&& avs(e.acts@) == f.0
    &&& cutv(e.cut) == f.1
    &&& e.next < states.len()
    &&& pcsv(states[e.next as int].pcs@) == apcs(f.0)
    &&& states[e.next as int].matched == (states[sid].matched || f.1 is Some)
}

pub open spec fn slot_ok(p: Seq<SInst>, st: int, states: Seq<MState>, ents: Seq<Ent>, sid: int, la: int, b: int, v: u32) -> bool {
    v == MUNK || v == MNO || (v < ents.len() && ent_ok(p, st, states, sid, la, b as u8, ents[v as int]))
}

impl Memo {
    pub open spec fn wf(&self, prog: &Prog) -> bool {
        &&& self.mark@.len() == prog.insts@.len()
        &&& forall|k: int| 0 <= k < self.mark@.len() ==> #[trigger] self.mark@[k] <= self.gen
        &&& self.stack@.len() == 0
        &&& (self.on ==> prog.nslots <= 64)
        &&& self.states@.len() <= MEMO_STATES
        &&& self.trans@.len() == self.states@.len() * 512
        &&& self.dn@.len() == self.trans@.len()
        &&& forall|i: int| 0 <= i < self.dn@.len() ==> dn_ok(self.ents@, self.trans@[i], #[trigger] self.dn@[i])
        &&& self.lat@.len() == 256
        &&& forall|b: int| 0 <= b < 256 ==> (#[trigger] self.lat@[b]) as int == lab(b as u8)
        &&& forall|sid: int| 0 <= sid < self.states@.len() ==> (#[trigger] self.states@[sid]).pcs@.len() <= prog.insts@.len()
        &&& forall|i: int| 0 <= i < self.ents@.len() ==> us_ok((#[trigger] self.ents@[i]).acts@, self.ents@[i].us)
        &&& forall|i: int| 0 <= i < self.ents@.len() ==> zb_ok((#[trigger] self.ents@[i]).acts@, self.ents@[i].zb)
        &&& self.un@.len() == self.trans@.len()
        &&& forall|i: int| 0 <= i < self.un@.len() ==> un_ok(self.ents@, self.trans@[i], #[trigger] self.un@[i])
        &&& forall|sid: int, la: int, b: int|
            0 <= sid < self.states@.len() && 0 <= la < 4 && 0 <= b < 128 ==> slot_ok(
                prog.sp(),
                prog.start as int,
                self.states@,
                self.ents@,
                sid,
                la,
                b,
                #[trigger] self.trans@[tidx(sid, la, b)],
            )
    }

    pub fn new(prog: &Prog) -> (r: Memo)
        requires
            prog.wf(),
        ensures
            r.wf(prog),
    {
        let n = prog.insts.len();
        let mut mark: Vec<u64> = Vec::new();
        let mut k = 0;
        while k < n
            invariant
                k <= n,
                mark@.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] mark@[j] == 0,
            decreases n - k,
        {
            mark.push(0);
            k += 1;
        }
        let mut lat: Vec<u8> = Vec::new();
        let mut b: usize = 0;
        while b < 256
            invariant
                b <= 256,
                lat@.len() == b,
                forall|j: int| 0 <= j < b ==> (#[trigger] lat@[j]) as int == lab(j as u8),
            decreases 256 - b,
        {
            let x = b as u8;
            lat.push(if word_byte(x) {
                0
            } else if x == 0x0A {
                1
            } else {
                2
            });
            b += 1;
        }
        Memo {
            on: prog.nslots <= 64,
            states: Vec::new(),
            trans: Vec::new(),
            dn: Vec::new(),
            un: Vec::new(),
            lat: lat,
            credit: 8,
            tick: 0,
            ents: Vec::new(),
            nacts: 0,
            mark: mark,
            gen: 0,
            stack: Vec::new(),
        }
    }
}

/// Whether two lists of instructions are equal. Gives false if it runs
/// out of fuel.
fn eq_pcs(a: &Vec<u32>, b: &Vec<u32>, fuel: &mut u64, it: &mut Ghost<int>) -> (r: bool)
    ensures
        r ==> a@ == b@,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut k = 0;
    while k < n
        invariant
            n == a@.len(),
            n == b@.len(),
            k <= n,
            forall|j: int| 0 <= j < k ==> a@[j] == b@[j],
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
        decreases n - k,
    {
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        if a[k] != b[k] {
            return false;
        }
        k += 1;
    }
    assert(a@ =~= b@);
    true
}

/// The list with instructions `pcs` and match flag `matched`, if the
/// table knows it; otherwise the number of lists.
fn find_state(states: &Vec<MState>, pcs: &Vec<u32>, matched: bool, fuel: &mut u64, it: &mut Ghost<int>) -> (r: usize)
    ensures
        r <= states@.len(),
        r < states@.len() ==> states@[r as int].pcs@ == pcs@ && states@[r as int].matched == matched,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
{
    let n = states.len();
    let mut k = 0;
    while k < n
        invariant
            n == states@.len(),
            k <= n,
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
        decreases n - k,
    {
        if *fuel == 0 {
            return n;
        }
        *fuel -= 1;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        if states[k].matched == matched && eq_pcs(&states[k].pcs, pcs, fuel, it) {
            return k;
        }
        k += 1;
    }
    n
}

pub open spec fn unks(k: nat) -> Seq<u32> {
    Seq::new(k, |j: int| MUNK)
}

/// Adds a list to the table, with no step known. Gives its number, or
/// `MNO` if the table is full or the fuel runs out.
fn add_state(prog: &Prog, memo: &mut Memo, pcs: Vec<u32>, matched: bool, fuel: &mut u64, it: &mut Ghost<int>) -> (r: u32)
    requires
        prog.wf(),
        old(memo).wf(prog),
        pcs@.len() <= prog.insts@.len(),
    ensures
        final(memo).wf(prog),
        final(memo).on == old(memo).on,
        final(memo).ents == old(memo).ents,
        final(memo).nacts == old(memo).nacts,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
        r == MNO ==> final(memo).states == old(memo).states,
        r != MNO ==> r == old(memo).states@.len() && final(memo).states@ == old(memo).states@.push(
            MState { pcs: pcs, matched: matched },
        ),
{
    if memo.states.len() >= MEMO_STATES || *fuel < 512 {
        return MNO;
    }
    *fuel -= 512;
    proof {
        *it.borrow_mut() = it@ + 512;
    }
    let ghost s0 = memo.states@;
    let ghost t0 = memo.trans@;
    let ghost d0 = memo.dn@;
    let ghost u0 = memo.un@;
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let id = memo.states.len();
    memo.states.push(MState { pcs: pcs, matched: matched });
    let mut k: usize = 0;
    assert(memo.trans@ =~= t0 + unks(0));
    while k < 512
        invariant
            k <= 512,
            memo.trans@ == t0 + unks(k as nat),
            memo.dn@.len() == d0.len() + k,
            forall|i: int| 0 <= i < d0.len() ==> #[trigger] memo.dn@[i] == d0[i],
            forall|i: int| d0.len() <= i < d0.len() + k ==> #[trigger] memo.dn@[i] == DSTOP,
            memo.un@.len() == u0.len() + k,
            forall|i: int| 0 <= i < u0.len() ==> #[trigger] memo.un@[i] == u0[i],
            forall|i: int| u0.len() <= i < u0.len() + k ==> !(#[trigger] memo.un@[i]).ok && memo.un@[i].us == 0,
            memo.lat == old(memo).lat,
            memo.states@ == s0.push(MState { pcs: pcs, matched: matched }),
            memo.ents == old(memo).ents,
            memo.on == old(memo).on,
            memo.nacts == old(memo).nacts,
            memo.mark == old(memo).mark,
            memo.gen == old(memo).gen,
            memo.stack == old(memo).stack,
        decreases 512 - k,
    {
        let ghost tk = memo.trans@;
        memo.trans.push(MUNK);
        memo.dn.push(DSTOP);
        memo.un.push(Un { zb: 0, cut: NOCUT, next: 0, us: 0, ok: false });
        assert(memo.trans@ == tk.push(MUNK));
        assert(unks((k + 1) as nat) =~= unks(k as nat).push(MUNK));
        assert(memo.trans@ =~= t0 + unks((k + 1) as nat));
        k += 1;
    }
    proof {
        let s1 = memo.states@;
        assert forall|i: int| 0 <= i < memo.un@.len() implies un_ok(memo.ents@, memo.trans@[i], #[trigger] memo.un@[i]) by {
            if i < u0.len() {
                assert(memo.un@[i] == u0[i]);
                assert(memo.trans@[i] == t0[i]);
                assert(un_ok(memo.ents@, t0[i], u0[i]));
            }
        }
        assert forall|i: int| 0 <= i < memo.dn@.len() implies dn_ok(memo.ents@, memo.trans@[i], #[trigger] memo.dn@[i]) by {
            if i < d0.len() {
                assert(memo.dn@[i] == d0[i]);
                assert(memo.trans@[i] == t0[i]);
                assert(dn_ok(memo.ents@, t0[i], d0[i]));
            }
        }
        assert forall|sid: int, la: int, b: int| 0 <= sid < s1.len() && 0 <= la < 4 && 0 <= b < 128 implies slot_ok(
            sp,
            st,
            s1,
            memo.ents@,
            sid,
            la,
            b,
            #[trigger] memo.trans@[tidx(sid, la, b)],
        ) by {
            let v = memo.trans@[tidx(sid, la, b)];
            if sid < s0.len() {
                assert(v == t0[tidx(sid, la, b)]);
                assert(slot_ok(sp, st, s0, memo.ents@, sid, la, b, v));
                if v != MUNK && v != MNO {
                    let e = memo.ents@[v as int];
                    assert(ent_ok(sp, st, s0, sid, la, b as u8, e));
                    assert(s1[sid] == s0[sid]);
                    assert(s1[e.next as int] == s0[e.next as int]);
                }
            }
        }
        assert forall|sid: int| 0 <= sid < s1.len() implies (#[trigger] s1[sid]).pcs@.len() <= prog.insts@.len() by {
            if sid < s0.len() {
                assert(s1[sid] == s0[sid]);
            }
        }
    }
    id as u32
}

/// The table's number for a list, adding it if need be, or `MNO`.
fn intern(prog: &Prog, memo: &mut Memo, pcs: Vec<u32>, matched: bool, fuel: &mut u64, it: &mut Ghost<int>) -> (r: u32)
    requires
        prog.wf(),
        old(memo).wf(prog),
        pcs@.len() <= prog.insts@.len(),
    ensures
        final(memo).wf(prog),
        final(memo).on == old(memo).on,
        final(memo).ents == old(memo).ents,
        final(memo).nacts == old(memo).nacts,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
        final(memo).states@.len() >= old(memo).states@.len(),
        forall|k: int| 0 <= k < old(memo).states@.len() ==> final(memo).states@[k] == old(memo).states@[k],
        r != MNO ==> r < final(memo).states@.len(),
        r != MNO ==> final(memo).states@[r as int].pcs@ == pcs@,
        r != MNO ==> final(memo).states@[r as int].matched == matched,
{
    let f = find_state(&memo.states, &pcs, matched, fuel, it);
    if f < memo.states.len() {
        return f as u32;
    }
    add_state(prog, memo, pcs, matched, fuel, it)
}

/// Records what the table holds for one list, kind of next byte and byte.
fn set_trans(prog: &Prog, memo: &mut Memo, sid: usize, la: u8, b: u8, v: u32)
    requires
        prog.wf(),
        old(memo).wf(prog),
        sid < old(memo).states@.len(),
        la < 4,
        b < 128,
        slot_ok(prog.sp(), prog.start as int, old(memo).states@, old(memo).ents@, sid as int, la as int, b as int, v),
    ensures
        final(memo).wf(prog),
        final(memo).on == old(memo).on,
        final(memo).states == old(memo).states,
        final(memo).ents == old(memo).ents,
        final(memo).nacts == old(memo).nacts,
        final(memo).trans@[tidx(sid as int, la as int, b as int)] == v,
{
    let ghost t0 = memo.trans@;
    let i = (sid * 4 + la as usize) * 128 + b as usize;
    assert(i == tidx(sid as int, la as int, b as int));
    memo.trans.set(i, v);
    let ghost d0 = memo.dn@;
    let d = if v != MUNK && v != MNO {
        assert(ent_ok(prog.sp(), prog.start as int, memo.states@, sid as int, la as int, b, memo.ents@[v as int]));
        let cut = memo.ents[v as usize].cut;
        let next = memo.ents[v as usize].next;
        let idle = memo.ents[v as usize].idle;
        if cut == NOCUT {
            let empty = memo.states[next as usize].pcs.len() == 0;
            4 * next + if empty {
                2
            } else {
                0
            } + if idle {
                1
            } else {
                0
            }
        } else {
            DSTOP
        }
    } else {
        DSTOP
    };
    memo.dn.set(i, d);
    let ghost u0 = memo.un@;
    let mut u = Un { zb: 0, cut: NOCUT, next: 0, us: 0, ok: false };
    if v != MUNK && v != MNO {
        let e = &memo.ents[v as usize];
        if !e.idle && e.next < 0x1_0000 {
            if e.acts.len() == 0 {
                u = Un { zb: e.zb, cut: e.cut, next: e.next as u16, us: 64, ok: false };
            } else if e.us < 64 {
                u = Un { zb: e.zb, cut: e.cut, next: e.next as u16, us: e.us as u8, ok: true };
            }
        }
    }
    memo.un.set(i, u);
    proof {
        assert forall|j: int| 0 <= j < memo.un@.len() implies un_ok(memo.ents@, memo.trans@[j], #[trigger] memo.un@[j]) by {
            if j != i {
                assert(memo.un@[j] == u0[j]);
                assert(memo.trans@[j] == t0[j]);
                assert(un_ok(memo.ents@, t0[j], u0[j]));
            }
        }
        assert forall|j: int| 0 <= j < memo.dn@.len() implies dn_ok(memo.ents@, memo.trans@[j], #[trigger] memo.dn@[j]) by {
            if j != i {
                assert(memo.dn@[j] == d0[j]);
                assert(memo.trans@[j] == t0[j]);
                assert(dn_ok(memo.ents@, t0[j], d0[j]));
            }
        }
        assert forall|s2: int, l2: int, b2: int|
            0 <= s2 < memo.states@.len() && 0 <= l2 < 4 && 0 <= b2 < 128 implies slot_ok(
            prog.sp(),
            prog.start as int,
            memo.states@,
            memo.ents@,
            s2,
            l2,
            b2,
            #[trigger] memo.trans@[tidx(s2, l2, b2)],
        ) by {
            if tidx(s2, l2, b2) != i {
                assert(memo.trans@[tidx(s2, l2, b2)] == t0[tidx(s2, l2, b2)]);
            } else {
                assert(s2 == sid && l2 == la && b2 == b);
            }
        }
    }
}

/// The instructions of the threads `acts`, and whether every one of
/// them belongs to a match starting at the new position. Gives false if
/// it runs out of fuel.
fn act_pcs(acts: &Vec<Act>, fuel: &mut u64, it: &mut Ghost<int>) -> (r: (bool, Vec<u32>, bool, u32, u64))
    ensures
        r.0 ==> pcsv(r.1@) == apcs(avs(acts@)),
        r.0 ==> us_ok(acts@, r.3),
        r.0 ==> zb_ok(acts@, r.4),
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
{
    let n = acts.len();
    let mut v: Vec<u32> = Vec::new();
    let mut fresh = true;
    let mut us: u32 = NOSRC;
    let mut zb: u64 = 0;
    proof {
        assert forall|j: int| !mbit(0, j) by {
            lemma_mbit0(j);
        }
    }
    let mut k = 0;
    while k < n
        invariant
            n == acts@.len(),
            k <= n,
            v@.len() == k,
            forall|j: int| #[trigger] mbit(zb, j) ==> j < k && acts@[j].src != NOSRC && acts@[j].mask == 0,
            us == UMIX || forall|j: int| 0 <= j < k ==> (#[trigger] acts@[j]).src == NOSRC || acts@[j].src == us,
            forall|j: int| 0 <= j < k ==> v@[j] == acts@[j].pc,
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
        decreases n - k,
    {
        if *fuel == 0 {
            return (false, v, false, UMIX, 0);
        }
        *fuel -= 1;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        v.push(acts[k].pc);
        let src = acts[k].src;
        if src != NOSRC {
            fresh = false;
            if us == NOSRC {
                us = src;
            } else if us != src {
                us = UMIX;
            }
            if k < 64 && acts[k].mask == 0 {
                let ghost z0 = zb;
                zb = zb | (1u64 << (k as u64));
                proof {
                    assert(zb == setb(z0, k as int));
                    assert forall|j: int| #[trigger] mbit(zb, j) implies j < k + 1 && acts@[j].src != NOSRC && acts@[j].mask
                        == 0 by {
                        lemma_setb(z0, k as int, j);
                    }
                }
            }
        }
        k += 1;
    }
    assert(pcsv(v@) =~= apcs(avs(acts@)));
    (true, v, fresh, us, zb)
}

/// Appends a stored step to the table.
fn add_ent(prog: &Prog, memo: &mut Memo, e: Ent) -> (r: u32)
    requires
        prog.wf(),
        old(memo).wf(prog),
        us_ok(e.acts@, e.us),
        zb_ok(e.acts@, e.zb),
    ensures
        final(memo).wf(prog),
        final(memo).on == old(memo).on,
        final(memo).states == old(memo).states,
        r == MNO ==> final(memo).ents == old(memo).ents,
        r != MNO ==> r == old(memo).ents@.len() && final(memo).ents@ == old(memo).ents@.push(e),
        r != MUNK,
{
    if memo.ents.len() >= 0x4000_0000 || memo.nacts > MEMO_ACTS || e.acts.len() > MEMO_ACTS {
        return MNO;
    }
    let ghost e0 = memo.ents@;
    let id = memo.ents.len();
    memo.nacts = memo.nacts + e.acts.len();
    memo.ents.push(e);
    proof {
        assert forall|i: int| 0 <= i < memo.ents@.len() implies us_ok(
            (#[trigger] memo.ents@[i]).acts@,
            memo.ents@[i].us,
        ) by {
            if i < e0.len() {
                assert(memo.ents@[i] == e0[i]);
            }
        }
        assert forall|i: int| 0 <= i < memo.ents@.len() implies zb_ok(
            (#[trigger] memo.ents@[i]).acts@,
            memo.ents@[i].zb,
        ) by {
            if i < e0.len() {
                assert(memo.ents@[i] == e0[i]);
            }
        }
        assert forall|i: int| 0 <= i < memo.un@.len() implies un_ok(memo.ents@, memo.trans@[i], #[trigger] memo.un@[i]) by {
            assert(un_ok(e0, memo.trans@[i], memo.un@[i]));
            if memo.un@[i].ok {
                assert(memo.ents@[memo.trans@[i] as int] == e0[memo.trans@[i] as int]);
            }
        }
        assert forall|i: int| 0 <= i < memo.dn@.len() implies dn_ok(memo.ents@, memo.trans@[i], #[trigger] memo.dn@[i]) by {
            assert(dn_ok(e0, memo.trans@[i], memo.dn@[i]));
            if memo.dn@[i] != DSTOP {
                assert(memo.ents@[memo.trans@[i] as int] == e0[memo.trans@[i] as int]);
            }
        }
        assert forall|sid: int, la: int, b: int|
            0 <= sid < memo.states@.len() && 0 <= la < 4 && 0 <= b < 128 implies slot_ok(
            prog.sp(),
            prog.start as int,
            memo.states@,
            memo.ents@,
            sid,
            la,
            b,
            #[trigger] memo.trans@[tidx(sid, la, b)],
        ) by {
            let v = memo.trans@[tidx(sid, la, b)];
            assert(slot_ok(prog.sp(), prog.start as int, memo.states@, e0, sid, la, b, v));
            if v != MUNK && v != MNO {
                assert(memo.ents@[v as int] == e0[v as int]);
            }
        }
    }
    id as u32
}

/// Computes and stores the step from list `sid` over byte `b` before a
/// byte of kind `la`. Gives its number, or `MNO` if the table cannot
/// hold it or the fuel runs out.
fn build_ent(prog: &Prog, memo: &mut Memo, sid: usize, la: u8, b: u8, fuel: &mut u64, it: &mut Ghost<int>) -> (r: u32)
    requires
        prog.wf(),
        old(memo).wf(prog),
        old(memo).on,
        sid < old(memo).states@.len(),
        la < 4,
        b < 128,
    ensures
        final(memo).wf(prog),
        final(memo).on == old(memo).on,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
        final(memo).states@.len() >= old(memo).states@.len(),
        forall|k: int| 0 <= k < old(memo).states@.len() ==> final(memo).states@[k] == old(memo).states@[k],
        slot_ok(prog.sp(), prog.start as int, final(memo).states@, final(memo).ents@, sid as int, la as int, b as int, r),
        r != MUNK,
{
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost s0 = memo.states@;
    let np = prog.insts.len();
    if *fuel < np as u64 {
        return MNO;
    }
    *fuel -= np as u64;
    let (g, bc) = bump(&mut memo.mark, memo.gen);
    proof {
        *it.borrow_mut() = it@ + bc@;
    }
    memo.gen = g;
    let matched = memo.states[sid].matched;
    let mut acts: Vec<Act> = Vec::new();
    let ghost pcs0 = memo.states@[sid as int].pcs@;
    let (ok, cut) = sbuild(
        prog,
        &memo.states[sid].pcs,
        matched,
        b,
        la,
        &mut memo.mark,
        g,
        &mut memo.stack,
        &mut acts,
        fuel,
        it,
    );
    if !ok || acts.len() > np {
        return MNO;
    }
    let ghost f = sfull(sp, st, b, la as int, pcsv(pcs0), matched);
    let (ok2, npcs, fresh, us, zb) = act_pcs(&acts, fuel, it);
    if !ok2 {
        return MNO;
    }
    let m2 = matched || cut != NOCUT;
    assert(pcsv(npcs@).len() == apcs(avs(acts@)).len());
    let next = intern(prog, memo, npcs, m2, fuel, it);
    if next == MNO {
        return MNO;
    }
    let e = Ent { acts: acts, cut: cut, next: next, idle: fresh && !m2, us: us, zb: zb };
    let r = add_ent(prog, memo, e);
    proof {
        if r != MNO {
            assert(memo.states@[sid as int] == s0[sid as int]);
            assert(ent_ok(sp, st, memo.states@, sid as int, la as int, b, e));
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Threads that share slot rows
// ---------------------------------------------------------------------------

/// A thread whose slots are not written out: they are those of row `row`
/// of an arena of rows (`NOROW`: all unset), with the slots in `mask`
/// set to `pos`.
#[derive(Clone, Copy)]
pub struct Th {
    pub row: u32,
    pub mask: u64,
    pub pos: usize,
}

pub const NOROW: u32 = 0xFFFF_FFFF;

pub open spec fn rowv(ar: Seq<usize>, r: int, ns: nat) -> Seq<int> {
    Seq::new(ns, |j: int| cv(ar[idx(r, ns as int, j)]))
}

/// The slots of the thread `t`.
pub open spec fn thv(ar: Seq<usize>, t: Th, ns: nat) -> Seq<int> {
    icap(
        if t.row == NOROW {
            unset(ns)
        } else {
            rowv(ar, t.row as int, ns)
        },
        t.mask,
        t.pos as int,
    )
}

pub open spec fn th_ok(t: Th, nr: int) -> bool {
    (t.row == NOROW || t.row < nr) && t.pos < usize::MAX
}

pub open spec fn ths_ok(ts: Seq<Th>, nr: int) -> bool {
    forall|k: int| 0 <= k < ts.len() ==> th_ok(#[trigger] ts[k], nr)
}

/// The thread list: instructions `pcs`, slots from `ts`.
pub open spec fn thl(ar: Seq<usize>, ts: Seq<Th>, pcs: Seq<u32>, ns: nat) -> Seq<T> {
    Seq::new(ts.len(), |k: int| T { pc: pcs[k] as int, caps: thv(ar, ts[k], ns) })
}

/// Appending to the arena changes no thread.
pub proof fn lemma_thv_frame(ar: Seq<usize>, ar2: Seq<usize>, t: Th, nr: int, ns: nat)
    requires
        th_ok(t, nr),
        forall|i: int| 0 <= i < nr * ns ==> ar2[i] == ar[i],
    ensures
        thv(ar2, t, ns) == thv(ar, t, ns),
{
    if t.row != NOROW {
        let r = t.row as int;
        assert forall|j: int| 0 <= j < ns implies rowv(ar2, r, ns)[j] == rowv(ar, r, ns)[j] by {
            lemma_idx(r, nr, ns as int, j);
        }
        assert(rowv(ar2, r, ns) =~= rowv(ar, r, ns));
    }
}

/// Slot `j` of the thread `t`.
fn slot_of(ar: &Vec<usize>, t: Th, j: usize, ns: usize, Ghost(nr): Ghost<int>) -> (x: usize)
    requires
        th_ok(t, nr),
        nr * ns <= ar@.len(),
        j < ns <= 64,
    ensures
        cv(x) == thv(ar@, t, ns as nat)[j as int],
{
    proof {
        assert(mbit(t.mask, j as int) == ((t.mask >> (j as u64)) & 1u64 == 1u64));
    }
    if (t.mask >> (j as u64)) & 1u64 == 1u64 {
        t.pos
    } else if t.row == NOROW {
        NONE
    } else {
        let cl = ar.len();
        proof {
            lemma_idx(t.row as int, nr, ns as int, j as int);
            assert(idx(t.row as int, ns as int, j as int) == t.row as int * ns as int + j);
            assert(t.row as int * ns as int + j < cl);
        }
        ar[t.row as usize * ns + j]
    }
}

/// Writes the slots of `t` out as a new row of the arena.
fn mat_row(ar: &mut Vec<usize>, t: Th, ns: usize, Ghost(nr): Ghost<int>) -> (cost: Ghost<int>)
    requires
        old(ar)@.len() == nr * ns,
        th_ok(t, nr),
        ns <= 64,
        0 <= nr,
    ensures
        final(ar)@.len() == (nr + 1) * ns,
        forall|i: int| 0 <= i < nr * ns ==> final(ar)@[i] == old(ar)@[i],
        rowv(final(ar)@, nr, ns as nat) == thv(old(ar)@, t, ns as nat),
        cost@ == ns,
{
    let ghost mut cnt: int = 0;
    let ghost a0 = ar@;
    let ghost want = thv(a0, t, ns as nat);
    let ghost l0 = ar@.len() as int;
    let mut j: usize = 0;
    while j < ns
        invariant
            j <= ns <= 64,
            th_ok(t, nr),
            l0 == nr * ns,
            a0.len() == l0,
            want == thv(a0, t, ns as nat),
            ar@.len() == l0 + j,
            forall|i: int| 0 <= i < l0 ==> ar@[i] == a0[i],
            forall|q: int| 0 <= q < j ==> cv(#[trigger] ar@[l0 + q]) == want[q],
            cnt == j,
        decreases ns - j,
    {
        proof {
            cnt = cnt + 1;
            lemma_thv_frame(a0, ar@, t, nr, ns as nat);
        }
        let x = slot_of(ar, t, j, ns, Ghost(nr));
        ar.push(x);
        j += 1;
    }
    proof {
        assert((nr + 1) * ns == nr * ns + ns) by (nonlinear_arith);
        assert forall|q: int| 0 <= q < ns implies rowv(ar@, nr, ns as nat)[q] == want[q] by {
            assert(idx(nr, ns as int, q) == l0 + q);
        }
        assert(rowv(ar@, nr, ns as nat) =~= want);
    }
    Ghost(cnt)
}

/// Replays a stored step on threads that share rows: `tb` becomes the
/// threads the step describes. A thread gets a row of its own only when
/// it lives on with slots pending. Gives the number of rows after.
fn apply_t(
    acts: &Vec<Act>,
    ta: &mut Vec<Th>,
    tb: &mut Vec<Th>,
    ar: &mut Vec<usize>,
    nrows: usize,
    pos: usize,
    ns: usize,
) -> (r: (usize, Ghost<int>))
    requires
        ns <= 64,
        pos < usize::MAX,
        old(ar)@.len() == nrows * ns,
        ths_ok(old(ta)@, nrows as int),
        srcs_ok(avs(acts@), old(ta)@.len() as int),
        nrows + acts@.len() < 0xFFFF_FFFF,
    ensures
        nrows <= r.0 <= nrows + acts@.len(),
        final(ar)@.len() == r.0 * ns,
        0 <= r.1@ <= acts@.len() + (r.0 - nrows) * ns,
        forall|i: int| 0 <= i < nrows * ns ==> final(ar)@[i] == old(ar)@[i],
        final(ta)@.len() == old(ta)@.len(),
        ths_ok(final(ta)@, r.0 as int),
        ths_ok(final(tb)@, r.0 as int),
        final(tb)@.len() == acts@.len(),
        forall|k: int|
            0 <= k < old(ta)@.len() ==> thv(final(ar)@, #[trigger] final(ta)@[k], ns as nat) == thv(
                old(ar)@,
                old(ta)@[k],
                ns as nat,
            ),
        forall|k: int|
            0 <= k < acts@.len() ==> thv(final(ar)@, #[trigger] final(tb)@[k], ns as nat) == icap(
                if acts@[k].src == NOSRC {
                    unset(ns as nat)
                } else {
                    thv(old(ar)@, old(ta)@[acts@[k].src as int], ns as nat)
                },
                acts@[k].mask,
                pos as int,
            ),
{
    let ghost a0 = ar@;
    let ghost ta0 = ta@;
    let ghost nsn = ns as nat;
    let n = acts.len();
    tb.clear();
    let mut nr = nrows;
    let ghost mut cnt: int = 0;
    proof {
        assert(0 * ns == 0) by (nonlinear_arith);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            n == acts@.len(),
            k <= n,
            ns <= 64,
            nsn == ns,
            pos < usize::MAX,
            nrows <= nr <= nrows + k,
            cnt == k + (nr - nrows) * ns,
            nrows + n < 0xFFFF_FFFF,
            a0.len() == nrows * ns,
            ar@.len() == nr * ns,
            forall|i: int| 0 <= i < nrows * ns ==> ar@[i] == a0[i],
            ta@.len() == ta0.len(),
            srcs_ok(avs(acts@), ta0.len() as int),
            ths_ok(ta0, nrows as int),
            ths_ok(ta@, nr as int),
            ths_ok(tb@, nr as int),
            tb@.len() == k,
            forall|kk: int| 0 <= kk < ta0.len() ==> thv(ar@, #[trigger] ta@[kk], nsn) == thv(a0, ta0[kk], nsn),
            forall|kk: int|
                0 <= kk < k ==> thv(ar@, #[trigger] tb@[kk], nsn) == icap(
                    if acts@[kk].src == NOSRC {
                        unset(nsn)
                    } else {
                        thv(a0, ta0[acts@[kk].src as int], nsn)
                    },
                    acts@[kk].mask,
                    pos as int,
                ),
        decreases n - k,
    {
        let act = acts[k];
        proof {
            assert(avs(acts@)[k as int] == av(act));
            assert(-1 <= avs(acts@)[k as int].src < ta0.len());
        }
        let ghost ar1 = ar@;
        let ghost ta1 = ta@;
        let ghost tb1 = tb@;
        let ghost nr1 = nr as int;
        let nt = if act.src == NOSRC {
            Th { row: NOROW, mask: act.mask, pos: pos }
        } else {
            let t = ta[act.src as usize];
            assert(th_ok(t, nr1));
            assert(thv(ar1, t, nsn) == thv(a0, ta0[act.src as int], nsn));
            if t.mask == 0 {
                proof {
                    if t.row == NOROW {
                        lemma_icap0(unset(nsn), t.pos as int);
                    } else {
                        lemma_icap0(rowv(ar1, t.row as int, nsn), t.pos as int);
                    }
                }
                Th { row: t.row, mask: act.mask, pos: pos }
            } else {
                // A thread with pending slots that lives on gets a row of
                // its own, once: every thread made from it shares the row.
                let mc = mat_row(ar, t, ns, Ghost(nr1));
                proof {
                    assert((nr1 + 1 - nrows) * ns == (nr1 - nrows) * ns + ns) by (nonlinear_arith);
                    cnt = cnt + mc@;
                }
                let t2 = Th { row: nr as u32, mask: 0, pos: 0 };
                ta.set(act.src as usize, t2);
                nr += 1;
                proof {
                    lemma_icap0(rowv(ar@, nr1, nsn), 0);
                    assert(thv(ar@, t2, nsn) == thv(ar1, t, nsn));
                    assert(nrows as int * ns as int <= nr1 * ns as int) by (nonlinear_arith)
                        requires
                            nrows <= nr1,
                            ns >= 0,
                    ;
                    assert forall|kk: int| 0 <= kk < ta0.len() implies thv(ar@, #[trigger] ta@[kk], nsn) == thv(
                        a0,
                        ta0[kk],
                        nsn,
                    ) by {
                        if kk != act.src as int {
                            assert(ta@[kk] == ta1[kk]);
                            assert(th_ok(ta1[kk], nr1));
                            lemma_thv_frame(ar1, ar@, ta1[kk], nr1, nsn);
                        }
                    }
                    assert forall|kk: int| 0 <= kk < k implies thv(ar@, #[trigger] tb@[kk], nsn) == thv(
                        ar1,
                        tb1[kk],
                        nsn,
                    ) by {
                        assert(th_ok(tb1[kk], nr1));
                        lemma_thv_frame(ar1, ar@, tb1[kk], nr1, nsn);
                    }
                    assert forall|kk: int| 0 <= kk < ta@.len() implies th_ok(#[trigger] ta@[kk], nr as int) by {
                        if kk != act.src as int {
                            assert(th_ok(ta1[kk], nr1));
                        }
                    }
                    assert forall|kk: int| 0 <= kk < tb@.len() implies th_ok(#[trigger] tb@[kk], nr as int) by {
                        assert(th_ok(tb1[kk], nr1));
                    }
                }
                Th { row: t2.row, mask: act.mask, pos: pos }
            }
        };
        let ghost tb2 = tb@;
        tb.push(nt);
        proof {
            assert forall|kk: int| 0 <= kk < tb@.len() implies th_ok(#[trigger] tb@[kk], nr as int) by {
                if kk < k {
                    assert(tb@[kk] == tb2[kk]);
                }
            }
            assert forall|kk: int| 0 <= kk < k + 1 implies thv(ar@, #[trigger] tb@[kk], nsn) == icap(
                if acts@[kk].src == NOSRC {
                    unset(nsn)
                } else {
                    thv(a0, ta0[acts@[kk].src as int], nsn)
                },
                acts@[kk].mask,
                pos as int,
            ) by {
                if kk < k {
                    assert(tb@[kk] == tb2[kk]);
                }
            }
        }
        k += 1;
        proof {
            cnt = cnt + 1;
        }
    }
    (nr, Ghost(cnt))
}

/// Writes the threads out as an ordinary list.
fn finish(ts: &Vec<Th>, ar: &Vec<usize>, pcs: &Vec<u32>, b: &mut List, ns: usize, Ghost(nr): Ghost<int>) -> (cost: Ghost<
    int,
>)
    requires
        ts@.len() == pcs@.len(),
        nr * ns <= ar@.len(),
        ths_ok(ts@, nr),
        ns <= 64,
    ensures
        final(b).wf(ns as nat),
        final(b).pcs@ == pcs@,
        final(b).v(ns as nat) == thl(ar@, ts@, pcs@, ns as nat),
        cost@ == ts@.len() * (ns + 1),
{
    let ghost nsn = ns as nat;
    let ghost mut cnt: int = 0;
    proof {
        assert(0 * (ns + 1) == 0) by (nonlinear_arith);
    }
    b.clear(Ghost(nsn));
    let n = ts.len();
    let mut k: usize = 0;
    proof {
        assert(0 * ns == 0) by (nonlinear_arith);
        assert(b.pcs@.len() == b.v(nsn).len());
        assert(b.pcs@ =~= pcs@.subrange(0, 0));
    }
    while k < n
        invariant
            n == ts@.len(),
            n == pcs@.len(),
            k <= n,
            ns <= 64,
            nsn == ns,
            nr * ns <= ar@.len(),
            ths_ok(ts@, nr),
            b.pcs@ == pcs@.subrange(0, k as int),
            b.caps@.len() == k * ns,
            cnt == k * (ns + 1),
            forall|kk: int, j: int|
                0 <= kk < k && 0 <= j < ns ==> cv(#[trigger] b.caps@[idx(kk, ns as int, j)]) == thv(ar@, ts@[kk], nsn)[j],
        decreases n - k,
    {
        b.pcs.push(pcs[k]);
        let t = ts[k];
        let ghost c0 = b.caps@;
        let ghost l0 = c0.len() as int;
        let ghost cnt0 = cnt;
        let mut j: usize = 0;
        while j < ns
            invariant
                cnt == cnt0 + j,
                j <= ns <= 64,
                nsn == ns,
                nr * ns <= ar@.len(),
                th_ok(t, nr),
                l0 == k * ns,
                c0.len() == l0,
                b.pcs@ == pcs@.subrange(0, k as int).push(pcs@[k as int]),
                b.caps@.len() == l0 + j,
                forall|i: int| 0 <= i < l0 ==> b.caps@[i] == c0[i],
                forall|q: int| 0 <= q < j ==> cv(#[trigger] b.caps@[l0 + q]) == thv(ar@, t, nsn)[q],
            decreases ns - j,
        {
            let x = slot_of(ar, t, j, ns, Ghost(nr));
            b.caps.push(x);
            j += 1;
            proof {
                cnt = cnt + 1;
            }
        }
        proof {
            cnt = cnt + 1;
            assert((k + 1) * (ns + 1) == k * (ns + 1) + ns + 1) by (nonlinear_arith);
            assert((k + 1) * ns == k * ns + ns) by (nonlinear_arith);
            assert(pcs@.subrange(0, k + 1) =~= pcs@.subrange(0, k as int).push(pcs@[k as int]));
            assert forall|kk: int, j: int| 0 <= kk < k + 1 && 0 <= j < ns implies cv(
                #[trigger] b.caps@[idx(kk, ns as int, j)],
            ) == thv(ar@, ts@[kk], nsn)[j] by {
                if kk < k {
                    lemma_idx(kk, k as int, ns as int, j);
                    assert(b.caps@[idx(kk, ns as int, j)] == c0[idx(kk, ns as int, j)]);
                } else {
                    assert(idx(kk, ns as int, j) == l0 + j);
                }
            }
        }
        k += 1;
    }
    proof {
        assert(pcs@.subrange(0, n as int) =~= pcs@);
        let x = b.v(nsn);
        let y = thl(ar@, ts@, pcs@, nsn);
        assert(x.len() == y.len());
        assert forall|kk: int| 0 <= kk < x.len() implies x[kk] == y[kk] by {
            assert forall|q: int| 0 <= q < ns implies x[kk].caps[q] == y[kk].caps[q] by {
                assert(x[kk].caps[q] == cv(b.caps@[idx(kk, ns as int, q)]));
            }
            assert(x[kk].caps =~= y[kk].caps);
        }
        assert(x =~= y);
    }
    Ghost(cnt)
}

/// Copies the slots of the thread `t` to `out`. Takes `ns` iterations.
fn load_th(ar: &Vec<usize>, t: Th, out: &mut Vec<usize>, ns: usize, Ghost(nr): Ghost<int>)
    requires
        th_ok(t, nr),
        nr * ns <= ar@.len(),
        ns <= 64,
        old(out)@.len() == ns,
    ensures
        final(out)@.len() == ns,
        capv(final(out)@) == thv(ar@, t, ns as nat),
{
    let mut j: usize = 0;
    while j < ns
        invariant
            j <= ns <= 64,
            th_ok(t, nr),
            nr * ns <= ar@.len(),
            out@.len() == ns,
            forall|q: int| 0 <= q < j ==> cv(#[trigger] out@[q]) == thv(ar@, t, ns as nat)[q],
        decreases ns - j,
    {
        let x = slot_of(ar, t, j, ns, Ghost(nr));
        out.set(j, x);
        j += 1;
    }
    assert(capv(out@) =~= thv(ar@, t, ns as nat));
}

// ---------------------------------------------------------------------------
// Running on stored steps
// ---------------------------------------------------------------------------

/// Writes the threads of `useq` out as a list.
fn expand(acts: &Vec<Act>, ux: u32, upos: usize, ta: &mut Vec<Th>) -> (cost: Ghost<int>)
    ensures
        final(ta)@ == useq(acts@, ux, upos),
        cost@ == acts@.len(),
{
    ta.clear();
    let n = acts.len();
    let mut k: usize = 0;
    while k < n
        invariant
            n == acts@.len(),
            k <= n,
            ta@.len() == k,
            forall|j: int| 0 <= j < k ==> (#[trigger] ta@[j]) == useq(acts@, ux, upos)[j],
        decreases n - k,
    {
        let a = acts[k];
        ta.push(
            Th {
                row: if a.src == NOSRC {
                    NOROW
                } else {
                    ux
                },
                mask: a.mask,
                pos: upos,
            },
        );
        k += 1;
    }
    assert(ta@ =~= useq(acts@, ux, upos));
    Ghost(n as int)
}

/// Thread `j` of `useq`.
#[inline]
fn uth(acts: &Vec<Act>, j: usize, ux: u32, upos: usize) -> (r: Th)
    requires
        j < acts@.len(),
    ensures
        r == useq(acts@, ux, upos)[j as int],
{
    let a = acts[j];
    Th {
        row: if a.src == NOSRC {
            NOROW
        } else {
            ux
        },
        mask: a.mask,
        pos: upos,
    }
}

/// The row a thread's slots are in: its own if it has nothing pending,
/// else a new one. Gives the row, the number of rows, and the cost.
fn uni_row(ar: &mut Vec<usize>, t0: Th, nrows: usize, ns: usize) -> (r: (u32, usize, Ghost<int>))
    requires
        old(ar)@.len() == nrows * ns,
        th_ok(t0, nrows as int),
        ns <= 64,
        nrows < 0xFFFF_FFFE,
    ensures
        r.1 == nrows || r.1 == nrows + 1,
        final(ar)@.len() == r.1 * ns,
        forall|i: int| 0 <= i < nrows * ns ==> final(ar)@[i] == old(ar)@[i],
        r.0 == NOROW || r.0 < r.1,
        (if r.0 == NOROW {
            unset(ns as nat)
        } else {
            rowv(final(ar)@, r.0 as int, ns as nat)
        }) == thv(old(ar)@, t0, ns as nat),
        r.2@ == 0 || r.2@ == ns,
{
    if t0.mask == 0 {
        proof {
            if t0.row == NOROW {
                lemma_icap0(unset(ns as nat), t0.pos as int);
            } else {
                lemma_icap0(rowv(ar@, t0.row as int, ns as nat), t0.pos as int);
            }
        }
        (t0.row, nrows, Ghost(0))
    } else {
        let mr = mat_row(ar, t0, ns, Ghost(nrows as int));
        (nrows as u32, nrows + 1, mr)
    }
}

/// The threads of a step with one source, kept as that source's row.
proof fn lemma_uni(
    acts: Seq<Act>,
    us: u32,
    base: u32,
    ar0: Seq<usize>,
    ar1: Seq<usize>,
    tg0: Seq<Th>,
    nr1: int,
    ns: nat,
    pos: usize,
)
    requires
        us_ok(acts, us),
        us != UMIX,
        srcs_ok(avs(acts), tg0.len() as int),
        pos < usize::MAX,
        base == NOROW || base < nr1,
        (us != NOSRC && us < tg0.len()) ==> (if base == NOROW {
            unset(ns)
        } else {
            rowv(ar1, base as int, ns)
        }) == thv(ar0, tg0[us as int], ns),
    ensures
        forall|kk: int|
            0 <= kk < acts.len() ==> th_ok(#[trigger] useq(acts, base, pos)[kk], nr1) && thv(
                ar1,
                useq(acts, base, pos)[kk],
                ns,
            ) == icap(
                if acts[kk].src == NOSRC {
                    unset(ns)
                } else {
                    thv(ar0, tg0[acts[kk].src as int], ns)
                },
                acts[kk].mask,
                pos as int,
            ),
{
    assert forall|kk: int| 0 <= kk < acts.len() implies th_ok(#[trigger] useq(acts, base, pos)[kk], nr1) && thv(
        ar1,
        useq(acts, base, pos)[kk],
        ns,
    ) == icap(
        if acts[kk].src == NOSRC {
            unset(ns)
        } else {
            thv(ar0, tg0[acts[kk].src as int], ns)
        },
        acts[kk].mask,
        pos as int,
    ) by {
        assert(avs(acts)[kk] == av(acts[kk]));
        assert(-1 <= avs(acts)[kk].src < tg0.len());
        if acts[kk].src != NOSRC {
            assert(acts[kk].src == us);
        }
    }
}

/// The state of the run at byte `p` when the list is kept as one row:
/// list `sid`, its threads those of `useq` for step `ue` and row `ux`.
pub open spec fn uok(
    prog: &Prog,
    s: Seq<u8>,
    memo: &Memo,
    ar: Seq<usize>,
    sid: int,
    p: int,
    ux: u32,
    ue: int,
    nrows: int,
    matched: bool,
    mv: M,
    ans: Option<M>,
) -> bool {
    let nsn = prog.nslots as nat;
    &&& 0 <= sid < memo.states@.len()
    &&& 0 <= ue < memo.ents@.len()
    &&& 0 <= p <= s.len()
    &&& (ux == NOROW || ux < nrows)
    &&& ar.len() == nrows * nsn
    &&& memo.ents@[ue].acts@.len() == memo.states@[sid].pcs@.len()
    &&& memo.states@[sid].matched == matched
    &&& ans == or(
        fr(
            prog.sp(),
            s,
            thl(ar, useq(memo.ents@[ue].acts@, ux, p as usize), memo.states@[sid].pcs@, nsn),
            p,
        ),
        if matched {
            Some(mv)
        } else {
            search_p(prog.sp(), s, prog.start as int, p + 1, nsn)
        },
    )
}

/// Follows stored steps while the list stays one row: each step's
/// threads all come from one thread of the list that has that row and
/// nothing pending, so the next list is the same row under the step's
/// masks and nothing is written. Gives the list, the position, the last
/// step, and, if a match was passed, the thread of the latest one and
/// where it ends. One loop iteration per byte.
fn urun(
    prog: &Prog,
    s: &[u8],
    memo: &Memo,
    ar: &Vec<usize>,
    sid0: usize,
    p0: usize,
    ux: u32,
    ue0: usize,
    matched0: bool,
    Ghost(nrows): Ghost<int>,
    Ghost(mv0): Ghost<M>,
    Ghost(ans): Ghost<Option<M>>,
) -> (r: (usize, usize, usize, bool, Th, usize, Ghost<M>))
    requires
        prog.wf(),
        memo.wf(prog),
        memo.on,
        s@.len() < usize::MAX,
        uok(prog, s@, memo, ar@, sid0 as int, p0 as int, ux, ue0 as int, nrows, matched0, mv0, ans),
    ensures
        uok(prog, s@, memo, ar@, r.0 as int, r.1 as int, ux, r.2 as int, nrows, matched0 || r.3, r.6@, ans),
        p0 <= r.1,
        !r.3 ==> r.6@ == mv0,
        r.3 ==> r.6@.end == r.5 && th_ok(r.4, nrows) && r.6@.caps == thv(ar@, r.4, prog.nslots as nat),
{
    let n = s.len();
    let ghost nsn = prog.nslots as nat;
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let mut sid = sid0;
    let mut p = p0;
    let mut zb = memo.ents[ue0].zb;
    let mut uti: usize = usize::MAX;
    let ghost mut ue: int = ue0 as int;
    let mut mdef = false;
    let mut mti: usize = usize::MAX;
    let mut mcut: u32 = 0;
    let mut mend: usize = 0;
    let ghost mut me: int = 0;
    let ghost mut matched = matched0;
    let ghost mut mv = mv0;
    let mut end = false;
    proof {
        lemma_slots_ok(prog);
    }
    while p < n
        invariant
            prog.wf(),
            memo.wf(prog),
            memo.on,
            n == s@.len(),
            n < usize::MAX,
            nsn == prog.nslots,
            sp == prog.sp(),
            st == prog.start,
            slots_ok(sp, nsn as int),
            uok(prog, s@, memo, ar@, sid as int, p as int, ux, ue, nrows, matched, mv, ans),
            zb == memo.ents@[ue].zb,
            uti == usize::MAX ==> ue == ue0,
            uti != usize::MAX ==> uti < memo.trans@.len() && memo.trans@[uti as int] == ue,
            matched == (matched0 || mdef),
            !mdef ==> mv == mv0,
            mdef ==> mv.end == mend && mend < usize::MAX && 0 <= me < memo.ents@.len() && mcut < memo.ents@[me].acts@.len()
                && mv.caps == thv(ar@, useq(memo.ents@[me].acts@, ux, mend)[mcut as int], nsn) && (mti == usize::MAX
                ==> me == ue0) && (mti != usize::MAX ==> mti < memo.trans@.len() && memo.trans@[mti as int] == me),
            p0 <= p,
        decreases n - p,
    {
        let c = s[p];
        if c >= 0x80 {
            break;
        }
        let la = laq(&memo.lat, s, p + 1);
        let ti = (sid * 4 + la as usize) * 128 + c as usize;
        assert(ti == tidx(sid as int, la as int, c as int));
        let u = memo.un[ti];
        if !u.ok {
            end = u.us == 64;
            break;
        }
        assert(un_ok(memo.ents@, memo.trans@[ti as int], u));
        assert(mbit(zb, u.us as int) == ((zb >> (u.us as u64)) & 1u64 == 1u64));
        if (zb >> (u.us as u64)) & 1u64 != 1u64 {
            break;
        }
        let ghost t = memo.trans@[ti as int];
        let ghost e = memo.ents@[t as int];
        let ghost pcs0 = memo.states@[sid as int].pcs@;
        let ghost tg0 = useq(memo.ents@[ue].acts@, ux, p);
        let ghost al = thl(ar@, tg0, pcs0, nsn);
        let ghost f = sfull(sp, st, c, la as int, pcsv(pcs0), matched);
        let ghost nx = memo.states@[e.next as int];
        proof {
            assert(un_ok(memo.ents@, t, u));
            assert(slot_ok(sp, st, memo.states@, memo.ents@, sid as int, la as int, c as int, memo.trans@[tidx(
                sid as int,
                la as int,
                c as int,
            )]));
            assert(ent_ok(sp, st, memo.states@, sid as int, la as int, c, e));
            assert(us_ok(e.acts@, e.us));
            assert(zb_ok(memo.ents@[ue].acts@, zb));
            assert(pcs_of(al) =~= pcsv(pcs0));
            assert(caps_ok(al, nsn));
            lemma_sfull(sp, s@, st, nsn, p as int, al, matched);
            lemma_cfull(sp, s@, st, nsn, p as int, al, matched, mv, ans);
            lemma_sfull_src(sp, st, c, la as int, pcsv(pcs0), matched);
            assert(pcsv(nx.pcs@).len() == apcs(f.0).len());
            assert(e.acts@.len() == avs(e.acts@).len());
            assert(e.acts@.len() == nx.pcs@.len());
        }
        if u.cut != NOCUT {
            mdef = true;
            mti = uti;
            mcut = u.cut;
            mend = p;
            proof {
                matched = true;
                me = ue;
                mv = M { end: p as int, caps: al[u.cut as int].caps };
            }
        }
        proof {
            let t0 = tg0[u.us as int];
            assert(t0 == Th { row: ux, mask: 0, pos: p });
            if ux == NOROW {
                lemma_icap0(unset(nsn), p as int);
            } else {
                lemma_icap0(rowv(ar@, ux as int, nsn), p as int);
            }
            assert(srcs_ok(avs(e.acts@), tg0.len() as int));
            lemma_uni(e.acts@, e.us, ux, ar@, ar@, tg0, nrows, nsn, (p + 1) as usize);
            let tg2 = useq(e.acts@, ux, (p + 1) as usize);
            let l2 = thl(ar@, tg2, nx.pcs@, nsn);
            let want = isa(f.0, al, nsn, p + 1);
            assert(l2.len() == want.len());
            assert forall|kk: int| 0 <= kk < l2.len() implies l2[kk] == want[kk] by {
                assert(f.0[kk] == av(e.acts@[kk]));
                assert(pcsv(nx.pcs@)[kk] == apcs(f.0)[kk]);
                assert(th_ok(tg2[kk], nrows));
                if e.acts@[kk].src != NOSRC {
                    assert(al[e.acts@[kk].src as int].caps == thv(ar@, tg0[e.acts@[kk].src as int], nsn));
                }
            }
            assert(l2 =~= want);
            ue = t as int;
        }
        zb = u.zb;
        uti = ti;
        sid = u.next as usize;
        p += 1;
    }
    if end && p < n && s[p] < 0x80 {
        // One more step, which leaves no thread.
        let c = s[p];
        let la = laq(&memo.lat, s, p + 1);
        let ti = (sid * 4 + la as usize) * 128 + c as usize;
        assert(ti == tidx(sid as int, la as int, c as int));
        let u = memo.un[ti];
        if !u.ok && u.us == 64 {
            let ghost t = memo.trans@[ti as int];
            let ghost e = memo.ents@[t as int];
            let ghost pcs0 = memo.states@[sid as int].pcs@;
            let ghost tg0 = useq(memo.ents@[ue].acts@, ux, p);
            let ghost al = thl(ar@, tg0, pcs0, nsn);
            let ghost f = sfull(sp, st, c, la as int, pcsv(pcs0), matched);
            let ghost nx = memo.states@[e.next as int];
            proof {
                assert(un_ok(memo.ents@, t, u));
                assert(slot_ok(sp, st, memo.states@, memo.ents@, sid as int, la as int, c as int, memo.trans@[tidx(
                    sid as int,
                    la as int,
                    c as int,
                )]));
                assert(ent_ok(sp, st, memo.states@, sid as int, la as int, c, e));
                assert(pcs_of(al) =~= pcsv(pcs0));
                assert(caps_ok(al, nsn));
                lemma_sfull(sp, s@, st, nsn, p as int, al, matched);
                lemma_cfull(sp, s@, st, nsn, p as int, al, matched, mv, ans);
                lemma_sfull_src(sp, st, c, la as int, pcsv(pcs0), matched);
                assert(pcsv(nx.pcs@).len() == apcs(f.0).len());
                assert(e.acts@.len() == avs(e.acts@).len());
                assert(e.acts@.len() == nx.pcs@.len());
            }
            if u.cut != NOCUT {
                mdef = true;
                mti = uti;
                mcut = u.cut;
                mend = p;
                proof {
                    matched = true;
                    me = ue;
                    mv = M { end: p as int, caps: al[u.cut as int].caps };
                }
            }
            proof {
                let tg2 = useq(e.acts@, ux, (p + 1) as usize);
                let l2 = thl(ar@, tg2, nx.pcs@, nsn);
                let want = isa(f.0, al, nsn, p + 1);
                assert(l2.len() == want.len());
                assert(l2 =~= want);
                ue = t as int;
            }
            uti = ti;
            sid = u.next as usize;
            p += 1;
        }
    }
    let ue1 = if uti == usize::MAX {
        ue0
    } else {
        memo.trans[uti] as usize
    };
    let mut mt = Th { row: NOROW, mask: 0, pos: 0 };
    if mdef {
        let me1 = if mti == usize::MAX {
            ue0
        } else {
            memo.trans[mti] as usize
        };
        mt = uth(&memo.ents[me1].acts, mcut as usize, ux, mend);
    }
    (sid, p, ue1, mdef, mt, mend, Ghost(mv))
}

/// Fuel for computing one step or finding one list: loop iterations.
pub open spec fn memo_fuel(np: int) -> int {
    400 * np + 2048
}

/// Loop iterations per byte the stored steps take, at most: computing a
/// step, finding the list, and copying the threads.
pub open spec fn memo_cost(np: int, ns: int) -> int {
    memo_step(np, ns) + 1
}

/// The same without the dry run's one iteration per byte.
pub open spec fn memo_step(np: int, ns: int) -> int {
    2 * memo_fuel(np) + 2 * (np * (ns + 2)) + 2 * ns + np + 4
}

/// `lac`, computed.
/// `lac`, computed.
#[inline]
fn laq(lat: &Vec<u8>, s: &[u8], j: usize) -> (r: u8)
    requires
        j <= s@.len(),
        lat@.len() == 256,
        forall|b: int| 0 <= b < 256 ==> (#[trigger] lat@[b]) as int == lab(b as u8),
    ensures
        r as int == lac(s@, j as int),
        r < 4,
{
    if j >= s.len() {
        3
    } else {
        let b = s[j];
        assert(lat@[b as int] as int == lab(b));
        lat[b as usize]
    }
}

pub proof fn lemma_slots_ok(prog: &Prog)
    requires
        prog.wf(),
        prog.nslots <= 64,
    ensures
        slots_ok(prog.sp(), prog.nslots as int),
{
    let sp = prog.sp();
    assert forall|q: int| 0 <= q < sp.len() implies match #[trigger] sp[q] {
        SInst::Save { slot, next } => 0 <= slot < 64 && slot < prog.nslots,
        _ => true,
    } by {
        assert(sp[q] == iv(prog.insts@[q], prog.classes@));
    }
}

/// A copy of `v`, or false if the fuel runs out.
fn copy_pcs(v: &Vec<u32>, fuel: &mut u64, it: &mut Ghost<int>) -> (r: (bool, Vec<u32>))
    ensures
        r.0 ==> r.1@ == v@,
        *final(fuel) <= *old(fuel),
        0 <= final(it)@ - old(it)@ <= *old(fuel) - *final(fuel),
{
    let n = v.len();
    let mut w: Vec<u32> = Vec::new();
    let mut k = 0;
    while k < n
        invariant
            n == v@.len(),
            k <= n,
            w@ == v@.subrange(0, k as int),
            *fuel <= *old(fuel),
            0 <= it@ - old(it)@ <= *old(fuel) - *fuel,
        decreases n - k,
    {
        if *fuel == 0 {
            return (false, w);
        }
        *fuel -= 1;
        proof {
            *it.borrow_mut() = it@ + 1;
        }
        w.push(v[k]);
        assert(v@.subrange(0, k + 1) =~= v@.subrange(0, k as int).push(v@[k as int]));
        k += 1;
    }
    assert(v@.subrange(0, n as int) =~= v@);
    (true, w)
}

/// The matcher's invariant between steps, with the threads of a match
/// starting at `p` already in the list.
pub open spec fn jinv(
    sp: Seq<SInst>,
    s: Seq<u8>,
    st: int,
    ns: nat,
    ans: Option<M>,
    l: Seq<T>,
    p: int,
    matched: bool,
    mv: M,
    mend: usize,
    out: Seq<usize>,
) -> bool {
    &&& ans == or(
        fr(sp, s, l, p),
        if matched {
            Some(mv)
        } else {
            search_p(sp, s, st, p + 1, ns)
        },
    )
    &&& (matched ==> mv.end == mend && capv(out) == mv.caps)
}

/// Runs the matcher from byte `p0` on stored steps for as long as it
/// can: over ASCII bytes, while the table can hold the steps, until the
/// list holds no thread of an earlier start. Leaves the same state the
/// Pike VM's own steps would. Gives the position reached, whether a
/// match is known and where it ends, and the loop iterations made.
///
/// Inside, the capture rows of `a` are an arena: threads point at rows
/// and share them, and the list is written out again at the end.
#[verifier::rlimit(100)]
#[verifier::spinoff_prover]
#[inline(never)]
pub fn fast_run(
    prog: &Prog,
    s: &[u8],
    p0: usize,
    memo: &mut Memo,
    a: &mut List,
    b: &mut List,
    ta: &mut Vec<Th>,
    tb: &mut Vec<Th>,
    out: &mut Vec<usize>,
    matched0: bool,
    mend0: usize,
    Ghost(mv0): Ghost<M>,
    Ghost(ans): Ghost<Option<M>>,
    hz0: usize,
) -> (r: (usize, bool, usize, Ghost<M>, Ghost<int>, usize))
    requires
        prog.wf(),
        old(memo).wf(prog),
        p0 <= s@.len() < usize::MAX,
        hz0 <= s@.len(),
        old(a).wf(prog.nslots as nat),
        old(a).pcs@.len() <= prog.insts@.len(),
        old(b).pcs@.len() <= prog.insts@.len(),
        old(out)@.len() == prog.nslots,
        jinv(
            prog.sp(),
            s@,
            prog.start as int,
            prog.nslots as nat,
            ans,
            old(a).v(prog.nslots as nat),
            p0 as int,
            matched0,
            mv0,
            mend0,
            old(out)@,
        ),
    ensures
        final(memo).wf(prog),
        p0 <= r.0 <= s@.len(),
        final(a).wf(prog.nslots as nat),
        final(a).pcs@.len() <= prog.insts@.len(),
        final(b).pcs@.len() <= prog.insts@.len(),
        final(out)@.len() == prog.nslots,
        jinv(
            prog.sp(),
            s@,
            prog.start as int,
            prog.nslots as nat,
            ans,
            final(a).v(prog.nslots as nat),
            r.0 as int,
            r.1,
            r.3@,
            r.2,
            final(out)@,
        ),
        hz0 <= r.5 <= s@.len(),
        0 <= r.4@ <= (r.0 - p0 + 1) * memo_step(prog.insts@.len() as int, prog.nslots as int) + (r.5 - hz0),
{
    let n = s.len();
    let ns = prog.nslots;
    let np = prog.insts.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost nsn = ns as nat;
    let ghost mc = memo_step(np as int, ns as int);
    let ghost mf = memo_fuel(np as int);
    proof {
        assert(np as int * (ns as int + 2) >= 0) by (nonlinear_arith)
            requires
                np >= 0,
                ns >= 0,
        ;
        assert(1 * mc == mc) by (nonlinear_arith);
    }
    if !memo.on || p0 >= n || s[p0] >= 0x80 || np >= 0x1000_0000 {
        return (p0, matched0, mend0, Ghost(mv0), Ghost(0), hz0);
    }
    let full: u64 = 400 * (np as u64) + 2048;
    let mut fuel: u64 = full;
    let mut it: Ghost<int> = Ghost(0);
    let f = find_state(&memo.states, &a.pcs, matched0, &mut fuel, &mut it);
    let mut sid: usize = if f < memo.states.len() {
        f
    } else {
        let (ok, v) = copy_pcs(&a.pcs, &mut fuel, &mut it);
        if !ok {
            return (p0, matched0, mend0, Ghost(mv0), Ghost(it@), hz0);
        }
        let x = add_state(prog, memo, v, matched0, &mut fuel, &mut it);
        if x == MNO {
            return (p0, matched0, mend0, Ghost(mv0), Ghost(it@), hz0);
        }
        x as usize
    };
    let ghost mut drys: int = 0;
    let mut hz = hz0;
    let ps = p0;
    let ghost mut c0: int = 0;
    proof {
        lemma_slots_ok(prog);
    }
    let mut go = false;
    if !matched0 && p0 >= hz0 {
        if memo.credit > 0 {
            go = true;
        } else if memo.tick >= 15 {
            memo.tick = 0;
            go = true;
        } else {
            memo.tick = memo.tick + 1;
        }
    }
    if go {
        // A dry run first: follow the stored steps by list number alone,
        // touching no thread. Most stretches end with every earlier
        // start dead and no match, and then the list is just the threads
        // of a new start, which the last step spells out in full. Only a
        // stretch that reaches a match (or stops for another reason) is
        // run again below with its threads.
        let mut q = p0;
        let mut ds = sid;
        let ghost mut dl = a.v(nsn);
        let mut halt = false;
        loop
            invariant_except_break
                !halt,
            invariant
                prog.wf(),
                memo.wf(prog),
                memo.on,
                n == s@.len(),
                n < usize::MAX,
                ns == prog.nslots,
                ns <= 64,
                np == prog.insts@.len(),
                np < 0x1000_0000,
                sp == prog.sp(),
                st == prog.start,
                nsn == ns,
                mf == memo_fuel(np as int),
                full == 400 * np + 2048,
                slots_ok(sp, ns as int),
                p0 <= q <= n,
                a.wf(nsn),
                a.pcs@.len() <= np,
                b.pcs@.len() <= np,
                out@.len() == ns,
                !matched0,
                sid < memo.states@.len(),
                memo.states@[sid as int].pcs@ == a.pcs@,
                memo.states@[sid as int].matched == matched0,
                ds < memo.states@.len(),
                !memo.states@[ds as int].matched,
                pcs_of(dl) =~= pcsv(memo.states@[ds as int].pcs@),
                caps_ok(dl, nsn),
                ans == or(fr(sp, s@, dl, q as int), search_p(sp, s@, st, q + 1, nsn)),
                0 <= it@ <= mf,
                hz0 <= p0,
                *a == *old(a),
                mc == memo_step(np as int, ns as int),
            ensures
                halt ==> q < n && ans == search_p(sp, s@, st, q + 1, nsn),
            decreases n - q,
        {
            if q >= n {
                break;
            }
            let c = s[q];
            if c >= 0x80 {
                break;
            }
            let la = laq(&memo.lat, s, q + 1);
            let ti = (ds * 4 + la as usize) * 128 + c as usize;
            assert(ti == tidx(ds as int, la as int, c as int));
            assert(ti < memo.states@.len() * 512) by (nonlinear_arith)
                requires
                    ti == (ds * 4 + la) * 128 + c,
                    ds < memo.states@.len(),
                    la < 4,
                    c < 128,
            ;
            let v = memo.dn[ti];
            if v == DSTOP {
                // A match, or a step not stored: left to the run below.
                break;
            }
            let ghost pcs0 = memo.states@[ds as int].pcs@;
            let ghost t = memo.trans@[ti as int];
            assert(dn_ok(memo.ents@, t, v));
            assert(slot_ok(sp, st, memo.states@, memo.ents@, ds as int, la as int, c as int, memo.trans@[tidx(
                ds as int,
                la as int,
                c as int,
            )]));
            let ghost e = memo.ents@[t as int];
            let ghost cut = e.cut;
            assert(ent_ok(sp, st, memo.states@, ds as int, la as int, c, e));
            let next = v / 4;
            let idle = v % 2 == 1;
            assert(next == e.next && idle == e.idle);
            let ghost f = sfull(sp, st, c, la as int, pcsv(pcs0), false);
            let ghost nx = memo.states@[next as int];
            let ghost l2 = isa(f.0, dl, nsn, q + 1);
            proof {
                assert(ent_ok(sp, st, memo.states@, ds as int, la as int, c, e));
                lemma_sfull(sp, s@, st, nsn, q as int, dl, false);
                lemma_cfull(sp, s@, st, nsn, q as int, dl, false, mv0, ans);
                assert(cutv(cut) is None);
                assert(pcs_of(l2) =~= apcs(f.0));
                assert(pcsv(nx.pcs@).len() == apcs(f.0).len());
                assert(e.acts@.len() == avs(e.acts@).len());
                assert(e.acts@.len() == nx.pcs@.len());
                assert(caps_ok(l2, nsn));
            }
            if idle {
                // Every earlier start dies on this byte and nothing
                // matches: back to the search for a start from the next
                // byte on, with no thread. The DFA and the skip tables
                // pass over text faster than this loop does.
                let rt = memo.trans[ti] as usize;
                if memo.ents[rt].us == NOSRC {
                    proof {
                        assert(us_ok(e.acts@, e.us));
                        assert forall|k: int| 0 <= k < f.0.len() implies (#[trigger] f.0[k]).src == -1 by {
                            assert(f.0[k] == av(e.acts@[k]));
                        }
                        lemma_idle(sp, s@, st, nsn, q as int, dl, ans);
                    }
                    halt = true;
                }
                break;
            }
            ds = next as usize;
            q += 1;
            proof {
                dl = l2;
            }
        }
        hz = q;
        proof {
            drys = q - p0;
        }
        if halt {
            if memo.credit < 8 {
                memo.credit = memo.credit + 1;
            }
            b.clear(Ghost(nsn));
            core::mem::swap(a, b);
            proof {
                lemma_fr_empty(sp, s@, a.v(nsn), q as int);
                assert(np * (ns + 2) >= 0) by (nonlinear_arith)
                    requires
                        np >= 0,
                        ns >= 0,
                ;
                assert(mc >= mf);
                assert((q - p0 + 1) * mc >= mc) by (nonlinear_arith)
                    requires
                        q - p0 >= 0,
                        mc >= 0,
                ;
            }
            return (q, false, mend0, Ghost(mv0), Ghost(it@ + (q - p0)), hz);
        } else if q > p0 && memo.credit > 0 {
            // Every byte of it has to be done again with threads.
            memo.credit = memo.credit - 1;
        }
    }
    assert(p0 <= ps <= n);
    assert(a.wf(nsn));
    assert(a.pcs@.len() <= np && b.pcs@.len() <= np);
    assert(sid < memo.states@.len() && memo.states@[sid as int].pcs@ == a.pcs@ && memo.states@[sid as int].matched
        == matched0);
    assert(ans == or(
        fr(sp, s@, a.v(nsn), ps as int),
        if matched0 {
            Some(mv0)
        } else {
            search_p(sp, s@, st, ps + 1, nsn)
        },
    ));
    assert(0 <= c0 <= (ps - p0) * mc);
    // The threads of `a`, each on its own row.
    let la = a.pcs.len();
    ta.clear();
    let mut k: usize = 0;
    while k < la
        invariant
            k <= la,
            la == a.pcs@.len(),
            la < 0x1000_0000,
            ta@.len() == k,
            forall|j: int| 0 <= j < k ==> (#[trigger] ta@[j]) == (Th { row: j as u32, mask: 0, pos: 0 }),
        decreases la - k,
    {
        ta.push(Th { row: k as u32, mask: 0, pos: 0 });
        k += 1;
    }
    let lim: usize = 4 * np + 64;
    let mut nrows: usize = la;
    let mut p = ps;
    let mut matched = matched0;
    let mut mend = mend0;
    let mut cutm = false;
    let mut mt = Th { row: NOROW, mask: 0, pos: 0 };
    let ghost mut mv = mv0;
    let ghost mut cost: int = it@ + c0 + la;
    let ghost mut extra: int = 0;
    let ghost mut l = a.v(nsn);
    // The list is `ta`, or, after a step whose threads all come from one
    // thread, row `ux` and the masks of step `ue` (`useq`).
    let mut halt2 = false;
    let mut um = false;
    let mut ux: u32 = NOROW;
    let mut ue: usize = 0;
    let mut upos: usize = 0;
    let ghost mut tg: Seq<Th> = ta@;
    let ghost mut xtra: int = 0;
    proof {
        lemma_slots_ok(prog);
        assert(0 * mc == 0) by (nonlinear_arith);
        let y = thl(a.caps@, ta@, a.pcs@, nsn);
        assert(l.len() == y.len());
        assert forall|kk: int| 0 <= kk < l.len() implies l[kk] == y[kk] by {
            lemma_icap0(rowv(a.caps@, kk, nsn), 0);
            assert(l[kk].caps =~= rowv(a.caps@, kk, nsn));
        }
        assert(l =~= y);
    }
    loop
        invariant_except_break
            xtra == 0,
            !halt2,
        invariant
            prog.wf(),
            memo.wf(prog),
            memo.on,
            n == s@.len(),
            n < usize::MAX,
            ns == prog.nslots,
            ns <= 64,
            np == prog.insts@.len(),
            np < 0x1000_0000,
            lim == 4 * np + 64,
            sp == prog.sp(),
            st == prog.start,
            nsn == ns,
            mc == memo_step(np as int, ns as int),
            mf == memo_fuel(np as int),
            np as int * (ns as int + 2) >= 0,
            full == 400 * np + 2048,
            slots_ok(sp, ns as int),
            p0 <= p <= n,
            a.pcs@.len() <= np,
            b.pcs@.len() <= np,
            out@.len() == ns,
            sid < memo.states@.len(),
            a.caps@.len() == nrows * ns,
            tg.len() == memo.states@[sid as int].pcs@.len(),
            ths_ok(tg, nrows as int),
            l == thl(a.caps@, tg, memo.states@[sid as int].pcs@, nsn),
            !um ==> tg == ta@,
            um ==> upos == p,
            um ==> ue < memo.ents@.len() && upos < usize::MAX && (ux == NOROW || ux < nrows) && tg == useq(
                memo.ents@[ue as int].acts@,
                ux,
                upos,
            ),
            memo.states@[sid as int].matched == matched,
            ans == or(
                fr(sp, s@, l, p as int),
                if matched {
                    Some(mv)
                } else {
                    search_p(sp, s@, st, p + 1, nsn)
                },
            ),
            matched ==> mv.end == mend,
            matched && cutm ==> th_ok(mt, nrows as int) && mv.caps == thv(a.caps@, mt, nsn),
            matched && !cutm ==> capv(out@) == mv.caps,
            cutm ==> matched,
            0 <= cost <= (p - p0) * mc + mf + np,
            0 <= extra <= mf,
        ensures
            halt2 ==> p < n && !matched && ans == search_p(sp, s@, st, p + 1, nsn),
            0 <= xtra <= np,
            um && !halt2 ==> xtra == 0,
        decreases n - p,
    {
        if um {
            let ghost pa = p;
            let r = urun(prog, s, memo, &a.caps, sid, p, ux, ue, matched, Ghost(nrows as int), Ghost(mv), Ghost(ans));
            sid = r.0;
            p = r.1;
            ue = r.2;
            upos = p;
            if r.3 {
                matched = true;
                cutm = true;
                mt = r.4;
                mend = r.5;
            }
            proof {
                mv = r.6@;
                tg = useq(memo.ents@[ue as int].acts@, ux, upos);
                l = thl(a.caps@, tg, memo.states@[sid as int].pcs@, nsn);
                assert((p - p0) * mc == (pa - p0) * mc + (p - pa) * mc) by (nonlinear_arith);
                assert((p - pa) <= (p - pa) * mc) by (nonlinear_arith)
                    requires
                        p - pa >= 0,
                        mc >= 1,
                ;
                cost = cost + (p - pa);
            }
            if matched && memo.ents[ue].acts.len() == 0 {
                break;
            }
        }
        proof {
            assert((p - p0 + 1) * mc == (p - p0) * mc + mc) by (nonlinear_arith);
        }
        if p >= n || nrows >= lim {
            break;
        }
        let c = s[p];
        if c >= 0x80 {
            break;
        }
        let la = laq(&memo.lat, s, p + 1);
        let ti = (sid * 4 + la as usize) * 128 + c as usize;
        assert(ti == tidx(sid as int, la as int, c as int));
        let mut t = memo.trans[ti];
        if t == MNO {
            break;
        }
        let ghost pcs0 = memo.states@[sid as int].pcs@;
        let ghost mut bcost: int = 0;
        let ghost mut xc: int = 0;
        if t == MUNK {
            if um {
                let x = expand(&memo.ents[ue].acts, ux, upos, ta);
                um = false;
                proof {
                    xc = x@;
                }
            }
            let mut fuel2: u64 = full;
            let mut it2: Ghost<int> = Ghost(0);
            t = build_ent(prog, memo, sid, la, c, &mut fuel2, &mut it2);
            proof {
                bcost = it2@;
            }
            set_trans(prog, memo, sid, la, c, t);
            assert(memo.states@[sid as int].pcs@ == pcs0);
            if t == MNO {
                proof {
                    extra = bcost;
                    xtra = xc;
                }
                break;
            }
        }
        assert(slot_ok(sp, st, memo.states@, memo.ents@, sid as int, la as int, c as int, memo.trans@[tidx(
            sid as int,
            la as int,
            c as int,
        )]));
        let ghost al = l;
        let ghost e = memo.ents@[t as int];
        let ghost f = sfull(sp, st, c, la as int, pcsv(pcs0), matched);
        proof {
            assert(ent_ok(sp, st, memo.states@, sid as int, la as int, c, e));
            assert(pcs_of(al) =~= pcsv(pcs0));
            assert(caps_ok(al, nsn));
            lemma_sfull(sp, s@, st, nsn, p as int, al, matched);
            lemma_cfull(sp, s@, st, nsn, p as int, al, matched, mv, ans);
            lemma_sfull_src(sp, st, c, la as int, pcsv(pcs0), matched);
        }
        let cut = memo.ents[t as usize].cut;
        let next = memo.ents[t as usize].next;
        let idle = memo.ents[t as usize].idle;
        let us = memo.ents[t as usize].us;
        let ln = memo.ents[t as usize].acts.len();
        if idle && us == NOSRC && cut == NOCUT && !matched {
            // No thread survives this byte and nothing matches: back to
            // the search for a start, with no thread.
            proof {
                assert(us_ok(e.acts@, e.us));
                assert forall|k: int| 0 <= k < f.0.len() implies (#[trigger] f.0[k]).src == -1 by {
                    assert(f.0[k] == av(e.acts@[k]));
                }
                lemma_idle(sp, s@, st, nsn, p as int, al, ans);
                extra = bcost;
                xtra = xc;
            }
            halt2 = true;
            break;
        }
        if cut != NOCUT {
            mt = if um {
                uth(&memo.ents[ue].acts, cut as usize, ux, upos)
            } else {
                ta[cut as usize]
            };
            assert(mt == tg[cut as int]);
            cutm = true;
            matched = true;
            mend = p;
            proof {
                mv = M { end: p as int, caps: al[cut as int].caps };
            }
        }
        let ghost ar0 = a.caps@;
        let ghost tg0 = tg;
        let ghost nr0 = nrows as int;
        let ghost nx = memo.states@[next as int];
        let ghost mut ac: int = 0;
        proof {
            assert(pcsv(nx.pcs@).len() == apcs(f.0).len());
            assert(e.acts@.len() == avs(e.acts@).len());
            assert(e.acts@.len() == nx.pcs@.len());
            assert(np * (ns + 2) == np * ns + 2 * np) by (nonlinear_arith);
            assert(us_ok(e.acts@, e.us));
        }
        if us != UMIX {
            // Every thread with a source has the same one: no list is
            // written, only that thread's row is kept.
            let mut base: u32 = NOROW;
            let tl = if um {
                memo.ents[ue].acts.len()
            } else {
                ta.len()
            };
            assert(tl == tg0.len());
            if us != NOSRC && (us as usize) < tl {
                let t0 = if um {
                    uth(&memo.ents[ue].acts, us as usize, ux, upos)
                } else {
                    ta[us as usize]
                };
                assert(t0 == tg0[us as int]);
                assert(th_ok(t0, nr0));
                let (b2, nr2, uc) = uni_row(&mut a.caps, t0, nrows, ns);
                base = b2;
                nrows = nr2;
                proof {
                    ac = uc@;
                    assert(ns <= np * ns + np) by (nonlinear_arith)
                        requires
                            np >= 1,
                            ns >= 0,
                    ;
                }
            }
            um = true;
            ux = base;
            ue = t as usize;
            upos = p + 1;
            proof {
                tg = useq(e.acts@, base, upos);
                assert(srcs_ok(avs(e.acts@), tg0.len() as int));
                lemma_uni(e.acts@, us, base, ar0, a.caps@, tg0, nrows as int, nsn, upos);
            }
        } else {
            if um {
                let x = expand(&memo.ents[ue].acts, ux, upos, ta);
                um = false;
                proof {
                    xc = x@;
                }
            }
            assert(ta@ == tg0);
            let (nr2, ac2) = apply_t(&memo.ents[t as usize].acts, ta, tb, &mut a.caps, nrows, p + 1, ns);
            nrows = nr2;
            proof {
                ac = ac2@;
                assert((nr2 - nr0) * ns <= np * ns) by (nonlinear_arith)
                    requires
                        0 <= nr2 - nr0 <= np,
                        ns >= 0,
                ;
                tg = tb@;
            }
            core::mem::swap(ta, tb);
        }
        proof {
            let l2 = thl(a.caps@, tg, nx.pcs@, nsn);
            let want = isa(f.0, al, nsn, p + 1);
            assert(l2.len() == want.len());
            assert forall|kk: int| 0 <= kk < l2.len() implies l2[kk] == want[kk] by {
                assert(f.0[kk] == av(e.acts@[kk]));
                assert(pcsv(nx.pcs@)[kk] == apcs(f.0)[kk]);
                assert(th_ok(tg[kk], nrows as int));
                if e.acts@[kk].src != NOSRC {
                    assert(al[e.acts@[kk].src as int].caps == thv(ar0, tg0[e.acts@[kk].src as int], nsn));
                }
            }
            assert(l2 =~= want);
            l = l2;
            if cutm {
                assert(nr0 * ns as int <= nrows as int * ns as int) by (nonlinear_arith)
                    requires
                        nr0 <= nrows,
                        ns >= 0,
                ;
                lemma_thv_frame(ar0, a.caps@, mt, nr0, nsn);
            }
        }
        sid = next as usize;
        p += 1;
        proof {
            cost = cost + bcost + xc + ac + 1;
        }
        if idle || (matched && ln == 0) {
            break;
        }
    }
    proof {
        assert((p - p0 + 1) * mc == (p - p0) * mc + mc) by (nonlinear_arith);
    }
    if halt2 {
        b.clear(Ghost(nsn));
        core::mem::swap(a, b);
        proof {
            lemma_fr_empty(sp, s@, a.v(nsn), p as int);
            assert(np * (ns + 2) >= 2 * np) by (nonlinear_arith)
                requires
                    np >= 0,
                    ns >= 0,
            ;
        }
        return (p, false, mend, Ghost(mv), Ghost(cost + extra + xtra + 1 + drys), hz);
    }
    if um {
        let x = expand(&memo.ents[ue].acts, ux, upos, ta);
        proof {
            xtra = x@;
        }
    }
    assert(ta@ == tg);
    if cutm {
        load_th(&a.caps, mt, out, ns, Ghost(nrows as int));
    }
    let fc = finish(ta, &a.caps, &memo.states[sid].pcs, b, ns, Ghost(nrows as int));
    proof {
        assert(ta@.len() * (ns + 1) <= np * (ns + 1)) by (nonlinear_arith)
            requires
                ta@.len() <= np,
                ns >= 0,
        ;
        assert(np * (ns + 2) == np * (ns + 1) + np) by (nonlinear_arith);
    }
    core::mem::swap(a, b);
    // The steps made, the one that stopped, writing the list out, and
    // the slots of the match.
    (p, matched, mend, Ghost(mv), Ghost(cost + extra + xtra + 1 + fc@ + ns + drys), hz)
}

} // verus!
