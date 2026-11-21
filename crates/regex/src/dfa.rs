//! A lazy DFA that proves stretches of text hold no match.
//!
//! A state is a set of instructions: those some thread could be at, if
//! every assertion held. The DFA starts from the empty set and steps over
//! ASCII bytes, adding the start of the pattern at every byte. When the
//! set is empty again and no `Match` instruction was ever in it, no match
//! starts anywhere in the bytes stepped over (`lemma_flow`), so the search
//! may resume from there. When a `Match` instruction turns up, or a byte
//! is not ASCII, the DFA stops and the Pike VM takes over from the last
//! byte where the set was empty.
//!
//! Because assertions are taken to hold, the sets only ever hold too
//! much, which costs time and not correctness. Sets and transitions are
//! computed when first needed and kept, up to a fixed budget.
use crate::class::*;
use crate::compile::*;
use crate::find::find_byte;
use crate::need::*;
use crate::prog::*;
use crate::sem::*;
use crate::skip::*;
use crate::spec::*;
use crate::vmspec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;
use verilith_text::utf::spec::*;

verus! {

/// At most this many states are kept.
pub const DFA_MAX_STATES: usize = 256;

/// At most this many flags are kept over all states.
pub const DFA_MAX_FLAGS: usize = 0x40_0000;

/// A transition not computed yet.
pub const UNK: u32 = 0xFFFF_FFFF;

/// A transition the DFA does not take: the Pike VM must look.
pub const STOP: u32 = 0xFFFF_FFFE;

pub struct Dfa {
    /// What the start of the pattern reaches without consuming.
    pub s0: Vec<bool>,
    /// The states. State 0 is the empty set.
    pub states: Vec<Vec<bool>>,
    /// 128 transitions per state, one per ASCII byte.
    pub trans: Vec<u32>,
    /// Few bytes can start a match, so skipping to one of them pays.
    pub sparse: bool,
}

pub open spec fn tix(k: int, b: int) -> int {
    k * 128 + b
}

/// Instruction `pc` is in the set `d` or reached from the start.
pub open spec fn live(d: Seq<bool>, s0: Seq<bool>, pc: int) -> bool {
    d[pc] || s0[pc]
}

/// From the set `d` with the start added, over the byte `b`, every
/// thread is in `d2`, and none is at `Match`.
pub open spec fn step_ok(p: Seq<SInst>, d: Seq<bool>, s0: Seq<bool>, b: u8, d2: Seq<bool>) -> bool {
    &&& d2.len() == p.len()
    &&& forall|pc: int|
        0 <= pc < p.len() && #[trigger] live(d, s0, pc) ==> match p[pc] {
            SInst::Match => false,
            SInst::Char { cls, next } => cls.contains(b as u32) ==> 0 <= next < p.len() && d2[next],
            _ => true,
        }
}

impl Dfa {
    pub open spec fn wf(&self, prog: &Prog) -> bool {
        let sp = prog.sp();
        &&& closed(sp, self.s0@)
        &&& self.s0@[prog.start as int]
        &&& 1 <= self.states@.len() <= DFA_MAX_STATES
        &&& self.trans@.len() == self.states@.len() * 128
        &&& forall|k: int| 0 <= k < self.states@.len() ==> closed(sp, (#[trigger] self.states@[k])@)
        &&& forall|pc: int| 0 <= pc < sp.len() ==> !#[trigger] self.states@[0]@[pc]
        &&& forall|k: int, b: int|
            0 <= k < self.states@.len() && 0 <= b < 128 ==> {
                let v = #[trigger] self.trans@[tix(k, b)];
                v == UNK || v == STOP || (v < self.states@.len() && step_ok(
                    sp,
                    self.states@[k]@,
                    self.s0@,
                    b as u8,
                    self.states@[v as int]@,
                ))
            }
    }

    pub fn new(prog: &Prog) -> (r: Dfa)
        requires
            prog.wf(),
        ensures
            r.wf(prog),
    {
        assert(prog.sp() =~= pv(prog.insts@, prog.classes@));
        let s0 = reach(&prog.insts, prog.start, Ghost(prog.classes@));
        let d0 = no_flags(prog.insts.len());
        let mut states: Vec<Vec<bool>> = Vec::new();
        states.push(d0);
        let mut trans: Vec<u32> = Vec::new();
        let mut k = 0;
        while k < 128
            invariant
                k <= 128,
                trans@.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] trans@[j] == UNK,
            decreases 128 - k,
        {
            trans.push(UNK);
            k += 1;
        }
        let mut cnt: usize = 0;
        let mut j = 0;
        while j < prog.skip.len()
            invariant
                j <= prog.skip@.len(),
                cnt <= j,
            decreases prog.skip@.len() - j,
        {
            if prog.skip[j] {
                cnt += 1;
            }
            j += 1;
        }
        Dfa { s0: s0, states: states, trans: trans, sparse: prog.skip.len() == 256 && cnt <= 32 }
    }
}

/// `m` is among the matches of some thread of `d` at byte `i`.
pub open spec fn thru(p: Seq<SInst>, s: Seq<u8>, m: M, d: Seq<bool>, i: int) -> bool {
    exists|pc: int, c: Seq<int>| 0 <= pc < p.len() && d[pc] && #[trigger] pm(p, s, pc, i, c).contains(m)
}

proof fn lemma_app_contains(a: Seq<M>, b: Seq<M>, m: M)
    requires
        (a + b).contains(m),
    ensures
        a.contains(m) || b.contains(m),
{
    let k = choose|k: int| 0 <= k < (a + b).len() && (a + b)[k] == m;
    if k < a.len() {
        assert(a[k] == m);
    } else {
        assert(b[k - a.len()] == m);
    }
}

/// A match of a thread in the set `d` (with the start added) at an ASCII
/// byte is a match of a thread in the next set at the next byte.
pub proof fn lemma_flow(
    p: Seq<SInst>,
    s: Seq<u8>,
    pc: int,
    i: int,
    c: Seq<int>,
    m: M,
    d: Seq<bool>,
    s0: Seq<bool>,
    d2: Seq<bool>,
)
    requires
        closed(p, d),
        closed(p, s0),
        0 <= pc < p.len(),
        d[pc] || s0[pc],
        0 <= i < s.len(),
        s[i] < 0x80,
        step_ok(p, d, s0, s[i], d2),
        pm(p, s, pc, i, c).contains(m),
    ensures
        thru(p, s, m, d2, i + 1),
    decreases p.len() - pc,
{
    assert(live(d, s0, pc));
    match p[pc] {
        SInst::Char { cls, next } => {
            assert(dec(s, i) == Some((s[i] as u32, 1int)));
            assert(pm(p, s, next, i + 1, c).contains(m));
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
            lemma_app_contains(x, y, m);
            if x.contains(m) {
                lemma_flow(p, s, a, i, c, m, d, s0, d2);
            } else {
                lemma_flow(p, s, b, i, c, m, d, s0, d2);
            }
        },
        SInst::Save { slot, next } => {
            lemma_flow(p, s, next, i, c.update(slot, i), m, d, s0, d2);
        },
        SInst::Look { k, next } => {
            lemma_flow(p, s, next, i, c, m, d, s0, d2);
        },
        _ => {},
    }
}

/// No match starts at any byte from `a` up to `b`.
pub open spec fn none_from(p: Seq<SInst>, s: Seq<u8>, st: int, a: int, b: int, ns: nat) -> bool {
    forall|j: int| a <= j < b ==> (#[trigger] pm(p, s, st, j, unset(ns))).len() == 0
}

pub proof fn lemma_none_from(p: Seq<SInst>, s: Seq<u8>, st: int, a: int, b: int, ns: nat)
    requires
        none_from(p, s, st, a, b, ns),
        0 <= a <= b <= s.len(),
    ensures
        search_p(p, s, st, a, ns) == search_p(p, s, st, b, ns),
    decreases b - a,
{
    if a < b {
        assert(pm(p, s, st, a, unset(ns)).len() == 0);
        lemma_none_from(p, s, st, a + 1, b, ns);
    }
}

/// What the DFA has established at byte `q`, in set `d`: every match
/// that starts at a byte from `p0` up to `q` is a match of a thread of
/// `d` at `q`.
pub open spec fn flows(p: Seq<SInst>, s: Seq<u8>, st: int, ns: nat, p0: int, q: int, d: Seq<bool>) -> bool {
    forall|j: int, m: M| p0 <= j < q && #[trigger] pm(p, s, st, j, unset(ns)).contains(m) ==> thru(p, s, m, d, q)
}

/// One step of the DFA keeps `flows`.
pub proof fn lemma_flows_step(
    p: Seq<SInst>,
    s: Seq<u8>,
    st: int,
    ns: nat,
    p0: int,
    q: int,
    d: Seq<bool>,
    s0: Seq<bool>,
    d2: Seq<bool>,
)
    requires
        flows(p, s, st, ns, p0, q, d),
        closed(p, d),
        closed(p, s0),
        0 <= st < p.len(),
        s0[st],
        0 <= q < s.len(),
        s[q] < 0x80,
        step_ok(p, d, s0, s[q], d2),
    ensures
        flows(p, s, st, ns, p0, q + 1, d2),
{
    assert forall|j: int, m: M| p0 <= j < q + 1 && #[trigger] pm(p, s, st, j, unset(ns)).contains(m) implies thru(
        p,
        s,
        m,
        d2,
        q + 1,
    ) by {
        if j < q {
            assert(thru(p, s, m, d, q));
            let (pc, c) = choose|pc: int, c: Seq<int>|
                0 <= pc < p.len() && d[pc] && #[trigger] pm(p, s, pc, q, c).contains(m);
            lemma_flow(p, s, pc, q, c, m, d, s0, d2);
        } else {
            lemma_flow(p, s, st, q, unset(ns), m, d, s0, d2);
        }
    }
}

/// With the empty set, `flows` says no match starts in the stretch.
pub proof fn lemma_flows_empty(p: Seq<SInst>, s: Seq<u8>, st: int, ns: nat, p0: int, q: int, d: Seq<bool>)
    requires
        flows(p, s, st, ns, p0, q, d),
        forall|pc: int| 0 <= pc < p.len() ==> !#[trigger] d[pc],
        0 <= p0 <= q <= s.len(),
    ensures
        search_p(p, s, st, p0, ns) == search_p(p, s, st, q, ns),
{
    assert forall|j: int| p0 <= j < q implies (#[trigger] pm(p, s, st, j, unset(ns))).len() == 0 by {
        let l = pm(p, s, st, j, unset(ns));
        if l.len() > 0 {
            assert(l.contains(l[0]));
            assert(thru(p, s, l[0], d, q));
        }
    }
    lemma_none_from(p, s, st, p0, q, ns);
}

/// Loop iterations one transition takes to compute, at most.
pub open spec fn trans_cost(np: int) -> int {
    330 * np + 300
}

fn eq_flags(a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
    requires
        a@.len() == b@.len(),
    ensures
        r ==> a@ == b@,
{
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// The state equal to `d2`, if one is kept; else the number of states.
fn find_state(states: &Vec<Vec<bool>>, d2: &Vec<bool>) -> (r: (usize, Ghost<int>))
    requires
        forall|k: int| 0 <= k < states@.len() ==> (#[trigger] states@[k])@.len() == d2@.len(),
    ensures
        r.0 <= states@.len(),
        r.0 < states@.len() ==> states@[r.0 as int]@ == d2@,
        0 <= r.1@ <= states@.len() * d2@.len(),
{
    let ns = states.len();
    let ghost np = d2@.len() as int;
    let mut k = 0;
    proof {
        assert(0 * np == 0) by (nonlinear_arith);
    }
    while k < ns
        invariant
            k <= ns,
            ns == states@.len(),
            np == d2@.len(),
            forall|k: int| 0 <= k < states@.len() ==> (#[trigger] states@[k])@.len() == d2@.len(),
        decreases ns - k,
    {
        proof {
            assert((k + 1) * np == k * np + np) by (nonlinear_arith);
            assert((k + 1) * np <= ns * np) by (nonlinear_arith)
                requires
                    k + 1 <= ns,
                    np >= 0,
            ;
        }
        if eq_flags(&states[k], d2) {
            return (k, Ghost((k + 1) * np));
        }
        k += 1;
    }
    (ns, Ghost(ns * np))
}

/// 128 more transitions, none computed.
fn push_unk(trans: &mut Vec<u32>)
    ensures
        final(trans)@.len() == old(trans)@.len() + 128,
        forall|i: int| 0 <= i < old(trans)@.len() ==> #[trigger] final(trans)@[i] == old(trans)@[i],
        forall|i: int| old(trans)@.len() <= i < old(trans)@.len() + 128 ==> #[trigger] final(trans)@[i] == UNK,
{
    let mut j: usize = 0;
    while j < 128
        invariant
            j <= 128,
            trans@.len() == old(trans)@.len() + j,
            forall|i: int| 0 <= i < old(trans)@.len() ==> #[trigger] trans@[i] == old(trans)@[i],
            forall|i: int| old(trans)@.len() <= i < old(trans)@.len() + j ==> #[trigger] trans@[i] == UNK,
        decreases 128 - j,
    {
        trans.push(UNK);
        j += 1;
    }
}

/// The set a step over `b` leads to from `d` with the start added,
/// before closing it; `None` if a thread is at `Match`.
fn seeds(prog: &Prog, d: &Vec<bool>, s0: &Vec<bool>, b: u8) -> (r: (Option<Vec<bool>>, Ghost<int>))
    requires
        prog.wf(),
        d@.len() == prog.insts@.len(),
        s0@.len() == prog.insts@.len(),
        b < 128,
    ensures
        r.0 matches Some(d2) ==> d2@.len() == prog.insts@.len() && forall|q: int|
            0 <= q < prog.insts@.len() && #[trigger] live(d@, s0@, q) ==> match prog.sp()[q] {
                SInst::Match => false,
                SInst::Char { cls, next } => cls.contains(b as u32) ==> 0 <= next < prog.insts@.len() && d2@[next],
                _ => true,
            },
        0 <= r.1@ <= 67 * prog.insts@.len(),
{
    let ghost sp = prog.sp();
    let np = prog.insts.len();
    let mut d2 = no_flags(np);
    let mut pc = 0;
    let ghost mut cost: int = np as int;
    while pc < np
        invariant
            pc <= np,
            np == prog.insts@.len(),
            prog.wf(),
            sp == prog.sp(),
            d2@.len() == np,
            d@.len() == np,
            s0@.len() == np,
            b < 128,
            np <= cost <= np + 66 * pc,
            forall|q: int|
                0 <= q < pc && #[trigger] live(d@, s0@, q) ==> match sp[q] {
                    SInst::Match => false,
                    SInst::Char { cls, next } => cls.contains(b as u32) ==> 0 <= next < np && d2@[next],
                    _ => true,
                },
        decreases np - pc,
    {
        assert(sp[pc as int] == iv(prog.insts@[pc as int], prog.classes@));
        assert(fwd_at(sp, pc as int));
        proof {
            cost = cost + 1;
        }
        if d[pc] || s0[pc] {
            match prog.insts[pc] {
                Inst::Match => {
                    return (None, Ghost(cost));
                },
                Inst::Char { cls, next } => {
                    let (has, cc) = prog.classes[cls as usize].contains_c(b as u32);
                    proof {
                        cost = cost + cc@;
                    }
                    if has {
                        let ghost e0 = d2@;
                        d2[next as usize] = true;
                        assert forall|q: int| 0 <= q < pc && #[trigger] live(d@, s0@, q) implies match sp[q] {
                            SInst::Match => false,
                            SInst::Char { cls, next } => cls.contains(b as u32) ==> 0 <= next < np && d2@[next],
                            _ => true,
                        } by {
                            match sp[q] {
                                SInst::Char { cls, next } => {
                                    if cls.contains(b as u32) {
                                        assert(e0[next]);
                                    }
                                },
                                _ => {},
                            }
                        }
                    }
                },
                _ => {},
            }
        }
        pc += 1;
    }
    (Some(d2), Ghost(cost))
}

/// Records `v` as the transition at `ix`, which keeps the DFA well-formed
/// if `v` is a right answer.
fn set_trans(prog: &Prog, dfa: &mut Dfa, cur: usize, b: u8, v: u32)
    requires
        prog.wf(),
        old(dfa).wf(prog),
        cur < old(dfa).states@.len(),
        b < 128,
        v == STOP || (v < old(dfa).states@.len() && step_ok(
            prog.sp(),
            old(dfa).states@[cur as int]@,
            old(dfa).s0@,
            b,
            old(dfa).states@[v as int]@,
        )),
    ensures
        final(dfa).wf(prog),
        final(dfa).s0 == old(dfa).s0,
        final(dfa).states == old(dfa).states,
{
    let ix = cur * 128 + b as usize;
    assert(ix == tix(cur as int, b as int));
    dfa.trans.set(ix, v);
    assert forall|k: int, bb: int| 0 <= k < dfa.states@.len() && 0 <= bb < 128 implies {
        let w = #[trigger] dfa.trans@[tix(k, bb)];
        w == UNK || w == STOP || (w < dfa.states@.len() && step_ok(
            prog.sp(),
            dfa.states@[k]@,
            dfa.s0@,
            bb as u8,
            dfa.states@[w as int]@,
        ))
    } by {
        if tix(k, bb) != ix {
            assert(dfa.trans@[tix(k, bb)] == old(dfa).trans@[tix(k, bb)]);
        } else {
            assert(k == cur && bb == b);
        }
    }
}

/// Keeps `d2` as a new state.
fn add_state(prog: &Prog, dfa: &mut Dfa, d2: Vec<bool>)
    requires
        prog.wf(),
        old(dfa).wf(prog),
        closed(prog.sp(), d2@),
        old(dfa).states@.len() < DFA_MAX_STATES,
    ensures
        final(dfa).wf(prog),
        final(dfa).s0 == old(dfa).s0,
        final(dfa).states@ == old(dfa).states@.push(d2),
{
    let ghost ns = dfa.states@.len() as int;
    dfa.states.push(d2);
    push_unk(&mut dfa.trans);
    assert forall|k: int, bb: int| 0 <= k < dfa.states@.len() && 0 <= bb < 128 implies {
        let w = #[trigger] dfa.trans@[tix(k, bb)];
        w == UNK || w == STOP || (w < dfa.states@.len() && step_ok(
            prog.sp(),
            dfa.states@[k]@,
            dfa.s0@,
            bb as u8,
            dfa.states@[w as int]@,
        ))
    } by {
        if k < ns {
            let w = old(dfa).trans@[tix(k, bb)];
            assert(dfa.trans@[tix(k, bb)] == w);
            assert(dfa.states@[k] == old(dfa).states@[k]);
            if w != UNK && w != STOP {
                assert(dfa.states@[w as int] == old(dfa).states@[w as int]);
            }
        }
    }
    assert forall|k: int| 0 <= k < dfa.states@.len() implies closed(prog.sp(), (#[trigger] dfa.states@[k])@) by {
        if k < ns {
            assert(dfa.states@[k] == old(dfa).states@[k]);
        }
    }
    assert(dfa.states@[0] == old(dfa).states@[0]);
}

/// Computes and records the transition from state `cur` over `b`.
fn dfa_trans(prog: &Prog, dfa: &mut Dfa, cur: usize, b: u8) -> (r: (u32, Ghost<int>))
    requires
        prog.wf(),
        old(dfa).wf(prog),
        cur < old(dfa).states@.len(),
        b < 128,
    ensures
        final(dfa).wf(prog),
        final(dfa).s0 == old(dfa).s0,
        old(dfa).states@.len() <= final(dfa).states@.len(),
        forall|k: int| 0 <= k < old(dfa).states@.len() ==> #[trigger] final(dfa).states@[k] == old(dfa).states@[k],
        r.0 == STOP || (r.0 < final(dfa).states@.len() && step_ok(
            prog.sp(),
            old(dfa).states@[cur as int]@,
            old(dfa).s0@,
            b,
            final(dfa).states@[r.0 as int]@,
        )),
        0 <= r.1@ <= trans_cost(prog.insts@.len() as int),
{
    let ghost sp = prog.sp();
    let ghost d = dfa.states@[cur as int]@;
    let ghost s0 = dfa.s0@;
    let np = prog.insts.len();
    assert(sp =~= pv(prog.insts@, prog.classes@));
    assert(closed(sp, d));
    let (sd, c1) = seeds(prog, &dfa.states[cur], &dfa.s0, b);
    let mut d2 = match sd {
        Some(d2) => d2,
        None => {
            set_trans(prog, dfa, cur, b, STOP);
            return (STOP, Ghost(c1@));
        },
    };
    let ghost sds = d2@;
    eps_close(&prog.insts, &mut d2, Ghost(prog.classes@));
    proof {
        assert forall|q: int| 0 <= q < np && #[trigger] live(d, s0, q) implies match sp[q] {
            SInst::Match => false,
            SInst::Char { cls, next } => cls.contains(b as u32) ==> 0 <= next < np && d2@[next],
            _ => true,
        } by {
            match sp[q] {
                SInst::Char { cls, next } => {
                    if cls.contains(b as u32) {
                        assert(sds[next]);
                    }
                },
                _ => {},
            }
        }
        assert(step_ok(sp, d, s0, b, d2@));
        assert forall|k: int| 0 <= k < dfa.states@.len() implies (#[trigger] dfa.states@[k])@.len() == d2@.len() by {
            assert(closed(sp, dfa.states@[k]@));
        }
    }
    let ns = dfa.states.len();
    let (found, c2) = find_state(&dfa.states, &d2);
    proof {
        assert(ns * np <= 256 * np) by (nonlinear_arith)
            requires
                ns <= 256,
                np >= 0,
        ;
    }
    if found == ns {
        if ns >= DFA_MAX_STATES || np > DFA_MAX_FLAGS / (ns + 1) {
            // Out of budget: leave this transition to the Pike VM.
            set_trans(prog, dfa, cur, b, STOP);
            return (STOP, Ghost(c1@ + np + c2@));
        }
        add_state(prog, dfa, d2);
    }
    set_trans(prog, dfa, cur, b, found as u32);
    (found as u32, Ghost(c1@ + np + c2@ + 128))
}

/// `skip_run` when `b` is the only byte that can begin a match. Kept out
/// of line so the callers' loops stay small.
#[inline(never)]
fn skip_find(prog: &Prog, s: &[u8], p: usize, b: u8) -> (r: (usize, Ghost<int>))
    requires
        prog.wf(),
        prog.skip@.len() == 256,
        prog.lead1 == Some(b),
        p <= s@.len(),
    ensures
        p <= r.0 <= s@.len(),
        r.0 < s@.len() ==> prog.skip@[s@[r.0 as int] as int],
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
        0 <= r.1@ <= 3 * (r.0 - p) + 1,
        r.0 > p ==> r.1@ <= 3 * (r.0 - p),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    let mut q = p;
    let ghost mut cost: int = 0;
    // Each find stops at `b`; `b` itself may not be flagged.
    loop
        invariant
            n == s@.len(),
            prog.wf(),
            prog.skip@.len() == 256,
            prog.lead1 == Some(b),
            sp == prog.sp(),
            st == prog.start,
            ns == prog.nslots,
            p <= q <= n,
            search_p(sp, s@, st, p as int, ns) == search_p(sp, s@, st, q as int, ns),
            0 <= cost <= 3 * (q - p),
            q > p ==> cost <= 3 * (q - p) - 1,
        decreases n - q,
    {
        let (e, fc) = crate::find::find_byte(s, q, b);
        proof {
            crate::skip::lemma_skip_range(sp, s@, st, q as int, e as int, ns, prog.reach@, prog.skip@);
        }
        if e >= n {
            return (e, Ghost(cost + fc@));
        }
        if prog.skip[b as usize] {
            // The byte after must be one the pattern can go on with.
            if b >= 0x80 || prog.next2.len() != 256 || (e + 1 < n && prog.next2[s[e + 1] as usize]) {
                return (e, Ghost(cost + fc@));
            }
            proof {
                crate::skip::lemma_pair(sp, s@, st, e as int, ns, prog.reach@, prog.skip@, prog.reach2@, prog.next2@);
            }
        } else {
            proof {
                crate::skip::lemma_skip(sp, s@, st, e as int, ns, prog.reach@, prog.skip@);
            }
        }
        proof {
            cost = cost + fc@ + 1;
        }
        q = e + 1;
    }
}

/// `skip_run` when the bytes that can begin a match lie in the ranges
/// `r`: looks for such a byte 16 bytes at a time.
#[inline(never)]
fn skip_rng(prog: &Prog, s: &[u8], p: usize, r: (u8, u8, u8, u8, u8, u8)) -> (x: (usize, Ghost<int>))
    requires
        prog.wf(),
        prog.skip@.len() == 256,
        prog.rng == Some(r),
        p <= s@.len(),
    ensures
        p <= x.0 <= s@.len(),
        x.0 < s@.len() ==> prog.skip@[s@[x.0 as int] as int],
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            x.0 as int,
            prog.nslots as nat,
        ),
        0 <= x.1@ <= 3 * (x.0 - p) + 1,
        x.0 > p ==> x.1@ <= 3 * (x.0 - p),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    let mut q = p;
    let ghost mut cost: int = 0;
    // Each find stops at a byte in the ranges, which may not be flagged.
    loop
        invariant
            n == s@.len(),
            prog.wf(),
            prog.skip@.len() == 256,
            prog.rng == Some(r),
            sp == prog.sp(),
            st == prog.start,
            ns == prog.nslots,
            p <= q <= n,
            search_p(sp, s@, st, p as int, ns) == search_p(sp, s@, st, q as int, ns),
            0 <= cost <= 3 * (q - p),
            q > p ==> cost <= 3 * (q - p) - 1,
        decreases n - q,
    {
        let (e, fc) = crate::find::find_rng(s, q, r);
        proof {
            assert forall|j: int| q <= j < e implies !#[trigger] prog.skip@[s@[j] as int] by {
                assert(!crate::find::inr(s@[j], r));
            }
            crate::skip::lemma_skip_range(sp, s@, st, q as int, e as int, ns, prog.reach@, prog.skip@);
        }
        if e >= n {
            return (e, Ghost(cost + fc@));
        }
        if prog.skip[s[e] as usize] {
            return (e, Ghost(cost + fc@));
        }
        proof {
            crate::skip::lemma_skip(sp, s@, st, e as int, ns, prog.reach@, prog.skip@);
            cost = cost + fc@ + 1;
        }
        q = e + 1;
    }
}

/// `skip_run` when every match starts with one of two ASCII bytes and
/// goes on with one of two bytes: looks for such a pair 16 bytes at a
/// time.
#[inline(never)]
fn skip_pair(prog: &Prog, s: &[u8], p: usize, q4: (u8, u8, u8, u8)) -> (r: (usize, Ghost<int>))
    requires
        prog.wf(),
        prog.skip@.len() == 256,
        prog.pair == Some(q4),
        p <= s@.len(),
    ensures
        p <= r.0 <= s@.len(),
        r.0 < s@.len() ==> prog.skip@[s@[r.0 as int] as int],
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
        0 <= r.1@ <= 3 * (r.0 - p) + 1,
        r.0 > p ==> r.1@ <= 3 * (r.0 - p),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    let mut q = p;
    let ghost mut cost: int = 0;
    loop
        invariant
            n == s@.len(),
            prog.wf(),
            prog.skip@.len() == 256,
            prog.pair == Some(q4),
            sp == prog.sp(),
            st == prog.start,
            ns == prog.nslots,
            p <= q <= n,
            search_p(sp, s@, st, p as int, ns) == search_p(sp, s@, st, q as int, ns),
            0 <= cost <= 3 * (q - p),
            q > p ==> cost <= 3 * (q - p) - 1,
        decreases n - q,
    {
        let (e, fc) = crate::find::find_pair(s, q, q4);
        proof {
            assert forall|j: int| q <= j < e implies (#[trigger] pm(sp, s@, st, j, unset(ns))).len() == 0 by {
                assert(!crate::find::cand(s@, j, q4));
                if s@[j] == q4.0 || s@[j] == q4.1 {
                    crate::skip::lemma_pair(sp, s@, st, j, ns, prog.reach@, prog.skip@, prog.reach2@, prog.next2@);
                } else {
                    crate::skip::lemma_skip_pm(sp, s@, st, j, unset(ns), prog.reach@, prog.skip@);
                }
            }
            lemma_none_from(sp, s@, st, q as int, e as int, ns);
        }
        if e >= n || prog.skip[s[e] as usize] {
            return (e, Ghost(cost + fc@));
        }
        proof {
            crate::skip::lemma_skip(sp, s@, st, e as int, ns, prog.reach@, prog.skip@);
            cost = cost + fc@ + 1;
        }
        q = e + 1;
    }
}

/// Passes over bytes that cannot begin a match, from `p`: 16 at a time
/// if only one byte can, or if the first two bytes are each one of two. The third result counts loop iterations.
#[inline(always)]
pub fn skip_run(prog: &Prog, s: &[u8], p: usize) -> (r: (usize, Ghost<int>))
    requires
        prog.wf(),
        prog.skip@.len() == 256,
        p <= s@.len(),
    ensures
        p <= r.0 <= s@.len(),
        r.0 < s@.len() ==> prog.skip@[s@[r.0 as int] as int],
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
        0 <= r.1@ <= 3 * (r.0 - p) + 1,
        r.0 > p ==> r.1@ <= 3 * (r.0 - p),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    // A pair costs more per block than one byte, so it is for first
    // bytes that are common in text: lower-case letters and the space.
    // With two first bytes it is the only fast scan there is.
    if let Some(q4) = prog.pair {
        if q4.0 != q4.1 || (q4.0 >= 0x61 && q4.0 <= 0x7A) || q4.0 == 0x20 {
            return skip_pair(prog, s, p, q4);
        }
    }
    match prog.lead1 {
        Some(b) => skip_find(prog, s, p, b),
        None => {
            if let Some(r) = prog.rng {
                // Worth a call only past a byte that cannot begin one.
                if p < n && !prog.skip[s[p] as usize] {
                    return skip_rng(prog, s, p, r);
                }
            }
            let mut q = p;
            while q < n && !prog.skip[s[q] as usize]
                invariant
                    n == s@.len(),
                    prog.wf(),
                    prog.skip@.len() == 256,
                    sp == prog.sp(),
                    st == prog.start,
                    ns == prog.nslots,
                    p <= q <= n,
                    search_p(sp, s@, st, p as int, ns) == search_p(sp, s@, st, q as int, ns),
                decreases n - q,
            {
                proof {
                    crate::skip::lemma_skip(sp, s@, st, q as int, ns, prog.reach@, prog.skip@);
                }
                q += 1;
            }
            (q, Ghost(q - p))
        },
    }
}

/// From byte `p`, with no thread alive: steps the DFA as far as it goes.
/// Gives `(q, e)`: the search may resume at `q`, and the DFA read up to
/// `e`.
pub fn dfa_ahead(prog: &Prog, s: &[u8], p: usize, dfa: &mut Dfa, nst: &mut NeedSt) -> (r: (
    usize,
    usize,
    Ghost<int>,
    Ghost<int>,
))
    requires
        prog.wf(),
        old(dfa).wf(prog),
        p <= s@.len(),
        prog.need matches Some(x) ==> old(nst).inv(s@, x) && (old(nst).have ==> old(nst).lo <= p),
        !old(nst).have ==> old(nst).h <= p,
    ensures
        final(dfa).wf(prog),
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
        p <= r.0 <= r.1 <= s@.len(),
        search_p(prog.sp(), s@, prog.start as int, p as int, prog.nslots as nat) == search_p(
            prog.sp(),
            s@,
            prog.start as int,
            r.0 as int,
            prog.nslots as nat,
        ),
        0 <= r.2@ <= (r.1 - p + 1) * (trans_cost(prog.insts@.len() as int) + 2),
{
    let n = s.len();
    let ghost sp = prog.sp();
    let ghost st = prog.start as int;
    let ghost ns = prog.nslots as nat;
    let ghost tc = trans_cost(prog.insts@.len() as int) + 2;
    let ghost mut cost: int = 0;
    let mut q = p;
    let mut p0 = p;
    let mut cur: usize = 0;
    let sk = dfa.sparse && prog.skip.len() == 256;
    let ghost mut ncost: int = 0;
    let ghost h0 = nst.h;
    let ghost have0 = nst.have;
    proof {
        assert(0 * tc == 0) by (nonlinear_arith);
    }
    loop
        invariant
            prog.need matches Some(x) ==> nst.inv(s@, x) && (nst.have ==> nst.lo <= p0),
            prog.need is None ==> *nst == *old(nst),
            have0 ==> nst.have,
            h0 == old(nst).h,
            have0 == old(nst).have,
            h0 <= nst.h,
            !nst.have ==> nst.h == h0 && h0 <= q,
            0 <= ncost <= 2 * (nst.h - h0) + if have0 || !nst.have {
                0int
            } else {
                1int
            },
            n == s@.len(),
            prog.wf(),
            dfa.wf(prog),
            sp == prog.sp(),
            st == prog.start,
            ns == prog.nslots,
            tc == trans_cost(prog.insts@.len() as int) + 2,
            tc >= 2,
            p <= p0 <= q <= n,
            cur < dfa.states@.len(),
            search_p(sp, s@, st, p as int, ns) == search_p(sp, s@, st, p0 as int, ns),
            flows(sp, s@, st, ns, p0 as int, q as int, dfa.states@[cur as int]@),
            0 <= cost <= (q - p) * tc,
            cur == 0 ==> p0 == q,
            sk ==> prog.skip@.len() == 256,
        decreases n - q,
    {
        let ghost q_in = q;
        if cur == 0 && q < n {
            if let Some(x) = prog.need {
                if !nst.have || q > nst.k {
                    // Where the next byte every match needs is.
                    let (k, fc) = find_byte(s, q, x);
                    nst.have = true;
                    nst.lo = q;
                    nst.k = k;
                    nst.h = k;
                    let ghost g = prog.needg@;
                    let ghost w = prog.needw@;
                    let ghost al = prog.alpha@;
                    let ghost qa = q;
                    let ghost nc0 = ncost + fc@;
                    proof {
                        ncost = nc0;
                    }
                    assert(forall|t: int| q <= t < k ==> #[trigger] s@[t] != x);
                    if k == n {
                        // There is none: nothing matches from here on.
                        proof {
                            lemma_need_end(sp, s@, st, ns, x, g, w, q as int);
                        }
                        q = n;
                        p0 = q;
                    } else if q < k {
                        // No match starts before the run of bytes the
                        // pattern can consume that leads up to it.
                        let mut j = k;
                        while j > q && prog.alpha[s[j - 1] as usize]
                            invariant
                                q <= j <= k,
                                k <= n,
                                n == s@.len(),
                                prog.alpha@.len() == 256,
                                ncost == nc0 + (k - j),
                            decreases j,
                        {
                            j -= 1;
                            proof {
                                ncost = ncost + 1;
                            }
                        }
                        if j > q {
                            proof {
                                lemma_need_jump(sp, s@, st, ns, x, g, w, al, q as int, j as int, k as int);
                            }
                            q = j;
                            p0 = q;
                        }
                    }
                    proof {
                        assert((q - p) * tc >= (qa - p) * tc) by (nonlinear_arith)
                            requires
                                q >= qa,
                                tc >= 0,
                        ;
                    }
                }
            }
        }
        if sk && cur == 0 {
            // In the empty state only a byte that can start a match matters.
            if q < n && !prog.skip[s[q] as usize] {
                let (q2, kc) = skip_run(prog, s, q);
                proof {
                    assert((q2 - p) * tc >= (q - p) * tc + 3 * (q2 - q)) by (nonlinear_arith)
                        requires
                            q2 >= q,
                            tc >= 3,
                    ;
                    cost = cost + kc@;
                }
                q = q2;
            }
            p0 = q;
        }
        proof {
            assert((q - p + 1) * tc == (q - p) * tc + tc) by (nonlinear_arith);
        }
        if q >= n {
            return (p0, q, Ghost(cost), Ghost(ncost));
        }
        let b = s[q];
        if b >= 0x80 {
            return (p0, q, Ghost(cost), Ghost(ncost));
        }
        let ix = cur * 128 + b as usize;
        assert(ix == tix(cur as int, b as int));
        let ghost d = dfa.states@[cur as int]@;
        let mut v = dfa.trans[ix];
        proof {
            cost = cost + 1;
        }
        if v == UNK {
            let (v2, tcst) = dfa_trans(prog, dfa, cur, b);
            v = v2;
            proof {
                cost = cost + tcst@;
            }
        }
        if v == STOP {
            return (p0, q, Ghost(cost), Ghost(ncost));
        }
        proof {
            assert(dfa.states@[cur as int]@ == d);
            assert(closed(sp, dfa.states@[cur as int]@));
            lemma_flows_step(sp, s@, st, ns, p0 as int, q as int, d, dfa.s0@, dfa.states@[v as int]@);
        }
        cur = v as usize;
        q += 1;
        if cur == 0 {
            proof {
                lemma_flows_empty(sp, s@, st, ns, p0 as int, q as int, dfa.states@[0]@);
            }
            p0 = q;
        }
    }
}

} // verus!
