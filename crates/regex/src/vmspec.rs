//! The Pike VM as mathematics: threads, the threads reached without
//! consuming, and why keeping one thread per instruction loses nothing.
use crate::sem::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A thread: an instruction and capture slots.
pub ghost struct T {
    pub pc: int,
    pub caps: Seq<int>,
}

/// The threads waiting at a `Char` or at `Match` that `pc` reaches at byte
/// `i` without consuming, in priority order.
pub open spec fn eclo(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>) -> Seq<T>
    decreases p.len() - pc,
{
    if pc < 0 || pc >= p.len() {
        seq![]
    } else {
        match p[pc] {
            SInst::Match => seq![T { pc: pc, caps: c }],
            SInst::Char { cls, next } => seq![T { pc: pc, caps: c }],
            SInst::Fail => seq![],
            SInst::Split { a, b } => (if pc < a < p.len() {
                eclo(p, s, i, a, c)
            } else {
                seq![]
            }) + (if pc < b < p.len() {
                eclo(p, s, i, b, c)
            } else {
                seq![]
            }),
            SInst::Save { slot, next } => if pc < next < p.len() {
                eclo(p, s, i, next, c.update(slot, i))
            } else {
                seq![]
            },
            SInst::Look { k, next } => if pc < next < p.len() && look_holds(k, s, i) {
                eclo(p, s, i, next, c)
            } else {
                seq![]
            },
        }
    }
}

/// The instructions of `eclo`, which do not depend on the capture slots.
pub open spec fn epcs(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int) -> Seq<int>
    decreases p.len() - pc,
{
    if pc < 0 || pc >= p.len() {
        seq![]
    } else {
        match p[pc] {
            SInst::Match => seq![pc],
            SInst::Char { cls, next } => seq![pc],
            SInst::Fail => seq![],
            SInst::Split { a, b } => (if pc < a < p.len() {
                epcs(p, s, i, a)
            } else {
                seq![]
            }) + (if pc < b < p.len() {
                epcs(p, s, i, b)
            } else {
                seq![]
            }),
            SInst::Save { slot, next } => if pc < next < p.len() {
                epcs(p, s, i, next)
            } else {
                seq![]
            },
            SInst::Look { k, next } => if pc < next < p.len() && look_holds(k, s, i) {
                epcs(p, s, i, next)
            } else {
                seq![]
            },
        }
    }
}

pub open spec fn pcs_of(ts: Seq<T>) -> Seq<int> {
    Seq::new(ts.len(), |k: int| ts[k].pc)
}

pub proof fn lemma_epcs(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>)
    ensures
        pcs_of(eclo(p, s, i, pc, c)) =~= epcs(p, s, i, pc),
    decreases p.len() - pc,
{
    if 0 <= pc < p.len() {
        match p[pc] {
            SInst::Split { a, b } => {
                if pc < a < p.len() {
                    lemma_epcs(p, s, i, a, c);
                }
                if pc < b < p.len() {
                    lemma_epcs(p, s, i, b, c);
                }
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_epcs(p, s, i, next, c.update(slot, i));
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_epcs(p, s, i, next, c);
                }
            },
            _ => {},
        }
    }
}

/// Every match thread `t` leads to from byte `i`, best first.
pub open spec fn pmt(p: Seq<SInst>, s: Seq<u8>, t: T, i: int) -> Seq<M> {
    if t.pc < 0 || t.pc >= p.len() || i < 0 || i > s.len() {
        seq![]
    } else {
        match p[t.pc] {
            SInst::Match => seq![M { end: i, caps: t.caps }],
            SInst::Char { cls, next } => match dec(s, i) {
                Some((cp, l)) => if cls.contains(cp) && l >= 1 {
                    pm(p, s, next, i + l, t.caps)
                } else {
                    seq![]
                },
                None => seq![],
            },
            _ => seq![],
        }
    }
}

/// Every match the threads `ts`, in order, lead to from byte `i`.
pub open spec fn res(p: Seq<SInst>, s: Seq<u8>, ts: Seq<T>, i: int) -> Seq<M>
    decreases ts.len(),
{
    if ts.len() == 0 {
        seq![]
    } else {
        pmt(p, s, ts[0], i) + res(p, s, ts.drop_first(), i)
    }
}

pub proof fn lemma_res_app(p: Seq<SInst>, s: Seq<u8>, a: Seq<T>, b: Seq<T>, i: int)
    ensures
        res(p, s, a + b, i) == res(p, s, a, i) + res(p, s, b, i),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_res_app(p, s, a.drop_first(), b, i);
    }
}

pub proof fn lemma_res_one(p: Seq<SInst>, s: Seq<u8>, t: T, i: int)
    ensures
        res(p, s, seq![t], i) == pmt(p, s, t, i),
{
    assert(seq![t].drop_first() =~= Seq::<T>::empty());
    assert(res(p, s, Seq::<T>::empty(), i) =~= Seq::<M>::empty());
}

/// A program run is the run of the threads it reaches.
pub proof fn lemma_pm_eclo(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c: Seq<int>)
    requires
        0 <= i <= s.len(),
    ensures
        pm(p, s, pc, i, c) == res(p, s, eclo(p, s, i, pc, c), i),
    decreases p.len() - pc,
{
    if 0 <= pc < p.len() {
        match p[pc] {
            SInst::Match => {
                lemma_res_one(p, s, T { pc: pc, caps: c }, i);
            },
            SInst::Char { cls, next } => {
                lemma_res_one(p, s, T { pc: pc, caps: c }, i);
            },
            SInst::Fail => {},
            SInst::Split { a, b } => {
                let ea = if pc < a < p.len() {
                    eclo(p, s, i, a, c)
                } else {
                    seq![]
                };
                let eb = if pc < b < p.len() {
                    eclo(p, s, i, b, c)
                } else {
                    seq![]
                };
                if pc < a < p.len() {
                    lemma_pm_eclo(p, s, a, i, c);
                }
                if pc < b < p.len() {
                    lemma_pm_eclo(p, s, b, i, c);
                }
                lemma_res_app(p, s, ea, eb, i);
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_pm_eclo(p, s, next, i, c.update(slot, i));
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_pm_eclo(p, s, next, i, c);
                }
            },
        }
    }
}

/// How many matches there are does not depend on the capture slots.
pub proof fn lemma_pm_len(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c1: Seq<int>, c2: Seq<int>)
    ensures
        pm(p, s, pc, i, c1).len() == pm(p, s, pc, i, c2).len(),
    decreases s.len() - i + 1, p.len() - pc,
{
    if !(pc < 0 || pc >= p.len() || i < 0 || i > s.len()) {
        match p[pc] {
            SInst::Match => {},
            SInst::Fail => {},
            SInst::Char { cls, next } => {
                match dec(s, i) {
                    Some((cp, l)) => {
                        if cls.contains(cp) && l >= 1 {
                            lemma_pm_len(p, s, next, i + l, c1, c2);
                        }
                    },
                    None => {},
                }
            },
            SInst::Split { a, b } => {
                if pc < a < p.len() {
                    lemma_pm_len(p, s, a, i, c1, c2);
                }
                if pc < b < p.len() {
                    lemma_pm_len(p, s, b, i, c1, c2);
                }
            },
            SInst::Save { slot, next } => {
                if pc < next < p.len() {
                    lemma_pm_len(p, s, next, i, c1.update(slot, i), c2.update(slot, i));
                }
            },
            SInst::Look { k, next } => {
                if pc < next < p.len() && look_holds(k, s, i) {
                    lemma_pm_len(p, s, next, i, c1, c2);
                }
            },
        }
    }
}

pub proof fn lemma_pmt_len(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c1: Seq<int>, c2: Seq<int>)
    ensures
        pmt(p, s, T { pc: pc, caps: c1 }, i).len() == pmt(p, s, T { pc: pc, caps: c2 }, i).len(),
{
    if !(pc < 0 || pc >= p.len() || i < 0 || i > s.len()) {
        match p[pc] {
            SInst::Char { cls, next } => {
                match dec(s, i) {
                    Some((cp, l)) => {
                        lemma_pm_len(p, s, next, i + l, c1, c2);
                    },
                    None => {},
                }
            },
            _ => {},
        }
    }
}

pub open spec fn first(l: Seq<M>) -> Option<M> {
    if l.len() > 0 {
        Some(l[0])
    } else {
        None
    }
}

pub open spec fn or(a: Option<M>, b: Option<M>) -> Option<M> {
    match a {
        Some(_) => a,
        None => b,
    }
}

/// The best match the threads `ts` lead to from byte `i`.
pub open spec fn fr(p: Seq<SInst>, s: Seq<u8>, ts: Seq<T>, i: int) -> Option<M> {
    first(res(p, s, ts, i))
}

pub proof fn lemma_fr_app(p: Seq<SInst>, s: Seq<u8>, a: Seq<T>, b: Seq<T>, i: int)
    ensures
        fr(p, s, a + b, i) == or(fr(p, s, a, i), fr(p, s, b, i)),
{
    lemma_res_app(p, s, a, b, i);
}

/// `ts` without the threads whose instruction is in `seen` or occurred
/// earlier in `ts`.
pub open spec fn dd(ts: Seq<T>, seen: ISet<int>) -> Seq<T>
    decreases ts.len(),
{
    if ts.len() == 0 {
        seq![]
    } else if seen.contains(ts[0].pc) {
        dd(ts.drop_first(), seen)
    } else {
        seq![ts[0]] + dd(ts.drop_first(), seen.insert(ts[0].pc))
    }
}

/// The instructions of the threads `ts`.
pub open spec fn pcset(ts: Seq<T>) -> ISet<int> {
    ISet::new(|x: int| exists|k: int| 0 <= k < ts.len() && (#[trigger] ts[k]).pc == x)
}

/// No thread at `pc` leads to a match from byte `i`.
pub open spec fn dead(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int) -> bool {
    forall|c: Seq<int>| (#[trigger] pmt(p, s, T { pc: pc, caps: c }, i)).len() == 0
}

/// Dropping threads whose instruction was seen does not change the best
/// match, if the seen ones lead nowhere.
pub proof fn lemma_dd(p: Seq<SInst>, s: Seq<u8>, ts: Seq<T>, seen: ISet<int>, i: int)
    requires
        forall|x: int| seen.contains(x) ==> dead(p, s, x, i),
    ensures
        fr(p, s, dd(ts, seen), i) == fr(p, s, ts, i),
    decreases ts.len(),
{
    if ts.len() > 0 {
        let t = ts[0];
        assert(t == T { pc: t.pc, caps: t.caps });
        if seen.contains(t.pc) {
            assert(pmt(p, s, T { pc: t.pc, caps: t.caps }, i).len() == 0);
            lemma_dd(p, s, ts.drop_first(), seen, i);
            assert(res(p, s, ts, i) =~= res(p, s, ts.drop_first(), i));
        } else {
            let rest = dd(ts.drop_first(), seen.insert(t.pc));
            lemma_res_app(p, s, seq![t], rest, i);
            lemma_res_one(p, s, t, i);
            if pmt(p, s, t, i).len() == 0 {
                assert forall|x: int| seen.insert(t.pc).contains(x) implies dead(p, s, x, i) by {
                    if x == t.pc {
                        assert forall|c: Seq<int>| (#[trigger] pmt(p, s, T { pc: x, caps: c }, i)).len() == 0 by {
                            lemma_pmt_len(p, s, x, i, c, t.caps);
                        }
                    }
                }
                lemma_dd(p, s, ts.drop_first(), seen.insert(t.pc), i);
                assert(res(p, s, ts, i) =~= res(p, s, ts.drop_first(), i));
                assert(res(p, s, seq![t] + rest, i) =~= res(p, s, rest, i));
            }
        }
    }
}

/// If the threads `l` lead nowhere, each of their instructions is dead.
pub proof fn lemma_none_dead(p: Seq<SInst>, s: Seq<u8>, l: Seq<T>, i: int)
    requires
        fr(p, s, l, i).is_none(),
    ensures
        forall|x: int| pcset(l).contains(x) ==> dead(p, s, x, i),
    decreases l.len(),
{
    if l.len() > 0 {
        let t = l[0];
        assert(pmt(p, s, t, i).len() == 0);
        assert(res(p, s, l, i) =~= res(p, s, l.drop_first(), i));
        lemma_none_dead(p, s, l.drop_first(), i);
        assert forall|x: int| pcset(l).contains(x) implies dead(p, s, x, i) by {
            let k = choose|k: int| 0 <= k < l.len() && (#[trigger] l[k]).pc == x;
            if k == 0 {
                assert(t == T { pc: t.pc, caps: t.caps });
                assert forall|c: Seq<int>| (#[trigger] pmt(p, s, T { pc: x, caps: c }, i)).len() == 0 by {
                    lemma_pmt_len(p, s, x, i, c, t.caps);
                }
            } else {
                assert(l.drop_first()[k - 1] == l[k]);
                assert(pcset(l.drop_first()).contains(x));
            }
        }
    }
}

/// Adding the threads of `y` that are not already in `l`, after `l`, is
/// as good as adding all of `y`.
pub proof fn lemma_add(p: Seq<SInst>, s: Seq<u8>, l: Seq<T>, y: Seq<T>, i: int)
    ensures
        fr(p, s, l + dd(y, pcset(l)), i) == or(fr(p, s, l, i), fr(p, s, y, i)),
{
    lemma_fr_app(p, s, l, dd(y, pcset(l)), i);
    if fr(p, s, l, i).is_none() {
        lemma_none_dead(p, s, l, i);
        lemma_dd(p, s, y, pcset(l), i);
    }
}


// ---------------------------------------------------------------------------
// The marking search
// ---------------------------------------------------------------------------

/// `eclo` as the matcher computes it: instructions in `seen` are skipped
/// and every instruction visited joins `seen`.
pub open spec fn ecd(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>, seen: Set<int>) -> (Seq<T>, Set<int>)
    decreases p.len() - pc,
{
    if pc < 0 || pc >= p.len() || seen.contains(pc) {
        (seq![], seen)
    } else {
        let sn = seen.insert(pc);
        match p[pc] {
            SInst::Match => (seq![T { pc: pc, caps: c }], sn),
            SInst::Char { cls, next } => (seq![T { pc: pc, caps: c }], sn),
            SInst::Fail => (seq![], sn),
            SInst::Split { a, b } => {
                let r1 = if pc < a < p.len() {
                    ecd(p, s, i, a, c, sn)
                } else {
                    (seq![], sn)
                };
                let r2 = if pc < b < p.len() {
                    ecd(p, s, i, b, c, r1.1)
                } else {
                    (seq![], r1.1)
                };
                (r1.0 + r2.0, r2.1)
            },
            SInst::Save { slot, next } => if pc < next < p.len() {
                ecd(p, s, i, next, c.update(slot, i), sn)
            } else {
                (seq![], sn)
            },
            SInst::Look { k, next } => if pc < next < p.len() && look_holds(k, s, i) {
                ecd(p, s, i, next, c, sn)
            } else {
                (seq![], sn)
            },
        }
    }
}

/// A frame of the matcher's stack: an instruction to explore, or a
/// capture slot to put back.
pub ghost enum F {
    Ex(int),
    Re(int, int),
}

/// What the matcher's stack still has to produce, top (last) first.
pub open spec fn wk(p: Seq<SInst>, s: Seq<u8>, i: int, st: Seq<F>, c: Seq<int>, seen: Set<int>) -> (Seq<T>, Set<int>)
    decreases st.len(),
{
    if st.len() == 0 {
        (seq![], seen)
    } else {
        match st.last() {
            F::Re(slot, old) => wk(p, s, i, st.drop_last(), c.update(slot, old), seen),
            F::Ex(pc) => {
                let r1 = ecd(p, s, i, pc, c, seen);
                let r2 = wk(p, s, i, st.drop_last(), c, r1.1);
                (r1.0 + r2.0, r2.1)
            },
        }
    }
}

pub proof fn lemma_wk_ex(p: Seq<SInst>, s: Seq<u8>, i: int, st: Seq<F>, pc: int, c: Seq<int>, seen: Set<int>)
    ensures
        wk(p, s, i, st.push(F::Ex(pc)), c, seen) == ({
            let r1 = ecd(p, s, i, pc, c, seen);
            let r2 = wk(p, s, i, st, c, r1.1);
            (r1.0 + r2.0, r2.1)
        }),
{
    assert(st.push(F::Ex(pc)).drop_last() =~= st);
}

pub proof fn lemma_wk_re(
    p: Seq<SInst>,
    s: Seq<u8>,
    i: int,
    st: Seq<F>,
    slot: int,
    old: int,
    c: Seq<int>,
    seen: Set<int>,
)
    ensures
        wk(p, s, i, st.push(F::Re(slot, old)), c, seen) == wk(p, s, i, st, c.update(slot, old), seen),
{
    assert(st.push(F::Re(slot, old)).drop_last() =~= st);
}

/// Every thread `v` reaches without consuming is in `lp`.
pub open spec fn closed_at(p: Seq<SInst>, s: Seq<u8>, i: int, v: int, lp: ISet<int>) -> bool {
    forall|k: int| 0 <= k < epcs(p, s, i, v).len() ==> lp.contains(#[trigger] epcs(p, s, i, v)[k])
}

pub open spec fn un(a: ISet<int>, b: ISet<int>) -> ISet<int> {
    ISet::new(|x: int| a.contains(x) || b.contains(x))
}

pub proof fn lemma_dd_all_seen(ts: Seq<T>, seen: ISet<int>)
    requires
        forall|k: int| 0 <= k < ts.len() ==> seen.contains((#[trigger] ts[k]).pc),
    ensures
        dd(ts, seen) == Seq::<T>::empty(),
    decreases ts.len(),
{
    if ts.len() > 0 {
        assert(seen.contains(ts[0].pc));
        assert forall|k: int| 0 <= k < ts.drop_first().len() implies seen.contains((#[trigger] ts.drop_first()[k]).pc) by {
            assert(ts.drop_first()[k] == ts[k + 1]);
        }
        lemma_dd_all_seen(ts.drop_first(), seen);
    }
}

pub proof fn lemma_pcset_first(x: Seq<T>)
    requires
        x.len() > 0,
    ensures
        pcset(x) =~= pcset(x.drop_first()).insert(x[0].pc),
{
    let a = pcset(x);
    let b = pcset(x.drop_first()).insert(x[0].pc);
    assert forall|v: int| a.contains(v) implies b.contains(v) by {
        let k = choose|k: int| 0 <= k < x.len() && (#[trigger] x[k]).pc == v;
        if k > 0 {
            assert(x.drop_first()[k - 1] == x[k]);
        }
    }
    assert forall|v: int| b.contains(v) implies a.contains(v) by {
        if v == x[0].pc {
            assert(x[0].pc == v);
        } else {
            let k = choose|k: int| 0 <= k < x.drop_first().len() && (#[trigger] x.drop_first()[k]).pc == v;
            assert(x[k + 1].pc == v);
        }
    }
}

pub proof fn lemma_pcset_app(x: Seq<T>, y: Seq<T>)
    ensures
        pcset(x + y) =~= un(pcset(x), pcset(y)),
{
    let a = pcset(x + y);
    let b = un(pcset(x), pcset(y));
    assert forall|v: int| a.contains(v) implies b.contains(v) by {
        let k = choose|k: int| 0 <= k < (x + y).len() && (#[trigger] (x + y)[k]).pc == v;
        if k < x.len() {
            assert(x[k].pc == v);
        } else {
            assert(y[k - x.len()].pc == v);
        }
    }
    assert forall|v: int| b.contains(v) implies a.contains(v) by {
        if pcset(x).contains(v) {
            let k = choose|k: int| 0 <= k < x.len() && (#[trigger] x[k]).pc == v;
            assert((x + y)[k].pc == v);
        } else {
            let k = choose|k: int| 0 <= k < y.len() && (#[trigger] y[k]).pc == v;
            assert((x + y)[k + x.len()].pc == v);
        }
    }
}

/// What `dd` keeps, together with `seen`, covers all of `x`.
pub proof fn lemma_dd_pcs(x: Seq<T>, seen: ISet<int>)
    ensures
        un(seen, pcset(dd(x, seen))) =~= un(seen, pcset(x)),
    decreases x.len(),
{
    if x.len() == 0 {
    } else {
        lemma_pcset_first(x);
        if seen.contains(x[0].pc) {
            lemma_dd_pcs(x.drop_first(), seen);
        } else {
            let s2 = seen.insert(x[0].pc);
            lemma_dd_pcs(x.drop_first(), s2);
            let d = dd(x.drop_first(), s2);
            lemma_pcset_app(seq![x[0]], d);
            lemma_pcset_first(seq![x[0]]);
            assert(seq![x[0]].drop_first() =~= Seq::<T>::empty());
            assert(pcset(Seq::<T>::empty()) =~= ISet::<int>::empty());
            assert forall|v: int| un(seen, pcset(dd(x, seen))).contains(v) == un(seen, pcset(x)).contains(v) by {
                assert(un(s2, pcset(d)).contains(v) == un(s2, pcset(x.drop_first())).contains(v));
            }
        }
    }
}

pub proof fn lemma_dd_app(x: Seq<T>, y: Seq<T>, seen: ISet<int>)
    ensures
        dd(x + y, seen) == dd(x, seen) + dd(y, un(seen, pcset(x))),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
        assert(un(seen, pcset(x)) =~= seen);
    } else {
        assert((x + y).drop_first() =~= x.drop_first() + y);
        lemma_pcset_first(x);
        if seen.contains(x[0].pc) {
            lemma_dd_app(x.drop_first(), y, seen);
            assert(un(seen, pcset(x)) =~= un(seen, pcset(x.drop_first())));
        } else {
            let s2 = seen.insert(x[0].pc);
            lemma_dd_app(x.drop_first(), y, s2);
            assert(un(seen, pcset(x)) =~= un(s2, pcset(x.drop_first())));
            assert(dd(x + y, seen) =~= dd(x, seen) + dd(y, un(seen, pcset(x))));
        }
    }
}

pub proof fn lemma_closed_mono(p: Seq<SInst>, s: Seq<u8>, i: int, v: int, a: ISet<int>, b: ISet<int>)
    requires
        closed_at(p, s, i, v, a),
        forall|x: int| a.contains(x) ==> b.contains(x),
    ensures
        closed_at(p, s, i, v, b),
{
}

/// The marking search finds exactly the threads `dd` keeps, provided what
/// was marked before is fully explored.
pub proof fn lemma_ecd(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>, seen: Set<int>, lp: ISet<int>)
    requires
        fwd(p),
        forall|v: int| seen.contains(v) && v >= pc ==> closed_at(p, s, i, v, lp),
        forall|x: int| lp.contains(x) ==> seen.contains(x),
    ensures
        ({
            let r = ecd(p, s, i, pc, c, seen);
            let lp2 = un(lp, pcset(r.0));
            &&& r.0 == dd(eclo(p, s, i, pc, c), lp)
            &&& forall|v: int| #[trigger] r.1.contains(v) && v >= pc ==> closed_at(p, s, i, v, lp2)
            &&& forall|v: int| seen.contains(v) ==> #[trigger] r.1.contains(v)
            &&& forall|v: int| #[trigger] r.1.contains(v) && !seen.contains(v) ==> v >= pc && 0 <= v < p.len()
            &&& forall|x: int| lp2.contains(x) ==> #[trigger] r.1.contains(x)
            &&& (0 <= pc < p.len() ==> r.1.contains(pc))
        }),
    decreases p.len() - pc,
{
    let r = ecd(p, s, i, pc, c, seen);
    let lp2 = un(lp, pcset(r.0));
    if pc < 0 || pc >= p.len() {
        assert(pcset(r.0) =~= ISet::<int>::empty());
        assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
            lemma_closed_mono(p, s, i, v, lp, lp2);
        }
    } else if seen.contains(pc) {
        let e = eclo(p, s, i, pc, c);
        lemma_epcs(p, s, i, pc, c);
        assert forall|k: int| 0 <= k < e.len() implies lp.contains((#[trigger] e[k]).pc) by {
            assert(pcs_of(e)[k] == e[k].pc);
            assert(lp.contains(epcs(p, s, i, pc)[k]));
        }
        lemma_dd_all_seen(e, lp);
        assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
            lemma_closed_mono(p, s, i, v, lp, lp2);
        }
    } else {
        let sn = seen.insert(pc);
        assert(fwd_at(p, pc));
        assert(!lp.contains(pc));
        match p[pc] {
            SInst::Match => {
                lemma_ecd_leaf(p, s, i, pc, c, seen, lp);
            },
            SInst::Char { cls, next } => {
                lemma_ecd_leaf(p, s, i, pc, c, seen, lp);
            },
            SInst::Fail => {
                assert(pcset(r.0) =~= ISet::<int>::empty());
                assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
                    if v != pc {
                        lemma_closed_mono(p, s, i, v, lp, lp2);
                    }
                }
            },
            SInst::Split { a, b } => {
                lemma_ecd(p, s, i, a, c, sn, lp);
                let r1 = ecd(p, s, i, a, c, sn);
                let lp1 = un(lp, pcset(r1.0));
                assert forall|v: int| r1.1.contains(v) && v >= b implies closed_at(p, s, i, v, lp1) by {
                    if sn.contains(v) {
                        lemma_closed_mono(p, s, i, v, lp, lp1);
                    }
                }
                lemma_ecd(p, s, i, b, c, r1.1, lp1);
                let r2 = ecd(p, s, i, b, c, r1.1);
                let ea = eclo(p, s, i, a, c);
                let eb = eclo(p, s, i, b, c);
                lemma_dd_pcs(ea, lp);
                lemma_dd_app(ea, eb, lp);
                lemma_pcset_app(r1.0, r2.0);
                let lpb = un(lp1, pcset(r2.0));
                assert(lp2 =~= lpb);
                assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
                    if v == pc {
                        lemma_closed_mono(p, s, i, a, lp1, lp2);
                        assert(closed_at(p, s, i, b, lp2));
                        let ee = epcs(p, s, i, pc);
                        assert(ee == epcs(p, s, i, a) + epcs(p, s, i, b));
                        assert forall|k: int| 0 <= k < ee.len() implies lp2.contains(#[trigger] ee[k]) by {
                            if k < epcs(p, s, i, a).len() {
                                assert(ee[k] == epcs(p, s, i, a)[k]);
                            } else {
                                assert(ee[k] == epcs(p, s, i, b)[k - epcs(p, s, i, a).len()]);
                            }
                        }
                    } else if seen.contains(v) {
                        lemma_closed_mono(p, s, i, v, lp, lp2);
                    } else if r1.1.contains(v) {
                        assert(!sn.contains(v));
                        assert(v >= a);
                        assert(closed_at(p, s, i, v, lp1));
                        lemma_closed_mono(p, s, i, v, lp1, lp2);
                    } else {
                        assert(r2.1.contains(v));
                        assert(v >= b);
                        assert(closed_at(p, s, i, v, lpb));
                    }
                }
            },
            SInst::Save { slot, next } => {
                lemma_ecd(p, s, i, next, c.update(slot, i), sn, lp);
                assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
                    if v == pc {
                        assert(r.1.contains(next));
                        assert(closed_at(p, s, i, next, lp2));
                        assert(epcs(p, s, i, pc) == epcs(p, s, i, next));
                    } else if seen.contains(v) {
                        lemma_closed_mono(p, s, i, v, lp, lp2);
                    } else {
                        assert(!sn.contains(v));
                        assert(v >= next);
                    }
                }
            },
            SInst::Look { k, next } => {
                if look_holds(k, s, i) {
                    lemma_ecd(p, s, i, next, c, sn, lp);
                    assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
                        if v == pc {
                            assert(r.1.contains(next));
                            assert(closed_at(p, s, i, next, lp2));
                            assert(epcs(p, s, i, pc) == epcs(p, s, i, next));
                        } else if seen.contains(v) {
                            lemma_closed_mono(p, s, i, v, lp, lp2);
                        } else {
                            assert(!sn.contains(v));
                            assert(v >= next);
                        }
                    }
                } else {
                    assert(pcset(r.0) =~= ISet::<int>::empty());
                    assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
                        if v != pc {
                            lemma_closed_mono(p, s, i, v, lp, lp2);
                        }
                    }
                }
            },
        }
    }
}

proof fn lemma_ecd_leaf(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>, seen: Set<int>, lp: ISet<int>)
    requires
        0 <= pc < p.len(),
        !seen.contains(pc),
        p[pc] is Match || p[pc] is Char,
        forall|v: int| seen.contains(v) && v >= pc ==> closed_at(p, s, i, v, lp),
        forall|x: int| lp.contains(x) ==> seen.contains(x),
    ensures
        ({
            let r = ecd(p, s, i, pc, c, seen);
            let lp2 = un(lp, pcset(r.0));
            &&& r.0 == dd(eclo(p, s, i, pc, c), lp)
            &&& forall|v: int| r.1.contains(v) && v >= pc ==> closed_at(p, s, i, v, lp2)
            &&& forall|x: int| lp2.contains(x) ==> r.1.contains(x)
        }),
{
    let t = T { pc: pc, caps: c };
    let r = ecd(p, s, i, pc, c, seen);
    let lp2 = un(lp, pcset(r.0));
    assert(r.0 == seq![t]);
    assert(eclo(p, s, i, pc, c) == seq![t]);
    assert(seq![t].drop_first() =~= Seq::<T>::empty());
    assert(dd(Seq::<T>::empty(), lp.insert(pc)) =~= Seq::<T>::empty());
    assert(dd(seq![t], lp) =~= seq![t]);
    assert(seq![t][0].pc == pc);
    assert(pcset(seq![t]).contains(pc));
    assert forall|v: int| r.1.contains(v) && v >= pc implies closed_at(p, s, i, v, lp2) by {
        if v != pc {
            lemma_closed_mono(p, s, i, v, lp, lp2);
        }
    }
    assert forall|x: int| lp2.contains(x) implies r.1.contains(x) by {
        if pcset(seq![t]).contains(x) {
            let k = choose|k: int| 0 <= k < seq![t].len() && (#[trigger] seq![t][k]).pc == x;
        }
    }
}

/// Between two runs of the marking search: everything marked is fully
/// explored into the list `l`.
pub open spec fn inv_list(p: Seq<SInst>, s: Seq<u8>, i: int, seen: Set<int>, l: Seq<T>) -> bool {
    &&& forall|v: int| seen.contains(v) ==> closed_at(p, s, i, v, pcset(l))
    &&& forall|x: int| pcset(l).contains(x) ==> seen.contains(x)
    &&& forall|v: int| seen.contains(v) ==> 0 <= v < p.len()
}

/// One run of the marking search from `pc` adds to the list `l` what a
/// full run of the program from `pc` would, as far as the best match goes.
pub proof fn lemma_add_ecd(p: Seq<SInst>, s: Seq<u8>, i: int, pc: int, c: Seq<int>, seen: Set<int>, l: Seq<T>)
    requires
        fwd(p),
        inv_list(p, s, i, seen, l),
        0 <= i <= s.len(),
        0 <= pc < p.len(),
    ensures
        ({
            let r = ecd(p, s, i, pc, c, seen);
            &&& inv_list(p, s, i, r.1, l + r.0)
            &&& fr(p, s, l + r.0, i) == or(fr(p, s, l, i), first(pm(p, s, pc, i, c)))
        }),
{
    let lp = pcset(l);
    let r = ecd(p, s, i, pc, c, seen);
    lemma_ecd(p, s, i, pc, c, seen, lp);
    lemma_add(p, s, l, eclo(p, s, i, pc, c), i);
    lemma_pm_eclo(p, s, pc, i, c);
    lemma_pcset_app(l, r.0);
    let lp2 = un(lp, pcset(r.0));
    assert forall|v: int| r.1.contains(v) implies closed_at(p, s, i, v, pcset(l + r.0)) by {
        if !(v >= pc) {
            assert(seen.contains(v));
            lemma_closed_mono(p, s, i, v, lp, lp2);
        }
        assert(closed_at(p, s, i, v, lp2));
    }
}

/// The match a search of `s` from byte `i` reports, in terms of the
/// program: the best match at the first position that has one.
pub open spec fn search_p(p: Seq<SInst>, s: Seq<u8>, start: int, i: int, ns: nat) -> Option<M>
    decreases s.len() - i + 1,
{
    if i < 0 || i > s.len() {
        None
    } else {
        or(first(pm(p, s, start, i, unset(ns))), search_p(p, s, start, i + 1, ns))
    }
}

} // verus!
