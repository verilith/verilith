//! From syntax tree to program.
//!
//! Every loop body is emitted in copies. The normal copy is where a thread
//! runs once it has consumed a character in the current iteration; a
//! no-progress copy is where an iteration starts, and its characters jump
//! into the normal copy. A later iteration that reaches the end of its
//! no-progress copy consumed nothing and fails. So no path through the
//! program returns to an instruction without consuming input, and every
//! jump that consumes nothing goes forward.
use crate::ast::*;
use crate::class::Class;
use crate::cproof::*;
use crate::lists::*;
use crate::prog::*;
use crate::sem;
use crate::sem::*;
use crate::spec::*;
use crate::vmspec::*;
use vstd::prelude::*;

verus! {

/// No address in a program reaches this.
pub const LIM: usize = 0x4000_0000;

/// Instructions as mathematics.
pub open spec fn pv(insts: Seq<Inst>, cl: Seq<Class>) -> Seq<SInst> {
    Seq::new(insts.len(), |k: int| iv(insts[k], cl))
}

/// Entry of the normal copy of `x` at `b`, leaving to `e`.
pub fn ent_n(x: &Ast, b: usize, e: usize, Ghost(cl): Ghost<Seq<Class>>) -> (r: usize)
    requires
        x.wf(),
        b + x.ln <= LIM,
    ensures
        r == sem::ent_n(x.re(cl), b as int, e as int),
        r == e || r < b + x.ln,
{
    proof {
        lemma_ent(x.re(cl), b as int, e as int);
    }
    if x.en == THRU {
        e
    } else {
        b + x.en
    }
}

/// Entry of the no-progress copy of `x` at `b`, leaving to `e0`.
pub fn ent_z(x: &Ast, b: usize, e0: usize, Ghost(cl): Ghost<Seq<Class>>) -> (r: usize)
    requires
        x.wf(),
        b + x.lz <= LIM,
    ensures
        r == sem::ent_z(x.re(cl), b as int, e0 as int),
        r == e0 || r < b + x.lz,
{
    proof {
        lemma_ent(x.re(cl), b as int, e0 as int);
    }
    if x.ez == THRU {
        e0
    } else {
        b + x.ez
    }
}

fn split(a: usize, b: usize, greedy: bool, Ghost(cl): Ghost<Seq<Class>>) -> (r: Inst)
    requires
        a <= LIM,
        b <= LIM,
    ensures
        iv(r, cl) == sem::split(a as int, b as int, greedy),
{
    if greedy {
        Inst::Split { a: a as u32, b: b as u32 }
    } else {
        Inst::Split { a: b as u32, b: a as u32 }
    }
}

proof fn lemma_pv_push(v: Seq<Inst>, i: Inst, cl: Seq<Class>)
    ensures
        pv(v.push(i), cl) == pv(v, cl) + seq![iv(i, cl)],
{
    assert(pv(v.push(i), cl) =~= pv(v, cl) + seq![iv(i, cl)]);
}

/// Appends the normal copy of `x`: based at `b`, leaving to `e`. `fail` is
/// the address of the program's `Fail`.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub fn emit_n(
    x: &Ast,
    b: usize,
    e: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.wf(),
        x.bounded(nc, ng),
        nc <= LIM,
        ng <= LIM,
        old(out)@.len() == b,
        b + x.ln <= LIM,
        e <= LIM,
        fail <= LIM,
    ensures
        pv(final(out)@, cl) == pv(old(out)@, cl) + code_n(x.re(cl), b as int, e as int, fail as int),
        final(out)@.len() == b + x.ln,
    decreases x,
{
    let ghost o0 = pv(out@, cl);
    let ghost r = x.re(cl);
    let ghost code = code_n(r, b as int, e as int, fail as int);
    proof {
        lemma_len(r, b as int, e as int, 0, 0, fail as int);
    }
    match &x.node {
        Node::Empty => {
            assert(o0 + code =~= o0);
        },
        Node::Char(c) => {
            proof {
                lemma_pv_push(out@, Inst::Char { cls: *c as u32, next: e as u32 }, cl);
            }
            out.push(Inst::Char { cls: *c as u32, next: e as u32 });
        },
        Node::Look(k) => {
            proof {
                lemma_pv_push(out@, Inst::Look { k: *k, next: e as u32 }, cl);
            }
            out.push(Inst::Look { k: *k, next: e as u32 });
        },
        Node::Group(k, p) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Group(*k as nat, Box::new(p.re(cl))));
            }
            let ghost rp = p.re(cl);
            let close = b + 1 + p.ln;
            let en = ent_n(p, b + 1, close, Ghost(cl));
            let i1 = Inst::Save { slot: (2 * *k) as u32, next: en as u32 };
            let i2 = Inst::Save { slot: (2 * *k + 1) as u32, next: e as u32 };
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_n(p, b + 1, close, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            proof {
                lemma_pv_push(out@, i2, cl);
            }
            out.push(i2);
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Cat(p, q) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Cat(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + p.ln;
            let en = ent_n(q, m, e, Ghost(cl));
            emit_n(p, b, en, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            emit_n(q, m, e, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Alt(p, q) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Alt(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + 1 + p.ln;
            let ea = ent_n(p, b + 1, e, Ghost(cl));
            let eb = ent_n(q, m, e, Ghost(cl));
            let i1 = Inst::Split { a: ea as u32, b: eb as u32 };
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_n(p, b + 1, e, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            emit_n(q, m, e, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Opt(p, g) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Opt(Box::new(p.re(cl)), *g));
            }
            let ea = ent_n(p, b + 1, e, Ghost(cl));
            let i1 = split(ea, e, *g, Ghost(cl));
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_n(p, b + 1, e, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Plus(p, g) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Plus(Box::new(p.re(cl)), *g));
            }
            // The normal copy; the loop head; the copy later iterations
            // start in (an empty one fails); the copy the first iteration
            // starts in (an empty one leaves the loop).
            let ghost rp = p.re(cl);
            proof {
                lemma_len(rp, b as int, 0, 0, 0, fail as int);
            }
            let l = b + p.ln;
            emit_n(p, b, l, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            let ez = ent_z(p, l + 1, fail, Ghost(cl));
            let i1 = split(ez, e, *g, Ghost(cl));
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_z(p, l + 1, fail, b, l, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            emit_z(p, l + 1 + p.lz, e, b, l, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
    }
}

/// Appends the no-progress copy of `x`: based at `b`, leaving to `e0` if it
/// consumed nothing. The normal copy of `x` is at `nb` and leaves to `ne`.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub fn emit_z(
    x: &Ast,
    b: usize,
    e0: usize,
    nb: usize,
    ne: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.wf(),
        x.bounded(nc, ng),
        nc <= LIM,
        ng <= LIM,
        old(out)@.len() == b,
        b + x.lz <= LIM,
        nb + x.ln <= LIM,
        e0 <= LIM,
        ne <= LIM,
        fail <= LIM,
    ensures
        pv(final(out)@, cl) == pv(old(out)@, cl) + code_z(
            x.re(cl),
            b as int,
            e0 as int,
            nb as int,
            ne as int,
            fail as int,
        ),
        final(out)@.len() == b + x.lz,
    decreases x,
{
    let ghost o0 = pv(out@, cl);
    let ghost r = x.re(cl);
    let ghost code = code_z(r, b as int, e0 as int, nb as int, ne as int, fail as int);
    proof {
        lemma_len(r, b as int, e0 as int, nb as int, ne as int, fail as int);
    }
    match &x.node {
        Node::Empty => {
            assert(o0 + code =~= o0);
        },
        Node::Char(c) => {
            proof {
                lemma_pv_push(out@, Inst::Char { cls: *c as u32, next: ne as u32 }, cl);
            }
            out.push(Inst::Char { cls: *c as u32, next: ne as u32 });
        },
        Node::Look(k) => {
            proof {
                lemma_pv_push(out@, Inst::Look { k: *k, next: e0 as u32 }, cl);
            }
            out.push(Inst::Look { k: *k, next: e0 as u32 });
        },
        Node::Group(k, p) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Group(*k as nat, Box::new(p.re(cl))));
            }
            let close = b + 1 + p.lz;
            let en = ent_z(p, b + 1, close, Ghost(cl));
            let i1 = Inst::Save { slot: (2 * *k) as u32, next: en as u32 };
            let i2 = Inst::Save { slot: (2 * *k + 1) as u32, next: e0 as u32 };
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_z(p, b + 1, close, nb + 1, nb + 1 + p.ln, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            proof {
                lemma_pv_push(out@, i2, cl);
            }
            out.push(i2);
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Cat(p, q) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Cat(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + p.lz;
            let nm = nb + p.ln;
            let ez = ent_z(q, m, e0, Ghost(cl));
            let en = ent_n(q, nm, ne, Ghost(cl));
            emit_z(p, b, ez, nb, en, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            emit_z(q, m, e0, nm, ne, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Alt(p, q) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Alt(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + 1 + p.lz;
            let ea = ent_z(p, b + 1, e0, Ghost(cl));
            let eb = ent_z(q, m, e0, Ghost(cl));
            let i1 = Inst::Split { a: ea as u32, b: eb as u32 };
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_z(p, b + 1, e0, nb + 1, ne, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            emit_z(q, m, e0, nb + 1 + p.ln, ne, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Opt(p, g) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Opt(Box::new(p.re(cl)), *g));
            }
            let ea = ent_z(p, b + 1, e0, Ghost(cl));
            let i1 = split(ea, e0, *g, Ghost(cl));
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            emit_z(p, b + 1, e0, nb + 1, ne, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
            assert(pv(out@, cl) =~= o0 + code);
        },
        Node::Plus(p, g) => {
            proof {
                x.lemma_wf(cl);
                p.lemma_wf(cl);
                assert(r == Re::Plus(Box::new(p.re(cl)), *g));
            }
            emit_z(p, b, e0, nb, nb + p.ln, fail, out, Ghost(cl), Ghost(nc), Ghost(ng));
        },
    }
}

/// Whether every jump that consumes nothing goes forward and every
/// address, class number and slot number is in range.
fn check(insts: &Vec<Inst>, nclasses: usize, nslots: usize, Ghost(cl): Ghost<Seq<Class>>) -> (r: bool)
    ensures
        r ==> fwd(pv(insts@, cl)) && forall|pc: int|
            0 <= pc < insts@.len() ==> match #[trigger] insts@[pc] {
                Inst::Char { cls, next } => cls < nclasses,
                Inst::Save { slot, next } => slot < nslots,
                _ => true,
            },
{
    let n = insts.len();
    let mut pc = 0;
    while pc < n
        invariant
            pc <= n,
            n == insts@.len(),
            forall|k: int| 0 <= k < pc ==> fwd_at(pv(insts@, cl), k),
            forall|k: int|
                0 <= k < pc ==> match #[trigger] insts@[k] {
                    Inst::Char { cls, next } => cls < nclasses,
                    Inst::Save { slot, next } => slot < nslots,
                    _ => true,
                },
        decreases n - pc,
    {
        let ok = match insts[pc] {
            Inst::Char { cls, next } => (next as usize) < n && (cls as usize) < nclasses,
            Inst::Split { a, b } => pc < a as usize && (a as usize) < n && pc < b as usize && (b as usize) < n,
            Inst::Save { slot, next } => pc < next as usize && (next as usize) < n && (slot as usize) < nslots,
            Inst::Look { k, next } => pc < next as usize && (next as usize) < n,
            Inst::Match => true,
            Inst::Fail => true,
        };
        if !ok {
            return false;
        }
        assert(pv(insts@, cl)[pc as int] == iv(insts@[pc as int], cl));
        pc += 1;
    }
    true
}

/// A run of the program from the end of the pattern's code reports the
/// matches it was handed.
pub proof fn lemma_pm_all_match(p: Seq<SInst>, s: Seq<u8>, m: int, rs: Seq<M>, lo: int)
    requires
        0 <= m < p.len(),
        p[m] == SInst::Match,
        ends_in(rs, lo, s.len() as int),
        0 <= lo,
    ensures
        pm_all(p, s, m, rs) == rs,
    decreases rs.len(),
{
    if rs.len() > 0 {
        assert(ends_in(rs.drop_first(), lo, s.len() as int)) by {
            assert forall|k: int| 0 <= k < rs.drop_first().len() implies lo <= (#[trigger] rs.drop_first()[k]).end
                <= s.len() by {
                assert(rs.drop_first()[k] == rs[k + 1]);
            }
        }
        lemma_pm_all_match(p, s, m, rs.drop_first(), lo);
        assert(pm(p, s, m, rs[0].end, rs[0].caps) == seq![rs[0]]);
        assert(seq![rs[0]] + rs.drop_first() =~= rs);
    } else {
        assert(pm_all(p, s, m, rs) =~= rs);
    }
}

/// The shape of a compiled program: the code of `g`, then `Match`, `Fail`.
pub open spec fn compiled(p: Seq<SInst>, g: Re) -> bool {
    p == code_n(g, 0, ln(g) as int, ln(g) as int + 1) + seq![SInst::Match, SInst::Fail]
}

/// A compiled program finds exactly the matches of its regular expression,
/// in the same order.
pub proof fn lemma_prog(p: Seq<SInst>, g: Re, s: Seq<u8>, i: int, c: Seq<int>)
    requires
        fwd(p),
        compiled(p, g),
        0 <= i <= s.len(),
    ensures
        pm(p, s, sem::ent_n(g, 0, ln(g) as int), i, c) == ms(g, s, i, c),
{
    let m = ln(g) as int;
    let code = code_n(g, 0, m, m + 1);
    lemma_len(g, 0, m, 0, 0, m + 1);
    assert(sem::has(p, 0, code));
    lemma_n(p, s, g, 0, m, m + 1, i, c);
    lemma_ms_ends(g, s, i, c);
    lemma_pm_all_match(p, s, m, ms(g, s, i, c), i);
}

/// So a search with the program reports what a search with the regular
/// expression does.
pub proof fn lemma_search(p: Seq<SInst>, g: Re, s: Seq<u8>, from: int, ns: nat)
    requires
        fwd(p),
        compiled(p, g),
    ensures
        search_p(p, s, sem::ent_n(g, 0, ln(g) as int), from, ns) == search(g, s, from, ns),
    decreases s.len() - from + 1,
{
    if 0 <= from <= s.len() {
        lemma_prog(p, g, s, from, unset(ns));
        lemma_search(p, g, s, from + 1, ns);
    }
}

/// The program for `x` (which is group 0 around the pattern). `None` only
/// if the final check of the program fails, which no pattern is known to
/// cause.
pub fn compile(x: &Ast, classes: Vec<Class>, ngroups: usize) -> (r: Option<Prog>)
    requires
        x.wf(),
        x.bounded(classes@.len() as int, ngroups as int),
        classes@.len() <= LIM,
        ngroups <= LIM,
        forall|k: int| 0 <= k < classes@.len() ==> (#[trigger] classes@[k]).wf(),
    ensures
        r matches Some(p) ==> {
            &&& p.wf()
            &&& p.classes == classes
            &&& p.nslots == 2 * ngroups
            &&& compiled(p.sp(), x.re(classes@))
            &&& p.start == sem::ent_n(x.re(classes@), 0, ln(x.re(classes@)) as int)
        },
{
    let ghost cl = classes@;
    let mut insts: Vec<Inst> = Vec::new();
    let m = x.ln;
    emit_n(x, 0, m, m + 1, &mut insts, Ghost(cl), Ghost(cl.len() as int), Ghost(ngroups as int));
    proof {
        lemma_pv_push(insts@, Inst::Match, cl);
        lemma_pv_push(insts@.push(Inst::Match), Inst::Fail, cl);
    }
    insts.push(Inst::Match);
    insts.push(Inst::Fail);
    let start = ent_n(x, 0, m, Ghost(cl));
    if !check(&insts, classes.len(), 2 * ngroups, Ghost(cl)) || start >= insts.len() {
        return None;
    }
    let r = crate::skip::reach(&insts, start, Ghost(cl));
    let skip = if crate::skip::eps_start(&insts, start, Ghost(cl)) {
        Vec::new()
    } else {
        crate::skip::first_table(&insts, &classes, &r)
    };
    let lead1 = crate::skip::only_byte(&skip);
    let (next2, r2) = if skip.len() == 256 {
        crate::skip::second_table(&insts, &classes, &r)
    } else {
        (Vec::new(), Ghost(Seq::<bool>::empty()))
    };
    let pair = match (crate::skip::only_two(&skip), crate::skip::only_two(&next2)) {
        (Some(ab), Some(cd)) => if ab.0 < 0x80 && ab.1 < 0x80 {
            Some((ab.0, ab.1, cd.0, cd.1))
        } else {
            None
        },
        _ => None,
    };
    let rng = if lead1.is_none() && pair.is_none() {
        crate::skip::rng_of(&skip)
    } else {
        None
    };
    let (need, ng, nw) = if lead1.is_none() && pair.is_none() {
        crate::need::find_need(&insts, &classes, start)
    } else {
        (None, Ghost(Seq::<bool>::empty()), Ghost(Seq::<bool>::empty()))
    };
    let alpha = if need.is_some() {
        crate::need::al_table(&insts, &classes)
    } else {
        Vec::new()
    };
    let p = Prog {
        insts: insts,
        classes: classes,
        start: start,
        nslots: 2 * ngroups,
        skip: skip,
        reach: Ghost(r@),
        lead1: lead1,
        next2: next2,
        reach2: r2,
        pair: pair,
        rng: rng,
        need: need,
        needg: ng,
        needw: nw,
        alpha: alpha,
    };
    proof {
        let code = code_n(x.re(cl), 0, m as int, m + 1);
        assert(pv(Seq::<Inst>::empty(), cl) =~= Seq::<SInst>::empty());
        assert(p.sp() =~= pv(p.insts@, cl));
        assert(p.sp() =~= code + seq![SInst::Match, SInst::Fail]);
    }
    Some(p)
}

} // verus!
