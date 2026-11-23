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

/// What is left to emit, the next piece last: the normal copy of a tree
/// (`N(x, b, e)`, as `code_n`), its no-progress copy (`Z(x, b, e0, nb,
/// ne)`, as `code_z`), or one instruction.
pub enum Task<'a> {
    N(&'a Ast, usize, usize),
    Z(&'a Ast, usize, usize, usize, usize),
    I(Inst),
}

/// The instructions a task stands for.
pub open spec fn tcode(t: Task, cl: Seq<Class>, f: int) -> Seq<SInst> {
    match t {
        Task::N(x, b, e) => code_n(x.re(cl), b as int, e as int, f),
        Task::Z(x, b, e0, nb, ne) => code_z(x.re(cl), b as int, e0 as int, nb as int, ne as int, f),
        Task::I(i) => seq![iv(i, cl)],
    }
}

pub open spec fn tlen(t: Task) -> int {
    match t {
        Task::N(x, _, _) => x.ln as int,
        Task::Z(x, _, _, _, _) => x.lz as int,
        Task::I(_) => 1,
    }
}

/// The instructions the tasks stand for, the last task's first.
pub open spec fn flat(ts: Seq<Task>, cl: Seq<Class>, f: int) -> Seq<SInst>
    decreases ts.len(),
{
    if ts.len() == 0 {
        seq![]
    } else {
        tcode(ts.last(), cl, f) + flat(ts.drop_last(), cl, f)
    }
}

/// A task can be emitted where it says it starts.
pub open spec fn task_ok(t: Task, pos: int, nc: int, ng: int) -> bool {
    match t {
        Task::N(x, b, e) => b == pos && x.wf() && x.bounded(nc, ng) && b + x.ln <= LIM && e <= LIM,
        Task::Z(x, b, e0, nb, ne) => b == pos && x.wf() && x.bounded(nc, ng) && b + x.lz <= LIM && nb + x.ln
            <= LIM && e0 <= LIM && ne <= LIM,
        Task::I(i) => true,
    }
}

/// The tasks, the last first, each start where the one before ends, the
/// first at `pos`.
pub open spec fn tasks_ok(ts: Seq<Task>, pos: int, nc: int, ng: int) -> bool
    decreases ts.len(),
{
    ts.len() == 0 || (task_ok(ts.last(), pos, nc, ng) && tasks_ok(ts.drop_last(), pos + tlen(ts.last()), nc, ng))
}

/// Termination: a task weighs more than the tasks it is replaced by.
pub open spec fn wn(r: Re) -> nat
    decreases r,
{
    match r {
        Re::Group(_, x) => 2 + wn(*x),
        Re::Cat(x, y) => 1 + wn(*x) + wn(*y),
        Re::Alt(x, y) => 1 + wn(*x) + wn(*y),
        Re::Opt(x, _) => 1 + wn(*x),
        Re::Plus(x, _) => 2 + wn(*x) + 2 * wz(*x),
        _ => 1,
    }
}

pub open spec fn wz(r: Re) -> nat
    decreases r,
{
    match r {
        Re::Group(_, x) => 2 + wz(*x),
        Re::Cat(x, y) => 1 + wz(*x) + wz(*y),
        Re::Alt(x, y) => 1 + wz(*x) + wz(*y),
        Re::Opt(x, _) => 1 + wz(*x),
        Re::Plus(x, _) => 1 + wz(*x),
        _ => 1,
    }
}

pub open spec fn tw(t: Task, cl: Seq<Class>) -> nat {
    match t {
        Task::N(x, _, _) => wn(x.re(cl)),
        Task::Z(x, _, _, _, _) => wz(x.re(cl)),
        Task::I(_) => 1,
    }
}

pub open spec fn wsum(ts: Seq<Task>, cl: Seq<Class>) -> nat
    decreases ts.len(),
{
    if ts.len() == 0 {
        0
    } else {
        tw(ts.last(), cl) + wsum(ts.drop_last(), cl)
    }
}

proof fn lemma_push_task(ts: Seq<Task>, t: Task, cl: Seq<Class>, f: int, pos: int, nc: int, ng: int)
    requires
        task_ok(t, pos, nc, ng),
        tasks_ok(ts, pos + tlen(t), nc, ng),
    ensures
        flat(ts.push(t), cl, f) == tcode(t, cl, f) + flat(ts, cl, f),
        tasks_ok(ts.push(t), pos, nc, ng),
        wsum(ts.push(t), cl) == tw(t, cl) + wsum(ts, cl),
{
    assert(ts.push(t).drop_last() =~= ts);
}

/// `expand_n` for `x`, which is `p+` (greedy if `g`).
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_plus<'a>(
    x: &'a Ast,
    p: &'a Ast,
    g: bool,
    b: usize,
    e: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.node == Node::Plus(Box::new(*p), g),
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::N(x, b, e), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::N(x, b, e)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::N(x, b, e), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::N(x, b, e), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_n(r, b as int, e as int, f);
    proof {
        lemma_len(r, b as int, e as int, 0, 0, f);
        x.lemma_wf(cl);
    }
    proof {
        p.lemma_wf(cl);
        assert(r == Re::Plus(Box::new(p.re(cl)), g));
    }
    // The normal copy; the loop head; the copy later
    // iterations start in (an empty one fails); the copy the
    // first iteration starts in (an empty one leaves the
    // loop).
    let l = b + p.ln;
    let ez = ent_z(p, l + 1, fail, Ghost(cl));
    let i1 = split(ez, e, g, Ghost(cl));
    let t4 = Task::Z(p, l + 1 + p.lz, e, b, l);
    let t3 = Task::Z(p, l + 1, fail, b, l);
    let t2 = Task::I(i1);
    let t1 = Task::N(p, b, l);
    proof {
        lemma_push_task(ts@, t4, cl, f, (l + 1 + p.lz) as int, nc, ng);
    }
    ts.push(t4);
    proof {
        lemma_push_task(ts@, t3, cl, f, (l + 1) as int, nc, ng);
    }
    ts.push(t3);
    proof {
        lemma_push_task(ts@, t2, cl, f, l as int, nc, ng);
    }
    ts.push(t2);
    proof {
        lemma_push_task(ts@, t1, cl, f, b as int, nc, ng);
    }
    ts.push(t1);
    assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
}

/// The normal copy of `x`, or what it is made of, as in [`expand`].
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_n<'a>(
    x: &'a Ast,
    b: usize,
    e: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::N(x, b, e), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::N(x, b, e)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::N(x, b, e), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::N(x, b, e), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_n(r, b as int, e as int, f);
    proof {
        lemma_len(r, b as int, e as int, 0, 0, f);
        x.lemma_wf(cl);
    }
    match &x.node {
        Node::Empty => {
            assert(o0 + code + rest =~= o0 + rest);
        },
        Node::Char(c) => {
            proof {
                lemma_pv_push(out@, Inst::Char { cls: *c as u32, next: e as u32 }, cl);
            }
            out.push(Inst::Char { cls: *c as u32, next: e as u32 });
            assert(pv(out@, cl) + rest =~= o0 + code + rest);
        },
        Node::Look(k) => {
            proof {
                lemma_pv_push(out@, Inst::Look { k: *k, next: e as u32 }, cl);
            }
            out.push(Inst::Look { k: *k, next: e as u32 });
            assert(pv(out@, cl) + rest =~= o0 + code + rest);
        },
        Node::Group(..) | Node::Cat(..) => {
            expand_n_seq(x, b, e, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng));
        },
        Node::Alt(..) | Node::Opt(..) => {
            expand_n_alt(x, b, e, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng));
        },
        Node::Plus(p, g) => {
            expand_plus(x, &**p, *g, b, e, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng));
        },
    }
}

/// [`expand_n`] for a group or a concatenation. A separate function, as is
/// [`expand_n_alt`], so that each proof stays small enough at a 32-bit usize.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_n_seq<'a>(
    x: &'a Ast,
    b: usize,
    e: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.node is Group || x.node is Cat,
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::N(x, b, e), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::N(x, b, e)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::N(x, b, e), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::N(x, b, e), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_n(r, b as int, e as int, f);
    proof {
        lemma_len(r, b as int, e as int, 0, 0, f);
        x.lemma_wf(cl);
    }
    match &x.node {
        Node::Group(k, p) => {
            proof {
                p.lemma_wf(cl);
                assert(r == Re::Group(*k as nat, Box::new(p.re(cl))));
            }
            let close = b + 1 + p.ln;
            let en = ent_n(p, b + 1, close, Ghost(cl));
            let i1 = Inst::Save { slot: (2 * *k) as u32, next: en as u32 };
            let i2 = Inst::Save { slot: (2 * *k + 1) as u32, next: e as u32 };
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            let t2 = Task::I(i2);
            let t1 = Task::N(&**p, b + 1, close);
            proof {
                lemma_push_task(ts@, t2, cl, f, close as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        Node::Cat(p, q) => {
            proof {
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Cat(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + p.ln;
            let en = ent_n(q, m, e, Ghost(cl));
            let t2 = Task::N(&**q, m, e);
            let t1 = Task::N(&**p, b, en);
            proof {
                lemma_push_task(ts@, t2, cl, f, m as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, b as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        _ => {},
    }
}

/// [`expand_n`] for an alternation or an option.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_n_alt<'a>(
    x: &'a Ast,
    b: usize,
    e: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.node is Alt || x.node is Opt,
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::N(x, b, e), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::N(x, b, e)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::N(x, b, e), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::N(x, b, e), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_n(r, b as int, e as int, f);
    proof {
        lemma_len(r, b as int, e as int, 0, 0, f);
        x.lemma_wf(cl);
    }
    match &x.node {
        Node::Alt(p, q) => {
            proof {
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
            let t2 = Task::N(&**q, m, e);
            let t1 = Task::N(&**p, b + 1, e);
            proof {
                lemma_push_task(ts@, t2, cl, f, m as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        Node::Opt(p, g) => {
            proof {
                p.lemma_wf(cl);
                assert(r == Re::Opt(Box::new(p.re(cl)), *g));
            }
            let ea = ent_n(p, b + 1, e, Ghost(cl));
            let i1 = split(ea, e, *g, Ghost(cl));
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            let t1 = Task::N(&**p, b + 1, e);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        _ => {},
    }
}

/// [`expand_z`] for a leaf or a group.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_z_leaf<'a>(
    x: &'a Ast,
    b: usize,
    e0: usize,
    nb: usize,
    ne: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        x.node is Empty || x.node is Char || x.node is Look || x.node is Group,
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::Z(x, b, e0, nb, ne), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::Z(x, b, e0, nb, ne)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::Z(x, b, e0, nb, ne), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::Z(x, b, e0, nb, ne), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_z(r, b as int, e0 as int, nb as int, ne as int, f);
    proof {
        lemma_len(r, b as int, e0 as int, nb as int, ne as int, f);
        x.lemma_wf(cl);
    }
    match &x.node {
        Node::Empty => {
            assert(o0 + code + rest =~= o0 + rest);
        },
        Node::Char(c) => {
            proof {
                lemma_pv_push(out@, Inst::Char { cls: *c as u32, next: ne as u32 }, cl);
            }
            out.push(Inst::Char { cls: *c as u32, next: ne as u32 });
            assert(pv(out@, cl) + rest =~= o0 + code + rest);
        },
        Node::Look(k) => {
            proof {
                lemma_pv_push(out@, Inst::Look { k: *k, next: e0 as u32 }, cl);
            }
            out.push(Inst::Look { k: *k, next: e0 as u32 });
            assert(pv(out@, cl) + rest =~= o0 + code + rest);
        },
        Node::Group(k, p) => {
            proof {
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
            let t2 = Task::I(i2);
            let t1 = Task::Z(&**p, b + 1, close, nb + 1, nb + 1 + p.ln);
            proof {
                lemma_push_task(ts@, t2, cl, f, close as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        _ => {},
    }
}

/// The no-progress copy of `x`, or what it is made of, as in [`expand`].
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn expand_z<'a>(
    x: &'a Ast,
    b: usize,
    e0: usize,
    nb: usize,
    ne: usize,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(Task::Z(x, b, e0, nb, ne), old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(Task::Z(x, b, e0, nb, ne)), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(Task::Z(x, b, e0, nb, ne), cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(Task::Z(x, b, e0, nb, ne), cl) + wsum(old(ts)@, cl),
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost rest = flat(ts@, cl, f);
    let ghost r = x.re(cl);
    let ghost code = code_z(r, b as int, e0 as int, nb as int, ne as int, f);
    proof {
        lemma_len(r, b as int, e0 as int, nb as int, ne as int, f);
        x.lemma_wf(cl);
    }
    match &x.node {
        Node::Empty | Node::Char(_) | Node::Look(_) | Node::Group(_, _) => {
            expand_z_leaf(x, b, e0, nb, ne, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng));
        },
        Node::Cat(p, q) => {
            proof {
                p.lemma_wf(cl);
                q.lemma_wf(cl);
                assert(r == Re::Cat(Box::new(p.re(cl)), Box::new(q.re(cl))));
            }
            let m = b + p.lz;
            let nm = nb + p.ln;
            let ez = ent_z(q, m, e0, Ghost(cl));
            let en = ent_n(q, nm, ne, Ghost(cl));
            let t2 = Task::Z(&**q, m, e0, nm, ne);
            let t1 = Task::Z(&**p, b, ez, nb, en);
            proof {
                lemma_push_task(ts@, t2, cl, f, m as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, b as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        Node::Alt(p, q) => {
            proof {
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
            let t2 = Task::Z(&**q, m, e0, nb + 1 + p.ln, ne);
            let t1 = Task::Z(&**p, b + 1, e0, nb + 1, ne);
            proof {
                lemma_push_task(ts@, t2, cl, f, m as int, nc, ng);
            }
            ts.push(t2);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        Node::Opt(p, g) => {
            proof {
                p.lemma_wf(cl);
                assert(r == Re::Opt(Box::new(p.re(cl)), *g));
            }
            let ea = ent_z(p, b + 1, e0, Ghost(cl));
            let i1 = split(ea, e0, *g, Ghost(cl));
            proof {
                lemma_pv_push(out@, i1, cl);
            }
            out.push(i1);
            let t1 = Task::Z(&**p, b + 1, e0, nb + 1, ne);
            proof {
                lemma_push_task(ts@, t1, cl, f, (b + 1) as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
        Node::Plus(p, g) => {
            proof {
                p.lemma_wf(cl);
                assert(r == Re::Plus(Box::new(p.re(cl)), *g));
            }
            let t1 = Task::Z(&**p, b, e0, nb, nb + p.ln);
            proof {
                lemma_push_task(ts@, t1, cl, f, b as int, nc, ng);
            }
            ts.push(t1);
            assert(pv(out@, cl) + flat(ts@, cl, f) =~= o0 + code + rest);
        },
    }
}

/// Appends what task `t` stands for to `out`, or puts the tasks for its
/// parts on `ts`.
fn expand<'a>(
    t: Task<'a>,
    fail: usize,
    out: &mut Vec<Inst>,
    ts: &mut Vec<Task<'a>>,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
)
    requires
        nc <= LIM,
        ng <= LIM,
        fail <= LIM,
        task_ok(t, old(out)@.len() as int, nc, ng),
        tasks_ok(old(ts)@, old(out)@.len() + tlen(t), nc, ng),
    ensures
        pv(final(out)@, cl) + flat(final(ts)@, cl, fail as int) == pv(old(out)@, cl) + tcode(t, cl, fail as int)
            + flat(old(ts)@, cl, fail as int),
        tasks_ok(final(ts)@, final(out)@.len() as int, nc, ng),
        wsum(final(ts)@, cl) < tw(t, cl) + wsum(old(ts)@, cl),
{
    match t {
        Task::I(i) => {
            let ghost o0 = pv(out@, cl);
            let ghost rest = flat(ts@, cl, fail as int);
            proof {
                lemma_pv_push(out@, i, cl);
            }
            out.push(i);
            assert(pv(out@, cl) + rest =~= o0 + tcode(t, cl, fail as int) + rest);
        },
        Task::N(x, b, e) => expand_n(x, b, e, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng)),
        Task::Z(x, b, e0, nb, ne) => expand_z(x, b, e0, nb, ne, fail, out, ts, Ghost(cl), Ghost(nc), Ghost(ng)),
    }
}

/// Appends the normal copy of `x`: based at `b`, leaving to `e`. `fail` is
/// the address of the program's `Fail`. The tree is walked with a list of
/// tasks on the heap, not by recursion, so its depth costs no call stack.
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
{
    let ghost o0 = pv(out@, cl);
    let ghost f = fail as int;
    let ghost goal = o0 + code_n(x.re(cl), b as int, e as int, f);
    let mut ts: Vec<Task> = Vec::new();
    let t0 = Task::N(x, b, e);
    proof {
        x.lemma_wf(cl);
        lemma_len(x.re(cl), b as int, e as int, 0, 0, f);
        lemma_push_task(ts@, t0, cl, f, b as int, nc, ng);
        assert(flat(Seq::<Task>::empty(), cl, f) =~= seq![]);
    }
    ts.push(t0);
    assert(pv(out@, cl) + flat(ts@, cl, f) =~= goal);
    while ts.len() > 0
        invariant
            nc <= LIM,
            ng <= LIM,
            fail <= LIM,
            f == fail,
            pv(out@, cl) + flat(ts@, cl, f) == goal,
            tasks_ok(ts@, out@.len() as int, nc, ng),
        decreases wsum(ts@, cl),
    {
        let ghost ts1 = ts@;
        let t = ts.pop().unwrap();
        proof {
            assert(t == ts1.last());
            assert(ts@ == ts1.drop_last());
        }
        expand(t, fail, out, &mut ts, Ghost(cl), Ghost(nc), Ghost(ng));
        assert(pv(out@, cl) + flat(ts@, cl, f) =~= goal);
    }
    proof {
        assert(flat(ts@, cl, f) =~= seq![]);
        assert(pv(out@, cl) =~= goal);
        lemma_len(x.re(cl), b as int, e as int, 0, 0, f);
        assert(pv(out@, cl).len() == out@.len());
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
            &&& p.insts@.len() == x.ln + 2
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
