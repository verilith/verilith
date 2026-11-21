//! Certified code never gets stuck (progress), and every step keeps the
//! machine's heights and labels equal to the certificate's (preservation).
//!
//! [`inv`] says each frame sits at a live position of its function's
//! certificate with exactly the certified stack height and label stack;
//! frames below the top are waiting at a call. [`lemma_step`] shows that
//! from such a state the semantics never returns `Stuck` and every
//! successor state satisfies [`inv`] again.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::cert::*;

verus! {

pub open spec fn labels_wf(ls: Seq<LabelRec>) -> bool {
    &&& ls.len() < NONE
    &&& forall|k: int| 0 <= k < ls.len() ==> (#[trigger] ls[k]).parent < k || ls[k].parent == NONE
}

pub open spec fn cert_of(cs: Seq<FuncCert>, f: Frame) -> FuncCert {
    cs[f.func as int]
}

/// `f` is about to run the instruction at a live position (or return, at
/// `pc == body.len()`) with the certified height and labels.
pub open spec fn frame_at(m: &Module, cs: Seq<FuncCert>, f: Frame) -> bool {
    let fc = cert_of(cs, f);
    &&& f.func < m.funcs@.len()
    &&& f.pc <= m.funcs@[f.func as int].body@.len()
    &&& live(fc, f.pc as int)
    &&& f.stack.len() == hgt(fc, f.pc as int)
    &&& f.labels == chain(fc.labels@, lab(fc, f.pc as int))
    &&& f.locals.len() == n_locals(m, f.func)
}

pub open spec fn is_call(i: Instr) -> bool {
    i is Call || i is CallIndirect
}

/// `f` is waiting at a call for a callee of type `t` to return.
pub open spec fn frame_waiting(m: &Module, cs: Seq<FuncCert>, f: Frame, t: &FuncType) -> bool {
    let fc = cert_of(cs, f);
    let i = m.funcs@[f.func as int].body@[f.pc as int];
    &&& f.func < m.funcs@.len()
    &&& f.pc < m.funcs@[f.func as int].body@.len()
    &&& live(fc, f.pc as int)
    &&& is_call(i)
    &&& f.stack.len() + call_pops(m, i) == hgt(fc, f.pc as int)
    &&& f.labels == chain(fc.labels@, lab(fc, f.pc as int))
    &&& f.locals.len() == n_locals(m, f.func)
    &&& n_results(t) == n_results(call_type(m, i))
}

pub open spec fn store_ok(m: &Module, s: Store) -> bool {
    &&& s.globals.len() == m.global_types@.len()
    &&& s.tables.len() == m.tables@.len()
    &&& s.data_dropped.len() == m.datas@.len()
    &&& forall|t: int, k: int| 0 <= t < s.tables.len() && 0 <= k < s.tables[t].len()
            && (#[trigger] s.tables[t][k]) is Some ==> s.tables[t][k]->Some_0 < m.func_types@.len()
}

pub open spec fn callers_ok(m: &Module, cs: Seq<FuncCert>, fr: Seq<Frame>) -> bool {
    forall|i: int| 0 <= i < fr.len() - 1 ==>
        #[trigger] frame_waiting(m, cs, fr[i], func_type(m, fr[i + 1].func + n_imp(m)))
}

pub proof fn lemma_caller(m: &Module, cs: Seq<FuncCert>, fr: Seq<Frame>, i: int)
    requires callers_ok(m, cs, fr), 0 <= i < fr.len() - 1,
    ensures frame_waiting(m, cs, fr[i], func_type(m, fr[i + 1].func + n_imp(m))),
{
}

pub open spec fn inv(m: &Module, cs: Seq<FuncCert>, c: Config) -> bool {
    &&& c.frames.len() >= 1
    &&& store_ok(m, c.store)
    &&& frame_at(m, cs, c.frames.last())
    &&& callers_ok(m, cs, c.frames)
}

/// The state while imported function `x` runs: the top frame waits on it.
pub open spec fn inv_host(m: &Module, cs: Seq<FuncCert>, c: Config, x: nat) -> bool {
    &&& c.frames.len() >= 1
    &&& store_ok(m, c.store)
    &&& x < m.func_types@.len()
    &&& frame_waiting(m, cs, c.frames.last(), func_type(m, x))
    &&& callers_ok(m, cs, c.frames)
}

/// What [`lemma_step`] guarantees about one step.
pub open spec fn step_ok(m: &Module, cs: Seq<FuncCert>, c: Config, r: Step) -> bool {
    match r {
        Step::Next(c2) => inv(m, cs, c2),
        Step::Host { func, args, cfg } => func < n_imp(m)
            && args.len() == n_params(func_type(m, func))
            && inv_host(m, cs, cfg, func),
        Step::Done(res, s) => c.frames.len() == 1
            && res.len() == n_results(func_type(m, c.frames[0].func + n_imp(m))),
        Step::Trap(..) => true,
        Step::Stuck => false,
    }
}

// ---------------------------------------------------------------------------
// Label chains
// ---------------------------------------------------------------------------

pub proof fn lemma_labels_wf(m: &Module, d: nat, fc: FuncCert)
    requires func_cert_ok(m, d, fc),
    ensures labels_wf(fc.labels@),
{
    assert forall|k: int| 0 <= k < fc.labels@.len() implies
        (#[trigger] fc.labels@[k]).parent < k || fc.labels@[k].parent == NONE by {
        assert(rec_ok(fc, m.funcs@[d as int].body@.len(), k));
    }
}

pub proof fn lemma_chain_unfold(ls: Seq<LabelRec>, k: u32)
    requires labels_wf(ls), (k as nat) < ls.len(),
    ensures chain(ls, k) == chain(ls, ls[k as int].parent).push(to_label(ls[k as int])),
{
    let p = ls[k as int].parent;
    if !(p < k) {
        assert(p == NONE);
        assert(chain(ls, p) == Seq::<Label>::empty());
    }
}

pub proof fn lemma_nth(ls: Seq<LabelRec>, l: u32, k: nat)
    requires labels_wf(ls), nth_id(ls, l, k) is Some,
    ensures ({
        let id = nth_id(ls, l, k)->Some_0;
        let ch = chain(ls, l);
        &&& (id as nat) < ls.len()
        &&& k < ch.len()
        &&& ch[ch.len() - 1 - k] == to_label(ls[id as int])
        &&& ch.subrange(0, ch.len() - 1 - k) == chain(ls, ls[id as int].parent)
    }),
    decreases k,
{
    lemma_chain_unfold(ls, l);
    let p = ls[l as int].parent;
    if k > 0 {
        lemma_nth(ls, p, (k - 1) as nat);
        let ch = chain(ls, l);
        let cp = chain(ls, p);
        assert(ch.subrange(0, ch.len() - 1 - k) =~= cp.subrange(0, cp.len() - 1 - (k - 1)));
    } else {
        let ch = chain(ls, l);
        assert(ch.subrange(0, ch.len() - 1) =~= chain(ls, p));
    }
}

/// A label pushed with parent `l` extends `l`'s chain.
pub proof fn lemma_chain_push(ls: Seq<LabelRec>, n: u32, l: u32)
    requires labels_wf(ls), (n as nat) < ls.len(), ls[n as int].parent == l, (l as nat) < ls.len(),
    ensures chain(ls, n) == chain(ls, l).push(to_label(ls[n as int])),
{
    lemma_chain_unfold(ls, n);
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

pub proof fn lemma_with_top(m: &Module, cs: Seq<FuncCert>, c: Config, s: Store, g: Frame)
    requires
        inv(m, cs, c),
        store_ok(m, s),
        frame_at(m, cs, g),
        g.func == top(c).func,
    ensures inv(m, cs, with_top(Config { store: s, ..c }, g)),
{
    let c2 = with_top(Config { store: s, ..c }, g);
    assert forall|i: int| 0 <= i < c2.frames.len() - 1 implies
        #[trigger] frame_waiting(m, cs, c2.frames[i], func_type(m, c2.frames[i + 1].func + n_imp(m))) by {
        assert(frame_waiting(m, cs, c.frames[i], func_type(m, c.frames[i + 1].func + n_imp(m))));
    }
}

/// Branching to label `k` from a frame at position `f.pc` whose stack has
/// `pops` values fewer than certified.
pub proof fn lemma_br(m: &Module, cs: Seq<FuncCert>, c: Config, f: Frame, k: nat, pops: nat)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        f.func == top(c).func,
        f.func < m.funcs@.len(),
        f.pc < m.funcs@[f.func as int].body@.len(),
        live(cert_of(cs, f), f.pc as int),
        f.stack.len() + pops == hgt(cert_of(cs, f), f.pc as int),
        f.labels == chain(cert_of(cs, f).labels@, lab(cert_of(cs, f), f.pc as int)),
        f.locals.len() == n_locals(m, f.func),
        br_ok(cert_of(cs, f), f.pc as int, k, pops),
    ensures step_ok(m, cs, c, br(c, f, k)),
{
    let fc = cert_of(cs, f);
    let d = f.func;
    assert(func_cert_ok(m, d, cs[d as int]));
    lemma_labels_wf(m, d, fc);
    let l = lab(fc, f.pc as int);
    lemma_nth(fc.labels@, l, k);
    let id = nth_id(fc.labels@, l, k)->Some_0;
    let r = fc.labels@[id as int];
    assert(rec_ok(fc, m.funcs@[d as int].body@.len(), id as int));
    let g = exit_label(f, k, r.cont as nat)->Some_0;
    assert(g.stack.len() == r.height + r.arity);
    lemma_with_top(m, cs, c, c.store, g);
    assert(Config { store: c.store, ..c } == c);
}

// ---------------------------------------------------------------------------
// The step lemma
// ---------------------------------------------------------------------------

pub proof fn lemma_step(m: &Module, cs: Seq<FuncCert>, c: Config)
    requires certs_ok(m, cs), inv(m, cs, c),
    ensures step_ok(m, cs, c, step(m, c)),
{
    let f = top(c);
    let d = f.func;
    let fc = cert_of(cs, f);
    assert(func_cert_ok(m, d, cs[d as int]));
    let len = m.funcs@[d as int].body@.len();
    if f.pc == len {
        lemma_ret(m, cs, c);
    } else {
        assert(pc_ok(m, d, fc, f.pc as int));
        lemma_instr(m, cs, c, m.funcs@[d as int].body@[f.pc as int]);
    }
}

pub proof fn lemma_ret(m: &Module, cs: Seq<FuncCert>, c: Config)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        top(c).pc == m.funcs@[top(c).func as int].body@.len(),
    ensures step_ok(m, cs, c, step(m, c)),
{
    let f = top(c);
    let d = f.func;
    let fc = cert_of(cs, f);
    assert(func_cert_ok(m, d, cs[d as int]));
    let k = n_results(func_type(m, f.func + n_imp(m)));
    if c.frames.len() > 1 {
        let n = c.frames.len();
        let caller = c.frames[n - 2];
        lemma_caller(m, cs, c.frames, n - 2);
        assert(c.frames[n - 2 + 1] == f);
        let cfc = cert_of(cs, caller);
        let cd = caller.func;
        assert(func_cert_ok(m, cd, cs[cd as int]));
        assert(pc_ok(m, cd, cfc, caller.pc as int));
        let res = f.stack.subrange(f.stack.len() - k, f.stack.len() as int);
        let g = Frame { pc: caller.pc + 1, stack: caller.stack + res, ..caller };
        let fr2 = c.frames.subrange(0, n - 1).update(n - 2, g);
        assert(frame_at(m, cs, g));
        assert forall|i: int| 0 <= i < fr2.len() - 1 implies
            #[trigger] frame_waiting(m, cs, fr2[i], func_type(m, fr2[i + 1].func + n_imp(m))) by {
            assert(frame_waiting(m, cs, c.frames[i], func_type(m, c.frames[i + 1].func + n_imp(m))));
        }
    }
}

/// The successor of a frame that only changes its stack and moves to the
/// next position.
pub open spec fn simple_next(m: &Module, cs: Seq<FuncCert>, f: Frame, g: Frame) -> bool {
    &&& g.func == f.func
    &&& g.pc == f.pc + 1
    &&& g.labels == f.labels
    &&& g.locals.len() == f.locals.len()
    &&& at(cert_of(cs, f), (f.pc + 1) as int, g.stack.len(), lab(cert_of(cs, f), f.pc as int))
}

pub proof fn lemma_simple(m: &Module, cs: Seq<FuncCert>, c: Config, s: Store, g: Frame)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        store_ok(m, s),
        simple_next(m, cs, top(c), g),
    ensures inv(m, cs, with_top(Config { store: s, ..c }, g)),
{
    let f = top(c);
    assert(func_cert_ok(m, f.func, cs[f.func as int]));
    assert(frame_at(m, cs, g));
    lemma_with_top(m, cs, c, s, g);
}

pub proof fn lemma_instr(m: &Module, cs: Seq<FuncCert>, c: Config, i: Instr)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        top(c).pc < m.funcs@[top(c).func as int].body@.len(),
        i == m.funcs@[top(c).func as int].body@[top(c).pc as int],
        local_ok(m, top(c).func, cert_of(cs, top(c)), top(c).pc as int),
    ensures step_ok(m, cs, c, step_instr(m, c, top(c), i)),
{
    reveal(step_instr);
    let f = top(c);
    let s = c.store;
    let fc = cert_of(cs, f);
    let d = f.func;
    assert(func_cert_ok(m, d, cs[d as int]));
    lemma_labels_wf(m, d, fc);
    assert(Config { store: s, ..c } == c);
    let h = f.stack.len();
    let pc = f.pc as int;
    if is_unop(i) {
        if let Ok(r) = eval_unop(i, peek(f, 0)) {
            lemma_simple(m, cs, c, s, adv(push(popn(f, 1), r)));
        }
    } else if is_binop(i) {
        if let Ok(r) = eval_binop(i, peek(f, 1), peek(f, 0)) {
            lemma_simple(m, cs, c, s, adv(push(popn(f, 2), r)));
        }
    } else if load_kind(i) is Some {
        let (n, signed, is64, off) = load_kind(i)->Some_0;
        let ea = crate::num::lo32(peek(f, 0)) as nat + off as nat;
        if ea + n <= s.mem.len() {
            lemma_simple(m, cs, c, s, adv(push(popn(f, 1), load_result(le(s.mem, ea as int, n), n, signed, is64))));
        }
    } else if store_kind(i) is Some {
        let (n, off) = store_kind(i)->Some_0;
        let ea = crate::num::lo32(peek(f, 1)) as nat + off as nat;
        if ea + n <= s.mem.len() {
            let s2 = Store { mem: write_le(s.mem, ea as int, store_value(peek(f, 0), n), n), ..s };
            lemma_simple(m, cs, c, s2, adv(popn(f, 2)));
        }
    } else {
        lemma_other(m, cs, c, i);
    }
}

pub proof fn lemma_other(m: &Module, cs: Seq<FuncCert>, c: Config, i: Instr)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        top(c).pc < m.funcs@[top(c).func as int].body@.len(),
        i == m.funcs@[top(c).func as int].body@[top(c).pc as int],
        local_ok(m, top(c).func, cert_of(cs, top(c)), top(c).pc as int),
        !is_unop(i), !is_binop(i), load_kind(i) is None, store_kind(i) is None,
    ensures step_ok(m, cs, c, step_instr(m, c, top(c), i)),
{
    reveal(step_instr);
    let f = top(c);
    let s = c.store;
    let fc = cert_of(cs, f);
    let d = f.func;
    assert(func_cert_ok(m, d, cs[d as int]));
    lemma_labels_wf(m, d, fc);
    assert(Config { store: s, ..c } == c);
    let h = f.stack.len();
    let pc = f.pc as int;
    let l = lab(fc, pc);
    match i {
        Instr::Block { .. } | Instr::Loop { .. } | Instr::If { .. } | Instr::Else { .. } | Instr::End
        | Instr::Br(_) | Instr::BrIf(_) | Instr::BrTable { .. } | Instr::Return => {
            lemma_control(m, cs, c, i);
        },
        Instr::Call(_) | Instr::CallIndirect { .. } => {
            lemma_call_instr(m, cs, c, i);
        },
        Instr::Nop | Instr::Drop | Instr::Select | Instr::I32Const(_) | Instr::I64Const(_)
        | Instr::F32Const(_) | Instr::F64Const(_) | Instr::MemorySize | Instr::LocalGet(_)
        | Instr::GlobalGet(_) => {
            let r = step_instr(m, c, f, i);
            if let Step::Next(c2) = r {
                lemma_simple(m, cs, c, s, top(c2));
                assert(c2 == with_top(c, top(c2)));
            }
        },
        Instr::LocalSet(x) => {
            lemma_simple(m, cs, c, s, adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..popn(f, 1) }));
        },
        Instr::LocalTee(x) => {
            lemma_simple(m, cs, c, s, adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..f }));
        },
        Instr::GlobalSet(x) => {
            let s2 = Store { globals: s.globals.update(x as int, peek(f, 0)), ..s };
            lemma_simple(m, cs, c, s2, adv(popn(f, 1)));
        },
        Instr::MemoryGrow => {
            let old = s.mem.len() / PAGE as nat;
            let n = crate::num::lo32(peek(f, 0)) as nat;
            if old + n > s.mem_max {
                lemma_simple(m, cs, c, s, adv(push(popn(f, 1), 0xffff_ffff)));
            } else {
                let s2 = Store { mem: s.mem + Seq::new(n * PAGE as nat, |_i| 0u8), ..s };
                lemma_simple(m, cs, c, s2, adv(push(popn(f, 1), old as u64)));
            }
        },
        Instr::MemoryFill | Instr::MemoryCopy | Instr::MemoryInit(_) | Instr::DataDrop(_) => {
            let r = step_instr(m, c, f, i);
            if let Step::Next(c2) = r {
                let s2 = c2.store;
                assert(store_ok(m, s2)) by {
                    assert(s2.tables == s.tables);
                }
                lemma_simple(m, cs, c, s2, top(c2));
                assert(c2 == with_top(Config { store: s2, ..c }, top(c2)));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_control(m: &Module, cs: Seq<FuncCert>, c: Config, i: Instr)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        top(c).pc < m.funcs@[top(c).func as int].body@.len(),
        i == m.funcs@[top(c).func as int].body@[top(c).pc as int],
        local_ok(m, top(c).func, cert_of(cs, top(c)), top(c).pc as int),
        i is Block || i is Loop || i is If || i is Else || i is End || i is Br || i is BrIf
            || i is BrTable || i is Return,
    ensures step_ok(m, cs, c, step_instr(m, c, top(c), i)),
{
    reveal(step_instr);
    let f = top(c);
    let s = c.store;
    let fc = cert_of(cs, f);
    let d = f.func;
    assert(func_cert_ok(m, d, cs[d as int]));
    lemma_labels_wf(m, d, fc);
    assert(Config { store: s, ..c } == c);
    let h = f.stack.len();
    let pc = f.pc as int;
    assert(pc_ok(m, d, fc, pc));
    let l = lab(fc, pc);
    let len = m.funcs@[d as int].body@.len();
    match i {
        Instr::Block { bt, end } => {
            let (np, nr) = bt_arity(m, bt)->Some_0;
            let n = lab(fc, pc + 1);
            lemma_chain_push(fc.labels@, n, l);
            let g = Frame {
                pc: f.pc + 1,
                labels: f.labels.push(Label { arity: nr, cont: (end + 1) as nat, height: (h - np) as nat }),
                ..f
            };
            assert(frame_at(m, cs, g));
            lemma_with_top(m, cs, c, s, g);
        },
        Instr::Loop { bt } => {
            let (np, nr) = bt_arity(m, bt)->Some_0;
            let n = lab(fc, pc + 1);
            lemma_chain_push(fc.labels@, n, l);
            let g = Frame {
                pc: f.pc + 1,
                labels: f.labels.push(Label { arity: np, cont: f.pc, height: (h - np) as nat }),
                ..f
            };
            assert(frame_at(m, cs, g));
            lemma_with_top(m, cs, c, s, g);
        },
        Instr::If { bt, else_, end } => {
            let (np, nr) = bt_arity(m, bt)->Some_0;
            let n = lab(fc, pc + 1);
            lemma_chain_push(fc.labels@, n, l);
            let gg = popn(f, 1);
            let lb = Label { arity: nr, cont: (end + 1) as nat, height: (h - 1 - np) as nat };
            let npc = if crate::num::lo32(peek(f, 0)) != 0 {
                f.pc + 1
            } else if else_ == end {
                end as nat
            } else {
                (else_ + 1) as nat
            };
            let g = Frame { pc: npc, labels: gg.labels.push(lb), ..gg };
            assert(to_label(fc.labels@[n as int]) == lb);
            assert(frame_at(m, cs, g));
            lemma_with_top(m, cs, c, s, g);
        },
        Instr::Else { end } => {
            assert(nth_id(fc.labels@, l, 0) == Some(l));
            lemma_br(m, cs, c, f, 0, 0);
        },
        Instr::End => {
            lemma_nth(fc.labels@, l, 0);
            let r = fc.labels@[l as int];
            let g = Frame { pc: f.pc + 1, labels: f.labels.drop_last(), ..f };
            assert(f.labels.drop_last() =~= chain(fc.labels@, r.parent));
            assert(frame_at(m, cs, g));
            lemma_with_top(m, cs, c, s, g);
        },
        Instr::Br(k) => {
            lemma_br(m, cs, c, f, k as nat, 0);
        },
        Instr::BrIf(k) => {
            if crate::num::lo32(peek(f, 0)) != 0 {
                lemma_br(m, cs, c, popn(f, 1), k as nat, 1);
            } else {
                lemma_simple(m, cs, c, s, adv(popn(f, 1)));
            }
        },
        Instr::BrTable { start, len: tl } => {
            let kk = crate::num::lo32(peek(f, 0));
            let j = if kk < tl - 1 { start + kk } else { start + tl - 1 };
            assert(br_ok(fc, pc, m.br_table@[j as int] as nat, 1));
            lemma_br(m, cs, c, popn(f, 1), m.br_table@[j as int] as nat, 1);
        },
        Instr::Return => {
            lemma_br(m, cs, c, f, (f.labels.len() - 1) as nat, 0);
        },
        _ => {},
    }
}

pub proof fn lemma_call_instr(m: &Module, cs: Seq<FuncCert>, c: Config, i: Instr)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        top(c).pc < m.funcs@[top(c).func as int].body@.len(),
        i == m.funcs@[top(c).func as int].body@[top(c).pc as int],
        local_ok(m, top(c).func, cert_of(cs, top(c)), top(c).pc as int),
        i is Call || i is CallIndirect,
    ensures step_ok(m, cs, c, step_instr(m, c, top(c), i)),
{
    reveal(step_instr);
    let f = top(c);
    let s = c.store;
    match i {
        Instr::Call(x) => {
            lemma_call(m, cs, c, f, x as nat);
        },
        Instr::CallIndirect { ty, table } => {
            let k = crate::num::lo32(peek(f, 0)) as nat;
            let tab = s.tables[table as int];
            if k < tab.len() {
                if let Some(x) = tab[k as int] {
                    if same_type(func_type(m, x), &m.types@[ty as int]) {
                        lemma_call(m, cs, c, popn(f, 1), x);
                    }
                }
            }
        },
        _ => {},
    }
}

/// A call from `f` (the top frame with the table index already popped for
/// `call_indirect`) to function `x`, whose type matches the instruction's.
pub proof fn lemma_call(m: &Module, cs: Seq<FuncCert>, c: Config, f: Frame, x: nat)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        f.func == top(c).func,
        f.pc == top(c).pc,
        f.labels == top(c).labels,
        f.locals == top(c).locals,
        f.pc < m.funcs@[f.func as int].body@.len(),
        is_call(m.funcs@[f.func as int].body@[f.pc as int]),
        local_ok(m, f.func, cert_of(cs, f), f.pc as int),
        x < m.func_types@.len(),
        f.stack.len() == hgt(cert_of(cs, f), f.pc as int)
            - (if m.funcs@[f.func as int].body@[f.pc as int] is CallIndirect { 1int } else { 0int }),
        same_type(func_type(m, x), call_type(m, m.funcs@[f.func as int].body@[f.pc as int])),
    ensures step_ok(m, cs, c, call(m, c, f, x)),
{
    let t = func_type(m, x);
    let n = n_params(t);
    let i = m.funcs@[f.func as int].body@[f.pc as int];
    assert(n == n_params(call_type(m, i)));
    let caller = popn(f, n);
    assert(frame_waiting(m, cs, caller, t));
    if x >= n_imp(m) {
        let dd = (x - n_imp(m)) as nat;
        let args = f.stack.subrange(f.stack.len() - n, f.stack.len() as int);
        let nf = new_frame(m, dd, args);
        assert(func_cert_ok(m, dd, cs[dd as int]));
        let fc2 = cs[dd as int];
        lemma_labels_wf(m, dd, fc2);
        lemma_chain_unfold(fc2.labels@, 0);
        assert(nf.labels =~= chain(fc2.labels@, 0));
        assert(frame_at(m, cs, nf));
        let fr2 = c.frames.update(c.frames.len() - 1, caller).push(nf);
        assert(dd + n_imp(m) == x);
        assert forall|j: int| 0 <= j < fr2.len() - 1 implies
            #[trigger] frame_waiting(m, cs, fr2[j], func_type(m, fr2[j + 1].func + n_imp(m))) by {
            if j < fr2.len() - 2 {
                assert(frame_waiting(m, cs, c.frames[j], func_type(m, c.frames[j + 1].func + n_imp(m))));
            }
        }
    } else {
        let cfg = with_top(c, caller);
        assert forall|j: int| 0 <= j < cfg.frames.len() - 1 implies
            #[trigger] frame_waiting(m, cs, cfg.frames[j], func_type(m, cfg.frames[j + 1].func + n_imp(m))) by {
            assert(frame_waiting(m, cs, c.frames[j], func_type(m, c.frames[j + 1].func + n_imp(m))));
        }
    }
}

/// Resuming after a host call with the right number of results restores
/// the invariant.
pub proof fn lemma_resume(m: &Module, cs: Seq<FuncCert>, c: Config, x: nat, s: Store, results: Seq<u64>)
    requires
        certs_ok(m, cs),
        inv_host(m, cs, c, x),
        store_ok(m, s),
        results.len() == n_results(func_type(m, x)),
    ensures inv(m, cs, resume(c, s, results)),
{
    let f = top(c);
    let fc = cert_of(cs, f);
    assert(func_cert_ok(m, f.func, cs[f.func as int]));
    assert(pc_ok(m, f.func, fc, f.pc as int));
    let c2 = resume(c, s, results);
    assert(frame_at(m, cs, top(c2)));
    assert forall|j: int| 0 <= j < c2.frames.len() - 1 implies
        #[trigger] frame_waiting(m, cs, c2.frames[j], func_type(m, c2.frames[j + 1].func + n_imp(m))) by {
        assert(frame_waiting(m, cs, c.frames[j], func_type(m, c.frames[j + 1].func + n_imp(m))));
    }
}

} // verus!
