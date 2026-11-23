//! Prepares checked functions for the interpreter: resolves every branch
//! target from the certificate, proven to give `code_ok`.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::cert::*;
use crate::preserve::*;
use crate::check::*;
use crate::interp::*;

verus! {

proof fn lemma_nth_le(ls: Seq<LabelRec>, l: u32, k: nat)
    requires nth_id(ls, l, k) is Some,
    ensures k <= l,
    decreases k,
{
    if k > 0 {
        let p = ls[l as int].parent;
        lemma_nth_le(ls, p, (k - 1) as nat);
    }
}

fn target_x(fc: &FuncCert, pc: usize, k: u32) -> (r: BrTarget)
    requires
        labels_wf(fc.labels@),
        pc < fc.lab@.len(),
        nth_id(fc.labels@, fc.lab@[pc as int], k as nat) is Some,
    ensures r == target_of(*fc, pc as int, k as nat),
{
    let l = fc.lab[pc];
    let id = match exec_nth_id(fc, l, k) {
        Some(id) => id,
        None => { proof { assert(false); } 0 },
    };
    proof { lemma_nth(fc.labels@, l, k as nat); }
    let r = fc.labels[id as usize];
    BrTarget { pc: r.cont, arity: r.arity, height: r.height }
}

/// Facts about the control instruction at live position `pc`.
proof fn lemma_ctl(m: &Module, d: nat, fc: FuncCert, pc: int)
    requires
        func_cert_ok(m, d, fc),
        0 <= pc < m.funcs@[d as int].body@.len(),
        live(fc, pc),
    ensures ({
        let i = m.funcs@[d as int].body@[pc];
        let l = lab(fc, pc);
        &&& (l as nat) < fc.labels@.len()
        &&& labels_wf(fc.labels@)
        &&& (i matches Instr::Br(k) ==> nth_id(fc.labels@, l, k as nat) is Some)
        &&& (i matches Instr::BrIf(k) ==> nth_id(fc.labels@, l, k as nat) is Some)
        &&& (i is Else ==> nth_id(fc.labels@, l, 0) is Some)
        &&& (i is Return ==> chain(fc.labels@, l).len() >= 1
            && nth_id(fc.labels@, l, (chain(fc.labels@, l).len() - 1) as nat) is Some)
        &&& (i matches Instr::BrTable { start, len } ==> start as nat + len as nat <= m.br_table@.len()
            && forall|j: int| start <= j < start + len
                ==> nth_id(fc.labels@, l, #[trigger] m.br_table@[j] as nat) is Some)
    }),
{
    assert(pc_ok(m, d, fc, pc));
    lemma_labels_wf(m, d, fc);
    let i = m.funcs@[d as int].body@[pc];
    let l = lab(fc, pc);
    if i is Br || i is BrIf || i is Else || i is Return || i is BrTable {
        assert(!is_unop(i) && !is_binop(i) && load_kind(i) is None && store_kind(i) is None);
    }
    if let Instr::BrTable { start, len } = i {
        assert forall|j: int| start <= j < start + len
            implies nth_id(fc.labels@, l, #[trigger] m.br_table@[j] as nat) is Some by {
            assert(br_ok(fc, pc, m.br_table@[j] as nat, 1));
        }
    }
}

/// The interpreter's form of defined function `d`; `None` only if its
/// `br_table` targets do not fit in 32-bit offsets.
pub fn compile(m: &Module, cs: &Vec<FuncCert>, d: usize) -> (r: Option<Code>)
    requires certs_ok(m, cs@), d < m.funcs@.len(),
    ensures r matches Some(code) ==> code_ok(m, cs@, d as nat, &code),
{
    let fc = &cs[d];
    proof {
        assert(func_cert_ok(m, d as nat, cs@[d as int]));
        lemma_labels_wf(m, d as nat, *fc);
    }
    let body = &m.funcs[d].body;
    let len = body.len();
    let mut ops: Vec<Instr> = Vec::new();
    let mut side: Vec<BrTarget> = Vec::new();
    let mut table: Vec<BrTarget> = Vec::new();
    let zero = BrTarget { pc: 0, arity: 0, height: 0 };
    let mut pc = 0;
    while pc < len
        invariant
            certs_ok(m, cs@),
            d < m.funcs@.len(),
            *fc == cs@[d as int],
            func_cert_ok(m, d as nat, *fc),
            labels_wf(fc.labels@),
            *body == m.funcs@[d as int].body,
            len == body@.len(),
            pc <= len,
            ops@.len() == pc,
            side@.len() == pc,
            forall|q: int| 0 <= q < pc ==> ops@[q] == #[trigger] body@[q],
            forall|q: int| 0 <= q < pc && live(*fc, q) ==> #[trigger] side_ok(m, *fc, side@, table@, q, body@[q]),
        decreases len - pc,
    {
        let i = body[pc];
        let live_pc = fc.h[pc] != NONE;
        proof {
            if live_pc { lemma_ctl(m, d as nat, *fc, pc as int); }
        }
        let ghost side0 = side@;
        let ghost table0 = table@;
        let t = if !live_pc {
            zero
        } else {
            match i {
                Instr::Br(k) | Instr::BrIf(k) => target_x(fc, pc, k),
                Instr::Else { .. } => target_x(fc, pc, 0),
                Instr::Return => {
                    let depth = exec_depth(fc, fc.lab[pc]);
                    proof { lemma_nth_le(fc.labels@, fc.lab@[pc as int], (depth - 1) as nat); }
                    target_x(fc, pc, (depth - 1) as u32)
                },
                Instr::BrTable { start, len: tl } => {
                    let base = table.len();
                    if base > u32::MAX as usize - tl as usize {
                        return None;
                    }
                    let mut j: u32 = 0;
                    while j < tl
                        invariant
                            labels_wf(fc.labels@),
                            live(*fc, pc as int),
                            pc < fc.lab@.len(),
                            start as nat + tl as nat <= m.br_table@.len(),
                            forall|jj: int| start <= jj < start + tl
                                ==> nth_id(fc.labels@, fc.lab@[pc as int], #[trigger] m.br_table@[jj] as nat) is Some,
                            j <= tl,
                            table@.len() == base + j,
                            table@.subrange(0, base as int) == table0,
                            base == table0.len(),
                            forall|jj: int| 0 <= jj < j ==> #[trigger] table@[base + jj]
                                == target_of(*fc, pc as int, m.br_table@[start + jj] as nat),
                        decreases tl - j,
                    {
                        let k = m.br_table[start as usize + j as usize];
                        assert(nth_id(fc.labels@, fc.lab@[pc as int], m.br_table@[start + j] as nat) is Some);
                        let tg = target_x(fc, pc, k);
                        let ghost t1 = table@;
                        table.push(tg);
                        proof {
                            assert(table@.subrange(0, base as int) =~= t1.subrange(0, base as int));
                            assert forall|jj: int| 0 <= jj < j + 1 implies #[trigger] table@[base + jj]
                                == target_of(*fc, pc as int, m.br_table@[start + jj] as nat) by {
                                if jj < j { assert(table@[base + jj] == t1[base + jj]); }
                            }
                        }
                        j = j + 1;
                    }
                    BrTarget { pc: base as u32, arity: 0, height: 0 }
                },
                _ => zero,
            }
        };
        ops.push(i);
        side.push(t);
        proof {
            assert forall|q: int| 0 <= q < pc + 1 && live(*fc, q)
                implies #[trigger] side_ok(m, *fc, side@, table@, q, body@[q]) by {
                if q < pc {
                    assert(side_ok(m, *fc, side0, table0, q, body@[q]));
                    assert(side@[q] == side0[q]);
                    if let Instr::BrTable { start, len: tl } = body@[q] {
                        assert forall|j: int| 0 <= j < tl implies #[trigger] table@[side@[q].pc + j]
                            == target_of(*fc, q, m.br_table@[start + j] as nat) by {
                            assert(table0[side0[q].pc + j] == target_of(*fc, q, m.br_table@[start + j] as nat));
                            assert(table@.subrange(0, table0.len() as int)[side0[q].pc + j] == table0[side0[q].pc + j]);
                        }
                    }
                } else {
                    if let Instr::BrTable { start, len: tl } = body@[q] {
                        assert forall|j: int| 0 <= j < tl implies #[trigger] table@[side@[q].pc + j]
                            == target_of(*fc, q, m.br_table@[start + j] as nat) by {
                            assert(table@[table0.len() + j] == target_of(*fc, q, m.br_table@[start + j] as nat));
                        }
                    }
                }
            }
        }
        pc = pc + 1;
    }
    let ghost side1 = side@;
    ops.push(Instr::Unreachable);
    side.push(zero);
    let ft = &m.types[m.func_types[d + m.n_imported_funcs as usize] as usize];
    let np = ft.params.len();
    let nr = ft.results.len();
    proof {
        assert(n_locals(m, d as nat) <= MAX_LOCALS as nat);
        assert(n_results(func_type(m, (d + n_imp(m)) as nat)) <= MAX_HEIGHT as nat);
    }
    let nl = np + m.funcs[d].locals.len();
    let mut code = Code {
        ops, side, table,
        n_params: np as u32,
        n_locals: nl as u32,
        n_results: nr as u32,
        frame: nl as u32 + fc.max_height,
        rops: Vec::new(),
        entry: Vec::new(),
    };
    if len >= NONE as usize {
        return None;
    }
    // The translation is checked; if it is rejected, every instruction
    // runs as a stack instruction instead.
    let (rops, entry) = crate::reg::translate(&code, fc, body);
    code.rops = rops;
    code.entry = entry;
    if !crate::rcheck::check_rcode(m, d, fc, &code) {
        let (rops, entry) = crate::reg::trivial(&code, fc, len);
        code.rops = rops;
        code.entry = entry;
        if !crate::rcheck::check_rcode(m, d, fc, &code) {
            return None;
        }
    }
    proof {
        assert forall|q: int| 0 <= q < len && live(*fc, q)
            implies #[trigger] side_ok(m, *fc, code.side@, code.table@, q, body@[q]) by {
            assert(side_ok(m, *fc, side1, code.table@, q, body@[q]));
            assert(code.side@[q] == side1[q]);
        }
    }
    Some(code)
}

/// Compiles every defined function.
pub fn compile_all(m: &Module, cs: &Vec<FuncCert>) -> (r: Option<Vec<Code>>)
    requires certs_ok(m, cs@),
    ensures r matches Some(codes) ==> codes_ok(m, cs@, codes@),
{
    let mut codes: Vec<Code> = Vec::new();
    let mut d = 0;
    while d < m.funcs.len()
        invariant
            certs_ok(m, cs@),
            d <= m.funcs@.len(),
            codes@.len() == d,
            forall|e: nat| e < d ==> #[trigger] code_ok(m, cs@, e, &codes@[e as int]),
        decreases m.funcs@.len() - d,
    {
        match compile(m, cs, d) {
            Some(c) => codes.push(c),
            None => return None,
        }
        d = d + 1;
    }
    Some(codes)
}

} // verus!
