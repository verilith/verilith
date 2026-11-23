//! The certificate checker: exec code proven to accept only certificates
//! satisfying `crate::cert::certs_ok`.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::cert::*;
#[allow(unused_imports)]
use crate::preserve::*;

verus! {

pub fn check_module(m: &Module) -> (r: bool)
    ensures r ==> module_ok(m),
{
    if m.n_imported_funcs as usize > m.func_types.len() || m.mems.len() > 1
        || m.func_types.len() >= NONE as usize {
        return false;
    }
    if m.funcs.len() != m.func_types.len() - m.n_imported_funcs as usize {
        return false;
    }
    let ft_len = m.func_types.len();
    let mut x = 0;
    while x < m.func_types.len()
        invariant
            x <= m.func_types@.len(),
            forall|y: int| 0 <= y < x ==> (#[trigger] m.func_types@[y]) < m.types@.len(),
        decreases m.func_types@.len() - x,
    {
        if m.func_types[x] as usize >= m.types.len() {
            return false;
        }
        x += 1;
    }
    let mut d = 0;
    while d < m.funcs.len()
        invariant
            d <= m.funcs@.len(),
            m.funcs@.len() == m.func_types@.len() - m.n_imported_funcs as nat,
            m.n_imported_funcs as nat <= m.func_types@.len(),
            m.func_types@.len() < NONE as nat,
            forall|y: int| 0 <= y < m.func_types@.len() ==> (#[trigger] m.func_types@[y]) < m.types@.len(),
            forall|e: nat| e < d ==> #[trigger] n_locals(m, e) <= MAX_LOCALS as nat,
            ft_len == m.func_types@.len(),
        decreases m.funcs@.len() - d,
    {
        let t = m.func_types[d + m.n_imported_funcs as usize] as usize;
        let np = m.types[t].params.len();
        let nl = m.funcs[d].locals.len();
        if np > MAX_LOCALS as usize || nl > MAX_LOCALS as usize - np {
            return false;
        }
        assert(n_locals(m, d as nat) == np + nl);
        d += 1;
    }
    true
}

pub fn exec_at(fc: &FuncCert, q: usize, h: u64, l: u32) -> (r: bool)
    ensures r == at(*fc, q as int, h as nat, l),
{
    q < fc.h.len() && q < fc.lab.len() && fc.h[q] != NONE && fc.h[q] as u64 == h && fc.lab[q] == l
}

pub fn exec_bt_arity(m: &Module, bt: BlockType) -> (r: Option<(u64, u64)>)
    ensures
        match r {
            Some((a, b)) => bt_arity(m, bt) == Some((a as nat, b as nat)),
            None => bt_arity(m, bt) is None,
        },
{
    match bt {
        BlockType::Empty => Some((0, 0)),
        BlockType::Val(_) => Some((0, 1)),
        BlockType::Type(i) => if (i as usize) < m.types.len() {
            Some((m.types[i as usize].params.len() as u64, m.types[i as usize].results.len() as u64))
        } else {
            None
        },
    }
}

pub fn exec_nth_id(fc: &FuncCert, l: u32, k: u32) -> (r: Option<u32>)
    requires labels_wf(fc.labels@),
    ensures r == nth_id(fc.labels@, l, k as nat),
{
    let mut cur = l;
    let mut j = k;
    while j > 0
        invariant
            labels_wf(fc.labels@),
            nth_id(fc.labels@, l, k as nat) == nth_id(fc.labels@, cur, j as nat),
        decreases j,
    {
        if cur as usize >= fc.labels.len() {
            return None;
        }
        let p = fc.labels[cur as usize].parent;
        if !(p < cur) {
            return None;
        }
        cur = p;
        j -= 1;
    }
    if (cur as usize) < fc.labels.len() { Some(cur) } else { None }
}

/// The number of labels in `l`'s chain.
pub fn exec_depth(fc: &FuncCert, l: u32) -> (r: u64)
    requires labels_wf(fc.labels@),
    ensures r as nat == chain(fc.labels@, l).len(),
{
    let ghost ls = fc.labels@;
    let mut cur = l;
    let mut n: u64 = 0;
    while (cur as usize) < fc.labels.len()
        invariant
            ls == fc.labels@,
            labels_wf(ls),
            n as nat + chain(ls, cur).len() == chain(ls, l).len(),
            n <= l as nat + 1 - (if (cur as nat) < ls.len() { cur as nat + 1 } else { 0 }),
            cur <= l || (cur as nat) >= ls.len(),
        decreases cur as nat + 1 - (if (cur as nat) < ls.len() { 0nat } else { cur as nat + 1 }),
    {
        proof { crate::preserve::lemma_chain_unfold(ls, cur); }
        let p = fc.labels[cur as usize].parent;
        n += 1;
        if p == NONE {
            assert(chain(ls, p).len() == 0);
            cur = p;
        } else {
            cur = p;
        }
    }
    n
}

/// Branching to label `k` from `pc` with `pops` values popped is fine.
fn exec_br_ok(fc: &FuncCert, pc: usize, k: u32, pops: u64) -> (r: bool)
    requires
        labels_wf(fc.labels@),
        pc < fc.lab@.len(),
        pc < fc.h@.len(),
        pops <= 1,
    ensures r ==> br_ok(*fc, pc as int, k as nat, pops as nat),
{
    match exec_nth_id(fc, fc.lab[pc], k) {
        Some(id) => {
            proof { crate::preserve::lemma_nth(fc.labels@, fc.lab@[pc as int], k as nat); }
            let r = fc.labels[id as usize];
            fc.h[pc] as u64 >= pops + r.height as u64 + r.arity as u64
        },
        None => false,
    }
}

fn n_locals_x(m: &Module, d: usize) -> (r: u64)
    requires module_ok(m), d < m.funcs@.len(),
    ensures r as nat == n_locals(m, d as nat),
{
    let ft_len = m.func_types.len();
    let t = m.func_types[d + m.n_imported_funcs as usize] as usize;
    assert(n_locals(m, d as nat) <= MAX_LOCALS as nat);
    (m.types[t].params.len() + m.funcs[d].locals.len()) as u64
}

/// The local check for the instruction at live position `pc`.
pub fn check_instr(m: &Module, d: usize, fc: &FuncCert, pc: usize) -> (r: bool)
    requires
        module_ok(m),
        d < m.funcs@.len(),
        labels_wf(fc.labels@),
        pc < m.funcs@[d as int].body@.len(),
        fc.h@.len() == m.funcs@[d as int].body@.len() + 1,
        fc.lab@.len() == m.funcs@[d as int].body@.len() + 1,
        live(*fc, pc as int),
        hgt(*fc, pc as int) <= MAX_HEIGHT as nat,
        m.funcs@[d as int].body@.len() < NONE,
    ensures r ==> local_ok(m, d as nat, *fc, pc as int),
{
    let i = m.funcs[d].body[pc];
    let len = m.funcs[d].body.len();
    let h = fc.h[pc] as u64;
    let l = fc.lab[pc];
    let n = pc + 1;
    match i {
        Instr::Unreachable => { let r = true; assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::Nop => { let r = exec_at(fc, n, h, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::Block { .. } | Instr::Loop { .. } | Instr::If { .. } | Instr::Else { .. } | Instr::End
        | Instr::Br(_) | Instr::BrIf(_) | Instr::BrTable { .. } | Instr::Return => check_control(m, d, fc, pc),
        Instr::Call(x) => {
            if x as usize >= m.func_types.len() {
                return false;
            }
            let t = &m.types[m.func_types[x as usize] as usize];
            let np = t.params.len() as u64;
            let nr = t.results.len() as u64;
            let r = h >= np && nr <= MAX_HEIGHT as u64 && exec_at(fc, n, h - np + nr, l);
            assert(r ==> local_ok(m, d as nat, *fc, pc as int));
            r
        },
        Instr::CallIndirect { ty, table } => {
            if ty as usize >= m.types.len() || table as usize >= m.tables.len() {
                return false;
            }
            let t = &m.types[ty as usize];
            let np = t.params.len() as u64;
            let nr = t.results.len() as u64;
            let r = np < MAX_HEIGHT as u64 && h >= 1 + np && nr <= MAX_HEIGHT as u64 && exec_at(fc, n, h - 1 - np + nr, l);
            assert(r ==> local_ok(m, d as nat, *fc, pc as int));
            r
        },
        Instr::Drop => { let r = h >= 1 && exec_at(fc, n, h - 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::Select => { let r = h >= 3 && exec_at(fc, n, h - 2, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::LocalGet(x) => { let r = (x as u64) < n_locals_x(m, d) && exec_at(fc, n, h + 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::LocalSet(x) => { let r = (x as u64) < n_locals_x(m, d) && h >= 1 && exec_at(fc, n, h - 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::LocalTee(x) => { let r = (x as u64) < n_locals_x(m, d) && h >= 1 && exec_at(fc, n, h, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::GlobalGet(x) => { let r = (x as usize) < m.global_types.len() && exec_at(fc, n, h + 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::GlobalSet(x) => { let r = (x as usize) < m.global_types.len() && h >= 1 && exec_at(fc, n, h - 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::MemorySize => { let r = m.mems.len() >= 1 && exec_at(fc, n, h + 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::MemoryGrow => { let r = m.mems.len() >= 1 && h >= 1 && exec_at(fc, n, h, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::MemoryFill | Instr::MemoryCopy => { let r = m.mems.len() >= 1 && h >= 3 && exec_at(fc, n, h - 3, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::MemoryInit(x) => m.mems.len() >= 1 && (x as usize) < m.datas.len() && h >= 3
            && exec_at(fc, n, h - 3, l),
        Instr::DataDrop(x) => { let r = (x as usize) < m.datas.len() && exec_at(fc, n, h, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::I32Const(_) | Instr::I64Const(_) | Instr::F32Const(_) | Instr::F64Const(_) =>
            exec_at(fc, n, h + 1, l),
        // Numeric instructions, loads and stores.
        _ => {
            let pops: u64 = pops_of(i);
            let pushes: u64 = if store_like(i) { 0 } else { 1 };
            let r = h >= pops && exec_at(fc, n, h - pops + pushes, l);
            assert(r ==> local_ok(m, d as nat, *fc, pc as int));
            r
        },
    }
}

/// [`check_instr`] for structured control and branches.
fn check_control(m: &Module, d: usize, fc: &FuncCert, pc: usize) -> (r: bool)
    requires
        module_ok(m),
        d < m.funcs@.len(),
        labels_wf(fc.labels@),
        pc < m.funcs@[d as int].body@.len(),
        fc.h@.len() == m.funcs@[d as int].body@.len() + 1,
        fc.lab@.len() == m.funcs@[d as int].body@.len() + 1,
        live(*fc, pc as int),
        hgt(*fc, pc as int) <= MAX_HEIGHT as nat,
        m.funcs@[d as int].body@.len() < NONE,
    ensures r ==> local_ok(m, d as nat, *fc, pc as int),
{
    let i = m.funcs[d].body[pc];
    let len = m.funcs[d].body.len();
    let h = fc.h[pc] as u64;
    let l = fc.lab[pc];
    let n = pc + 1;
    match i {
        Instr::Block { bt, end } => match exec_bt_arity(m, bt) {
            Some((np, nr)) => {
                if np > MAX_HEIGHT as u64 || nr > MAX_HEIGHT as u64 || h < np || !(n < fc.h.len()) || fc.h[n] == NONE || fc.h[n] as u64 != h {
                    return false;
                }
                let k = fc.lab[n];
                if k as usize >= fc.labels.len() || nr >= NONE as u64 || end as u64 + 1 > len as u64 {
                    return false;
                }
                let lr = fc.labels[k as usize];
                let r = lr.arity == nr as u32 && lr.cont == end + 1 && lr.height == (h - np) as u32 && lr.parent == l;
                assert(r ==> local_ok(m, d as nat, *fc, pc as int));
                r
            },
            None => false,
        },
        Instr::Loop { bt } => match exec_bt_arity(m, bt) {
            Some((np, nr)) => {
                if np > MAX_HEIGHT as u64 || nr > MAX_HEIGHT as u64 || h < np || !(n < fc.h.len()) || fc.h[n] == NONE || fc.h[n] as u64 != h {
                    return false;
                }
                let k = fc.lab[n];
                if k as usize >= fc.labels.len() || np >= NONE as u64 {
                    return false;
                }
                let lr = fc.labels[k as usize];
                let r = lr.arity == np as u32 && lr.cont == pc as u32 && lr.height == (h - np) as u32 && lr.parent == l;
                assert(r ==> local_ok(m, d as nat, *fc, pc as int));
                r
            },
            None => false,
        },
        Instr::If { bt, else_, end } => match exec_bt_arity(m, bt) {
            Some((np, nr)) => {
                if np > MAX_HEIGHT as u64 || nr > MAX_HEIGHT as u64 || h < np + 1 || !(n < fc.h.len()) || fc.h[n] == NONE || fc.h[n] as u64 != h - 1 {
                    return false;
                }
                let k = fc.lab[n];
                if k as usize >= fc.labels.len() || nr >= NONE as u64 || end as u64 + 1 > len as u64 {
                    return false;
                }
                let lr = fc.labels[k as usize];
                if !(lr.arity == nr as u32 && lr.cont == end + 1 && lr.height == (h - 1 - np) as u32 && lr.parent == l) {
                    return false;
                }
                let r = if else_ == end {
                    exec_at(fc, end as usize, h - 1, k)
                } else {
                    else_ < NONE && exec_at(fc, else_ as usize + 1, h - 1, k)
                };
                assert(r ==> local_ok(m, d as nat, *fc, pc as int));
                r
            },
            None => false,
        },
        Instr::Else { .. } => {
            (l as usize) < fc.labels.len()
                && h == fc.labels[l as usize].height as u64 + fc.labels[l as usize].arity as u64
        },
        Instr::End => {
            (l as usize) < fc.labels.len()
                && exec_at(fc, n, h, fc.labels[l as usize].parent)
        },
        Instr::Br(k) => { let r = exec_br_ok(fc, pc, k, 0); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::BrIf(k) => { let r = h >= 1 && exec_br_ok(fc, pc, k, 1) && exec_at(fc, n, h - 1, l); assert(r ==> local_ok(m, d as nat, *fc, pc as int)); r },
        Instr::BrTable { start, len: tl } => {
            if h < 1 || tl < 1 || start as usize > m.br_table.len() || tl as usize > m.br_table.len() - start as usize {
                return false;
            }
            let mut j = start as usize;
            let e = start as usize + tl as usize;
            while j < e
                invariant
                    start <= j <= e,
                    e == start + tl,
                    e <= m.br_table@.len(),
                    labels_wf(fc.labels@),
                    pc < fc.lab@.len(),
                    pc < fc.h@.len(),
                    forall|q: int| start <= q < j ==> br_ok(*fc, pc as int, #[trigger] m.br_table@[q] as nat, 1),
                decreases e - j,
            {
                if !exec_br_ok(fc, pc, m.br_table[j], 1) {
                    return false;
                }
                j += 1;
            }
            assert(local_ok(m, d as nat, *fc, pc as int));
            true
        },
        Instr::Return => {
            let dep = exec_depth(fc, l);
            let r = dep >= 1 && dep - 1 <= u32::MAX as u64 && exec_br_ok(fc, pc, (dep - 1) as u32, 0);
            assert(r ==> local_ok(m, d as nat, *fc, pc as int));
            r
        },
        _ => false,
    }
}

/// Operands popped by a numeric, load or store instruction.
#[inline(always)]
fn pops_of(i: Instr) -> (r: u64)
    ensures
        is_unop(i) ==> r == 1,
        is_binop(i) ==> r == 2,
        load_kind(i) is Some ==> r == 1,
        store_kind(i) is Some ==> r == 2,
{
    if is_binop_x(i) || store_like(i) { 2 } else { 1 }
}

fn is_binop_x(i: Instr) -> (r: bool)
    ensures r == is_binop(i),
{
    match i {
        Instr::I32Eq | Instr::I32Ne | Instr::I32LtS | Instr::I32LtU | Instr::I32GtS
        | Instr::I32GtU | Instr::I32LeS | Instr::I32LeU | Instr::I32GeS | Instr::I32GeU
        | Instr::I32Add | Instr::I32Sub | Instr::I32Mul | Instr::I32DivS | Instr::I32DivU
        | Instr::I32RemS | Instr::I32RemU | Instr::I32And | Instr::I32Or | Instr::I32Xor
        | Instr::I32Shl | Instr::I32ShrS | Instr::I32ShrU | Instr::I32Rotl | Instr::I32Rotr
        | Instr::I64Eq | Instr::I64Ne | Instr::I64LtS | Instr::I64LtU | Instr::I64GtS
        | Instr::I64GtU | Instr::I64LeS | Instr::I64LeU | Instr::I64GeS | Instr::I64GeU
        | Instr::I64Add | Instr::I64Sub | Instr::I64Mul | Instr::I64DivS | Instr::I64DivU
        | Instr::I64RemS | Instr::I64RemU | Instr::I64And | Instr::I64Or | Instr::I64Xor
        | Instr::I64Shl | Instr::I64ShrS | Instr::I64ShrU | Instr::I64Rotl | Instr::I64Rotr
        | Instr::FBin(_) | Instr::FCmp(_) => true,
        _ => false,
    }
}

fn store_like(i: Instr) -> (r: bool)
    ensures r == (store_kind(i) is Some),
{
    match i {
        Instr::I32Store(_) | Instr::I64Store(_) | Instr::F32Store(_) | Instr::F64Store(_)
        | Instr::I32Store8(_) | Instr::I32Store16(_) | Instr::I64Store8(_) | Instr::I64Store16(_)
        | Instr::I64Store32(_) => true,
        _ => false,
    }
}

/// Checks one function's certificate.
pub fn check_func(m: &Module, d: usize, fc: &FuncCert) -> (r: bool)
    requires module_ok(m), d < m.funcs@.len(),
    ensures r ==> func_cert_ok(m, d as nat, *fc),
{
    let len = m.funcs[d].body.len();
    let ft_len = m.func_types.len();
    let t = &m.types[m.func_types[d + m.n_imported_funcs as usize] as usize];
    let nres = t.results.len();
    if len < 1 || len >= NONE as usize || fc.h.len() != len + 1 || fc.lab.len() != len + 1
        || fc.max_height > MAX_HEIGHT || fc.labels.len() < 1 || fc.labels.len() >= NONE as usize
        || nres > MAX_HEIGHT as usize {
        return false;
    }
    let r0 = fc.labels[0];
    if !(r0.arity == nres as u32 && r0.cont == len as u32 && r0.height == 0 && r0.parent == NONE) {
        return false;
    }
    if !exec_at(fc, 0, 0, 0) || !exec_at(fc, len, nres as u64, NONE) {
        return false;
    }
    // Label records.
    let mut k = 0;
    while k < fc.labels.len()
        invariant
            k <= fc.labels@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] rec_ok(*fc, len as nat, j),
        decreases fc.labels@.len() - k,
    {
        let r = fc.labels[k];
        if !((r.parent as usize) < k || r.parent == NONE) || r.cont as usize > len
            || r.height as u64 + r.arity as u64 > MAX_HEIGHT as u64
            || !exec_at(fc, r.cont as usize, r.height as u64 + r.arity as u64, r.parent) {
            return false;
        }
        k += 1;
    }
    assert(labels_wf(fc.labels@)) by {
        assert forall|j: int| 0 <= j < fc.labels@.len() implies
            (#[trigger] fc.labels@[j]).parent < j || fc.labels@[j].parent == NONE by {
            assert(rec_ok(*fc, len as nat, j));
        }
    }
    // Heights.
    let mut pc = 0;
    while pc <= len
        invariant
            pc <= len + 1,
            len < NONE,
            fc.h@.len() == len + 1,
            forall|q: int| 0 <= q < pc && live(*fc, q) ==> #[trigger] hgt(*fc, q) <= fc.max_height,
        decreases len + 1 - pc,
    {
        if fc.h[pc] != NONE && fc.h[pc] > fc.max_height {
            return false;
        }
        pc += 1;
    }
    // Instructions.
    let mut i = 0;
    while i < len
        invariant
            module_ok(m),
            d < m.funcs@.len(),
            len == m.funcs@[d as int].body@.len(),
            len < NONE,
            fc.h@.len() == len + 1,
            fc.lab@.len() == len + 1,
            labels_wf(fc.labels@),
            fc.max_height <= MAX_HEIGHT,
            forall|q: int| 0 <= q <= len && live(*fc, q) ==> #[trigger] hgt(*fc, q) <= fc.max_height,
            forall|q: int| 0 <= q < i ==> #[trigger] pc_ok(m, d as nat, *fc, q),
        decreases len - i,
    {
        if fc.h[i] != NONE {
            assert(hgt(*fc, i as int) <= fc.max_height);
            if fc.lab[i] as usize >= fc.labels.len() || !check_instr(m, d, fc, i) {
                return false;
            }
            assert(local_ok(m, d as nat, *fc, i as int));
        }
        assert(pc_ok(m, d as nat, *fc, i as int));
        i += 1;
    }
    let ghost body = m.funcs@[d as int].body@;
    let ghost nres2 = n_results(func_type(m, d as nat + n_imp(m)));
    assert(nres2 == nres);
    assert(at(*fc, 0, 0, 0));
    assert(at(*fc, len as int, nres2, NONE));
    assert(fc.labels@[0] == (LabelRec { arity: nres2 as u32, cont: len as u32, height: 0, parent: NONE }));
    assert(forall|k: int| 0 <= k < fc.labels@.len() ==> #[trigger] rec_ok(*fc, len as nat, k));
    assert(forall|pc: int| 0 <= pc <= len && live(*fc, pc) ==> #[trigger] hgt(*fc, pc) <= fc.max_height);
    true
}

pub fn check_certs(m: &Module, cs: &Vec<FuncCert>) -> (r: bool)
    ensures r ==> certs_ok(m, cs@),
{
    if !check_module(m) || cs.len() != m.funcs.len() {
        return false;
    }
    let mut d = 0;
    while d < cs.len()
        invariant
            module_ok(m),
            cs@.len() == m.funcs@.len(),
            d <= cs@.len(),
            forall|e: nat| e < d ==> #[trigger] func_cert_ok(m, e, cs@[e as int]),
        decreases cs@.len() - d,
    {
        if !check_func(m, d, &cs[d]) {
            return false;
        }
        d += 1;
    }
    true
}

} // verus!
