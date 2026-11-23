//! The validator (§3). Not verified: besides checking the module's types
//! it produces the stack-height certificates that [`crate::check`]
//! verifies, so a validator bug can only make vwasm reject a module (or
//! accept a type-incorrect one, which then still cannot escape).
use crate::ast::*;
use crate::cert::{FuncCert, LabelRec, MAX_HEIGHT, MAX_LOCALS, NONE};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidateError(pub String);

type R<T> = Result<T, ValidateError>;

fn err<T>(msg: &str) -> R<T> {
    Err(ValidateError(msg.to_string()))
}

use ValType::*;

/// Validates `m` and returns the certificate of every defined function.
pub fn validate(m: &Module) -> R<Vec<FuncCert>> {
    for &t in &m.func_types {
        if t as usize >= m.types.len() {
            return err("unknown type");
        }
    }
    if m.func_types.len() >= NONE as usize {
        return err("too many functions");
    }
    for t in &m.tables {
        if let Some(max) = t.max {
            if max < t.min {
                return err("size minimum must not be greater than maximum");
            }
        }
    }
    if m.mems.len() > 1 {
        return err("multiple memories");
    }
    for l in &m.mems {
        if l.min > 65536 || l.max.is_some_and(|x| x > 65536) {
            return err("memory size must be at most 65536 pages (4GiB)");
        }
        if let Some(max) = l.max {
            if max < l.min {
                return err("size minimum must not be greater than maximum");
            }
        }
    }
    let nf = m.func_types.len() as u32;
    let ng_imp = m.n_imported_globals;
    for (i, e) in m.globals.iter().enumerate() {
        let gt = m.global_types[ng_imp as usize + i];
        const_expr(m, e, gt.vt)?;
    }
    let mut names = std::collections::HashSet::new();
    for e in &m.exports {
        if !names.insert(e.name.clone()) {
            return err("duplicate export name");
        }
        let ok = match e.desc {
            ExportDesc::Func(x) => x < nf,
            ExportDesc::Table(x) => (x as usize) < m.tables.len(),
            ExportDesc::Mem(x) => (x as usize) < m.mems.len(),
            ExportDesc::Global(x) => (x as usize) < m.global_types.len(),
        };
        if !ok {
            return err("unknown export");
        }
    }
    if let Some(s) = m.start {
        if s >= nf {
            return err("unknown function");
        }
        let t = &m.types[m.func_types[s as usize] as usize];
        if !t.params.is_empty() || !t.results.is_empty() {
            return err("start function");
        }
    }
    for e in &m.elems {
        if let ElemMode::Active { table, offset } = &e.mode {
            if *table as usize >= m.tables.len() {
                return err("unknown table");
            }
            const_expr(m, offset, I32)?;
        }
        for x in e.init.iter().flatten() {
            if *x >= nf {
                return err("unknown function");
            }
        }
    }
    for d in &m.datas {
        if let DataMode::Active { offset } = &d.mode {
            if m.mems.is_empty() {
                return err("unknown memory");
            }
            const_expr(m, offset, I32)?;
        }
    }
    let mut certs = Vec::with_capacity(m.funcs.len());
    for (d, f) in m.funcs.iter().enumerate() {
        let t = &m.types[m.func_types[m.n_imported_funcs as usize + d] as usize];
        if t.params.len() + f.locals.len() > MAX_LOCALS as usize {
            return err("too many locals");
        }
        certs.push(func(m, t, f)?);
    }
    Ok(certs)
}

fn const_expr(m: &Module, e: &ConstExpr, want: ValType) -> R<()> {
    let t = match *e {
        ConstExpr::I32(_) => I32,
        ConstExpr::I64(_) => I64,
        ConstExpr::F32(_) => F32,
        ConstExpr::F64(_) => F64,
        ConstExpr::GlobalGet(x) => {
            if x >= m.n_imported_globals {
                return err("unknown global");
            }
            let g = m.global_types[x as usize];
            if g.mutable {
                return err("constant expression required");
            }
            g.vt
        }
        ConstExpr::RefNull | ConstExpr::RefFunc(_) => return err("type mismatch"),
    };
    if t != want {
        return err("type mismatch");
    }
    Ok(())
}

struct Ctrl {
    params: Vec<ValType>,
    results: Vec<ValType>,
    height: usize,
    unreachable: bool,
    is_loop: bool,
    is_if: bool,
    has_else: bool,
    /// The positions inside were reachable when the block was entered.
    live: bool,
    label: u32,
}

impl Ctrl {
    fn label_types(&self) -> &[ValType] {
        if self.is_loop { &self.params } else { &self.results }
    }
}

struct V<'a> {
    m: &'a Module,
    opds: Vec<Option<ValType>>,
    ctrls: Vec<Ctrl>,
}

impl V<'_> {
    fn push(&mut self, t: ValType) {
        self.opds.push(Some(t));
    }

    fn pop(&mut self) -> R<Option<ValType>> {
        let c = self.ctrls.last().unwrap();
        if self.opds.len() == c.height {
            if c.unreachable {
                return Ok(None);
            }
            return err("type mismatch");
        }
        Ok(self.opds.pop().unwrap())
    }

    fn pop_t(&mut self, t: ValType) -> R<()> {
        match self.pop()? {
            Some(u) if u != t => err("type mismatch"),
            _ => Ok(()),
        }
    }

    fn pop_all(&mut self, ts: &[ValType]) -> R<()> {
        for &t in ts.iter().rev() {
            self.pop_t(t)?;
        }
        Ok(())
    }

    fn unreachable(&mut self) {
        let c = self.ctrls.last_mut().unwrap();
        self.opds.truncate(c.height);
        c.unreachable = true;
    }

    fn label(&self, k: u32) -> R<&Ctrl> {
        let n = self.ctrls.len();
        if k as usize >= n {
            return err("unknown label");
        }
        Ok(&self.ctrls[n - 1 - k as usize])
    }

    fn bt(&self, bt: BlockType) -> R<(Vec<ValType>, Vec<ValType>)> {
        Ok(match bt {
            BlockType::Empty => (vec![], vec![]),
            BlockType::Val(t) => (vec![], vec![t]),
            BlockType::Type(x) => match self.m.types.get(x as usize) {
                Some(t) => (t.params.clone(), t.results.clone()),
                None => return err("unknown type"),
            },
        })
    }
}

fn mem_op(i: Instr) -> Option<(ValType, ValType, bool)> {
    // (address type, value type, is_store)
    use Instr::*;
    Some(match i {
        I32Load(_) | I32Load8S(_) | I32Load8U(_) | I32Load16S(_) | I32Load16U(_) => (I32, I32, false),
        I64Load(_) | I64Load8S(_) | I64Load8U(_) | I64Load16S(_) | I64Load16U(_) | I64Load32S(_)
        | I64Load32U(_) => (I32, I64, false),
        F32Load(_) => (I32, F32, false),
        F64Load(_) => (I32, F64, false),
        I32Store(_) | I32Store8(_) | I32Store16(_) => (I32, I32, true),
        I64Store(_) | I64Store8(_) | I64Store16(_) | I64Store32(_) => (I32, I64, true),
        F32Store(_) => (I32, F32, true),
        F64Store(_) => (I32, F64, true),
        _ => return None,
    })
}

/// Operand and result types of a numeric instruction.
fn num_op(i: Instr) -> Option<(&'static [ValType], ValType)> {
    use Instr::*;
    const I: &[ValType] = &[I32];
    const II: &[ValType] = &[I32, I32];
    const L: &[ValType] = &[I64];
    const LL: &[ValType] = &[I64, I64];
    const F: &[ValType] = &[F32];
    const FF: &[ValType] = &[F32, F32];
    const D: &[ValType] = &[F64];
    const DD: &[ValType] = &[F64, F64];
    Some(match i {
        I32Eqz => (I, I32),
        I32Eq | I32Ne | I32LtS | I32LtU | I32GtS | I32GtU | I32LeS | I32LeU | I32GeS | I32GeU => (II, I32),
        I64Eqz => (L, I32),
        I64Eq | I64Ne | I64LtS | I64LtU | I64GtS | I64GtU | I64LeS | I64LeU | I64GeS | I64GeU => (LL, I32),
        I32Clz | I32Ctz | I32Popcnt | I32Extend8S | I32Extend16S => (I, I32),
        I32Add | I32Sub | I32Mul | I32DivS | I32DivU | I32RemS | I32RemU | I32And | I32Or | I32Xor | I32Shl
        | I32ShrS | I32ShrU | I32Rotl | I32Rotr => (II, I32),
        I64Clz | I64Ctz | I64Popcnt | I64Extend8S | I64Extend16S | I64Extend32S => (L, I64),
        I64Add | I64Sub | I64Mul | I64DivS | I64DivU | I64RemS | I64RemU | I64And | I64Or | I64Xor | I64Shl
        | I64ShrS | I64ShrU | I64Rotl | I64Rotr => (LL, I64),
        I32WrapI64 => (L, I32),
        I64ExtendI32S | I64ExtendI32U => (I, I64),
        FUn(op) => if (op as u8) < 7 { (F, F32) } else { (D, F64) },
        FBin(op) => if (op as u8) < 7 { (FF, F32) } else { (DD, F64) },
        FCmp(op) => if (op as u8) < 6 { (FF, I32) } else { (DD, I32) },
        Cvt(op) => {
            use CvtOp::*;
            match op {
                I32TruncF32S | I32TruncF32U | I32TruncSatF32S | I32TruncSatF32U | I32ReinterpretF32 => (F, I32),
                I32TruncF64S | I32TruncF64U | I32TruncSatF64S | I32TruncSatF64U => (D, I32),
                I64TruncF32S | I64TruncF32U | I64TruncSatF32S | I64TruncSatF32U => (F, I64),
                I64TruncF64S | I64TruncF64U | I64TruncSatF64S | I64TruncSatF64U | I64ReinterpretF64 => (D, I64),
                F32ConvertI32S | F32ConvertI32U | F32ReinterpretI32 => (I, F32),
                F32ConvertI64S | F32ConvertI64U => (L, F32),
                F32DemoteF64 => (D, F32),
                F64ConvertI32S | F64ConvertI32U => (I, F64),
                F64ConvertI64S | F64ConvertI64U | F64ReinterpretI64 => (L, F64),
                F64PromoteF32 => (F, F64),
            }
        }
        _ => return None,
    })
}

fn func(m: &Module, t: &FuncType, f: &Func) -> R<FuncCert> {
    use Instr::*;
    let body = &f.body;
    let len = body.len();
    if len == 0 || len >= NONE as usize - 1 {
        return err("function too large");
    }
    let mut locals: Vec<ValType> = t.params.clone();
    locals.extend_from_slice(&f.locals);
    let mut h = vec![NONE; len + 1];
    let mut lab = vec![NONE; len + 1];
    let mut labels = vec![LabelRec { arity: t.results.len() as u32, cont: len as u32, height: 0, parent: NONE }];
    let mut v = V {
        m,
        opds: Vec::new(),
        ctrls: vec![Ctrl {
            params: vec![],
            results: t.results.clone(),
            height: 0,
            unreachable: false,
            is_loop: false,
            is_if: false,
            has_else: false,
            live: true,
            label: 0,
        }],
    };
    let mut max_height = t.results.len();
    let has_mem = !m.mems.is_empty();
    for pc in 0..len {
        let i = body[pc];
        if v.ctrls.is_empty() {
            return err("operators remaining after end of function");
        }
        let top = v.ctrls.last().unwrap();
        let mut live = top.live && !top.unreachable;
        // The `end` of an `if` without `else` is reached from the `if`.
        if matches!(i, End) && top.is_if && !top.has_else && top.live {
            live = true;
        }
        if live {
            let ht = if matches!(i, End) && top.unreachable {
                top.height + top.results.len()
            } else {
                v.opds.len()
            };
            h[pc] = ht as u32;
            lab[pc] = top.label;
            max_height = max_height.max(ht);
        }
        let cur_label = top.label;
        let cur_live = live;
        if let Some((ins, out)) = num_op(i) {
            v.pop_all(ins)?;
            v.push(out);
            continue;
        }
        if let Some((at, vt, is_store)) = mem_op(i) {
            if !has_mem {
                return err("unknown memory");
            }
            if is_store {
                v.pop_t(vt)?;
                v.pop_t(at)?;
            } else {
                v.pop_t(at)?;
                v.push(vt);
            }
            continue;
        }
        match i {
            Unreachable => v.unreachable(),
            Nop => {}
            Block { bt, .. } | Loop { bt } | If { bt, .. } => {
                let (params, results) = v.bt(bt)?;
                let is_if = matches!(i, If { .. });
                if is_if {
                    v.pop_t(I32)?;
                }
                v.pop_all(&params)?;
                let height = v.opds.len();
                for &p in &params {
                    v.push(p);
                }
                let label = if cur_live {
                    let id = labels.len() as u32;
                    let (arity, cont) = match i {
                        Block { end, .. } | If { end, .. } => (results.len(), end + 1),
                        _ => (params.len(), pc as u32),
                    };
                    if height + arity > MAX_HEIGHT as usize || arity >= NONE as usize {
                        return err("operand stack too deep");
                    }
                    labels.push(LabelRec { arity: arity as u32, cont, height: height as u32, parent: cur_label });
                    id
                } else {
                    NONE
                };
                v.ctrls.push(Ctrl {
                    params,
                    results,
                    height,
                    unreachable: false,
                    is_loop: matches!(i, Loop { .. }),
                    is_if,
                    has_else: false,
                    live: cur_live,
                    label,
                });
            }
            Else { .. } => {
                let c = v.ctrls.last().unwrap();
                if !c.is_if || c.has_else {
                    return err("else without if");
                }
                let results = c.results.clone();
                v.pop_all(&results)?;
                let c = v.ctrls.last().unwrap();
                if v.opds.len() != c.height {
                    return err("type mismatch");
                }
                let c = v.ctrls.last_mut().unwrap();
                c.has_else = true;
                c.unreachable = false;
                let params = c.params.clone();
                for p in params {
                    v.push(p);
                }
            }
            End => {
                let c = v.ctrls.last().unwrap();
                let results = c.results.clone();
                if c.is_if && !c.has_else && c.params != c.results {
                    return err("type mismatch");
                }
                v.pop_all(&results)?;
                let c = v.ctrls.pop().unwrap();
                if v.opds.len() != c.height {
                    return err("type mismatch");
                }
                for t in results {
                    v.opds.push(Some(t));
                }
                if v.ctrls.is_empty() && pc + 1 != len {
                    return err("operators remaining after end of function");
                }
            }
            Br(k) => {
                let ts = v.label(k)?.label_types().to_vec();
                v.pop_all(&ts)?;
                v.unreachable();
            }
            BrIf(k) => {
                v.pop_t(I32)?;
                let ts = v.label(k)?.label_types().to_vec();
                v.pop_all(&ts)?;
                for t in ts {
                    v.push(t);
                }
            }
            BrTable { start, len: tl } => {
                v.pop_t(I32)?;
                let ks = &m.br_table[start as usize..(start + tl) as usize];
                let default = *ks.last().unwrap();
                let arity = v.label(default)?.label_types().len();
                for &k in ks {
                    let ts = v.label(k)?.label_types().to_vec();
                    if ts.len() != arity {
                        return err("type mismatch");
                    }
                    // Check without consuming: pop and push back.
                    let saved = v.opds.clone();
                    v.pop_all(&ts)?;
                    v.opds = saved;
                }
                let ts = v.label(default)?.label_types().to_vec();
                v.pop_all(&ts)?;
                v.unreachable();
            }
            Return => {
                let ts = v.ctrls[0].results.clone();
                v.pop_all(&ts)?;
                v.unreachable();
            }
            Call(x) => {
                let ft = match m.func_types.get(x as usize) {
                    Some(&ty) => &m.types[ty as usize],
                    None => return err("unknown function"),
                };
                v.pop_all(&ft.params)?;
                for &r in &ft.results {
                    v.push(r);
                }
            }
            CallIndirect { ty, table } => {
                if table as usize >= m.tables.len() {
                    return err("unknown table");
                }
                let ft = match m.types.get(ty as usize) {
                    Some(t) => t,
                    None => return err("unknown type"),
                };
                v.pop_t(I32)?;
                v.pop_all(&ft.params)?;
                for &r in &ft.results {
                    v.push(r);
                }
            }
            Drop => {
                v.pop()?;
            }
            Select => {
                v.pop_t(I32)?;
                let a = v.pop()?;
                let b = v.pop()?;
                let t = match (a, b) {
                    (Some(a), Some(b)) => {
                        if a != b {
                            return err("type mismatch");
                        }
                        Some(a)
                    }
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                };
                v.opds.push(t);
            }
            LocalGet(x) | LocalSet(x) | LocalTee(x) => {
                let t = match locals.get(x as usize) {
                    Some(&t) => t,
                    None => return err("unknown local"),
                };
                match i {
                    LocalGet(_) => v.push(t),
                    LocalSet(_) => v.pop_t(t)?,
                    _ => {
                        v.pop_t(t)?;
                        v.push(t);
                    }
                }
            }
            GlobalGet(x) | GlobalSet(x) => {
                let g = match m.global_types.get(x as usize) {
                    Some(&g) => g,
                    None => return err("unknown global"),
                };
                if matches!(i, GlobalGet(_)) {
                    v.push(g.vt);
                } else {
                    if !g.mutable {
                        return err("global is immutable");
                    }
                    v.pop_t(g.vt)?;
                }
            }
            MemorySize | MemoryGrow | MemoryFill | MemoryCopy | MemoryInit(_) => {
                if !has_mem {
                    return err("unknown memory");
                }
                match i {
                    MemorySize => v.push(I32),
                    MemoryGrow => {
                        v.pop_t(I32)?;
                        v.push(I32);
                    }
                    MemoryInit(x) => {
                        if x as usize >= m.datas.len() {
                            return err("unknown data segment");
                        }
                        v.pop_all(&[I32, I32, I32])?;
                    }
                    _ => v.pop_all(&[I32, I32, I32])?,
                }
            }
            DataDrop(x) => {
                if x as usize >= m.datas.len() {
                    return err("unknown data segment");
                }
            }
            I32Const(_) => v.push(I32),
            I64Const(_) => v.push(I64),
            F32Const(_) => v.push(F32),
            F64Const(_) => v.push(F64),
            _ => return err("unsupported instruction"),
        }
    }
    if !v.ctrls.is_empty() {
        return err("unexpected end of function");
    }
    h[len] = t.results.len() as u32;
    lab[len] = NONE;
    if max_height > MAX_HEIGHT as usize {
        return err("operand stack too deep");
    }
    Ok(FuncCert { h, lab, labels, max_height: max_height as u32 })
}

impl core::fmt::Display for ValidateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "invalid module: {}", self.0)
    }
}

impl std::error::Error for ValidateError {}
