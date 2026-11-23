//! The binary decoder (§5). Not verified: it is safe Rust, and whatever
//! module it produces is checked by [`crate::check`] before it runs, so
//! a decoder bug can make vwasm run the wrong program but never let a
//! guest escape its sandbox.
use crate::ast::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodeError(pub &'static str);

type R<T> = Result<T, DecodeError>;

fn err<T>(msg: &'static str) -> R<T> {
    Err(DecodeError(msg))
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Reader<'a> {
    fn eof(&self) -> bool {
        self.p >= self.b.len()
    }

    fn byte(&mut self) -> R<u8> {
        match self.b.get(self.p) {
            Some(&x) => {
                self.p += 1;
                Ok(x)
            }
            None => err("unexpected end"),
        }
    }

    fn bytes(&mut self, n: usize) -> R<&'a [u8]> {
        if n > self.b.len() - self.p {
            return err("unexpected end");
        }
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        Ok(s)
    }

    fn uleb(&mut self, bits: u32) -> R<u64> {
        let mut r: u64 = 0;
        let mut shift = 0;
        loop {
            let x = self.byte()?;
            let v = (x & 0x7f) as u64;
            if shift + 7 > bits {
                // Last byte: the bits above `bits` must be zero.
                if x & 0x80 != 0 || (v >> (bits - shift)) != 0 {
                    return err("integer too large");
                }
                return Ok(r | (v << shift));
            }
            r |= v << shift;
            shift += 7;
            if x & 0x80 == 0 {
                return Ok(r);
            }
        }
    }

    fn sleb(&mut self, bits: u32) -> R<i64> {
        let mut r: i64 = 0;
        let mut shift = 0;
        loop {
            let x = self.byte()?;
            let v = (x & 0x7f) as i64;
            if shift + 7 >= bits {
                // Last byte: the unused bits must sign-extend.
                if x & 0x80 != 0 {
                    return err("integer too large");
                }
                let used = bits - shift; // 1..=7
                // Bits `used - 1 ..= 6` are the sign and its extension.
                let mask = (0x7f_i64 << (used - 1)) & 0x7f;
                if v & mask != 0 && v & mask != mask {
                    return err("integer too large");
                }
                let full = r | (v << shift);
                let sh = 64 - bits;
                return Ok(full << sh >> sh);
            }
            r |= v << shift;
            shift += 7;
            if x & 0x80 == 0 {
                let sh = 64 - shift;
                return Ok(r << sh >> sh);
            }
        }
    }

    fn u32(&mut self) -> R<u32> {
        Ok(self.uleb(32)? as u32)
    }

    fn len(&mut self) -> R<usize> {
        let n = self.u32()? as usize;
        // Every element takes at least one byte.
        if n > self.b.len() - self.p {
            return err("length out of bounds");
        }
        Ok(n)
    }

    fn name(&mut self) -> R<Vec<u8>> {
        let n = self.u32()? as usize;
        let s = self.bytes(n)?;
        if core::str::from_utf8(s).is_err() {
            return err("malformed UTF-8 encoding");
        }
        Ok(s.to_vec())
    }
}

fn valtype(b: u8) -> R<ValType> {
    match b {
        0x7f => Ok(ValType::I32),
        0x7e => Ok(ValType::I64),
        0x7d => Ok(ValType::F32),
        0x7c => Ok(ValType::F64),
        _ => err("malformed value type"),
    }
}

fn limits(r: &mut Reader, max_bits: u32) -> R<Limits> {
    let flag = r.byte()?;
    let min = r.uleb(max_bits)? as u32;
    let max = match flag {
        0 => None,
        1 => Some(r.uleb(max_bits)? as u32),
        _ => return err("malformed limits flags"),
    };
    Ok(Limits { min, max })
}

fn table_type(r: &mut Reader) -> R<Limits> {
    if r.byte()? != 0x70 {
        return err("unsupported table element type");
    }
    limits(r, 32)
}

fn global_type(r: &mut Reader) -> R<GlobalType> {
    let vt = valtype(r.byte()?)?;
    let mutable = match r.byte()? {
        0 => false,
        1 => true,
        _ => return err("malformed mutability"),
    };
    Ok(GlobalType { vt, mutable })
}

fn const_expr(r: &mut Reader) -> R<ConstExpr> {
    let e = match r.byte()? {
        0x41 => ConstExpr::I32(r.sleb(32)? as u32),
        0x42 => ConstExpr::I64(r.sleb(64)? as u64),
        0x43 => ConstExpr::F32(u32::from_le_bytes(r.bytes(4)?.try_into().unwrap())),
        0x44 => ConstExpr::F64(u64::from_le_bytes(r.bytes(8)?.try_into().unwrap())),
        0x23 => ConstExpr::GlobalGet(r.u32()?),
        0xd0 => {
            if r.byte()? != 0x70 {
                return err("unsupported reference type");
            }
            ConstExpr::RefNull
        }
        0xd2 => ConstExpr::RefFunc(r.u32()?),
        _ => return err("constant expression required"),
    };
    if r.byte()? != 0x0b {
        return err("constant expression required");
    }
    Ok(e)
}

/// Decodes `bytes` into a module.
pub fn decode(bytes: &[u8]) -> R<Module> {
    let mut r = Reader { b: bytes, p: 0 };
    if r.bytes(4).map_err(|_| DecodeError("unexpected end"))? != b"\0asm" {
        return err("magic header not detected");
    }
    if r.bytes(4).map_err(|_| DecodeError("unexpected end"))? != [1, 0, 0, 0] {
        return err("unknown binary version");
    }
    let mut m = Module {
        types: Vec::new(),
        imports: Vec::new(),
        func_types: Vec::new(),
        n_imported_funcs: 0,
        funcs: Vec::new(),
        tables: Vec::new(),
        n_imported_tables: 0,
        mems: Vec::new(),
        n_imported_mems: 0,
        global_types: Vec::new(),
        n_imported_globals: 0,
        globals: Vec::new(),
        exports: Vec::new(),
        start: None,
        elems: Vec::new(),
        datas: Vec::new(),
        br_table: Vec::new(),
    };
    let mut last_id = 0u8;
    let mut n_defined: Option<usize> = None;
    let mut data_count: Option<u32> = None;
    let mut saw_code = false;
    // Section order (the data count section comes before code).
    let order = |id: u8| -> u8 {
        match id {
            12 => 10,
            10 => 11,
            11 => 12,
            x => x,
        }
    };
    while !r.eof() {
        let id = r.byte()?;
        let size = r.u32()? as usize;
        let body = r.bytes(size)?;
        let mut s = Reader { b: body, p: 0 };
        if id != 0 {
            if id > 12 {
                return err("malformed section id");
            }
            if order(id) <= last_id {
                return err("unexpected content after last section");
            }
            last_id = order(id);
        }
        match id {
            0 => {
                s.name()?;
                continue;
            }
            1 => {
                for _ in 0..s.len()? {
                    if s.byte()? != 0x60 {
                        return err("malformed function type");
                    }
                    let mut params = Vec::new();
                    for _ in 0..s.len()? {
                        params.push(valtype(s.byte()?)?);
                    }
                    let mut results = Vec::new();
                    for _ in 0..s.len()? {
                        results.push(valtype(s.byte()?)?);
                    }
                    m.types.push(FuncType { params, results });
                }
            }
            2 => {
                for _ in 0..s.len()? {
                    let module = s.name()?;
                    let name = s.name()?;
                    let desc = match s.byte()? {
                        0 => {
                            let t = s.u32()?;
                            m.func_types.push(t);
                            m.n_imported_funcs += 1;
                            ImportDesc::Func(t)
                        }
                        1 => {
                            let t = table_type(&mut s)?;
                            m.tables.push(t);
                            m.n_imported_tables += 1;
                            ImportDesc::Table(t)
                        }
                        2 => {
                            let l = limits(&mut s, 32)?;
                            m.mems.push(l);
                            m.n_imported_mems += 1;
                            ImportDesc::Mem(l)
                        }
                        3 => {
                            let g = global_type(&mut s)?;
                            m.global_types.push(g);
                            m.n_imported_globals += 1;
                            ImportDesc::Global(g)
                        }
                        _ => return err("malformed import kind"),
                    };
                    m.imports.push(Import { module, name, desc });
                }
            }
            3 => {
                let n = s.len()?;
                for _ in 0..n {
                    m.func_types.push(s.u32()?);
                }
                n_defined = Some(n);
            }
            4 => {
                for _ in 0..s.len()? {
                    m.tables.push(table_type(&mut s)?);
                }
            }
            5 => {
                for _ in 0..s.len()? {
                    m.mems.push(limits(&mut s, 32)?);
                }
            }
            6 => {
                for _ in 0..s.len()? {
                    m.global_types.push(global_type(&mut s)?);
                    m.globals.push(const_expr(&mut s)?);
                }
            }
            7 => {
                for _ in 0..s.len()? {
                    let name = s.name()?;
                    let k = s.byte()?;
                    let x = s.u32()?;
                    let desc = match k {
                        0 => ExportDesc::Func(x),
                        1 => ExportDesc::Table(x),
                        2 => ExportDesc::Mem(x),
                        3 => ExportDesc::Global(x),
                        _ => return err("malformed export kind"),
                    };
                    m.exports.push(Export { name, desc });
                }
            }
            8 => m.start = Some(s.u32()?),
            9 => {
                for _ in 0..s.len()? {
                    m.elems.push(elem(&mut s)?);
                }
            }
            12 => data_count = Some(s.u32()?),
            10 => {
                saw_code = true;
                let n = s.len()?;
                if n != n_defined.unwrap_or(0) {
                    return err("function and code section have inconsistent lengths");
                }
                for i in 0..n {
                    let size = s.u32()? as usize;
                    let fb = s.bytes(size)?;
                    let mut f = Reader { b: fb, p: 0 };
                    let mut locals = Vec::new();
                    let mut total: u64 = 0;
                    for _ in 0..f.u32()? {
                        let k = f.u32()?;
                        let t = valtype(f.byte()?)?;
                        total += k as u64;
                        if total > 50_000 {
                            return err("too many locals");
                        }
                        for _ in 0..k {
                            locals.push(t);
                        }
                    }
                    let body = code(&mut f, &mut m.br_table, data_count)?;
                    if !f.eof() {
                        return err("section size mismatch");
                    }
                    let ty = m.func_types[m.n_imported_funcs as usize + i];
                    m.funcs.push(Func { ty, locals, body });
                }
            }
            11 => {
                let n = s.len()?;
                if let Some(c) = data_count {
                    if c as usize != n {
                        return err("data count and data section have inconsistent lengths");
                    }
                }
                for _ in 0..n {
                    let mode = match s.u32()? {
                        0 => DataMode::Active { offset: const_expr(&mut s)? },
                        1 => DataMode::Passive,
                        2 => {
                            if s.u32()? != 0 {
                                return err("multiple memories are not supported");
                            }
                            DataMode::Active { offset: const_expr(&mut s)? }
                        }
                        _ => return err("malformed data segment kind"),
                    };
                    let n = s.u32()? as usize;
                    let bytes = s.bytes(n)?.to_vec();
                    m.datas.push(Data { mode, bytes });
                }
            }
            _ => unreachable!(),
        }
        if !s.eof() {
            return err("section size mismatch");
        }
    }
    if n_defined.unwrap_or(0) > 0 && !saw_code {
        return err("function and code section have inconsistent lengths");
    }
    if let Some(c) = data_count {
        if m.datas.len() != c as usize {
            return err("data count and data section have inconsistent lengths");
        }
    }
    Ok(m)
}

fn elem(s: &mut Reader) -> R<Elem> {
    let flags = s.u32()?;
    if flags > 7 {
        return err("malformed elements segment kind");
    }
    let passive_or_decl = flags & 1 != 0;
    let explicit_table = flags & 2 != 0;
    let exprs = flags & 4 != 0;
    let mode = if !passive_or_decl {
        let table = if explicit_table { s.u32()? } else { 0 };
        ElemMode::Active { table, offset: const_expr(s)? }
    } else if explicit_table {
        ElemMode::Declarative
    } else {
        ElemMode::Passive
    };
    // Element kind / type.
    if passive_or_decl || explicit_table {
        let k = s.byte()?;
        if (exprs && k != 0x70) || (!exprs && k != 0x00) {
            return err("unsupported element type");
        }
    }
    let mut init = Vec::new();
    for _ in 0..s.len()? {
        if exprs {
            match const_expr(s)? {
                ConstExpr::RefFunc(x) => init.push(Some(x)),
                ConstExpr::RefNull => init.push(None),
                _ => return err("type mismatch"),
            }
        } else {
            init.push(Some(s.u32()?));
        }
    }
    Ok(Elem { mode, init })
}

fn blocktype(r: &mut Reader) -> R<BlockType> {
    let b = *r.b.get(r.p).ok_or(DecodeError("unexpected end"))?;
    if b == 0x40 {
        r.p += 1;
        return Ok(BlockType::Empty);
    }
    if let Ok(t) = valtype(b) {
        r.p += 1;
        return Ok(BlockType::Val(t));
    }
    let x = r.sleb(33)?;
    if x < 0 {
        return err("malformed block type");
    }
    Ok(BlockType::Type(x as u32))
}

fn memarg(r: &mut Reader, natural: u32) -> R<u32> {
    let align = r.u32()?;
    if align >= 64 {
        return err("malformed memop flags");
    }
    if align > natural {
        return err("alignment must not be larger than natural");
    }
    r.u32()
}

/// Decodes a function body up to and including its final `end`.
fn code(r: &mut Reader, br_table: &mut Vec<u32>, data_count: Option<u32>) -> R<Vec<Instr>> {
    use Instr::*;
    let mut body: Vec<Instr> = Vec::new();
    // Open blocks: their positions (and the `else` position, if any).
    let mut open: Vec<(usize, Option<usize>)> = Vec::new();
    loop {
        if body.len() as u64 >= 0xffff_fff0 {
            return err("function too large");
        }
        let pc = body.len();
        let op = r.byte()?;
        let i = match op {
            0x00 => Unreachable,
            0x01 => Nop,
            0x02 => {
                let bt = blocktype(r)?;
                open.push((pc, None));
                Block { bt, end: 0 }
            }
            0x03 => {
                let bt = blocktype(r)?;
                open.push((pc, None));
                Loop { bt }
            }
            0x04 => {
                let bt = blocktype(r)?;
                open.push((pc, None));
                If { bt, else_: 0, end: 0 }
            }
            0x05 => {
                match open.last_mut() {
                    Some((start, e)) if matches!(body[*start], If { .. }) && e.is_none() => *e = Some(pc),
                    _ => return err("else without if"),
                }
                Else { end: 0 }
            }
            0x0b => {
                match open.pop() {
                    None => {
                        body.push(End);
                        return Ok(body);
                    }
                    Some((start, e)) => {
                        let end = pc as u32;
                        match &mut body[start] {
                            Block { end: x, .. } => *x = end,
                            If { else_, end: x, .. } => {
                                *x = end;
                                *else_ = e.map(|p| p as u32).unwrap_or(end);
                            }
                            _ => {}
                        }
                        if let Some(p) = e {
                            body[p] = Else { end };
                        }
                    }
                }
                End
            }
            0x0c => Br(r.u32()?),
            0x0d => BrIf(r.u32()?),
            0x0e => {
                let n = r.len()?;
                let start = br_table.len();
                for _ in 0..n + 1 {
                    br_table.push(r.u32()?);
                }
                if br_table.len() > u32::MAX as usize {
                    return err("too many branch targets");
                }
                BrTable { start: start as u32, len: n as u32 + 1 }
            }
            0x0f => Return,
            0x10 => Call(r.u32()?),
            0x11 => {
                let ty = r.u32()?;
                let table = r.u32()?;
                CallIndirect { ty, table }
            }
            0x1a => Drop,
            0x1b => Select,
            0x1c => {
                if r.u32()? != 1 {
                    return err("invalid result arity");
                }
                valtype(r.byte()?)?;
                Select
            }
            0x20 => LocalGet(r.u32()?),
            0x21 => LocalSet(r.u32()?),
            0x22 => LocalTee(r.u32()?),
            0x23 => GlobalGet(r.u32()?),
            0x24 => GlobalSet(r.u32()?),
            0x28 => I32Load(memarg(r, 2)?),
            0x29 => I64Load(memarg(r, 3)?),
            0x2a => F32Load(memarg(r, 2)?),
            0x2b => F64Load(memarg(r, 3)?),
            0x2c => I32Load8S(memarg(r, 0)?),
            0x2d => I32Load8U(memarg(r, 0)?),
            0x2e => I32Load16S(memarg(r, 1)?),
            0x2f => I32Load16U(memarg(r, 1)?),
            0x30 => I64Load8S(memarg(r, 0)?),
            0x31 => I64Load8U(memarg(r, 0)?),
            0x32 => I64Load16S(memarg(r, 1)?),
            0x33 => I64Load16U(memarg(r, 1)?),
            0x34 => I64Load32S(memarg(r, 2)?),
            0x35 => I64Load32U(memarg(r, 2)?),
            0x36 => I32Store(memarg(r, 2)?),
            0x37 => I64Store(memarg(r, 3)?),
            0x38 => F32Store(memarg(r, 2)?),
            0x39 => F64Store(memarg(r, 3)?),
            0x3a => I32Store8(memarg(r, 0)?),
            0x3b => I32Store16(memarg(r, 1)?),
            0x3c => I64Store8(memarg(r, 0)?),
            0x3d => I64Store16(memarg(r, 1)?),
            0x3e => I64Store32(memarg(r, 2)?),
            0x3f => {
                if r.byte()? != 0 {
                    return err("zero byte expected");
                }
                MemorySize
            }
            0x40 => {
                if r.byte()? != 0 {
                    return err("zero byte expected");
                }
                MemoryGrow
            }
            0x41 => I32Const(r.sleb(32)? as u32),
            0x42 => I64Const(r.sleb(64)? as u64),
            0x43 => F32Const(u32::from_le_bytes(r.bytes(4)?.try_into().unwrap())),
            0x44 => F64Const(u64::from_le_bytes(r.bytes(8)?.try_into().unwrap())),
            0x45..=0xc4 => simple(op).ok_or(DecodeError("illegal opcode"))?,
            0xfc => {
                let sub = r.u32()?;
                match sub {
                    0..=7 => Cvt([
                        CvtOp::I32TruncSatF32S, CvtOp::I32TruncSatF32U, CvtOp::I32TruncSatF64S,
                        CvtOp::I32TruncSatF64U, CvtOp::I64TruncSatF32S, CvtOp::I64TruncSatF32U,
                        CvtOp::I64TruncSatF64S, CvtOp::I64TruncSatF64U,
                    ][sub as usize]),
                    8 => {
                        let x = r.u32()?;
                        if r.byte()? != 0 {
                            return err("zero byte expected");
                        }
                        if data_count.is_none() {
                            return err("data count section required");
                        }
                        MemoryInit(x)
                    }
                    9 => {
                        if data_count.is_none() {
                            return err("data count section required");
                        }
                        DataDrop(r.u32()?)
                    }
                    10 => {
                        if r.byte()? != 0 || r.byte()? != 0 {
                            return err("zero byte expected");
                        }
                        MemoryCopy
                    }
                    11 => {
                        if r.byte()? != 0 {
                            return err("zero byte expected");
                        }
                        MemoryFill
                    }
                    _ => return err("unsupported instruction"),
                }
            }
            0xd0..=0xd2 | 0x25 | 0x26 | 0xfd => return err("unsupported instruction"),
            _ => return err("illegal opcode"),
        };
        body.push(i);
    }
}

/// Opcodes 0x45..=0xc4, which have no immediates.
fn simple(op: u8) -> Option<Instr> {
    use Instr::*;
    use CvtOp::*;
    use FBinOp::*;
    use FCmpOp::*;
    use FUnOp::*;
    const I32: [Instr; 11] = [I32Eqz, I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU];
    const I64: [Instr; 11] = [I64Eqz, I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU];
    const FC: [FCmpOp; 12] = [F32Eq, F32Ne, F32Lt, F32Gt, F32Le, F32Ge, F64Eq, F64Ne, F64Lt, F64Gt, F64Le, F64Ge];
    const I32A: [Instr; 18] = [
        I32Clz, I32Ctz, I32Popcnt, I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU, I32And, I32Or,
        I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr,
    ];
    const I64A: [Instr; 18] = [
        I64Clz, I64Ctz, I64Popcnt, I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU, I64And, I64Or,
        I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr,
    ];
    const F32U: [FUnOp; 7] = [F32Abs, F32Neg, F32Ceil, F32Floor, F32Trunc, F32Nearest, F32Sqrt];
    const F32B: [FBinOp; 7] = [F32Add, F32Sub, F32Mul, F32Div, F32Min, F32Max, F32Copysign];
    const F64U: [FUnOp; 7] = [F64Abs, F64Neg, F64Ceil, F64Floor, F64Trunc, F64Nearest, F64Sqrt];
    const F64B: [FBinOp; 7] = [F64Add, F64Sub, F64Mul, F64Div, F64Min, F64Max, F64Copysign];
    let o = op as usize;
    Some(match op {
        0x45..=0x4f => I32[o - 0x45],
        0x50..=0x5a => I64[o - 0x50],
        0x5b..=0x66 => FCmp(FC[o - 0x5b]),
        0x67..=0x78 => I32A[o - 0x67],
        0x79..=0x8a => I64A[o - 0x79],
        0x8b..=0x91 => FUn(F32U[o - 0x8b]),
        0x92..=0x98 => FBin(F32B[o - 0x92]),
        0x99..=0x9f => FUn(F64U[o - 0x99]),
        0xa0..=0xa6 => FBin(F64B[o - 0xa0]),
        0xa7 => I32WrapI64,
        0xa8 => Cvt(I32TruncF32S),
        0xa9 => Cvt(I32TruncF32U),
        0xaa => Cvt(I32TruncF64S),
        0xab => Cvt(I32TruncF64U),
        0xac => I64ExtendI32S,
        0xad => I64ExtendI32U,
        0xae => Cvt(I64TruncF32S),
        0xaf => Cvt(I64TruncF32U),
        0xb0 => Cvt(I64TruncF64S),
        0xb1 => Cvt(I64TruncF64U),
        0xb2 => Cvt(F32ConvertI32S),
        0xb3 => Cvt(F32ConvertI32U),
        0xb4 => Cvt(F32ConvertI64S),
        0xb5 => Cvt(F32ConvertI64U),
        0xb6 => Cvt(F32DemoteF64),
        0xb7 => Cvt(F64ConvertI32S),
        0xb8 => Cvt(F64ConvertI32U),
        0xb9 => Cvt(F64ConvertI64S),
        0xba => Cvt(F64ConvertI64U),
        0xbb => Cvt(F64PromoteF32),
        0xbc => Cvt(I32ReinterpretF32),
        0xbd => Cvt(I64ReinterpretF64),
        0xbe => Cvt(F32ReinterpretI32),
        0xbf => Cvt(F64ReinterpretI64),
        0xc0 => I32Extend8S,
        0xc1 => I32Extend16S,
        0xc2 => I64Extend8S,
        0xc3 => I64Extend16S,
        0xc4 => I64Extend32S,
        _ => return None,
    })
}

impl core::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "malformed module: {}", self.0)
    }
}

impl std::error::Error for DecodeError {}
