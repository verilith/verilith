//! The decoded module (WebAssembly 2.0 core, without SIMD, reference
//! types beyond `funcref` tables, or multiple memories).
//!
//! These are plain exec types; the specification in [`crate::sem`] reads
//! them directly, so the decoder's output is exactly what the spec runs.
use vstd::prelude::*;

verus! {

/// Why execution trapped (§4.4: the spec's single `trap`, refined by
/// cause so callers can report it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Trap {
    Unreachable,
    DivByZero,
    IntOverflow,
    InvalidConversion,
    MemoryOutOfBounds,
    TableOutOfBounds,
    /// `call_indirect` to a null table entry.
    UninitializedElement,
    /// `call_indirect` whose function type differs from the expected one.
    IndirectCallTypeMismatch,
    /// The call stack or value stack is exhausted (implementation limits).
    Exhausted,
    /// Raised by a host function.
    Host,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BlockType {
    Empty,
    Val(ValType),
    /// A type index (multi-value block types).
    Type(u32),
}

/// One instruction, with structured-control immediates resolved by the
/// decoder: `end` and `else_` are the positions of the matching `end` and
/// `else` in the function's instruction sequence.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Instr {
    // Control (§5.4.1)
    Unreachable,
    Nop,
    Block { bt: BlockType, end: u32 },
    Loop { bt: BlockType },
    /// `else_ == end` when there is no `else`.
    If { bt: BlockType, else_: u32, end: u32 },
    Else { end: u32 },
    End,
    Br(u32),
    BrIf(u32),
    /// Label indices are `br_table[start..start + len]`, the last being the
    /// default; `len >= 1`.
    BrTable { start: u32, len: u32 },
    Return,
    Call(u32),
    CallIndirect { ty: u32, table: u32 },
    // Parametric
    Drop,
    Select,
    // Variable
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    // Memory: the static offset is the only immediate that matters.
    I32Load(u32),
    I64Load(u32),
    F32Load(u32),
    F64Load(u32),
    I32Load8S(u32),
    I32Load8U(u32),
    I32Load16S(u32),
    I32Load16U(u32),
    I64Load8S(u32),
    I64Load8U(u32),
    I64Load16S(u32),
    I64Load16U(u32),
    I64Load32S(u32),
    I64Load32U(u32),
    I32Store(u32),
    I64Store(u32),
    F32Store(u32),
    F64Store(u32),
    I32Store8(u32),
    I32Store16(u32),
    I64Store8(u32),
    I64Store16(u32),
    I64Store32(u32),
    MemorySize,
    MemoryGrow,
    MemoryInit(u32),
    DataDrop(u32),
    MemoryCopy,
    MemoryFill,
    // Constants (floats as their bit patterns)
    I32Const(u32),
    I64Const(u64),
    F32Const(u32),
    F64Const(u64),
    // i32
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,
    // i64
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
    // Integer conversions
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    // Floating point and float/int conversions, grouped (see `fops`).
    FUn(FUnOp),
    FBin(FBinOp),
    FCmp(FCmpOp),
    Cvt(CvtOp),
}

/// Unary float operations, f32 then f64.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FUnOp {
    F32Abs, F32Neg, F32Ceil, F32Floor, F32Trunc, F32Nearest, F32Sqrt,
    F64Abs, F64Neg, F64Ceil, F64Floor, F64Trunc, F64Nearest, F64Sqrt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FBinOp {
    F32Add, F32Sub, F32Mul, F32Div, F32Min, F32Max, F32Copysign,
    F64Add, F64Sub, F64Mul, F64Div, F64Min, F64Max, F64Copysign,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FCmpOp {
    F32Eq, F32Ne, F32Lt, F32Gt, F32Le, F32Ge,
    F64Eq, F64Ne, F64Lt, F64Gt, F64Le, F64Ge,
}

/// Conversions that involve a float (the integer-only ones are `Instr`s).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CvtOp {
    I32TruncF32S, I32TruncF32U, I32TruncF64S, I32TruncF64U,
    I64TruncF32S, I64TruncF32U, I64TruncF64S, I64TruncF64U,
    F32ConvertI32S, F32ConvertI32U, F32ConvertI64S, F32ConvertI64U, F32DemoteF64,
    F64ConvertI32S, F64ConvertI32U, F64ConvertI64S, F64ConvertI64U, F64PromoteF32,
    I32ReinterpretF32, I64ReinterpretF64, F32ReinterpretI32, F64ReinterpretI64,
    I32TruncSatF32S, I32TruncSatF32U, I32TruncSatF64S, I32TruncSatF64U,
    I64TruncSatF32S, I64TruncSatF32U, I64TruncSatF64S, I64TruncSatF64U,
}

pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Limits {
    pub min: u32,
    pub max: Option<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct GlobalType {
    pub vt: ValType,
    pub mutable: bool,
}

/// Constant expressions (§3.3.10): one instruction then `end`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstExpr {
    I32(u32),
    I64(u64),
    F32(u32),
    F64(u64),
    /// An imported global.
    GlobalGet(u32),
    RefNull,
    RefFunc(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ImportDesc {
    Func(u32),
    Table(Limits),
    Mem(Limits),
    Global(GlobalType),
}

pub struct Import {
    pub module: Vec<u8>,
    pub name: Vec<u8>,
    pub desc: ImportDesc,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExportDesc {
    Func(u32),
    Table(u32),
    Mem(u32),
    Global(u32),
}

pub struct Export {
    pub name: Vec<u8>,
    pub desc: ExportDesc,
}

pub struct Func {
    /// Type index.
    pub ty: u32,
    /// Locals after the parameters, one entry per local.
    pub locals: Vec<ValType>,
    /// The body; the last instruction is the function's `end`.
    pub body: Vec<Instr>,
}

pub struct Global {
    pub ty: GlobalType,
    pub init: ConstExpr,
}

pub enum ElemMode {
    Active { table: u32, offset: ConstExpr },
    Passive,
    Declarative,
}

pub struct Elem {
    pub mode: ElemMode,
    /// Function indices; `None` is `ref.null`.
    pub init: Vec<Option<u32>>,
}

pub enum DataMode {
    Active { offset: ConstExpr },
    Passive,
}

pub struct Data {
    pub mode: DataMode,
    pub bytes: Vec<u8>,
}

pub struct Module {
    pub types: Vec<FuncType>,
    pub imports: Vec<Import>,
    /// Type index of every function, imported ones first.
    pub func_types: Vec<u32>,
    /// Number of imported functions (a prefix of `func_types`).
    pub n_imported_funcs: u32,
    /// Bodies of the defined functions.
    pub funcs: Vec<Func>,
    /// All tables, imported first.
    pub tables: Vec<Limits>,
    pub n_imported_tables: u32,
    /// All memories (at most one), imported first.
    pub mems: Vec<Limits>,
    pub n_imported_mems: u32,
    /// All global types, imported first.
    pub global_types: Vec<GlobalType>,
    pub n_imported_globals: u32,
    /// Initializers of the defined globals.
    pub globals: Vec<ConstExpr>,
    pub exports: Vec<Export>,
    pub start: Option<u32>,
    pub elems: Vec<Elem>,
    pub datas: Vec<Data>,
    /// Label indices of every `br_table`, concatenated.
    pub br_table: Vec<u32>,
}

} // verus!
