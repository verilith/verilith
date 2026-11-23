//! The Rust embedding API: decode, validate, link and instantiate a
//! module, then call its exports.
//!
//! Everything here is unverified glue around [`Checked`], whose type
//! invariant guarantees that only checked code runs, against a store
//! that was checked when the instance was created.
use std::collections::HashMap;

use crate::ast::{self, ConstExpr, DataMode, ElemMode, ExportDesc, FuncType, ImportDesc, Trap, ValType};
use crate::cert::NONE;
use crate::instance::Checked;
use crate::interp::{Host, Store};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Val {
    I32(i32),
    I64(i64),
    /// Bit pattern.
    F32(u32),
    /// Bit pattern.
    F64(u64),
}

impl Val {
    pub fn ty(&self) -> ValType {
        match self {
            Val::I32(_) => ValType::I32,
            Val::I64(_) => ValType::I64,
            Val::F32(_) => ValType::F32,
            Val::F64(_) => ValType::F64,
        }
    }

    fn to_slot(self) -> u64 {
        match self {
            Val::I32(x) => x as u32 as u64,
            Val::I64(x) => x as u64,
            Val::F32(x) => x as u64,
            Val::F64(x) => x,
        }
    }

    fn from_slot(t: ValType, s: u64) -> Val {
        match t {
            ValType::I32 => Val::I32(s as u32 as i32),
            ValType::I64 => Val::I64(s as i64),
            ValType::F32 => Val::F32(s as u32),
            ValType::F64 => Val::F64(s),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The binary is malformed.
    Decode(&'static str),
    /// The module is invalid.
    Invalid(String),
    /// Linking failed (missing or mistyped import).
    Link(String),
    /// Instantiation failed (a segment does not fit, or the start function trapped).
    Instantiate(String),
    /// The call trapped.
    Trap(Trap),
    /// No such export, or the wrong arguments.
    Call(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExternType {
    Func(Vec<ValType>, Vec<ValType>),
    Global(ast::GlobalType),
    Memory(ast::Limits),
    Table(ast::Limits),
}

/// A decoded and validated module, with its certificates.
pub struct Module {
    m: ast::Module,
    certs: Vec<crate::cert::FuncCert>,
}

impl Module {
    pub fn new(bytes: &[u8]) -> Result<Module, Error> {
        let m = crate::decode::decode(bytes).map_err(|e| Error::Decode(e.0))?;
        let certs = crate::validate::validate(&m).map_err(|e| Error::Invalid(e.0))?;
        Ok(Module { m, certs })
    }

    pub fn imports(&self) -> &[ast::Import] {
        &self.m.imports
    }

    pub fn exports(&self) -> &[ast::Export] {
        &self.m.exports
    }
}

/// A host function: arguments, results to fill, and the caller's memory.
pub type HostFunc = Box<dyn FnMut(&[Val], &mut [Val], &mut [u8]) -> Result<(), Trap>>;

/// Imports by `(module, name)`.
#[derive(Default)]
pub struct Linker {
    funcs: HashMap<(Vec<u8>, Vec<u8>), (Vec<ValType>, Vec<ValType>, std::rc::Rc<std::cell::RefCell<HostFunc>>)>,
    globals: HashMap<(Vec<u8>, Vec<u8>), (Val, bool)>,
    mems: HashMap<(Vec<u8>, Vec<u8>), ast::Limits>,
    tables: HashMap<(Vec<u8>, Vec<u8>), ast::Limits>,
    /// Cap on every instance's memory, in pages.
    max_pages: Option<u32>,
    /// Fuel each instance starts with (`None`: unmetered).
    fuel: Option<u64>,
}

fn key(module: &str, name: &str) -> (Vec<u8>, Vec<u8>) {
    (module.as_bytes().to_vec(), name.as_bytes().to_vec())
}

impl Linker {
    pub fn new() -> Linker {
        Linker::default()
    }

    pub fn func(&mut self, module: &str, name: &str, params: &[ValType], results: &[ValType],
        f: impl FnMut(&[Val], &mut [Val], &mut [u8]) -> Result<(), Trap> + 'static) -> &mut Self
    {
        self.funcs.insert(key(module, name),
            (params.to_vec(), results.to_vec(), std::rc::Rc::new(std::cell::RefCell::new(Box::new(f)))));
        self
    }

    pub fn global(&mut self, module: &str, name: &str, v: Val, mutable: bool) -> &mut Self {
        self.globals.insert(key(module, name), (v, mutable));
        self
    }

    /// Makes an importable memory available. Each importing instance
    /// gets its own memory with these limits (memories are not shared).
    pub fn memory(&mut self, module: &str, name: &str, min: u32, max: Option<u32>) -> &mut Self {
        self.mems.insert(key(module, name), ast::Limits { min, max });
        self
    }

    /// As [`Linker::memory`], for tables.
    pub fn table(&mut self, module: &str, name: &str, min: u32, max: Option<u32>) -> &mut Self {
        self.tables.insert(key(module, name), ast::Limits { min, max });
        self
    }

    /// Caps the linear memory of instances made with this linker at
    /// `bytes` (rounded down to whole 64 KiB pages). An instance whose
    /// memory starts above the cap fails to instantiate, and `memory.grow`
    /// past it returns -1, as it does past the module's own maximum.
    pub fn max_memory(&mut self, bytes: u64) -> &mut Self {
        self.max_pages = Some((bytes / 65536).min(65536) as u32);
        self
    }

    /// Meters instances made with this linker: each starts with `fuel`
    /// units (see [`Instance::set_fuel`]). Unmetered by default.
    pub fn fuel(&mut self, fuel: u64) -> &mut Self {
        self.fuel = Some(fuel);
        self
    }
}

fn limits_match(have: ast::Limits, want: ast::Limits) -> bool {
    have.min >= want.min
        && match want.max {
            None => true,
            Some(wm) => have.max.is_some_and(|hm| hm <= wm),
        }
}

struct Funcs {
    /// Indexed by imported function index.
    funcs: Vec<(Vec<ValType>, Vec<ValType>, std::rc::Rc<std::cell::RefCell<HostFunc>>)>,
    args: Vec<Val>,
    results: Vec<Val>,
}

impl Host for Funcs {
    fn call(&mut self, func: u32, args: &[u64], results: &mut [u64], mem: &mut [u8]) -> bool {
        let Some((params, rtys, f)) = self.funcs.get(func as usize) else { return false };
        self.args.clear();
        self.args.extend(params.iter().zip(args).map(|(&t, &s)| Val::from_slot(t, s)));
        self.results.clear();
        self.results.extend(rtys.iter().map(|&t| Val::from_slot(t, 0)));
        let Ok(mut f) = f.try_borrow_mut() else { return false };
        if f(&self.args, &mut self.results, mem).is_err() {
            return false;
        }
        for (i, (r, &t)) in self.results.iter().zip(rtys).enumerate() {
            if r.ty() != t {
                return false;
            }
            results[i] = r.to_slot();
        }
        true
    }
}

/// A running instance.
pub struct Instance {
    inner: Option<Checked>,
    host: Funcs,
    exports: HashMap<Vec<u8>, ExportDesc>,
    types: Vec<(Vec<ValType>, Vec<ValType>)>,
    fuel: Option<u64>,
}

/// Largest table we allocate.
const MAX_TABLE: u32 = 10_000_000;

impl Instance {
    pub fn new(module: Module, linker: &Linker) -> Result<Instance, Error> {
        let Module { m, certs } = module;
        let mut funcs = Vec::new();
        let mut globals: Vec<u64> = Vec::new();
        let mut mem_limits = None;
        let mut table_limits = Vec::new();
        for imp in &m.imports {
            let k = (imp.module.clone(), imp.name.clone());
            let what = || format!("{}::{}", String::from_utf8_lossy(&imp.module), String::from_utf8_lossy(&imp.name));
            match imp.desc {
                ImportDesc::Func(t) => {
                    let ft: &FuncType = &m.types[t as usize];
                    match linker.funcs.get(&k) {
                        Some((p, r, f)) if *p == ft.params && *r == ft.results => {
                            funcs.push((p.clone(), r.clone(), f.clone()))
                        }
                        Some(_) => return Err(Error::Link(format!("incompatible import type: {}", what()))),
                        None => return Err(Error::Link(format!("unknown import: {}", what()))),
                    }
                }
                ImportDesc::Global(g) => match linker.globals.get(&k) {
                    Some((v, mt)) if v.ty() == g.vt && *mt == g.mutable => globals.push(v.to_slot()),
                    Some(_) => return Err(Error::Link(format!("incompatible import type: {}", what()))),
                    None => return Err(Error::Link(format!("unknown import: {}", what()))),
                },
                ImportDesc::Mem(l) => match linker.mems.get(&k) {
                    Some(&have) if limits_match(have, l) => mem_limits = Some(have),
                    Some(_) => return Err(Error::Link(format!("incompatible import type: {}", what()))),
                    None => return Err(Error::Link(format!("unknown import: {}", what()))),
                },
                ImportDesc::Table(l) => match linker.tables.get(&k) {
                    Some(&have) if limits_match(have, l) => table_limits.push(have),
                    Some(_) => return Err(Error::Link(format!("incompatible import type: {}", what()))),
                    None => return Err(Error::Link(format!("unknown import: {}", what()))),
                },
            }
        }
        for g in &m.globals {
            globals.push(match *g {
                ConstExpr::I32(x) => x as u64,
                ConstExpr::I64(x) => x,
                ConstExpr::F32(x) => x as u64,
                ConstExpr::F64(x) => x,
                ConstExpr::GlobalGet(x) => globals[x as usize],
                ConstExpr::RefNull | ConstExpr::RefFunc(_) => 0,
            });
        }
        let eval = |e: &ConstExpr, globals: &[u64]| -> u32 {
            match *e {
                ConstExpr::I32(x) => x,
                ConstExpr::GlobalGet(x) => globals[x as usize] as u32,
                _ => 0,
            }
        };
        let mem_limits = mem_limits.or_else(|| m.mems.get(m.n_imported_mems as usize).copied());
        let cap = linker.max_pages.unwrap_or(65536);
        let (mem, mem_max) = match mem_limits {
            Some(l) => {
                if l.min > cap {
                    return Err(Error::Instantiate("memory larger than the embedder's limit".into()));
                }
                let mut mem = Vec::new();
                if mem.try_reserve_exact(l.min as usize * 65536).is_err() {
                    return Err(Error::Instantiate("cannot allocate memory".into()));
                }
                mem.resize(l.min as usize * 65536, 0);
                (mem, l.max.unwrap_or(65536).min(cap))
            }
            None => (Vec::new(), 0),
        };
        table_limits.extend_from_slice(&m.tables[m.n_imported_tables as usize..]);
        let mut tables = Vec::new();
        for l in &table_limits {
            if l.min > MAX_TABLE {
                return Err(Error::Instantiate("table too large".into()));
            }
            tables.push(vec![NONE; l.min as usize]);
        }
        let mut st = Store { mem, mem_max, globals, tables, dropped: vec![false; m.datas.len()] };
        for e in &m.elems {
            if let ElemMode::Active { table, offset } = &e.mode {
                let off = eval(offset, &st.globals) as usize;
                let tab = &mut st.tables[*table as usize];
                if off.checked_add(e.init.len()).is_none_or(|end| end > tab.len()) {
                    return Err(Error::Instantiate("out of bounds table access".into()));
                }
                for (i, x) in e.init.iter().enumerate() {
                    tab[off + i] = x.unwrap_or(NONE);
                }
            }
        }
        for (i, d) in m.datas.iter().enumerate() {
            if let DataMode::Active { offset } = &d.mode {
                let off = eval(offset, &st.globals) as usize;
                if off + d.bytes.len() > st.mem.len() {
                    return Err(Error::Instantiate("out of bounds memory access".into()));
                }
                st.mem[off..off + d.bytes.len()].copy_from_slice(&d.bytes);
                st.dropped[i] = true;
            }
        }
        let exports = m.exports.iter().map(|e| (e.name.clone(), e.desc)).collect();
        let types = m.func_types.iter().map(|&t| {
            let t = &m.types[t as usize];
            (t.params.clone(), t.results.clone())
        }).collect();
        let start = m.start;
        let inner = Checked::new(m, certs, st)
            .ok_or_else(|| Error::Invalid("certificate or store rejected".into()))?;
        let mut inst = Instance {
            inner: Some(inner),
            host: Funcs { funcs, args: Vec::new(), results: Vec::new() },
            exports,
            types,
            fuel: linker.fuel,
        };
        if let Some(s) = start {
            inst.invoke(s, &[]).map_err(|e| Error::Instantiate(format!("start function: {e}")))?;
        }
        Ok(inst)
    }

    /// Calls function `func` (an index among all the module's functions).
    pub fn invoke(&mut self, func: u32, args: &[Val]) -> Result<Vec<Val>, Error> {
        let (params, results) = self.types.get(func as usize).ok_or(Error::Call("unknown function".into()))?;
        if args.len() != params.len() || args.iter().zip(params).any(|(a, &t)| a.ty() != t) {
            return Err(Error::Call("wrong arguments".into()));
        }
        let slots: Vec<u64> = args.iter().map(|a| a.to_slot()).collect();
        let inner = self.inner.take().ok_or(Error::Call("instance poisoned by an earlier panic".into()))?;
        let mut fuel = self.fuel.unwrap_or(0);
        let (inner, r) = inner.invoke(func, &slots, &mut self.host, self.fuel.is_some(), &mut fuel);
        self.inner = Some(inner);
        if self.fuel.is_some() {
            self.fuel = Some(fuel);
        }
        match r {
            Ok(v) => Ok(v.iter().zip(results).map(|(&s, &t)| Val::from_slot(t, s)).collect()),
            Err(t) => Err(Error::Trap(t)),
        }
    }

    /// Sets the fuel left (`None`: unmetered). Each branch, call and
    /// return costs one unit, and a call that runs out traps with
    /// [`Trap::Exhausted`], leaving the fuel at 0. Fuel carries over
    /// between calls.
    pub fn set_fuel(&mut self, fuel: Option<u64>) {
        self.fuel = fuel;
    }

    /// The fuel left, or `None` if unmetered.
    pub fn fuel(&self) -> Option<u64> {
        self.fuel
    }

    /// Calls the exported function `name`.
    pub fn call(&mut self, name: &str, args: &[Val]) -> Result<Vec<Val>, Error> {
        match self.exports.get(name.as_bytes()) {
            Some(&ExportDesc::Func(x)) => self.invoke(x, args),
            _ => Err(Error::Call(format!("unknown export: {name}"))),
        }
    }

    /// Every export with its type.
    pub fn exports(&self) -> Vec<(String, ExternType)> {
        let Some(inner) = self.inner.as_ref() else { return Vec::new() };
        let m = inner.module();
        m.exports.iter().map(|e| {
            let t = match e.desc {
                ExportDesc::Func(x) => {
                    let (p, r) = &self.types[x as usize];
                    ExternType::Func(p.clone(), r.clone())
                }
                ExportDesc::Global(x) => ExternType::Global(m.global_types[x as usize]),
                ExportDesc::Mem(_) => ExternType::Memory(ast::Limits {
                    min: (inner.memory().len() / 65536) as u32,
                    max: m.mems[0].max,
                }),
                ExportDesc::Table(x) => ExternType::Table(m.tables[x as usize]),
            };
            (String::from_utf8_lossy(&e.name).into_owned(), t)
        }).collect()
    }

    /// The value of the exported global `name`.
    pub fn global(&self, name: &str) -> Option<Val> {
        let inner = self.inner.as_ref()?;
        match self.exports.get(name.as_bytes()) {
            Some(&ExportDesc::Global(x)) => {
                let t = inner.module().global_types[x as usize].vt;
                Some(Val::from_slot(t, inner.globals()[x as usize]))
            }
            _ => None,
        }
    }

    pub fn memory(&self) -> &[u8] {
        match &self.inner {
            Some(i) => i.memory(),
            None => &[],
        }
    }

    /// Mutable access to linear memory (empty while a call is running).
    pub fn memory_mut(&mut self) -> &mut [u8] {
        match &mut self.inner {
            Some(i) => i.memory_mut(),
            None => &mut [],
        }
    }

    /// Writes `bytes` into linear memory at `offset`.
    pub fn write_memory(&mut self, offset: usize, bytes: &[u8]) -> Result<(), Error> {
        let inner = self.inner.take().ok_or(Error::Call("instance poisoned by an earlier panic".into()))?;
        let (inner, ok) = inner.write_memory(offset, bytes);
        self.inner = Some(inner);
        if ok { Ok(()) } else { Err(Error::Trap(Trap::MemoryOutOfBounds)) }
    }
}
