//! A subset of the standard WebAssembly C API (`include/wasm.h`, from
//! WebAssembly/wasm-c-api), enough for its `hello`, `callback`, `global`,
//! `memory` and `multi` style programs: engines, stores, modules,
//! functions (host and exported), instances, exported memories and
//! globals, and traps.
//!
//! Not implemented: tables as externs, references, frames/traces,
//! serialization, and importing a memory or table *shared* with another
//! instance (an imported memory is a fresh one with the import's limits).
//! A host function cannot call back into the instance that called it.
#![allow(non_camel_case_types, clippy::missing_safety_doc)]

use std::cell::RefCell;
use std::ffi::c_void;
use std::rc::Rc;

use crate::api::{Error, ExternType, Instance, Linker, Module, Val};
use crate::ast::{ImportDesc, Trap, ValType};

// ---------------------------------------------------------------------------
// Vectors
// ---------------------------------------------------------------------------

#[repr(C)]
pub struct wasm_vec_t<T> {
    pub size: usize,
    pub data: *mut T,
}

pub type wasm_byte_vec_t = wasm_vec_t<u8>;

unsafe fn vec_new<T>(out: *mut wasm_vec_t<T>, v: Vec<T>) {
    let b = v.into_boxed_slice();
    let size = b.len();
    let data = if size == 0 { std::ptr::null_mut() } else { Box::into_raw(b) as *mut T };
    *out = wasm_vec_t { size, data };
}

unsafe fn vec_take<T>(v: *mut wasm_vec_t<T>) -> Vec<T> {
    if v.is_null() || (*v).data.is_null() {
        return Vec::new();
    }
    let b = Box::from_raw(std::ptr::slice_from_raw_parts_mut((*v).data, (*v).size));
    (*v).data = std::ptr::null_mut();
    (*v).size = 0;
    b.into_vec()
}

unsafe fn vec_slice<'a, T>(v: *const wasm_vec_t<T>) -> &'a [T] {
    if v.is_null() || (*v).data.is_null() {
        &[]
    } else {
        std::slice::from_raw_parts((*v).data, (*v).size)
    }
}

macro_rules! plain_vec {
    ($t:ty, $new_empty:ident, $new_uninit:ident, $new:ident, $copy:ident, $delete:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $new_empty(out: *mut wasm_vec_t<$t>) {
            vec_new(out, Vec::new());
        }
        #[no_mangle]
        pub unsafe extern "C" fn $new_uninit(out: *mut wasm_vec_t<$t>, n: usize) {
            vec_new(out, vec![<$t>::default(); n]);
        }
        #[no_mangle]
        pub unsafe extern "C" fn $new(out: *mut wasm_vec_t<$t>, n: usize, data: *const $t) {
            let v = if n == 0 { Vec::new() } else { std::slice::from_raw_parts(data, n).to_vec() };
            vec_new(out, v);
        }
        #[no_mangle]
        pub unsafe extern "C" fn $copy(out: *mut wasm_vec_t<$t>, src: *const wasm_vec_t<$t>) {
            vec_new(out, vec_slice(src).to_vec());
        }
        #[no_mangle]
        pub unsafe extern "C" fn $delete(v: *mut wasm_vec_t<$t>) {
            drop(vec_take(v));
        }
    };
}

plain_vec!(u8, wasm_byte_vec_new_empty, wasm_byte_vec_new_uninitialized, wasm_byte_vec_new,
    wasm_byte_vec_copy, wasm_byte_vec_delete);

/// Vectors of owned pointers: deleting the vector deletes the elements.
macro_rules! ptr_vec {
    ($t:ty, $new_empty:ident, $new_uninit:ident, $new:ident, $delete:ident, $elem_delete:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $new_empty(out: *mut wasm_vec_t<*mut $t>) {
            vec_new(out, Vec::new());
        }
        #[no_mangle]
        pub unsafe extern "C" fn $new_uninit(out: *mut wasm_vec_t<*mut $t>, n: usize) {
            vec_new(out, vec![std::ptr::null_mut(); n]);
        }
        #[no_mangle]
        pub unsafe extern "C" fn $new(out: *mut wasm_vec_t<*mut $t>, n: usize, data: *const *mut $t) {
            let v = if n == 0 { Vec::new() } else { std::slice::from_raw_parts(data, n).to_vec() };
            vec_new(out, v);
        }
        #[no_mangle]
        pub unsafe extern "C" fn $delete(v: *mut wasm_vec_t<*mut $t>) {
            for p in vec_take(v) {
                $elem_delete(p);
            }
        }
    };
}

// ---------------------------------------------------------------------------
// Engine and store
// ---------------------------------------------------------------------------

pub struct wasm_engine_t;
pub struct wasm_store_t;
pub struct wasm_config_t;

#[no_mangle]
pub extern "C" fn wasm_config_new() -> *mut wasm_config_t {
    Box::into_raw(Box::new(wasm_config_t))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_config_delete(c: *mut wasm_config_t) {
    if !c.is_null() {
        drop(Box::from_raw(c));
    }
}

#[no_mangle]
pub extern "C" fn wasm_engine_new() -> *mut wasm_engine_t {
    Box::into_raw(Box::new(wasm_engine_t))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_engine_new_with_config(c: *mut wasm_config_t) -> *mut wasm_engine_t {
    wasm_config_delete(c);
    wasm_engine_new()
}

#[no_mangle]
pub unsafe extern "C" fn wasm_engine_delete(e: *mut wasm_engine_t) {
    if !e.is_null() {
        drop(Box::from_raw(e));
    }
}

#[no_mangle]
pub extern "C" fn wasm_store_new(_: *mut wasm_engine_t) -> *mut wasm_store_t {
    Box::into_raw(Box::new(wasm_store_t))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_store_delete(s: *mut wasm_store_t) {
    if !s.is_null() {
        drop(Box::from_raw(s));
    }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

pub struct wasm_valtype_t {
    kind: u8,
}

pub type wasm_valtype_vec_t = wasm_vec_t<*mut wasm_valtype_t>;

#[no_mangle]
pub extern "C" fn wasm_valtype_new(kind: u8) -> *mut wasm_valtype_t {
    Box::into_raw(Box::new(wasm_valtype_t { kind }))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_valtype_kind(t: *const wasm_valtype_t) -> u8 {
    (*t).kind
}

#[no_mangle]
pub unsafe extern "C" fn wasm_valtype_copy(t: *const wasm_valtype_t) -> *mut wasm_valtype_t {
    wasm_valtype_new((*t).kind)
}

#[no_mangle]
pub unsafe extern "C" fn wasm_valtype_delete(t: *mut wasm_valtype_t) {
    if !t.is_null() {
        drop(Box::from_raw(t));
    }
}

ptr_vec!(wasm_valtype_t, wasm_valtype_vec_new_empty, wasm_valtype_vec_new_uninitialized, wasm_valtype_vec_new,
    wasm_valtype_vec_delete, wasm_valtype_delete);

#[no_mangle]
pub unsafe extern "C" fn wasm_valtype_vec_copy(out: *mut wasm_valtype_vec_t, src: *const wasm_valtype_vec_t) {
    let v = vec_slice(src).iter().map(|&t| wasm_valtype_copy(t)).collect();
    vec_new(out, v);
}

fn kind_of(t: ValType) -> u8 {
    match t {
        ValType::I32 => 0,
        ValType::I64 => 1,
        ValType::F32 => 2,
        ValType::F64 => 3,
    }
}

fn type_of(k: u8) -> Option<ValType> {
    Some(match k {
        0 => ValType::I32,
        1 => ValType::I64,
        2 => ValType::F32,
        3 => ValType::F64,
        _ => return None,
    })
}

pub struct wasm_functype_t {
    params: wasm_valtype_vec_t,
    results: wasm_valtype_vec_t,
}

unsafe fn functype(p: &[ValType], r: &[ValType]) -> *mut wasm_functype_t {
    let mut f = Box::new(wasm_functype_t {
        params: wasm_vec_t { size: 0, data: std::ptr::null_mut() },
        results: wasm_vec_t { size: 0, data: std::ptr::null_mut() },
    });
    vec_new(&mut f.params, p.iter().map(|&t| wasm_valtype_new(kind_of(t))).collect());
    vec_new(&mut f.results, r.iter().map(|&t| wasm_valtype_new(kind_of(t))).collect());
    Box::into_raw(f)
}

unsafe fn types(v: *const wasm_valtype_vec_t) -> Option<Vec<ValType>> {
    vec_slice(v).iter().map(|&t| type_of((*t).kind)).collect()
}

#[no_mangle]
pub unsafe extern "C" fn wasm_functype_new(params: *mut wasm_valtype_vec_t, results: *mut wasm_valtype_vec_t)
    -> *mut wasm_functype_t
{
    let f = Box::new(wasm_functype_t {
        params: wasm_vec_t { size: (*params).size, data: (*params).data },
        results: wasm_vec_t { size: (*results).size, data: (*results).data },
    });
    (*params).data = std::ptr::null_mut();
    (*params).size = 0;
    (*results).data = std::ptr::null_mut();
    (*results).size = 0;
    Box::into_raw(f)
}

#[no_mangle]
pub unsafe extern "C" fn wasm_functype_params(f: *const wasm_functype_t) -> *const wasm_valtype_vec_t {
    &(*f).params
}

#[no_mangle]
pub unsafe extern "C" fn wasm_functype_results(f: *const wasm_functype_t) -> *const wasm_valtype_vec_t {
    &(*f).results
}

#[no_mangle]
pub unsafe extern "C" fn wasm_functype_copy(f: *const wasm_functype_t) -> *mut wasm_functype_t {
    let mut g = Box::new(wasm_functype_t {
        params: wasm_vec_t { size: 0, data: std::ptr::null_mut() },
        results: wasm_vec_t { size: 0, data: std::ptr::null_mut() },
    });
    wasm_valtype_vec_copy(&mut g.params, &(*f).params);
    wasm_valtype_vec_copy(&mut g.results, &(*f).results);
    Box::into_raw(g)
}

#[no_mangle]
pub unsafe extern "C" fn wasm_functype_delete(f: *mut wasm_functype_t) {
    if f.is_null() {
        return;
    }
    let mut f = Box::from_raw(f);
    wasm_valtype_vec_delete(&mut f.params);
    wasm_valtype_vec_delete(&mut f.results);
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

#[repr(C)]
#[derive(Clone, Copy)]
pub union wasm_val_union {
    pub i32: i32,
    pub i64: i64,
    pub f32: f32,
    pub f64: f64,
    pub ref_: *mut c_void,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct wasm_val_t {
    pub kind: u8,
    pub of: wasm_val_union,
}

impl Default for wasm_val_t {
    fn default() -> Self {
        wasm_val_t { kind: 0, of: wasm_val_union { i64: 0 } }
    }
}

pub type wasm_val_vec_t = wasm_vec_t<wasm_val_t>;

plain_vec!(wasm_val_t, wasm_val_vec_new_empty, wasm_val_vec_new_uninitialized, wasm_val_vec_new,
    wasm_val_vec_copy, wasm_val_vec_delete);

#[no_mangle]
pub unsafe extern "C" fn wasm_val_copy(out: *mut wasm_val_t, v: *const wasm_val_t) {
    *out = *v;
}

#[no_mangle]
pub extern "C" fn wasm_val_delete(_: *mut wasm_val_t) {}

fn to_c(v: Val) -> wasm_val_t {
    match v {
        Val::I32(x) => wasm_val_t { kind: 0, of: wasm_val_union { i32: x } },
        Val::I64(x) => wasm_val_t { kind: 1, of: wasm_val_union { i64: x } },
        Val::F32(x) => wasm_val_t { kind: 2, of: wasm_val_union { f32: f32::from_bits(x) } },
        Val::F64(x) => wasm_val_t { kind: 3, of: wasm_val_union { f64: f64::from_bits(x) } },
    }
}

unsafe fn from_c(v: &wasm_val_t) -> Option<Val> {
    Some(match v.kind {
        0 => Val::I32(v.of.i32),
        1 => Val::I64(v.of.i64),
        2 => Val::F32(v.of.f32.to_bits()),
        3 => Val::F64(v.of.f64.to_bits()),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Traps
// ---------------------------------------------------------------------------

pub struct wasm_trap_t {
    message: String,
}

pub struct wasm_frame_t;

fn trap(message: String) -> *mut wasm_trap_t {
    Box::into_raw(Box::new(wasm_trap_t { message }))
}

fn trap_message(t: Trap) -> &'static str {
    match t {
        Trap::Unreachable => "unreachable",
        Trap::DivByZero => "integer divide by zero",
        Trap::IntOverflow => "integer overflow",
        Trap::InvalidConversion => "invalid conversion to integer",
        Trap::MemoryOutOfBounds => "out of bounds memory access",
        Trap::TableOutOfBounds => "undefined element",
        Trap::UninitializedElement => "uninitialized element",
        Trap::IndirectCallTypeMismatch => "indirect call type mismatch",
        Trap::Exhausted => "call stack exhausted",
        Trap::Host => "host trap",
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_trap_new(_: *mut wasm_store_t, msg: *const wasm_byte_vec_t) -> *mut wasm_trap_t {
    let b = vec_slice(msg);
    let b = b.strip_suffix(&[0]).unwrap_or(b);
    trap(String::from_utf8_lossy(b).into_owned())
}

#[no_mangle]
pub unsafe extern "C" fn wasm_trap_message(t: *const wasm_trap_t, out: *mut wasm_byte_vec_t) {
    let mut v = (*t).message.as_bytes().to_vec();
    v.push(0);
    vec_new(out, v);
}

#[no_mangle]
pub extern "C" fn wasm_trap_origin(_: *const wasm_trap_t) -> *mut wasm_frame_t {
    std::ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn wasm_trap_trace(_: *const wasm_trap_t, out: *mut wasm_vec_t<*mut wasm_frame_t>) {
    vec_new(out, Vec::new());
}

#[no_mangle]
pub unsafe extern "C" fn wasm_trap_delete(t: *mut wasm_trap_t) {
    if !t.is_null() {
        drop(Box::from_raw(t));
    }
}

// ---------------------------------------------------------------------------
// Modules
// ---------------------------------------------------------------------------

pub struct wasm_module_t {
    bytes: Vec<u8>,
    imports: Vec<(Vec<u8>, Vec<u8>, ImportDesc)>,
}

#[no_mangle]
pub unsafe extern "C" fn wasm_module_new(_: *mut wasm_store_t, binary: *const wasm_byte_vec_t) -> *mut wasm_module_t {
    let bytes = vec_slice(binary).to_vec();
    match Module::new(&bytes) {
        Ok(m) => {
            let imports = m.imports().iter().map(|i| (i.module.clone(), i.name.clone(), i.desc)).collect();
            Box::into_raw(Box::new(wasm_module_t { bytes, imports }))
        }
        Err(_) => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_module_validate(_: *mut wasm_store_t, binary: *const wasm_byte_vec_t) -> bool {
    Module::new(vec_slice(binary)).is_ok()
}

#[no_mangle]
pub unsafe extern "C" fn wasm_module_delete(m: *mut wasm_module_t) {
    if !m.is_null() {
        drop(Box::from_raw(m));
    }
}

// ---------------------------------------------------------------------------
// Externs: functions, memories, globals
// ---------------------------------------------------------------------------

type Callback = unsafe extern "C" fn(*const wasm_val_vec_t, *mut wasm_val_vec_t) -> *mut wasm_trap_t;
type CallbackEnv = unsafe extern "C" fn(*mut c_void, *const wasm_val_vec_t, *mut wasm_val_vec_t) -> *mut wasm_trap_t;

struct Env {
    env: *mut c_void,
    finalizer: Option<unsafe extern "C" fn(*mut c_void)>,
}

impl Drop for Env {
    fn drop(&mut self) {
        if let Some(f) = self.finalizer {
            unsafe { f(self.env) }
        }
    }
}

enum Host {
    Plain(Callback),
    WithEnv(CallbackEnv, Rc<Env>),
}

enum Ext {
    HostFunc { params: Vec<ValType>, results: Vec<ValType>, host: Host },
    Func { inst: Rc<RefCell<Instance>>, name: String, params: Vec<ValType>, results: Vec<ValType> },
    Memory { inst: Rc<RefCell<Instance>>, max: Option<u32> },
    Global { inst: Rc<RefCell<Instance>>, name: String, mutable: bool },
}

/// `wasm_extern_t`, `wasm_func_t`, `wasm_memory_t` and `wasm_global_t`
/// are all this one type, so the `as_` conversions are casts.
pub struct wasm_extern_t {
    ext: Ext,
}

pub type wasm_func_t = wasm_extern_t;
pub type wasm_memory_t = wasm_extern_t;
pub type wasm_global_t = wasm_extern_t;
pub type wasm_extern_vec_t = wasm_vec_t<*mut wasm_extern_t>;

#[no_mangle]
pub unsafe extern "C" fn wasm_extern_delete(e: *mut wasm_extern_t) {
    if !e.is_null() {
        drop(Box::from_raw(e));
    }
}

ptr_vec!(wasm_extern_t, wasm_extern_vec_new_empty, wasm_extern_vec_new_uninitialized, wasm_extern_vec_new,
    wasm_extern_vec_delete, wasm_extern_delete);

#[no_mangle]
pub unsafe extern "C" fn wasm_extern_kind(e: *const wasm_extern_t) -> u8 {
    match (*e).ext {
        Ext::HostFunc { .. } | Ext::Func { .. } => 0,
        Ext::Global { .. } => 1,
        Ext::Memory { .. } => 3,
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_extern_as_func(e: *mut wasm_extern_t) -> *mut wasm_func_t {
    if e.is_null() || wasm_extern_kind(e) != 0 { std::ptr::null_mut() } else { e }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_extern_as_memory(e: *mut wasm_extern_t) -> *mut wasm_memory_t {
    if e.is_null() || wasm_extern_kind(e) != 3 { std::ptr::null_mut() } else { e }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_extern_as_global(e: *mut wasm_extern_t) -> *mut wasm_global_t {
    if e.is_null() || wasm_extern_kind(e) != 1 { std::ptr::null_mut() } else { e }
}

#[no_mangle]
pub extern "C" fn wasm_func_as_extern(f: *mut wasm_func_t) -> *mut wasm_extern_t {
    f
}

#[no_mangle]
pub extern "C" fn wasm_memory_as_extern(m: *mut wasm_memory_t) -> *mut wasm_extern_t {
    m
}

#[no_mangle]
pub extern "C" fn wasm_global_as_extern(g: *mut wasm_global_t) -> *mut wasm_extern_t {
    g
}

unsafe fn host_func(t: *const wasm_functype_t, host: Host) -> *mut wasm_func_t {
    let (Some(params), Some(results)) = (types(&(*t).params), types(&(*t).results)) else {
        return std::ptr::null_mut();
    };
    Box::into_raw(Box::new(wasm_extern_t { ext: Ext::HostFunc { params, results, host } }))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_new(_: *mut wasm_store_t, t: *const wasm_functype_t, cb: Callback) -> *mut wasm_func_t {
    host_func(t, Host::Plain(cb))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_new_with_env(_: *mut wasm_store_t, t: *const wasm_functype_t, cb: CallbackEnv,
    env: *mut c_void, finalizer: Option<unsafe extern "C" fn(*mut c_void)>) -> *mut wasm_func_t
{
    host_func(t, Host::WithEnv(cb, Rc::new(Env { env, finalizer })))
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_delete(f: *mut wasm_func_t) {
    wasm_extern_delete(f)
}

unsafe fn func_sig(f: *const wasm_func_t) -> (&'static [ValType], &'static [ValType]) {
    match &(*f).ext {
        Ext::HostFunc { params, results, .. } | Ext::Func { params, results, .. } => {
            (std::mem::transmute::<&[ValType], &'static [ValType]>(params.as_slice()),
             std::mem::transmute::<&[ValType], &'static [ValType]>(results.as_slice()))
        }
        _ => (&[], &[]),
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_type(f: *const wasm_func_t) -> *mut wasm_functype_t {
    let (p, r) = func_sig(f);
    functype(p, r)
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_param_arity(f: *const wasm_func_t) -> usize {
    func_sig(f).0.len()
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_result_arity(f: *const wasm_func_t) -> usize {
    func_sig(f).1.len()
}

/// Calls a host callback with Rust values.
unsafe fn call_host(host: &Host, args: &[Val], results: &mut [Val]) -> Result<(), String> {
    let mut a = wasm_vec_t { size: 0, data: std::ptr::null_mut() };
    vec_new(&mut a, args.iter().map(|&v| to_c(v)).collect());
    let mut r = wasm_vec_t { size: 0, data: std::ptr::null_mut() };
    vec_new(&mut r, results.iter().map(|&v| to_c(v)).collect());
    let t = match host {
        Host::Plain(cb) => cb(&a, &mut r),
        Host::WithEnv(cb, env) => cb(env.env, &a, &mut r),
    };
    let out = vec_take(&mut r);
    drop(vec_take(&mut a));
    if !t.is_null() {
        let msg = (*t).message.clone();
        wasm_trap_delete(t);
        return Err(msg);
    }
    for (slot, v) in results.iter_mut().zip(&out) {
        *slot = from_c(v).ok_or("bad result")?;
    }
    Ok(())
}

#[no_mangle]
pub unsafe extern "C" fn wasm_func_call(f: *const wasm_func_t, args: *const wasm_val_vec_t,
    results: *mut wasm_val_vec_t) -> *mut wasm_trap_t
{
    let Some(a) = vec_slice(args).iter().map(|v| from_c(v)).collect::<Option<Vec<Val>>>() else {
        return trap("bad argument".into());
    };
    let out: Result<Vec<Val>, String> = match &(*f).ext {
        Ext::HostFunc { results: rt, host, .. } => {
            let mut r: Vec<Val> = rt.iter().map(|&t| to_val(t, 0)).collect();
            call_host(host, &a, &mut r).map(|_| r)
        }
        Ext::Func { inst, name, .. } => match inst.try_borrow_mut() {
            Ok(mut i) => i.call(name, &a).map_err(|e| match e {
                Error::Trap(t) => trap_message(t).to_string(),
                e => e.to_string(),
            }),
            Err(_) => Err("re-entrant call into an instance".into()),
        },
        _ => Err("not a function".into()),
    };
    match out {
        Ok(v) => {
            let dst = if results.is_null() || (*results).data.is_null() {
                &mut [][..]
            } else {
                std::slice::from_raw_parts_mut((*results).data, (*results).size)
            };
            for (d, s) in dst.iter_mut().zip(v) {
                *d = to_c(s);
            }
            std::ptr::null_mut()
        }
        Err(m) => trap(m),
    }
}

fn to_val(t: ValType, x: u64) -> Val {
    match t {
        ValType::I32 => Val::I32(x as i32),
        ValType::I64 => Val::I64(x as i64),
        ValType::F32 => Val::F32(x as u32),
        ValType::F64 => Val::F64(x),
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_memory_data(m: *mut wasm_memory_t) -> *mut u8 {
    match &(*m).ext {
        Ext::Memory { inst, .. } => match inst.try_borrow_mut() {
            Ok(mut i) => i.memory_mut().as_mut_ptr(),
            Err(_) => std::ptr::null_mut(),
        },
        _ => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_memory_data_size(m: *const wasm_memory_t) -> usize {
    match &(*m).ext {
        Ext::Memory { inst, .. } => inst.try_borrow().map(|i| i.memory().len()).unwrap_or(0),
        _ => 0,
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_memory_size(m: *const wasm_memory_t) -> u32 {
    (wasm_memory_data_size(m) / 65536) as u32
}

#[no_mangle]
pub unsafe extern "C" fn wasm_memory_delete(m: *mut wasm_memory_t) {
    wasm_extern_delete(m)
}

#[no_mangle]
pub unsafe extern "C" fn wasm_global_get(g: *const wasm_global_t, out: *mut wasm_val_t) {
    if let Ext::Global { inst, name, .. } = &(*g).ext {
        if let Some(v) = inst.try_borrow().ok().and_then(|i| i.global(name)) {
            *out = to_c(v);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_global_delete(g: *mut wasm_global_t) {
    wasm_extern_delete(g)
}

// ---------------------------------------------------------------------------
// Instances
// ---------------------------------------------------------------------------

pub struct wasm_instance_t {
    inst: Rc<RefCell<Instance>>,
}

#[no_mangle]
pub unsafe extern "C" fn wasm_instance_new(_: *mut wasm_store_t, m: *const wasm_module_t,
    imports: *const wasm_extern_vec_t, trap_out: *mut *mut wasm_trap_t) -> *mut wasm_instance_t
{
    let fail = |msg: String| {
        if !trap_out.is_null() {
            *trap_out = trap(msg);
        }
        std::ptr::null_mut()
    };
    let externs = vec_slice(imports);
    if externs.len() != (*m).imports.len() {
        return fail("wrong number of imports".into());
    }
    let mut linker = Linker::new();
    for ((module, name, desc), &e) in (*m).imports.iter().zip(externs) {
        let (module, name) = (String::from_utf8_lossy(module), String::from_utf8_lossy(name));
        if e.is_null() {
            return fail(format!("missing import {module}::{name}"));
        }
        match (&(*e).ext, desc) {
            (Ext::HostFunc { params, results, host }, ImportDesc::Func(_)) => {
                let host = match host {
                    Host::Plain(cb) => Host::Plain(*cb),
                    Host::WithEnv(cb, env) => Host::WithEnv(*cb, env.clone()),
                };
                linker.func(&module, &name, params, results, move |a, r, _mem| {
                    call_host(&host, a, r).map_err(|_| Trap::Host)
                });
            }
            (Ext::Func { inst, name: export, params, results }, ImportDesc::Func(_)) => {
                let (inst, export) = (inst.clone(), export.clone());
                linker.func(&module, &name, params, results, move |a, r, _mem| {
                    let mut i = inst.try_borrow_mut().map_err(|_| Trap::Host)?;
                    let out = i.call(&export, a).map_err(|e| match e {
                        Error::Trap(t) => t,
                        _ => Trap::Host,
                    })?;
                    r.copy_from_slice(&out);
                    Ok(())
                });
            }
            (Ext::Global { inst, name: g, mutable }, ImportDesc::Global(_)) => {
                let Some(v) = inst.borrow().global(g) else { return fail("bad global".into()) };
                linker.global(&module, &name, v, *mutable);
            }
            (Ext::Memory { inst, max }, ImportDesc::Mem(_)) => {
                let pages = (inst.borrow().memory().len() / 65536) as u32;
                linker.memory(&module, &name, pages, *max);
            }
            _ => return fail(format!("incompatible import {module}::{name}")),
        }
    }
    let module = match Module::new(&(*m).bytes) {
        Ok(x) => x,
        Err(e) => return fail(e.to_string()),
    };
    match Instance::new(module, &linker) {
        Ok(i) => Box::into_raw(Box::new(wasm_instance_t { inst: Rc::new(RefCell::new(i)) })),
        Err(Error::Trap(t)) => fail(trap_message(t).into()),
        Err(e) => fail(e.to_string()),
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_instance_delete(i: *mut wasm_instance_t) {
    if !i.is_null() {
        drop(Box::from_raw(i));
    }
}

#[no_mangle]
pub unsafe extern "C" fn wasm_instance_exports(i: *const wasm_instance_t, out: *mut wasm_extern_vec_t) {
    let inst = &(*i).inst;
    let exports = inst.borrow().exports();
    let v = exports.into_iter().filter_map(|(name, t)| {
        let ext = match t {
            ExternType::Func(params, results) => Ext::Func { inst: inst.clone(), name, params, results },
            ExternType::Memory(l) => Ext::Memory { inst: inst.clone(), max: l.max },
            ExternType::Global(g) => Ext::Global { inst: inst.clone(), name, mutable: g.mutable },
            ExternType::Table(_) => return None,
        };
        Some(Box::into_raw(Box::new(wasm_extern_t { ext })))
    }).collect();
    vec_new(out, v);
}

// ---------------------------------------------------------------------------
// Frames (traps carry no trace, so these only exist to link)
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn wasm_frame_delete(f: *mut wasm_frame_t) {
    if !f.is_null() {
        drop(Box::from_raw(f));
    }
}

#[no_mangle]
pub extern "C" fn wasm_frame_copy(_: *const wasm_frame_t) -> *mut wasm_frame_t {
    Box::into_raw(Box::new(wasm_frame_t))
}

#[no_mangle]
pub extern "C" fn wasm_frame_instance(_: *const wasm_frame_t) -> *mut wasm_instance_t {
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn wasm_frame_func_index(_: *const wasm_frame_t) -> u32 {
    0
}

#[no_mangle]
pub extern "C" fn wasm_frame_func_offset(_: *const wasm_frame_t) -> usize {
    0
}

#[no_mangle]
pub extern "C" fn wasm_frame_module_offset(_: *const wasm_frame_t) -> usize {
    0
}

ptr_vec!(wasm_frame_t, wasm_frame_vec_new_empty, wasm_frame_vec_new_uninitialized, wasm_frame_vec_new,
    wasm_frame_vec_delete, wasm_frame_delete);
