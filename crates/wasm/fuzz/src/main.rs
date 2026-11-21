//! Differential testing against wasmi: `vwasm-diff [iterations] [first seed]`.
//!
//! Generates modules with wasm-smith (only the features vwasm implements,
//! NaNs canonicalized, fuel-bounded loops), runs every exported function
//! in both engines on the same arguments, and compares results, traps,
//! linear memory and exported globals after every call.
use arbitrary::Unstructured;
use verilith_wasm::api as v;
use verilith_wasm::ast::{Trap, ValType};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn config(tables: bool) -> wasm_smith::Config {
    let mut c = wasm_smith::Config::default();
    c.simd_enabled = false;
    c.relaxed_simd_enabled = false;
    c.reference_types_enabled = false;
    c.gc_enabled = false;
    c.exceptions_enabled = false;
    c.tail_call_enabled = false;
    c.threads_enabled = false;
    c.memory64_enabled = false;
    c.custom_page_sizes_enabled = false;
    c.wide_arithmetic_enabled = false;
    c.extended_const_enabled = false;
    c.shared_everything_threads_enabled = false;
    c.bulk_memory_enabled = !tables;
    c.multi_value_enabled = true;
    c.saturating_float_to_int_enabled = true;
    c.sign_extension_ops_enabled = true;
    c.canonicalize_nans = true;
    c.export_everything = true;
    c.max_imports = 0;
    c.max_memories = 1;
    c.max_memory32_bytes = 1 << 20;
    c.max_tables = if tables { 1 } else { 0 };
    c.max_table_elements = 100;
    c.min_funcs = 1;
    c.max_funcs = 10;
    c.max_instructions = 200;
    c
}

#[derive(Debug, PartialEq)]
enum Out {
    Vals(Vec<u64>),
    Trap,
    /// Stack exhaustion: the engines' limits differ, so stop comparing.
    Exhausted,
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let iters: u64 = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(1000);
    let first: u64 = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(1);
    let (mut ran, mut calls, mut unsupported, mut mismatches) = (0, 0, 0, 0);
    for it in first..first + iters {
        let mut seed = it.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        let bytes: Vec<u8> = (0..8192).map(|_| rng(&mut seed) as u8).collect();
        let mut u = Unstructured::new(&bytes);
        let Ok(mut m) = wasm_smith::Module::new(config(it % 2 == 0), &mut u) else { continue };
        if m.ensure_termination(1000).is_err() {
            continue;
        }
        let wasm = m.to_bytes();
        match run(&wasm, &mut seed) {
            Ok(n) => {
                ran += 1;
                calls += n;
            }
            Err(Some(msg)) => {
                mismatches += 1;
                let path = format!("mismatch-{it}.wasm");
                std::fs::write(&path, &wasm).unwrap();
                eprintln!("seed {it}: {msg} (saved {path})");
            }
            Err(None) => unsupported += 1,
        }
    }
    println!("{ran} modules, {calls} calls compared, {unsupported} unsupported, {mismatches} mismatches");
    if mismatches > 0 {
        std::process::exit(1);
    }
}

/// `Err(None)`: vwasm does not support the module.
fn run(wasm: &[u8], seed: &mut u64) -> Result<usize, Option<String>> {
    let vm = match v::Module::new(wasm) {
        Ok(m) => m,
        Err(v::Error::Decode("unsupported instruction")) | Err(v::Error::Decode("unsupported table element type"))
        | Err(v::Error::Decode("malformed value type")) => return Err(None),
        Err(e) => return Err(Some(format!("vwasm rejected a valid module: {e:?}"))),
    };
    let engine = wasmi::Engine::default();
    let wm = wasmi::Module::new(&engine, wasm).map_err(|e| Some(format!("wasmi rejected: {e}")))?;
    let mut store = wasmi::Store::new(&engine, ());
    let linker = wasmi::Linker::<()>::new(&engine);
    let wi = linker.instantiate(&mut store, &wm).and_then(|p| p.start(&mut store).map_err(Into::into));
    let vi = v::Instance::new(vm, &v::Linker::new());
    let (wi, mut vi) = match (wi, vi) {
        (Ok(w), Ok(v)) => (w, v),
        (Err(_), Err(_)) => return Ok(0),
        (w, v) => return Err(Some(format!("instantiation differs: wasmi ok={} vwasm={:?}", w.is_ok(), v.err()))),
    };
    let exports = vi.exports();
    let mut n = 0;
    for (name, t) in &exports {
        let v::ExternType::Func(params, results) = t else { continue };
        for round in 0..3 {
            let args: Vec<u64> = params.iter().map(|_| match round {
                0 => 0,
                1 => 1,
                _ => rng(seed),
            }).collect();
            let vo = {
                let vals: Vec<v::Val> = params.iter().zip(&args).map(|(t, &x)| match t {
                    ValType::I32 => v::Val::I32(x as i32),
                    ValType::I64 => v::Val::I64(x as i64),
                    ValType::F32 => v::Val::F32(x as u32),
                    ValType::F64 => v::Val::F64(x),
                }).collect();
                match vi.call(name, &vals) {
                    Ok(r) => Out::Vals(r.iter().map(|x| match *x {
                        v::Val::I32(x) => x as u32 as u64,
                        v::Val::I64(x) => x as u64,
                        v::Val::F32(x) => x as u64,
                        v::Val::F64(x) => x,
                    }).collect()),
                    Err(v::Error::Trap(Trap::Exhausted)) => Out::Exhausted,
                    Err(v::Error::Trap(_)) => Out::Trap,
                    Err(e) => return Err(Some(format!("vwasm call error {e:?}"))),
                }
            };
            let wo = {
                use wasmi::Val;
                let f = wi.get_func(&store, name).unwrap();
                let vals: Vec<Val> = params.iter().zip(&args).map(|(t, &x)| match t {
                    ValType::I32 => Val::I32(x as i32),
                    ValType::I64 => Val::I64(x as i64),
                    ValType::F32 => Val::F32(wasmi::core::F32::from_bits(x as u32)),
                    ValType::F64 => Val::F64(wasmi::core::F64::from_bits(x)),
                }).collect();
                let mut out = vec![Val::I32(0); results.len()];
                match f.call(&mut store, &vals, &mut out) {
                    Ok(()) => Out::Vals(out.iter().map(|x| match x {
                        Val::I32(x) => *x as u32 as u64,
                        Val::I64(x) => *x as u64,
                        Val::F32(x) => x.to_bits() as u64,
                        Val::F64(x) => x.to_bits(),
                        _ => 0,
                    }).collect()),
                    Err(e) => match e.as_trap_code() {
                        Some(wasmi::core::TrapCode::StackOverflow) => Out::Exhausted,
                        _ => Out::Trap,
                    },
                }
            };
            n += 1;
            if vo == Out::Exhausted || wo == Out::Exhausted {
                return Ok(n);
            }
            if vo != wo {
                return Err(Some(format!("{name}{args:x?}: vwasm {vo:?}, wasmi {wo:?}")));
            }
            // Memory and exported globals.
            let wmem = wi.get_memory(&store, "").or_else(|| {
                exports.iter().find_map(|(n, t)| matches!(t, v::ExternType::Memory(_)).then(|| wi.get_memory(&store, n)).flatten())
            });
            if let Some(mem) = wmem {
                if mem.data(&store) != vi.memory() {
                    return Err(Some(format!("{name}{args:x?}: memories differ")));
                }
            }
            for (g, gt) in &exports {
                if !matches!(gt, v::ExternType::Global(_)) {
                    continue;
                }
                let wv = wi.get_global(&store, g).unwrap().get(&store);
                let vv = vi.global(g).unwrap();
                let same = match (wv, vv) {
                    (wasmi::Val::I32(a), v::Val::I32(b)) => a == b,
                    (wasmi::Val::I64(a), v::Val::I64(b)) => a == b,
                    (wasmi::Val::F32(a), v::Val::F32(b)) => a.to_bits() == b,
                    (wasmi::Val::F64(a), v::Val::F64(b)) => a.to_bits() == b,
                    _ => false,
                };
                if !same {
                    return Err(Some(format!("{name}{args:x?}: global {g} differs")));
                }
            }
        }
    }
    Ok(n)
}
