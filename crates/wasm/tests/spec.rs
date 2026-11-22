//! Runs the WebAssembly 2.0 core spec tests (fetched by
//! `scripts/fetch-testsuite.sh`) and compares the pass counts with
//! `tests/spec-expected.txt`.
//!
//! Files for features vwasm does not implement (SIMD, the reference-types
//! table instructions) are skipped. Within the other files, directives
//! that need an unsupported feature (multiple tables used by instructions,
//! shared memories or tables between instances, `ref.func` in code) count
//! as failures, so the expected-results file records exactly where
//! vwasm stands.
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use verilith_wasm::api::{Error, ExternType, Instance, Linker, Module, Val};
use verilith_wasm::ast::{Trap, ValType};
use wast::core::{NanPattern, WastArgCore, WastRetCore};
use wast::parser::{self, ParseBuffer};
use wast::{Wast, WastArg, WastDirective, WastExecute, WastInvoke, WastRet};

fn skipped(name: &str) -> bool {
    // Only skip what needs unsupported features wholesale.
    name.starts_with("simd_")
        || matches!(name, "table_copy" | "table_fill" | "table_get" | "table_grow" | "table_init"
            | "table_set" | "table_size" | "ref_func" | "ref_is_null" | "ref_null" | "table-sub")
}

type Inst = Rc<RefCell<Instance>>;

struct Runner {
    current: Option<Inst>,
    named: HashMap<String, Inst>,
    registered: HashMap<String, Inst>,
}

fn spectest(l: &mut Linker) {
    use ValType::*;
    for (name, ps) in [
        ("print", vec![]),
        ("print_i32", vec![I32]),
        ("print_i64", vec![I64]),
        ("print_f32", vec![F32]),
        ("print_f64", vec![F64]),
        ("print_i32_f32", vec![I32, F32]),
        ("print_f64_f64", vec![F64, F64]),
    ] {
        l.func("spectest", name, &ps, &[], |_, _, _| Ok(()));
    }
    l.global("spectest", "global_i32", Val::I32(666), false);
    l.global("spectest", "global_i64", Val::I64(666), false);
    l.global("spectest", "global_f32", Val::F32(666.6f32.to_bits()), false);
    l.global("spectest", "global_f64", Val::F64(666.6f64.to_bits()), false);
    l.table("spectest", "table", 10, Some(20));
    l.memory("spectest", "memory", 1, Some(2));
}

impl Runner {
    fn linker(&self) -> Linker {
        let mut l = Linker::new();
        spectest(&mut l);
        for (mname, inst) in &self.registered {
            let exports = inst.borrow().exports();
            for (name, t) in exports {
                match t {
                    ExternType::Func(p, r) => {
                        let i = inst.clone();
                        let n = name.clone();
                        l.func(mname, &name, &p, &r, move |args, results, _| {
                            let Ok(mut i) = i.try_borrow_mut() else { return Err(Trap::Host) };
                            match i.call(&n, args) {
                                Ok(v) => {
                                    results.copy_from_slice(&v);
                                    Ok(())
                                }
                                Err(Error::Trap(t)) => Err(t),
                                Err(_) => Err(Trap::Host),
                            }
                        });
                    }
                    ExternType::Global(g) => {
                        let v = inst.borrow().global(&name).unwrap();
                        l.global(mname, &name, v, g.mutable);
                    }
                    ExternType::Memory(lim) => {
                        l.memory(mname, &name, lim.min, lim.max);
                    }
                    ExternType::Table(lim) => {
                        l.table(mname, &name, lim.min, lim.max);
                    }
                }
            }
        }
        l
    }

    fn instantiate(&self, bytes: &[u8]) -> Result<Instance, Error> {
        let m = Module::new(bytes)?;
        Instance::new(m, &self.linker())
    }

    fn inst(&self, id: Option<wast::token::Id>) -> Result<Inst, String> {
        match id {
            Some(id) => self.named.get(id.name()).cloned().ok_or("unknown module".into()),
            None => self.current.clone().ok_or("no module".into()),
        }
    }

    fn invoke(&self, inv: &WastInvoke) -> Result<Result<Vec<Val>, Error>, String> {
        let inst = self.inst(inv.module)?;
        let mut args = Vec::new();
        for a in &inv.args {
            args.push(match a {
                WastArg::Core(WastArgCore::I32(x)) => Val::I32(*x),
                WastArg::Core(WastArgCore::I64(x)) => Val::I64(*x),
                WastArg::Core(WastArgCore::F32(x)) => Val::F32(x.bits),
                WastArg::Core(WastArgCore::F64(x)) => Val::F64(x.bits),
                _ => return Err("unsupported argument".into()),
            });
        }
        let r = inst.borrow_mut().call(inv.name, &args);
        Ok(r)
    }

    fn exec(&mut self, e: &mut WastExecute) -> Result<Result<Vec<Val>, Error>, String> {
        match e {
            WastExecute::Invoke(inv) => self.invoke(inv),
            WastExecute::Wat(w) => {
                let bytes = w.encode().map_err(|e| e.to_string())?;
                Ok(self.instantiate(&bytes).map(|_| vec![]))
            }
            WastExecute::Get { module, global, .. } => {
                let inst = self.inst(*module)?;
                let v = inst.borrow().global(global).ok_or("unknown global")?;
                Ok(Ok(vec![v]))
            }
        }
    }
}

fn f32_matches(p: &NanPattern<wast::token::F32>, bits: u32) -> bool {
    match p {
        NanPattern::CanonicalNan => bits & 0x7fff_ffff == 0x7fc0_0000,
        NanPattern::ArithmeticNan => bits & 0x7fc0_0000 == 0x7fc0_0000,
        NanPattern::Value(v) => v.bits == bits,
    }
}

fn f64_matches(p: &NanPattern<wast::token::F64>, bits: u64) -> bool {
    match p {
        NanPattern::CanonicalNan => bits & 0x7fff_ffff_ffff_ffff == 0x7ff8_0000_0000_0000,
        NanPattern::ArithmeticNan => bits & 0x7ff8_0000_0000_0000 == 0x7ff8_0000_0000_0000,
        NanPattern::Value(v) => v.bits == bits,
    }
}

fn ret_matches(want: &WastRet, got: &Val) -> bool {
    match (want, got) {
        (WastRet::Core(WastRetCore::I32(a)), Val::I32(b)) => a == b,
        (WastRet::Core(WastRetCore::I64(a)), Val::I64(b)) => a == b,
        (WastRet::Core(WastRetCore::F32(p)), Val::F32(b)) => f32_matches(p, *b),
        (WastRet::Core(WastRetCore::F64(p)), Val::F64(b)) => f64_matches(p, *b),
        _ => false,
    }
}

/// Runs one directive; `Ok(())` if it passed.
fn directive(r: &mut Runner, d: WastDirective) -> Result<(), String> {
    match d {
        WastDirective::Module(mut q) => {
            let name = q.name().map(|n| n.name().to_string());
            let bytes = q.encode().map_err(|e| e.to_string())?;
            match r.instantiate(&bytes) {
                Ok(i) => {
                    let i = Rc::new(RefCell::new(i));
                    if let Some(n) = name {
                        r.named.insert(n, i.clone());
                    }
                    r.current = Some(i);
                    Ok(())
                }
                Err(e) => {
                    r.current = None;
                    Err(format!("module failed: {e}"))
                }
            }
        }
        WastDirective::Register { name, module, .. } => {
            let i = r.inst(module)?;
            r.registered.insert(name.to_string(), i);
            Ok(())
        }
        WastDirective::Invoke(inv) => match r.invoke(&inv)? {
            Ok(_) => Ok(()),
            Err(e) => Err(format!("invoke {}: {e}", inv.name)),
        },
        WastDirective::AssertReturn { mut exec, results, .. } => match r.exec(&mut exec)? {
            Ok(got) => {
                if got.len() == results.len() && results.iter().zip(&got).all(|(w, g)| ret_matches(w, g)) {
                    Ok(())
                } else {
                    Err(format!("wrong result {got:?}, want {results:?}"))
                }
            }
            Err(e) => Err(format!("error {e}")),
        },
        WastDirective::AssertTrap { mut exec, message, .. } => match r.exec(&mut exec)? {
            Err(Error::Trap(_)) => Ok(()),
            Err(Error::Instantiate(_)) => Ok(()),
            other => Err(format!("expected trap {message}, got {other:?}")),
        },
        WastDirective::AssertExhaustion { call, .. } => match r.invoke(&call)? {
            Err(Error::Trap(Trap::Exhausted)) => Ok(()),
            other => Err(format!("expected exhaustion, got {other:?}")),
        },
        WastDirective::AssertInvalid { mut module, message, .. }
        | WastDirective::AssertMalformed { mut module, message, .. } => {
            let bytes = match module.encode() {
                Ok(b) => b,
                // Text the encoder rejects is malformed already.
                Err(_) => return Ok(()),
            };
            match Module::new(&bytes) {
                Err(_) => Ok(()),
                Ok(_) => Err(format!("expected invalid/malformed ({message}), accepted")),
            }
        }
        WastDirective::AssertUnlinkable { mut module, .. } => {
            let bytes = module.encode().map_err(|e| e.to_string())?;
            match r.instantiate(&bytes) {
                Err(Error::Link(_)) | Err(Error::Instantiate(_)) => Ok(()),
                other => Err(format!("expected unlinkable, got {:?}", other.err())),
            }
        }
        _ => Err("unsupported directive".into()),
    }
}

fn run_file(path: &std::path::Path) -> (usize, usize, Vec<String>) {
    let src = std::fs::read_to_string(path).unwrap();
    let buf = ParseBuffer::new(&src).unwrap();
    let wast: Wast = match parser::parse(&buf) {
        Ok(w) => w,
        Err(e) => return (0, 1, vec![format!("parse: {e}")]),
    };
    let mut r = Runner { current: None, named: HashMap::new(), registered: HashMap::new() };
    let (mut pass, mut fail, mut msgs) = (0, 0, Vec::new());
    for d in wast.directives {
        let (line, _) = d.span().linecol_in(&src);
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| directive(&mut r, d)));
        match res {
            Ok(Ok(())) => pass += 1,
            Ok(Err(m)) => {
                fail += 1;
                msgs.push(format!("line {}: {m}", line + 1));
            }
            Err(_) => {
                fail += 1;
                msgs.push(format!("line {}: panic", line + 1));
            }
        }
    }
    (pass, fail, msgs)
}

#[test]
fn spec() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/testsuite");
    if !dir.exists() {
        eprintln!("tests/testsuite missing; run scripts/fetch-testsuite.sh");
        return;
    }
    let mut files: Vec<_> = std::fs::read_dir(&dir).unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "wast"))
        .collect();
    files.sort();
    let verbose = std::env::var("SPEC_VERBOSE").is_ok();
    let mut report = String::new();
    let (mut tp, mut tf) = (0, 0);
    for f in files {
        let name = f.file_stem().unwrap().to_string_lossy().into_owned();
        if skipped(&name) {
            continue;
        }
        let (p, fl, msgs) = run_file(&f);
        tp += p;
        tf += fl;
        report.push_str(&format!("{name} {p} {fl}\n"));
        if verbose && fl > 0 {
            for m in msgs.iter().take(8) {
                eprintln!("  {name}: {m}");
            }
        }
    }
    report.push_str(&format!("TOTAL {tp} {tf}\n"));
    eprint!("{report}");
    let expected_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/spec-expected.txt");
    if std::env::var("SPEC_BLESS").is_ok() {
        std::fs::write(&expected_path, &report).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&expected_path).unwrap_or_default();
    // Every file must pass at least as many directives as recorded.
    let want: HashMap<&str, usize> = expected.lines()
        .filter_map(|l| {
            let mut it = l.split_whitespace();
            Some((it.next()?, it.next()?.parse().ok()?))
        })
        .collect();
    let mut regressions = Vec::new();
    for l in report.lines() {
        let mut it = l.split_whitespace();
        let (n, p) = (it.next().unwrap(), it.next().unwrap().parse::<usize>().unwrap());
        if let Some(&w) = want.get(n) {
            if p < w {
                regressions.push(format!("{n}: {p} passed, expected {w}"));
            }
        }
    }
    assert!(regressions.is_empty(), "spec test regressions:\n{}", regressions.join("\n"));
}
