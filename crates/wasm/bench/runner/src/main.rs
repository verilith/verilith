//! `runner <vwasm|vwasm-fuel|wasmtime|wasmi> <file.wasm> <func> <args...>`: runs one
//! exported function and prints its result (the bench script times the
//! whole process, as it does for the wasm3 and iwasm command lines).
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (engine, file, func) = (&a[1], &a[2], &a[3]);
    let args: Vec<i64> = a[4..].iter().map(|s| s.parse().unwrap()).collect();
    let bytes = std::fs::read(file).unwrap();
    let r = match engine.as_str() {
        "vwasm" => vwasm_run(&bytes, func, &args, false),
        // Metered, with more fuel than the run needs.
        "vwasm-fuel" => vwasm_run(&bytes, func, &args, true),
        "wasmtime" => wasmtime_run(&bytes, func, &args),
        "wasmi" => wasmi_run(&bytes, func, &args),
        _ => panic!("unknown engine"),
    };
    println!("{r}");
}

fn vwasm_run(bytes: &[u8], func: &str, args: &[i64], metered: bool) -> String {
    use verilith_wasm::api::*;
    use verilith_wasm::ast::ValType;
    let m = Module::new(bytes).unwrap();
    let mut linker = Linker::new();
    if metered {
        linker.fuel(u64::MAX);
    }
    let mut inst = Instance::new(m, &linker).unwrap();
    let params = inst.exports().into_iter().find(|(n, _)| n == func).map(|(_, t)| match t {
        ExternType::Func(p, _) => p,
        _ => panic!(),
    }).unwrap();
    let vals: Vec<Val> = params.iter().zip(args).map(|(t, &x)| match t {
        ValType::I32 => Val::I32(x as i32),
        ValType::I64 => Val::I64(x),
        _ => panic!(),
    }).collect();
    let r = inst.call(func, &vals).unwrap();
    match r[0] {
        Val::I32(x) => (x as u32).to_string(),
        Val::I64(x) => x.to_string(),
        Val::F32(x) => f32::from_bits(x).to_string(),
        Val::F64(x) => f64::from_bits(x).to_string(),
    }
}

fn wasmtime_run(bytes: &[u8], func: &str, args: &[i64]) -> String {
    use wasmtime::*;
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let inst = Instance::new(&mut store, &module, &[]).unwrap();
    let f = inst.get_func(&mut store, func).unwrap();
    let ty = f.ty(&store);
    let vals: Vec<Val> = ty.params().zip(args).map(|(t, &x)| match t {
        ValType::I32 => Val::I32(x as i32),
        ValType::I64 => Val::I64(x),
        _ => panic!(),
    }).collect();
    let mut out = vec![Val::I32(0); ty.results().len()];
    f.call(&mut store, &vals, &mut out).unwrap();
    match out[0] {
        Val::I32(x) => (x as u32).to_string(),
        Val::I64(x) => x.to_string(),
        Val::F64(x) => f64::from_bits(x).to_string(),
        _ => panic!(),
    }
}

fn wasmi_run(bytes: &[u8], func: &str, args: &[i64]) -> String {
    use wasmi::*;
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = Linker::<()>::new(&engine);
    let inst = linker.instantiate_and_start(&mut store, &module).unwrap();
    let f = inst.get_func(&store, func).unwrap();
    let ty = f.ty(&store);
    let vals: Vec<Val> = ty.params().iter().zip(args).map(|(t, &x)| match t {
        ValType::I32 => Val::I32(x as i32),
        ValType::I64 => Val::I64(x),
        _ => panic!(),
    }).collect();
    let mut out = vec![Val::I32(0); ty.results().len()];
    f.call(&mut store, &vals, &mut out).unwrap();
    match out[0] {
        Val::I32(x) => (x as u32).to_string(),
        Val::I64(x) => x.to_string(),
        Val::F64(x) => x.to_float().to_string(),
        _ => panic!(),
    }
}
