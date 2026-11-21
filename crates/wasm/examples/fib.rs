use verilith_wasm::api::*;
fn main() {
    let wasm = wat::parse_str(r#"(module
      (func $fib (export "fib") (param i64) (result i64)
        (if (result i64) (i64.lt_u (local.get 0) (i64.const 2))
          (then (local.get 0))
          (else (i64.add (call $fib (i64.sub (local.get 0) (i64.const 1)))
                         (call $fib (i64.sub (local.get 0) (i64.const 2))))))))"#).unwrap();
    let mut i = Instance::new(Module::new(&wasm).unwrap(), &Linker::new()).unwrap();
    let t = std::time::Instant::now();
    let r = i.call("fib", &[Val::I64(32)]).unwrap();
    println!("{:?} in {:?}", r, t.elapsed());
}
