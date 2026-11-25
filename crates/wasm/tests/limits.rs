//! Limits: memory limits that depend on the host's pointer width (a
//! 32-bit host, wasm32 included, has room for at most `interp::MAX_PAGES`
//! pages, and the instantiation arithmetic must not wrap there), fuel, and
//! the embedder's memory cap.
use verilith_wasm::api::{Error, Instance, Linker, Module, Val};
use verilith_wasm::ast::Trap;

fn inst(wat: &str) -> Result<Instance, Error> {
    let m = Module::new(&wat::parse_str(wat).unwrap())?;
    Instance::new(m, &Linker::new())
}

/// A data segment whose end passes 2^32 is out of bounds, not a wrapped
/// index.
#[test]
fn data_segment_past_4gib() {
    let r = inst(r#"(module (memory 1) (data (i32.const -1) "ab"))"#);
    assert!(matches!(r, Err(Error::Instantiate(_))));
}

#[test]
fn small_memory_grows() {
    let mut i = inst(
        r#"(module (memory 1 4)
        (func (export "grow") (param i32) (result i32) (memory.grow (local.get 0))))"#,
    )
    .unwrap();
    assert_eq!(i.call("grow", &[Val::I32(2)]).unwrap(), vec![Val::I32(1)]);
    assert_eq!(i.call("grow", &[Val::I32(2)]).unwrap(), vec![Val::I32(-1)]);
}

/// Past `MAX_PAGES` a 32-bit host refuses the memory, or the growth.
#[cfg(target_pointer_width = "32")]
#[test]
fn over_max_pages_on_32_bit() {
    use verilith_wasm::interp::MAX_PAGES;
    let r = inst(&format!("(module (memory {}))", MAX_PAGES + 1));
    assert!(matches!(r, Err(Error::Instantiate(_))));
    let mut i = inst(
        r#"(module (memory 0)
        (func (export "grow") (param i32) (result i32) (memory.grow (local.get 0))))"#,
    )
    .unwrap();
    let n = (MAX_PAGES + 1) as i32;
    assert_eq!(i.call("grow", &[Val::I32(n)]).unwrap(), vec![Val::I32(-1)]);
}

// Fuel and the embedder's memory cap.
fn module(wat: &str) -> Module {
    Module::new(&wat::parse_str(wat).unwrap()).unwrap()
}

const SPIN: &str = r#"(module
  (func (export "spin") (loop br 0))
  (func (export "spin_calls") (call 1))
  (func (export "seven") (result i32) i32.const 7))"#;

#[test]
fn spin_runs_out_of_fuel() {
    let mut linker = Linker::new();
    linker.fuel(1_000_000);
    let mut i = Instance::new(module(SPIN), &linker).unwrap();
    assert_eq!(i.call("spin", &[]), Err(Error::Trap(Trap::Exhausted)));
    assert_eq!(i.fuel(), Some(0));
    // Still out of fuel: nothing runs.
    assert_eq!(i.call("seven", &[]), Err(Error::Trap(Trap::Exhausted)));
    // Refuelled, the instance is usable again.
    i.set_fuel(Some(100));
    assert_eq!(i.call("seven", &[]), Ok(vec![Val::I32(7)]));
    let left = i.fuel().unwrap();
    assert!(left < 100 && left > 90, "{left}");
    // Unmetered.
    i.set_fuel(None);
    assert_eq!(i.call("seven", &[]), Ok(vec![Val::I32(7)]));
    assert_eq!(i.fuel(), None);
}

#[test]
fn recursion_runs_out_of_stack_or_fuel() {
    let mut linker = Linker::new();
    linker.fuel(10_000);
    let mut i = Instance::new(module(SPIN), &linker).unwrap();
    assert_eq!(i.call("spin_calls", &[]), Err(Error::Trap(Trap::Exhausted)));
    assert_eq!(i.fuel(), Some(0));
}

#[test]
fn start_function_is_metered() {
    let wat = r#"(module (func $s (loop br 0)) (start $s))"#;
    let mut linker = Linker::new();
    linker.fuel(1000);
    assert!(matches!(Instance::new(module(wat), &linker), Err(Error::Instantiate(_))));
}

const GROW: &str = r#"(module
  (memory 1)
  (func (export "grow") (param i32) (result i32) local.get 0 memory.grow)
  (func (export "size") (result i32) memory.size))"#;

#[test]
fn memory_cap() {
    let mut linker = Linker::new();
    linker.max_memory(3 * 65536 + 100);
    let mut i = Instance::new(module(GROW), &linker).unwrap();
    assert_eq!(i.call("grow", &[Val::I32(3)]), Ok(vec![Val::I32(-1)]));
    assert_eq!(i.call("grow", &[Val::I32(2)]), Ok(vec![Val::I32(1)]));
    assert_eq!(i.call("grow", &[Val::I32(1)]), Ok(vec![Val::I32(-1)]));
    assert_eq!(i.call("grow", &[Val::I32(0)]), Ok(vec![Val::I32(3)]));
    assert_eq!(i.call("size", &[]), Ok(vec![Val::I32(3)]));
    assert_eq!(i.memory().len(), 3 * 65536);
}

#[test]
fn memory_cap_below_minimum() {
    let mut linker = Linker::new();
    linker.max_memory(65535);
    assert!(matches!(Instance::new(module(GROW), &linker), Err(Error::Instantiate(_))));
}

#[test]
fn memory_cap_above_module_maximum() {
    // The module's own maximum still applies under a larger cap.
    let wat = r#"(module (memory 1 2)
      (func (export "grow") (param i32) (result i32) local.get 0 memory.grow))"#;
    let mut linker = Linker::new();
    linker.max_memory(1 << 30);
    let mut i = Instance::new(module(wat), &linker).unwrap();
    assert_eq!(i.call("grow", &[Val::I32(2)]), Ok(vec![Val::I32(-1)]));
    assert_eq!(i.call("grow", &[Val::I32(1)]), Ok(vec![Val::I32(1)]));
}

#[test]
fn unlimited_by_default() {
    let mut i = Instance::new(module(GROW), &Linker::new()).unwrap();
    assert_eq!(i.fuel(), None);
    assert_eq!(i.call("grow", &[Val::I32(15)]), Ok(vec![Val::I32(1)]));
}
