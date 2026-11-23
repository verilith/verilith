//! Memory limits that depend on the host's pointer width: a 32-bit host
//! (wasm32 included) has room for at most `interp::MAX_PAGES` pages, and
//! the instantiation arithmetic must not wrap there.
use verilith_wasm::api::{Error, Instance, Linker, Module, Val};

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
