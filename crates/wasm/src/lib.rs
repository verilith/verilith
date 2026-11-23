//! A formally verified WebAssembly validator and sandboxed interpreter.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_braces, non_shorthand_field_patterns))]
#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-wasm is proven for 64-bit targets only");

// Only where it holds, so that a 32-bit build stops at the error above
// rather than at the size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
    global size_of usize == 8;
}

pub mod ast;
pub mod num;
pub mod sint;
pub mod fops;
pub mod sem;
pub mod cert;
pub mod preserve;
pub mod check;
pub mod prims;
pub mod exec_num;
pub mod interp;
pub mod run;
pub mod compile;
pub mod reg_ops;
pub mod mach;
pub mod rcheck;
pub mod reg;
pub mod rrun;
pub mod rsteps;
pub mod instance;
pub mod decode;
pub mod validate;
pub mod api;
pub mod capi;
