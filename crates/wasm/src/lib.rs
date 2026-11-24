#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified WebAssembly validator and sandboxed interpreter.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_braces, non_shorthand_field_patterns))]
#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-wasm is proven for 64-bit targets only");

// Only where it holds, so that a 32-bit build stops at the error above
// rather than at the size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
    global size_of usize == 8;
}

#[doc(hidden)]
pub mod ast;
#[doc(hidden)]
pub mod num;
#[doc(hidden)]
pub mod sint;
#[doc(hidden)]
pub mod fops;
#[doc(hidden)]
pub mod sem;
#[doc(hidden)]
pub mod cert;
#[doc(hidden)]
pub mod preserve;
#[doc(hidden)]
pub mod check;
#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod exec_num;
#[doc(hidden)]
pub mod interp;
#[doc(hidden)]
pub mod run;
#[doc(hidden)]
pub mod compile;
#[doc(hidden)]
pub mod reg_ops;
#[doc(hidden)]
pub mod mach;
#[doc(hidden)]
pub mod rcheck;
#[doc(hidden)]
pub mod reg;
#[doc(hidden)]
pub mod rrun;
#[doc(hidden)]
pub mod rsteps;
#[doc(hidden)]
pub mod instance;
#[doc(hidden)]
pub mod decode;
#[doc(hidden)]
pub mod validate;
pub mod api;
#[doc(hidden)]
pub mod capi;

pub use api::{Error, ExternType, Instance, Linker, Module, Val};
pub use ast::ValType;
