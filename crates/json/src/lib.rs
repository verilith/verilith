#![doc = include_str!("../README.md")]
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, unused_braces))]
// vjson: a fast JSON parser formally verified with Verus.
//
// * [`parse`] / [`Document`] / [`Value`]: the Rust API (zero-copy views).
// * [`Writer`]: writing JSON; `from_slice`/`to_vec` with the `serde`
//   feature.
// * `utf8`   - verified UTF-8 validation.
// * `write`  - verified string escaping for the writer.
// * `spec`   - the RFC 8259 grammar as Verus spec functions.
// * `parser` - the one-pass parser, proven equal to the spec.
// * `index`  - stage 1 of the two-pass parser: the structural index.
// * `stage2` - stage 2: parsing through the index.
// * `lanes`  - single-instruction SIMD specs (the trusted base).
// * `simd`   - verified byte classification built from them.
// * `lemmas` - proofs about the spec.
// * `number` - number conversion (not verified).
// * `ffi`    - the cJSON-compatible C ABI (not verified), behind the
//   `cjson` feature.
// * `native` - the native C API (not verified), behind the `capi`
//   feature.

#[doc(hidden)]
pub mod error;
#[doc(hidden)]
pub mod float;
#[doc(hidden)]
pub mod index;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod minify;
#[doc(hidden)]
pub mod number;
pub mod ondemand;
mod pow5;
#[doc(hidden)]
pub mod parser;
#[doc(hidden)]
pub mod neon;
#[doc(hidden)]
pub mod simd;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod stage2;
#[doc(hidden)]
pub mod utf8;
#[doc(hidden)]
pub mod write;
mod value;
// The writer depends on crates outside Verus's view; nothing in it is
// verified, and the verified modules do not use it.
#[cfg(not(verus_keep_ghost))]
mod writer;

#[cfg(feature = "cjson")]
#[doc(hidden)]
pub mod ffi;

// Not compiled when verifying: it is unverified glue over `value.rs`.
#[cfg(all(feature = "capi", not(verus_keep_ghost)))]
#[doc(hidden)]
pub mod native;

#[cfg(all(feature = "serde", not(verus_keep_ghost)))]
mod serde_support;
#[cfg(all(feature = "serde", not(verus_keep_ghost)))]
pub use serde_support::{from_slice, from_str, to_string, to_vec, to_vec_pretty, Error as SerdeError};

pub use value::{parse, parse_prefix, Document, Elements, Error, ErrorKind, Key, Members, Parser, Type, Value};
#[cfg(not(verus_keep_ghost))]
pub use writer::{WriteError, Writer};
