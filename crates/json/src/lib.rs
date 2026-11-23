//! vjson: a fast JSON parser formally verified with Verus.
//!
//! * [`parse`] / [`Document`] / [`Value`]: the Rust API (zero-copy views).
//! * [`Writer`]: writing JSON; `from_slice`/`to_vec` with the `serde`
//!   feature.
//! * `utf8`   - verified UTF-8 validation.
//! * `write`  - verified string escaping for the writer.
//! * `spec`   - the RFC 8259 grammar as Verus spec functions.
//! * `parser` - the one-pass parser, proven equal to the spec.
//! * `index`  - stage 1 of the two-pass parser: the structural index.
//! * `stage2` - stage 2: parsing through the index.
//! * `lanes`  - single-instruction SIMD specs (the trusted base).
//! * `simd`   - verified byte classification built from them.
//! * `lemmas` - proofs about the spec.
//! * `number` - number conversion (not verified).
//! * `ffi`    - the cJSON-compatible C ABI (not verified), behind the
//!   `cjson` feature.
//! * `native` - the native C API (not verified), behind the `capi`
//!   feature.

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-json is proven for 64-bit targets only");

pub mod error;
pub mod float;
pub mod index;
pub mod lanes;
pub mod lemmas;
pub mod minify;
pub mod number;
pub mod ondemand;
mod pow5;
pub mod parser;
pub mod neon;
pub mod simd;
pub mod spec;
pub mod stage2;
pub mod utf8;
pub mod write;
mod value;
// The writer depends on crates outside Verus's view; nothing in it is
// verified, and the verified modules do not use it.
#[cfg(not(verus_keep_ghost))]
mod writer;

#[cfg(feature = "cjson")]
pub mod ffi;

// Not compiled when verifying: it is unverified glue over `value.rs`.
#[cfg(all(feature = "capi", not(verus_keep_ghost)))]
pub mod native;

#[cfg(all(feature = "serde", not(verus_keep_ghost)))]
mod serde_support;
#[cfg(all(feature = "serde", not(verus_keep_ghost)))]
pub use serde_support::{from_slice, from_str, to_string, to_vec, to_vec_pretty, Error as SerdeError};

pub use value::{parse, parse_prefix, Document, Elements, Error, ErrorKind, Key, Members, Parser, Type, Value};
#[cfg(not(verus_keep_ghost))]
pub use writer::{WriteError, Writer};
