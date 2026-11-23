#![doc = include_str!("../README.md")]
// verilith-xml: an XML 1.0 parser formally verified with Verus.
//
// * [`parse`], [`Document`], [`Element`], [`Child`]: the Rust API,
//   borrowed views of the verified tape.
// * `spec`    - XML 1.0 (Fifth Edition) well-formedness as Verus spec
//   functions, from the input bytes to the tape.
// * `chars`   - `Char` and `Name` characters, verified.
// * `lex`, `dtd`, `content`, `doc` - the parser, proven equal to the
//   spec on every input.
// * `ent`     - internal entities: replacement text and the fixed point of
//   which may be referred to where.
// * `enc`     - choosing the encoding, and verified UTF-16 and ISO-8859-1
//   decoders.
// * `decode`  - verified line-end and attribute-value normalization.
// * `scan`, `lanes` - the SSE2 scanners, verified over verilith-simd.
// * `tape`    - the tokens the parser writes.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
#[doc(hidden)]
pub mod chars;
#[doc(hidden)]
pub mod content;
#[doc(hidden)]
pub mod decode;
#[doc(hidden)]
pub mod doc;
#[doc(hidden)]
pub mod dtd;
#[doc(hidden)]
pub mod enc;
#[doc(hidden)]
pub mod fix;
#[doc(hidden)]
pub mod index;
#[doc(hidden)]
pub mod ent;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod lenient;
#[doc(hidden)]
pub mod lex;
#[doc(hidden)]
pub mod scan;
#[doc(hidden)]
pub mod spec;
pub mod tape;
#[doc(hidden)]
pub mod uniq;

// Not compiled when verifying: ordinary Rust over the verified modules.
#[cfg(not(verus_keep_ghost))]
mod api;
#[cfg(not(verus_keep_ghost))]
pub mod recover;
#[cfg(not(verus_keep_ghost))]
pub use api::{parse, Attribute, Attrs, Child, Children, Document, Element, Error, ErrorKind};

/// Whether `s` is a well-formed XML document, with its tape in `tape`: the
/// verified check alone, with no tables built for reading.
pub fn check(s: &[u8], tape: &mut tape::Tape) -> bool {
    enc::ex_parse(s, tape).is_some()
}
