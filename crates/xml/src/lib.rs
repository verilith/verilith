#![warn(missing_docs)]
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
// * `pe_spec`, `pe` - the DTD read whole: parameter entities, conditional
//   sections, the external subset (`parse_with`), verified.
// * `stream_spec`, `stream`, `push`, `reader` - the push parser, verified;
//   `items_spec` - what it emits, proven to be the whole parse's tape.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables))]
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
pub mod items_spec;
#[doc(hidden)]
pub mod ent;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod lenient;
/// The recovering parser (libxml2's parser.c), run only on documents the
/// verified parser rejected.
#[doc(hidden)]
pub mod recover;
#[doc(hidden)]
pub mod lex;
#[doc(hidden)]
pub mod scan;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod pe_spec;
pub mod pe;
#[doc(hidden)]
pub mod stable;
#[doc(hidden)]
pub mod stable_pro;
#[doc(hidden)]
pub mod stream_spec;
pub mod stream;
pub mod push;
pub mod reader;
pub mod tape;
#[doc(hidden)]
pub mod uniq;

// Not compiled when verifying: ordinary Rust over the verified modules.
#[cfg(not(verus_keep_ghost))]
mod api;
#[cfg(not(verus_keep_ghost))]
pub use api::{parse, parse_with, Attribute, Attrs, Child, Children, Document, Element, Error, ErrorKind};

/// Whether `s` is a well-formed XML document, with its tape in `tape`: the
/// verified check alone, with no tables built for reading.
pub fn check(s: &[u8], tape: &mut tape::Tape) -> bool {
    matches!(
        pe::ex_parse_x(s, tape, false, &mut pe::Loader::none(), pe::FLAT_FUEL),
        Some((_, pe::XDocRes::Ok(_)))
    )
}

/// `check`, reading the external subset and external entities with
/// `loader` (as `parse_with` does). The tape is the document's.
#[cfg(not(verus_keep_ghost))]
pub fn check_with(s: &[u8], tape: &mut tape::Tape, loader: &mut pe::Loader) -> bool {
    match parse_with(s, loader) {
        Ok(d) => {
            *tape = d.into_tape();
            true
        }
        Err(_) => false,
    }
}
