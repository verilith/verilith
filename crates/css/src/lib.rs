#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// - `spec`: CSS Syntax Level 3 preprocessing and tokenization as spec
//   functions (the trusted specification).
// - `lex`: `preprocess` and `tokenize`, proven equal to the specification.
// - `parse_spec`: CSS Syntax Level 3 parsing (§5.4, §5.5) as spec functions
//   over the tokens (trusted).
// - `parse`: `parse_stylesheet`, `parse_block_contents` and
//   `parse_component_values`, proven equal to it.
// - `api`: plain Rust convenience on top: tokenizing and parsing a `&str`,
//   and reading a token's value and number as Rust types. Not verified.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[doc(hidden)]
pub mod spec;

#[cfg(verus_only)]
vstd::prelude::verus! {
// The proofs are checked once per pointer width.
#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

#[cfg(target_pointer_width = "32")]
global size_of usize == 4;
} // verus!

#[doc(hidden)]
pub mod lex;
#[doc(hidden)]
pub mod parse_spec;
#[doc(hidden)]
pub mod parse;

mod api;

pub use api::{
    Parsed, TooDeep, Tokens, parse_block_contents_str, parse_component_values_str, parse_stylesheet_str, tokenize_str,
};
pub use lex::{Token, preprocess, tokenize};
pub use parse::{ComponentValue, Declaration, Item, parse_block_contents, parse_component_values, parse_stylesheet};
pub use parse_spec::MAX_DEPTH;
pub use spec::Kind;
