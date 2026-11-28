#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// - `spec`: CSS Syntax Level 3 preprocessing and tokenization as spec
//   functions (the trusted specification).
// - `lex`: `preprocess` and `tokenize`, proven equal to the specification.
// - `api`: plain Rust convenience on top: tokenizing a `&str`, and reading
//   a token's value and number as Rust types. Not verified.
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

mod api;

pub use api::{Tokens, tokenize_str};
pub use lex::{Token, preprocess, tokenize};
pub use spec::Kind;
