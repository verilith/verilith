#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified HTTP/1.1 (RFC 9112) parser.
//
// - [`spec`]: message heads, framing and the smuggling rules as pure
//   functions (the trusted specification).
// - [`parse`]: the verified head parser.
// - [`framing`]: the verified body-framing decision.
// - [`chunked`]: the chunked coding as a state machine, the
//   split-invariance theorem, and the verified in-place decoder.
// - [`lemmas`]: extension stability and the incremental-parsing theorem.
// - [`api`]: the Rust API (thin wrappers).
// - [`capi`]: a picohttpparser-compatible C API (thin wrappers).
// - `native` (feature `capi`): the native C API, `include/vhttp.h` (thin
//   wrappers over [`api`]).
// - [`httparse`]: the API of the httparse crate, as used by hyper.
// - [`rfc`]: a model of RFC 9112 recipients and of known deviations
//   (trusted), for the uniqueness theorems.
// - [`unique`], [`unique_chunked`]: every recipient in the model reads a
//   message vhttp accepts with the same head end, framing and body.
// - [`llcore`], [`llproof`]: every decision the llhttp drop-in makes
//   about a head, verified, and the theorems about those decisions.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod api;
#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod chunked;
mod diagnose;
#[doc(hidden)]
pub mod framing;
pub mod httparse;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod lemmas;
// Unverified glue over `api`; not compiled when verifying.
#[cfg(all(feature = "capi", not(verus_keep_ghost)))]
#[doc(hidden)]
pub mod native;
#[doc(hidden)]
pub mod llcore;
#[doc(hidden)]
pub mod llproof;
#[cfg(feature = "llhttp-abi")]
#[doc(hidden)]
pub mod llhttp;
#[doc(hidden)]
pub mod parse;
#[doc(hidden)]
pub mod rfc;
#[doc(hidden)]
pub mod scan;
#[doc(hidden)]
pub mod scan_neon;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod stream;
#[doc(hidden)]
pub mod stream_proof;
#[doc(hidden)]
pub mod unique;
#[doc(hidden)]
pub mod unique_chunked;

pub use api::{
    parse_request, parse_request_with, parse_response, Chunked, ChunkedDecoder, Error, Request,
    Response, Status, DEFAULT_MAX_HEADERS,
};
pub use parse::{Header, Span};
pub use spec::Body;
