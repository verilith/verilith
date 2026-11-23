//! Formally verified zip and tar readers.
//!
//! - [`spec`]: what a zip or tar archive is, and what a member's data is
//!   (the trusted specification, written from the format documents).
//! - [`policy`]: what it means to extract safely, including a model of how
//!   the operating system resolves paths (the trusted specification of the
//!   safety theorems).
//! - [`zip`], [`tar`], [`reader`]: the parsers, proven to compute `spec`.
//! - [`read`]: member data, proven to be exactly what `spec` says.
//! - [`plan`]: the extraction planner and the containment theorem.
//! - [`order`]: an order on paths that the planner's proofs use.
//! - [`api`], [`extract`], [`capi`]: the Rust API, the extractor and
//!   libarchive's read API. Plain Rust over the proven parts.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("verilith-archive is proven for 64-bit targets only");

#[cfg(verus_only)]
vstd::prelude::verus! {

global size_of usize == 8;

} // verus!

pub mod spec;
pub mod policy;
pub mod order;
pub mod zip;
pub mod tar;
pub mod reader;
pub mod read;
pub mod plan;
pub mod api;
#[cfg(unix)]
pub mod extract;
pub mod capi;

pub use api::{Archive, Filter, OpenError};
pub use plan::{Item, Rejected, Why};
pub use read::Error;
pub use reader::Format;
pub use spec::Kind;
pub use zip::Entry;
