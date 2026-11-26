#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// Sans-I/O HTTP/3 (RFC 9114) framing, formally verified with Verus.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod varint;
#[doc(hidden)]
pub mod frame;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod reader;
pub use reader::{Event, Reader, Src};
pub use spec::Settings;
