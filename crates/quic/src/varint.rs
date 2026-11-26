//! Variable-length integers (§16): the verified reader and writer, and the
//! round trip. They are verilith-core's, shared with HTTP/3.
pub use verilith_core::varint::{lo8, put, read, size, write};
#[cfg(verus_only)]
pub use verilith_core::varint::{lemma_varint_bound, lemma_varint_frame, lemma_varint_roundtrip};
