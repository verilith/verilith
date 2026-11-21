//! Adler-32 (RFC 1950) and CRC-32 (RFC 1952), proven to compute
//! `spec::adler32` and `spec::crc32`. They live in `verilith_core::checksum`; this
//! module re-exports them under their old paths.
pub use verilith_core::checksum::*;
