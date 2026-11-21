//! Base64 (RFC 4648): `spec` defines it and proves the round trip,
//! `scalar` is the verified codec, and `api` is the public interface.
pub mod api;
pub mod avx2;
pub mod forgiving;
pub mod scalar;
pub mod spec;
pub mod tables;

pub use api::*;

/// Writes `spec::encode(cfg, x)` into `out`.
pub(crate) fn encode_into(cfg: spec::Config, x: &[u8], out: &mut [u8]) {
    scalar::encode_into(cfg, x, out)
}

/// Decodes `s` into `out`; `true` iff `s` is a canonical encoding.
pub(crate) fn decode_into(cfg: spec::Config, s: &[u8], out: &mut [u8]) -> bool {
    scalar::decode_into(cfg, s, out)
}
