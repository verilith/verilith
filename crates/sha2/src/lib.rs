//! SHA-224 and SHA-256 (FIPS 180-4), proven with Verus.
//!
//! - [`spec`]: the standard as spec functions (trusted).
//! - [`compress`]: the compression function, proven to compute
//!   `spec::compress`.
//! - [`hash`]: [`Sha256`] and [`Sha224`], whose `finalize` is proven to
//!   return `spec::sha256` (or `spec::sha224`) of everything passed to
//!   `update`; and the one-shot [`sha256`] and [`sha224`].
//! - [`cpu`]: SHA-NI and ARMv8 SHA2 kernels, chosen at run time (trusted,
//!   tested against [`compress`]).
//! - [`capi`]: OpenSSL's `SHA256_*` and `SHA224_*` C API (unverified
//!   adapter).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]

pub mod spec;
pub mod compress;
pub mod cpu;
pub mod hash;
#[allow(non_camel_case_types)]
pub mod capi;

pub use hash::{sha224, sha256, Sha224, Sha256};
