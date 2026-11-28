#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// SHA-2 (FIPS 180-4), proven with Verus: SHA-224 and SHA-256, and the
// 64-bit family SHA-384, SHA-512, SHA-512/224 and SHA-512/256.
//
// - [`spec`] and [`spec512`]: the standard as spec functions (trusted).
// - [`compress`] and [`compress512`]: the compression functions, proven
//   to compute `spec::compress` and `spec512::compress`.
// - [`hash`]: [`Sha256`] and [`Sha224`], whose `finalize` is proven to
//   return `spec::sha256` (or `spec::sha224`) of everything passed to
//   `update`; and the one-shot [`sha256`] and [`sha224`].
// - [`hash512`]: [`Sha512`], [`Sha384`], [`Sha512_224`] and [`Sha512_256`],
//   proven the same way against [`spec512`].
// - [`spec_hmac`]: HMAC (FIPS 198-1) as spec functions (trusted).
// - [`hmac`]: HMAC over each hash, proven against [`spec_hmac`].
// - [`cpu`]: SHA-NI, ARMv8 SHA2 and ARMv8.2 SHA512 kernels, chosen at run
//   time (trusted, tested against the verified kernels).
// - [`capi`]: OpenSSL's `SHA224_*`, `SHA256_*`, `SHA384_*` and `SHA512_*`
//   C API (unverified adapter).
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod compress;
#[doc(hidden)]
pub mod spec512;
#[doc(hidden)]
pub mod compress512;
#[doc(hidden)]
pub mod cpu;
/// The SHA instructions' specifications and their verified references,
/// from verilith-simd.
#[doc(hidden)]
pub use verilith_simd::sha as isa;
#[doc(hidden)]
pub use verilith_simd::sha_ref as isa_ref;
#[doc(hidden)]
pub mod sha_lemmas;
#[doc(hidden)]
pub mod armv8;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[doc(hidden)]
pub mod shani;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[doc(hidden)]
pub mod avx2;
mod store;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod hash;
#[doc(hidden)]
pub mod hash512;
#[doc(hidden)]
pub mod spec_hmac;
#[allow(non_camel_case_types)]
#[doc(hidden)]
pub mod hmac;
#[allow(non_camel_case_types)]
#[doc(hidden)]
pub mod capi;

mod digest_impls;
#[cfg(feature = "digest")]
pub use digest011 as digest;
#[cfg(feature = "digest010")]
pub use digest010;

pub use hash::{sha224, sha256, Sha224, Sha256};
pub use hash512::{sha384, sha512, sha512_224, sha512_256, Sha384, Sha512, Sha512_224, Sha512_256};
pub use hmac::{
    hmac_sha224, hmac_sha256, hmac_sha384, hmac_sha512, hmac_sha512_224, hmac_sha512_256, HmacSha224, HmacSha256,
    HmacSha384, HmacSha512, HmacSha512_224, HmacSha512_256,
};
