#![doc = include_str!("../README.md")]
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod gf;
#[doc(hidden)]
pub mod isa;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod isa_ref;
#[doc(hidden)]
pub mod arch;
#[doc(hidden)]
pub mod kernels;
#[doc(hidden)]
pub mod gcm;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[doc(hidden)]
pub mod x86;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[doc(hidden)]
pub mod ni;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[doc(hidden)]
pub mod vaes;
#[cfg(any(target_endian = "little", verus_only))]
#[doc(hidden)]
pub mod neon;
#[cfg(any(target_endian = "little", verus_only))]
#[doc(hidden)]
pub mod arm;
mod aead;
pub use aead::{Aes, AesGcm};
