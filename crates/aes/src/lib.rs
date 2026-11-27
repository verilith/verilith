//! AES-128, AES-256 and AES-GCM, proven with Verus.
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
pub mod arch;
#[doc(hidden)]
pub mod kernels;
#[doc(hidden)]
pub mod gcm;
#[cfg(target_arch = "x86_64")]
#[doc(hidden)]
pub mod x86;
#[cfg(target_arch = "x86_64")]
#[doc(hidden)]
pub mod ni;
#[cfg(target_arch = "x86_64")]
#[doc(hidden)]
pub mod vaes;
#[cfg(target_arch = "x86_64")]
mod aead;
#[cfg(target_arch = "x86_64")]
pub use aead::AesGcm;
