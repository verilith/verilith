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
#[doc(hidden)]
pub mod ct;
mod dit;
mod aead;
pub use aead::{Aes, AesGcm};

/// What `examples/ctcheck.rs` tells the static constant-time check.
#[doc(hidden)]
pub mod layout {
    /// The offset of `Gcm::nr`, the one field of an expanded key that is
    /// public (the number of rounds).
    pub const NR_OFFSET: usize = core::mem::offset_of!(crate::gcm::Gcm, nr);
}
