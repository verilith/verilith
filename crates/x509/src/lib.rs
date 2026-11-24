#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A formally verified (Verus) DER and X.509 certificate parser.
#![cfg_attr(not(verus_only), allow(unused_variables, non_shorthand_field_patterns))]
//
// - [`spec`]: DER and the RFC 5280 certificate profile as pure functions
//   (the trusted specification).
// - [`der`], [`time`], [`x509`], [`ext`], [`cert`]: the parser, proven to
//   compute exactly the spec.
// - [`iter`]: iterators over names, extensions and GeneralNames, proven to
//   yield exactly the spec's lists.
// - [`api`], [`error`]: unverified conveniences (`Iterator` impls, text,
//   timestamps, and [`try_parse`], which says why a certificate was
//   rejected).
// - `native` (feature `capi`): the unverified native C API,
//   `include/vx509.h`.
//
// The crate is `no_std` and never allocates. The `alloc` feature (on by
// default, through `std`) adds [`oid_to_string`].
#![no_std]
#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;
pub mod api;
#[doc(hidden)]
pub mod cert;
#[doc(hidden)]
pub mod der;
#[doc(hidden)]
pub mod error;
#[doc(hidden)]
pub mod ext;
pub mod iter;
#[cfg(feature = "mbedtls")]
#[doc(hidden)]
pub mod mbedtls;
#[cfg(feature = "mbedtls")]
#[doc(hidden)]
pub mod mbedtls_err;
// Unverified glue over the modules above; not compiled when verifying.
#[cfg(all(feature = "capi", not(verus_only)))]
#[doc(hidden)]
pub mod native;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod time;
#[doc(hidden)]
pub mod x509;

#[cfg(feature = "alloc")]
pub use api::oid_to_string;
pub use api::OidDisplay;
pub use cert::{parse, Certificate};
pub use error::{try_parse, Error, ErrorKind};
pub use ext::{AuthorityKeyId, BasicConstraints, Extension, NameConstraints};
pub use time::Time;
pub use x509::{AlgId, Atv, GeneralName, Name, Spki};

// A staticlib needs a panic handler. Without std (the mbedTLS drop-in on
// bare metal), panics call the C library's abort(). The verified parser
// cannot panic; this covers the unverified C ABI glue.
#[cfg(all(any(feature = "mbedtls", feature = "capi"), not(feature = "std"), not(test)))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe extern "C" {
        fn abort() -> !;
    }
    unsafe { abort() }
}
