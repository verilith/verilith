//! RustCrypto's `digest` traits, for using these hashers and MACs where
//! RustCrypto's `sha2` and `hmac` are expected (an unverified adapter: each
//! method calls the verified one of the same name and copies the result).
//!
//! - With the `digest` feature, `digest` 0.11 (RustCrypto `sha2` 0.11,
//!   `hmac` 0.13).
//! - With `digest010`, `digest` 0.10 (RustCrypto `sha2` 0.10, `hmac` 0.12).
//!
//! The hashers implement `Default`, `Update`, `FixedOutput`,
//! `FixedOutputReset`, `Reset`, `HashMarker`, `OutputSizeUser` and
//! `BlockSizeUser`, so they are `Digest`, and `DynDigest` when `digest`'s
//! `alloc` feature is on. With the `oid` feature, `AssociatedOid` too, for
//! RSA and ECDSA signatures. The block size makes RustCrypto's own
//! `hmac::SimpleHmac` work over them.
//!
//! The MACs implement `KeyInit` (any key length through
//! `new_from_slice`), `Update`, `FixedOutput`, `FixedOutputReset`, `Reset`
//! and `MacMarker`, so they are `Mac`.

/// The traits of one `digest` release, at the paths `$d` (the crate) and
/// `$c` (its `crypto-common`).
#[allow(unused_macros)]
macro_rules! digest_traits {
    ($d:ident, $c:path) => {
        use crate::hash::{Sha224, Sha256};
        use crate::hash512::{Sha384, Sha512, Sha512_224, Sha512_256};
        use crate::hmac::{HmacSha224, HmacSha256, HmacSha384, HmacSha512, HmacSha512_224, HmacSha512_256};
        use $c as common;
        use $d::consts::{U128, U28, U32, U48, U64};
        use $d::{FixedOutput, FixedOutputReset, HashMarker, Output, OutputSizeUser, Reset, Update};

        macro_rules! hash {
            ($t:ident, $out:ty, $block:ty, $oid:literal) => {
                impl HashMarker for $t {}

                impl OutputSizeUser for $t {
                    type OutputSize = $out;
                }

                impl common::BlockSizeUser for $t {
                    type BlockSize = $block;
                }

                impl Update for $t {
                    #[inline]
                    fn update(&mut self, data: &[u8]) {
                        $t::update(self, data)
                    }
                }

                impl FixedOutput for $t {
                    #[inline]
                    fn finalize_into(self, out: &mut Output<Self>) {
                        out.copy_from_slice(&$t::finalize(&self))
                    }
                }

                impl Reset for $t {
                    #[inline]
                    fn reset(&mut self) {
                        *self = $t::new()
                    }
                }

                impl FixedOutputReset for $t {
                    #[inline]
                    fn finalize_into_reset(&mut self, out: &mut Output<Self>) {
                        out.copy_from_slice(&$t::finalize(self));
                        *self = $t::new()
                    }
                }

                #[cfg(feature = "oid")]
                impl $d::const_oid::AssociatedOid for $t {
                    const OID: $d::const_oid::ObjectIdentifier = $d::const_oid::ObjectIdentifier::new_unwrap($oid);
                }
            };
        }

        hash!(Sha224, U28, U64, "2.16.840.1.101.3.4.2.4");
        hash!(Sha256, U32, U64, "2.16.840.1.101.3.4.2.1");
        hash!(Sha384, U48, U128, "2.16.840.1.101.3.4.2.2");
        hash!(Sha512, U64, U128, "2.16.840.1.101.3.4.2.3");
        hash!(Sha512_224, U28, U128, "2.16.840.1.101.3.4.2.5");
        hash!(Sha512_256, U32, U128, "2.16.840.1.101.3.4.2.6");

        macro_rules! mac {
            ($t:ident, $out:ty, $block:ty) => {
                impl $d::MacMarker for $t {}

                impl OutputSizeUser for $t {
                    type OutputSize = $out;
                }

                impl common::KeySizeUser for $t {
                    type KeySize = $block;
                }

                impl $d::KeyInit for $t {
                    #[inline]
                    fn new(key: &$d::Key<Self>) -> Self {
                        $t::new(&key[..])
                    }

                    /// Any length of key, as HMAC allows.
                    #[inline]
                    fn new_from_slice(key: &[u8]) -> Result<Self, $d::InvalidLength> {
                        Ok($t::new(key))
                    }
                }

                impl Update for $t {
                    #[inline]
                    fn update(&mut self, data: &[u8]) {
                        $t::update(self, data)
                    }
                }

                impl FixedOutput for $t {
                    #[inline]
                    fn finalize_into(self, out: &mut Output<Self>) {
                        out.copy_from_slice(&$t::finalize(&self))
                    }
                }

                impl Reset for $t {
                    #[inline]
                    fn reset(&mut self) {
                        $t::reset(self)
                    }
                }

                impl FixedOutputReset for $t {
                    #[inline]
                    fn finalize_into_reset(&mut self, out: &mut Output<Self>) {
                        out.copy_from_slice(&$t::finalize(self));
                        $t::reset(self)
                    }
                }
            };
        }

        mac!(HmacSha224, U28, U64);
        mac!(HmacSha256, U32, U64);
        mac!(HmacSha384, U48, U128);
        mac!(HmacSha512, U64, U128);
        mac!(HmacSha512_224, U28, U128);
        mac!(HmacSha512_256, U32, U128);
    };
}

#[cfg(feature = "digest")]
mod v011 {
    digest_traits!(digest011, digest011::common);
}

#[cfg(feature = "digest010")]
mod v010 {
    digest_traits!(digest010, digest010::crypto_common);
}
