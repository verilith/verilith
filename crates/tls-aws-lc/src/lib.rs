//! The cryptography verilith-tls trusts, over aws-lc (through aws-lc-rs):
//! an implementation of `verilith_tls::crypto::{Provider, AeadKey}`.
//!
//! Nothing here is verified. verilith-tls's proofs assume each function
//! meets the contract written on the trait in `crypto.rs`; this crate is
//! where that assumption is kept, small enough to read in one sitting.
//! It supports the cipher suites TLS_AES_128_GCM_SHA256,
//! TLS_AES_256_GCM_SHA384 and TLS_CHACHA20_POLY1305_SHA256, the groups
//! x25519, secp256r1, secp384r1 and X25519MLKEM768, and server keys for
//! ecdsa_secp256r1_sha256, ecdsa_secp384r1_sha384, ed25519 and
//! rsa_pss_rsae_sha256/384/512.
use aws_lc_rs::aead::{self, Aad, LessSafeKey, Nonce, UnboundKey};
use aws_lc_rs::agreement::{self, EphemeralPrivateKey, UnparsedPublicKey};
use aws_lc_rs::kem::{EncapsulationKey, ML_KEM_768};
use aws_lc_rs::rand::{SecureRandom, SystemRandom};
use aws_lc_rs::signature::{self, EcdsaKeyPair, Ed25519KeyPair, KeyPair, RsaKeyPair};
use std::sync::Arc;
use verilith_tls::crypto::{AeadKey, Provider};

pub const TLS_AES_128_GCM_SHA256: u16 = 0x1301;
pub const TLS_AES_256_GCM_SHA384: u16 = 0x1302;
pub const TLS_CHACHA20_POLY1305_SHA256: u16 = 0x1303;

pub const X25519: u16 = 0x001d;
pub const SECP256R1: u16 = 0x0017;
pub const SECP384R1: u16 = 0x0018;
pub const X25519MLKEM768: u16 = 0x11ec;

pub const ECDSA_SECP256R1_SHA256: u16 = 0x0403;
pub const ECDSA_SECP384R1_SHA384: u16 = 0x0503;
pub const ED25519: u16 = 0x0807;
pub const RSA_PSS_RSAE_SHA256: u16 = 0x0804;
pub const RSA_PSS_RSAE_SHA384: u16 = 0x0805;
pub const RSA_PSS_RSAE_SHA512: u16 = 0x0806;

/// The suites, in this crate's order of preference.
pub const SUITES: [u16; 3] = [TLS_AES_128_GCM_SHA256, TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256];

/// The groups, in this crate's order of preference.
pub const GROUPS: [u16; 4] = [X25519MLKEM768, X25519, SECP256R1, SECP384R1];

/// An AEAD key of one of the three suites.
pub struct Key {
    key: LessSafeKey,
}

impl AeadKey for Key {
    fn seal_in_place(&self, nonce: &[u8; 12], aad: &[u8; 5], buf: &mut Vec<u8>, start: usize) {
        let tag = self
            .key
            .seal_in_place_separate_tag(Nonce::assume_unique_for_key(*nonce), Aad::from(aad), &mut buf[start..])
            .expect("seal fails only past the AEAD's length limit, far above a record's");
        buf.extend_from_slice(tag.as_ref());
    }

    fn open_in_place(&self, nonce: &[u8; 12], aad: &[u8; 5], buf: &mut [u8]) -> Option<usize> {
        match self.key.open_in_place(Nonce::assume_unique_for_key(*nonce), Aad::from(aad), buf) {
            Ok(pt) => Some(pt.len()),
            Err(_) => None,
        }
    }
}

/// The server's signing key.
pub enum SigningKey {
    Ecdsa256(EcdsaKeyPair),
    Ecdsa384(EcdsaKeyPair),
    Ed25519(Ed25519KeyPair),
    Rsa(RsaKeyPair),
}

impl SigningKey {
    /// A key from its PKCS#8 DER encoding: ECDSA P-256 or P-384, Ed25519,
    /// or RSA.
    pub fn from_pkcs8(der: &[u8]) -> Option<SigningKey> {
        if let Ok(k) = EcdsaKeyPair::from_pkcs8(&signature::ECDSA_P256_SHA256_ASN1_SIGNING, der) {
            return Some(SigningKey::Ecdsa256(k));
        }
        if let Ok(k) = EcdsaKeyPair::from_pkcs8(&signature::ECDSA_P384_SHA384_ASN1_SIGNING, der) {
            return Some(SigningKey::Ecdsa384(k));
        }
        if let Ok(k) = Ed25519KeyPair::from_pkcs8_maybe_unchecked(der) {
            return Some(SigningKey::Ed25519(k));
        }
        if let Ok(k) = RsaKeyPair::from_pkcs8(der) {
            return Some(SigningKey::Rsa(k));
        }
        None
    }

    /// The signature schemes this key signs with, in order of preference.
    pub fn schemes(&self) -> &'static [u16] {
        match self {
            SigningKey::Ecdsa256(_) => &[ECDSA_SECP256R1_SHA256],
            SigningKey::Ecdsa384(_) => &[ECDSA_SECP384R1_SHA384],
            SigningKey::Ed25519(_) => &[ED25519],
            SigningKey::Rsa(_) => &[RSA_PSS_RSAE_SHA256, RSA_PSS_RSAE_SHA384, RSA_PSS_RSAE_SHA512],
        }
    }

    /// The public key, for tests.
    pub fn public_key(&self) -> Vec<u8> {
        match self {
            SigningKey::Ecdsa256(k) | SigningKey::Ecdsa384(k) => k.public_key().as_ref().to_vec(),
            SigningKey::Ed25519(k) => k.public_key().as_ref().to_vec(),
            SigningKey::Rsa(k) => k.public_key().as_ref().to_vec(),
        }
    }
}

/// aws-lc, with the server's signing key.
pub struct AwsLc {
    rng: SystemRandom,
    key: Option<Arc<SigningKey>>,
}

impl AwsLc {
    pub fn new(key: Option<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: key.map(Arc::new) }
    }

    /// With a key shared by many connections (a server's), parsed once.
    pub fn shared(key: Arc<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: Some(key) }
    }

    pub fn signing_key(&self) -> Option<&SigningKey> {
        self.key.as_deref()
    }
}

fn ecdh(
    alg: &'static agreement::Algorithm,
    rng: &SystemRandom,
    peer: &[u8],
    share: &mut Vec<u8>,
    shared: &mut [u8],
) -> Option<usize> {
    let ours = EphemeralPrivateKey::generate(alg, rng).ok()?;
    let public = ours.compute_public_key().ok()?;
    let n = agreement::agree_ephemeral(ours, UnparsedPublicKey::new(alg, peer), (), |s| {
        if s.len() > shared.len() {
            return Err(());
        }
        shared[..s.len()].copy_from_slice(s);
        Ok(s.len())
    })
    .ok()?;
    // §7.4.2: an all-zero X25519 output is an error.
    if shared[..n].iter().all(|&b| b == 0) {
        return None;
    }
    share.extend_from_slice(public.as_ref());
    Some(n)
}

impl Provider for AwsLc {
    type Key = Key;

    fn aead_key(&self, suite: u16, key: &[u8]) -> Key {
        let alg = match suite {
            TLS_AES_128_GCM_SHA256 => &aead::AES_128_GCM,
            TLS_AES_256_GCM_SHA384 => &aead::AES_256_GCM,
            _ => &aead::CHACHA20_POLY1305,
        };
        let key = UnboundKey::new(alg, key).expect("key length is the suite's");
        Key { key: LessSafeKey::new(key) }
    }

    fn key_exchange(&mut self, group: u16, peer: &[u8], share: &mut Vec<u8>, shared: &mut [u8; 64]) -> Option<usize> {
        match group {
            X25519 => ecdh(&agreement::X25519, &self.rng, peer, share, shared),
            SECP256R1 => ecdh(&agreement::ECDH_P256, &self.rng, peer, share, shared),
            SECP384R1 => ecdh(&agreement::ECDH_P384, &self.rng, peer, share, shared),
            X25519MLKEM768 => {
                // draft-ietf-tls-ecdhe-mlkem: the client's share is the
                // ML-KEM-768 encapsulation key then the X25519 share; ours
                // the ciphertext then our X25519 share; the secret the
                // ML-KEM secret then the X25519 one.
                if peer.len() != 1184 + 32 {
                    return None;
                }
                let ek = EncapsulationKey::new(&ML_KEM_768, &peer[..1184]).ok()?;
                let (ct, ss) = ek.encapsulate().ok()?;
                let mut x = Vec::with_capacity(32);
                let n = ecdh(&agreement::X25519, &self.rng, &peer[1184..], &mut x, &mut shared[32..])?;
                if n != 32 || ss.as_ref().len() != 32 {
                    return None;
                }
                shared[..32].copy_from_slice(ss.as_ref());
                share.extend_from_slice(ct.as_ref());
                share.extend_from_slice(&x);
                Some(64)
            }
            _ => None,
        }
    }

    fn sign(&mut self, scheme: u16, msg: &[u8], out: &mut Vec<u8>) -> bool {
        let sig = match (self.key.as_deref(), scheme) {
            (Some(SigningKey::Ecdsa256(k)), ECDSA_SECP256R1_SHA256) | (Some(SigningKey::Ecdsa384(k)), ECDSA_SECP384R1_SHA384) => {
                match k.sign(&self.rng, msg) {
                    Ok(s) => s.as_ref().to_vec(),
                    Err(_) => return false,
                }
            }
            (Some(SigningKey::Ed25519(k)), ED25519) => k.sign(msg).as_ref().to_vec(),
            (Some(SigningKey::Rsa(k)), s @ (RSA_PSS_RSAE_SHA256 | RSA_PSS_RSAE_SHA384 | RSA_PSS_RSAE_SHA512)) => {
                let pad: &'static dyn signature::RsaEncoding = match s {
                    RSA_PSS_RSAE_SHA256 => &signature::RSA_PSS_SHA256,
                    RSA_PSS_RSAE_SHA384 => &signature::RSA_PSS_SHA384,
                    _ => &signature::RSA_PSS_SHA512,
                };
                let mut sig = vec![0u8; k.public_modulus_len()];
                if k.sign(pad, &self.rng, msg, &mut sig).is_err() {
                    return false;
                }
                sig
            }
            _ => return false,
        };
        out.extend_from_slice(&sig);
        true
    }

    fn random(&mut self, out: &mut [u8; 32]) {
        self.rng.fill(out).expect("the system's random number generator works");
    }
}
