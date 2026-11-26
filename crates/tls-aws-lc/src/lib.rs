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
use std::sync::{Arc, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};
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

/// Seconds since the Unix epoch.
fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// One ticket key: a name (the first 4 bytes of every ticket it seals)
/// and a ChaCha20-Poly1305 key.
struct TicketKey {
    name: [u8; 4],
    key: LessSafeKey,
}

impl TicketKey {
    fn generate(rng: &SystemRandom) -> TicketKey {
        let mut k = [0u8; 32];
        let mut name = [0u8; 4];
        rng.fill(&mut k).expect("the system's random number generator works");
        rng.fill(&mut name).expect("the system's random number generator works");
        let key = UnboundKey::new(&aead::CHACHA20_POLY1305, &k).expect("a 32-byte key");
        TicketKey { name, key: LessSafeKey::new(key) }
    }
}

struct Keys {
    current: TicketKey,
    previous: Option<TicketKey>,
    /// When `current` was made.
    since: u64,
}

/// Session ticket keys, made at random and shared by every connection of
/// a server, across its threads (`Arc<TicketKeys>`). A ticket is
/// `name(4) | nonce(12) | ChaCha20-Poly1305(state) | tag(16)`, the name as
/// associated data. The key changes every `period` seconds, and the one
/// before it still opens tickets, so a ticket opens for at least `period`
/// seconds after it was issued: give the server's `Config::set_tickets`
/// the same lifetime.
pub struct TicketKeys {
    keys: RwLock<Keys>,
    period: u64,
    rng: SystemRandom,
}

/// Bytes a sealed ticket adds to its state.
pub const TICKET_OVERHEAD: usize = 4 + 12 + 16;

impl TicketKeys {
    /// Keys that change every `period` seconds (6 hours is rustls's).
    pub fn new(period: u64) -> TicketKeys {
        let rng = SystemRandom::new();
        let current = TicketKey::generate(&rng);
        TicketKeys { keys: RwLock::new(Keys { current, previous: None, since: unix_now() }), period: period.max(1), rng }
    }

    pub fn period(&self) -> u64 {
        self.period
    }

    fn rotate_if_due(&self, now: u64) {
        let due = { self.keys.read().map(|k| now.saturating_sub(k.since) >= self.period).unwrap_or(false) };
        if !due {
            return;
        }
        if let Ok(mut k) = self.keys.write() {
            // Another thread may have rotated first.
            if now.saturating_sub(k.since) >= self.period {
                let fresh = TicketKey::generate(&self.rng);
                let old = std::mem::replace(&mut k.current, fresh);
                k.previous = Some(old);
                k.since = now;
            }
        }
    }

    /// Seals `state`, appending the ticket to `out`.
    pub fn seal(&self, state: &[u8], out: &mut Vec<u8>) -> bool {
        self.rotate_if_due(unix_now());
        let Ok(keys) = self.keys.read() else { return false };
        let k = &keys.current;
        let mut nonce = [0u8; 12];
        if self.rng.fill(&mut nonce).is_err() {
            return false;
        }
        let start = out.len();
        out.reserve(state.len() + TICKET_OVERHEAD);
        out.extend_from_slice(&k.name);
        out.extend_from_slice(&nonce);
        out.extend_from_slice(state);
        let at = start + 16;
        match k.key.seal_in_place_separate_tag(Nonce::assume_unique_for_key(nonce), Aad::from(k.name), &mut out[at..]) {
            Ok(tag) => {
                out.extend_from_slice(tag.as_ref());
                true
            }
            Err(_) => {
                out.truncate(start);
                false
            }
        }
    }

    /// Opens a ticket these keys sealed into `out`.
    pub fn open(&self, ticket: &[u8], out: &mut Vec<u8>) -> bool {
        if ticket.len() < TICKET_OVERHEAD {
            return false;
        }
        let Ok(keys) = self.keys.read() else { return false };
        let name = &ticket[..4];
        let k = if keys.current.name == name {
            &keys.current
        } else {
            match &keys.previous {
                Some(p) if p.name == name => p,
                _ => return false,
            }
        };
        let mut nonce = [0u8; 12];
        nonce.copy_from_slice(&ticket[4..16]);
        let start = out.len();
        out.extend_from_slice(&ticket[16..]);
        let mut name4 = [0u8; 4];
        name4.copy_from_slice(name);
        match k.key.open_in_place(Nonce::assume_unique_for_key(nonce), Aad::from(name4), &mut out[start..]) {
            Ok(pt) => {
                let n = pt.len();
                out.truncate(start + n);
                true
            }
            Err(_) => {
                out.truncate(start);
                false
            }
        }
    }
}

/// aws-lc, with the server's signing key and session ticket keys.
pub struct AwsLc {
    rng: SystemRandom,
    key: Option<Arc<SigningKey>>,
    tickets: Option<Arc<TicketKeys>>,
}

impl AwsLc {
    pub fn new(key: Option<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: key.map(Arc::new), tickets: None }
    }

    /// With a key shared by many connections (a server's), parsed once.
    pub fn shared(key: Arc<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: Some(key), tickets: None }
    }

    /// And session tickets sealed with `keys`, which every connection that
    /// should resume each other's sessions shares.
    pub fn with_tickets(mut self, keys: Arc<TicketKeys>) -> AwsLc {
        self.tickets = Some(keys);
        self
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

    fn tickets(&self) -> bool {
        self.tickets.is_some()
    }

    fn seal_ticket(&mut self, state: &[u8], out: &mut Vec<u8>) -> bool {
        match &self.tickets {
            Some(t) => t.seal(state, out),
            None => false,
        }
    }

    fn open_ticket(&self, ticket: &[u8], out: &mut Vec<u8>) -> bool {
        match &self.tickets {
            Some(t) => t.open(ticket, out),
            None => false,
        }
    }

    fn now(&mut self) -> u64 {
        unix_now()
    }
}
