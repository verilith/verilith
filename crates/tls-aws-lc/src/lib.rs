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
//!
//! Session tickets and HPKE's ChaCha20-Poly1305 are libcrux's (HACL*,
//! verified), and HPKE's HMAC is verilith-sha2's (Verus): CRYPTO.md lists
//! every primitive, its proofs, and why the rest is aws-lc.
use aws_lc_rs::aead::{self, Aad, LessSafeKey, Nonce, UnboundKey};
use aws_lc_rs::agreement::{self, EphemeralPrivateKey, UnparsedPublicKey};
use aws_lc_rs::kem::{EncapsulationKey, ML_KEM_768};
use aws_lc_rs::rand::{SecureRandom, SystemRandom};
use aws_lc_rs::signature::{self, EcdsaKeyPair, Ed25519KeyPair, KeyPair, RsaKeyPair};
use verilith_tls::antireplay;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};
use aws_lc_rs::aead::quic::{self as quic_hp, HeaderProtectionKey};
use verilith_tls::crypto::{AeadKey, HpKey, Provider};
use verilith_x509::{AlgId, Spki, Time};

pub mod hpke;

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

    fn seal_after(&self, nonce: &[u8; 12], buf: &mut Vec<u8>, aad_start: usize, start: usize) {
        let (head, body) = buf.split_at_mut(start);
        let tag = self
            .key
            .seal_in_place_separate_tag(Nonce::assume_unique_for_key(*nonce), Aad::from(&head[aad_start..]), body)
            .expect("seal fails only past the AEAD's length limit, far above a packet's");
        buf.extend_from_slice(tag.as_ref());
    }

    fn open_after(&self, nonce: &[u8; 12], buf: &mut [u8], start: usize) -> Option<usize> {
        let (head, body) = buf.split_at_mut(start);
        match self.key.open_in_place(Nonce::assume_unique_for_key(*nonce), Aad::from(&*head), body) {
            Ok(pt) => Some(pt.len()),
            Err(_) => None,
        }
    }
}

/// A QUIC header protection key of one of the three suites.
pub struct Hp {
    key: HeaderProtectionKey,
}

impl HpKey for Hp {
    fn mask(&self, sample: &[u8]) -> [u8; 5] {
        self.key.new_mask(sample).expect("the sample is 16 bytes")
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
/// and a ChaCha20-Poly1305 key, used with libcrux's ChaCha20-Poly1305
/// (HACL*, verified; CRYPTO.md).
struct TicketKey {
    name: [u8; 4],
    key: [u8; 32],
}

impl TicketKey {
    fn generate(rng: &SystemRandom) -> TicketKey {
        let mut k = [0u8; 32];
        let mut name = [0u8; 4];
        rng.fill(&mut k).expect("the system's random number generator works");
        rng.fill(&mut name).expect("the system's random number generator works");
        TicketKey { name, key: k }
    }
}

struct Keys {
    current: TicketKey,
    previous: Option<TicketKey>,
    /// When `current` was made.
    since: u64,
}

/// How far apart (ms) the client's and the server's view of a ticket's
/// age may be for its 0-RTT data to be taken (RFC 8446 §8.3).
pub const EARLY_WINDOW_MS: u64 = antireplay::WINDOW_MS;

/// The most ClientHellos the anti-replay register holds per generation.
/// When it is full, 0-RTT is refused (the handshake goes on, 1-RTT).
pub const EARLY_REGISTER_MAX: usize = antireplay::MAX;

fn unix_now_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as u64).unwrap_or(0)
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
    /// The single-use register of RFC 8446 §8.1, verified
    /// (verilith-tls's `antireplay`).
    register: Mutex<antireplay::Register>,
}

/// Bytes a sealed ticket adds to its state.
pub const TICKET_OVERHEAD: usize = 4 + 12 + 16;

impl TicketKeys {
    /// Keys that change every `period` seconds (6 hours is rustls's).
    pub fn new(period: u64) -> TicketKeys {
        let rng = SystemRandom::new();
        let current = TicketKey::generate(&rng);
        let register = Mutex::new(antireplay::Register::new(unix_now_ms()));
        TicketKeys { keys: RwLock::new(Keys { current, previous: None, since: unix_now() }), period: period.max(1), rng, register }
    }

    /// Anti-replay for 0-RTT data (RFC 8446 §8): `true` if the client's
    /// view of the ticket's age (`obfuscated_age - age_add`, ms) is within
    /// `EARLY_WINDOW_MS` of the server's (now less `issued`, s), and no
    /// ClientHello with this `binder` has had its 0-RTT data taken here
    /// before (in the `2 * EARLY_WINDOW_MS + 1 s` before; the same
    /// ClientHello, never). The checks and the register are verilith-tls's
    /// `antireplay::Register::claim`, verified; this is only the clock,
    /// the lock, and the key (the binder's first 16 bytes). The register
    /// is this process's: servers that share ticket keys across machines
    /// must not enable 0-RTT without a shared one.
    pub fn claim_early(&self, binder: &[u8], obfuscated_age: u32, issued: u64, age_add: u32) -> bool {
        if binder.len() < 32 {
            return false;
        }
        let key = u128::from_le_bytes(binder[..16].try_into().expect("16 bytes"));
        let now = unix_now_ms();
        let Ok(mut r) = self.register.lock() else { return false };
        r.claim(key, now, obfuscated_age, issued, age_add)
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
        out.resize(start + TICKET_OVERHEAD + state.len(), 0);
        let (ct, tag) = out[start + 16..].split_at_mut(state.len());
        let tag: &mut [u8; 16] = tag.try_into().expect("16 bytes are left for the tag");
        if libcrux_chacha20poly1305::encrypt_detached(&k.key, state, ct, tag, &k.name, &nonce).is_err() {
            out.truncate(start);
            return false;
        }
        true
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
        let ct = &ticket[16..];
        out.resize(start + ct.len() - 16, 0);
        if libcrux_chacha20poly1305::decrypt(&k.key, &mut out[start..], ct, name, &nonce).is_err() {
            out.truncate(start);
            return false;
        }
        true
    }
}

/// aws-lc, with the server's signing key and session ticket keys.
pub struct AwsLc {
    rng: SystemRandom,
    key: Option<Arc<SigningKey>>,
    tickets: Option<Arc<TicketKeys>>,
    ech: Option<Arc<hpke::EchKeys>>,
}

impl AwsLc {
    pub fn new(key: Option<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: key.map(Arc::new), tickets: None, ech: None }
    }

    /// With a key shared by many connections (a server's), parsed once.
    pub fn shared(key: Arc<SigningKey>) -> AwsLc {
        AwsLc { rng: SystemRandom::new(), key: Some(key), tickets: None, ech: None }
    }

    /// And session tickets sealed with `keys`, which every connection that
    /// should resume each other's sessions shares.
    pub fn with_tickets(mut self, keys: Arc<TicketKeys>) -> AwsLc {
        self.tickets = Some(keys);
        self
    }

    /// And Encrypted Client Hello with `keys` (give the server's
    /// `Config::set_ech` their `config_list`).
    pub fn with_ech(mut self, keys: Arc<hpke::EchKeys>) -> AwsLc {
        self.ech = Some(keys);
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

// Algorithm identifiers (RFC 5758, RFC 8017, RFC 8410), OID contents octets.
const OID_EC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const OID_P256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
const OID_P384: &[u8] = &[0x2b, 0x81, 0x04, 0x00, 0x22];
const OID_RSA_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01];
const OID_ED25519: &[u8] = &[0x2b, 0x65, 0x70];
const OID_ECDSA_SHA256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02];
const OID_ECDSA_SHA384: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03];
const OID_RSA_SHA256: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b];
const OID_RSA_SHA384: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c];
const OID_RSA_SHA512: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0d];

/// A public key's type, from its SubjectPublicKeyInfo algorithm.
#[derive(Clone, Copy, PartialEq, Eq)]
enum KeyType {
    P256,
    P384,
    Rsa,
    Ed25519,
}

fn key_type(key: &Spki) -> Option<KeyType> {
    let curve = |oid: &[u8]| match key.alg.params {
        Some(p) => p.tag == [0x06] && p.content == oid,
        None => false,
    };
    if key.alg.oid == OID_EC_KEY {
        if curve(OID_P256) {
            Some(KeyType::P256)
        } else if curve(OID_P384) {
            Some(KeyType::P384)
        } else {
            None
        }
    } else if key.alg.oid == OID_RSA_KEY {
        Some(KeyType::Rsa)
    } else if key.alg.oid == OID_ED25519 && key.alg.params.is_none() {
        Some(KeyType::Ed25519)
    } else {
        None
    }
}

fn verify_with(alg: &'static dyn signature::VerificationAlgorithm, key: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    signature::UnparsedPublicKey::new(alg, key).verify(msg, sig).is_ok()
}

/// The certificate signature algorithm `alg` (RFC 5280 §4.1.1.2) with a key
/// of type `kt`, if aws-lc does it. RSASSA-PSS certificate signatures are
/// not taken.
fn cert_alg(alg: &AlgId, kt: KeyType) -> Option<&'static dyn signature::VerificationAlgorithm> {
    // ECDSA and Ed25519 identifiers have no parameters; RSA ones have NULL.
    let none = alg.params.is_none();
    let null = matches!(alg.params, Some(p) if p.tag == [0x05] && p.content.is_empty());
    let a: &'static dyn signature::VerificationAlgorithm = match (alg.oid, kt) {
        (o, KeyType::P256) if o == OID_ECDSA_SHA256 && none => &signature::ECDSA_P256_SHA256_ASN1,
        (o, KeyType::P256) if o == OID_ECDSA_SHA384 && none => &signature::ECDSA_P256_SHA384_ASN1,
        (o, KeyType::P384) if o == OID_ECDSA_SHA256 && none => &signature::ECDSA_P384_SHA256_ASN1,
        (o, KeyType::P384) if o == OID_ECDSA_SHA384 && none => &signature::ECDSA_P384_SHA384_ASN1,
        (o, KeyType::Rsa) if o == OID_RSA_SHA256 && (none || null) => &signature::RSA_PKCS1_2048_8192_SHA256,
        (o, KeyType::Rsa) if o == OID_RSA_SHA384 && (none || null) => &signature::RSA_PKCS1_2048_8192_SHA384,
        (o, KeyType::Rsa) if o == OID_RSA_SHA512 && (none || null) => &signature::RSA_PKCS1_2048_8192_SHA512,
        (o, KeyType::Ed25519) if o == OID_ED25519 && none => &signature::ED25519,
        _ => return None,
    };
    Some(a)
}

/// The TLS 1.3 signature scheme `scheme` (RFC 8446 §4.2.3) with a key of
/// type `kt`, if it is one for that key. PKCS #1 v1.5 schemes are not
/// defined for handshake signatures, so not taken.
fn tls_alg(scheme: u16, kt: KeyType) -> Option<&'static dyn signature::VerificationAlgorithm> {
    let a: &'static dyn signature::VerificationAlgorithm = match (scheme, kt) {
        (ECDSA_SECP256R1_SHA256, KeyType::P256) => &signature::ECDSA_P256_SHA256_ASN1,
        (ECDSA_SECP384R1_SHA384, KeyType::P384) => &signature::ECDSA_P384_SHA384_ASN1,
        (RSA_PSS_RSAE_SHA256, KeyType::Rsa) => &signature::RSA_PSS_2048_8192_SHA256,
        (RSA_PSS_RSAE_SHA384, KeyType::Rsa) => &signature::RSA_PSS_2048_8192_SHA384,
        (RSA_PSS_RSAE_SHA512, KeyType::Rsa) => &signature::RSA_PSS_2048_8192_SHA512,
        (ED25519, KeyType::Ed25519) => &signature::ED25519,
        _ => return None,
    };
    Some(a)
}

/// The civil date and time, UTC, `secs` seconds after the Unix epoch
/// (proleptic Gregorian calendar; H. Hinnant's `civil_from_days`).
pub fn utc_time(secs: u64) -> Time {
    let days = (secs / 86400) as i64;
    let rem = secs % 86400;
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u8;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u8;
    let year = yoe + era * 400 + if month <= 2 { 1 } else { 0 };
    Time {
        year: year.clamp(0, 9999) as u16,
        month,
        day,
        hour: (rem / 3600) as u8,
        minute: ((rem / 60) % 60) as u8,
        second: (rem % 60) as u8,
    }
}

impl Provider for AwsLc {
    type Key = Key;
    type Hp = Hp;

    fn hp_key(&self, suite: u16, key: &[u8]) -> Hp {
        let alg = match suite {
            TLS_AES_128_GCM_SHA256 => &quic_hp::AES_128,
            TLS_AES_256_GCM_SHA384 => &quic_hp::AES_256,
            _ => &quic_hp::CHACHA20,
        };
        Hp { key: HeaderProtectionKey::new(alg, key).expect("key length is the suite's") }
    }

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

    fn ech_open(&mut self, config_id: u8, kdf: u16, aead: u16, enc: &[u8], aad: &[u8], payload: &[u8], out: &mut Vec<u8>) -> bool {
        match self.ech.as_ref().and_then(|k| k.open(config_id, kdf, aead, enc, aad, payload)) {
            Some(pt) => {
                *out = pt;
                true
            }
            None => false,
        }
    }

    fn claim_early(&mut self, _ch: &[u8], binder: &[u8], obfuscated_age: u32, issued: u64, age_add: u32) -> bool {
        match &self.tickets {
            Some(t) => t.claim_early(binder, obfuscated_age, issued, age_add),
            None => false,
        }
    }

    fn verify_cert_sig(&self, alg: &AlgId, key: &Spki, msg: &[u8], sig: &[u8]) -> bool {
        match key_type(key).and_then(|kt| cert_alg(alg, kt)) {
            Some(a) => verify_with(a, key.key, msg, sig),
            None => false,
        }
    }

    fn verify_tls_sig(&self, scheme: u16, key: &Spki, msg: &[u8], sig: &[u8]) -> bool {
        match key_type(key).and_then(|kt| tls_alg(scheme, kt)) {
            Some(a) => verify_with(a, key.key, msg, sig),
            None => false,
        }
    }

    fn now_utc(&mut self) -> Time {
        utc_time(unix_now())
    }
}
