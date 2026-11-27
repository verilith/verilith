//! HPKE (RFC 9180), base mode, receiver side only, as Encrypted Client
//! Hello needs (RFC 9849 §6.1): DHKEM(X25519, HKDF-SHA256) with
//! HKDF-SHA256 and AES-128-GCM, AES-256-GCM or ChaCha20-Poly1305.
//! Trusted, like the rest of this crate; `tests/ech.rs` checks it against
//! rustls's HPKE.
use aws_lc_rs::aead::{self, Aad, LessSafeKey, Nonce, UnboundKey};
use aws_lc_rs::agreement::{self, PrivateKey, UnparsedPublicKey};
use verilith_sha2::HmacSha256;

pub const KEM_X25519_SHA256: u16 = 0x0020;
pub const KDF_SHA256: u16 = 0x0001;
pub const AEAD_AES_128_GCM: u16 = 0x0001;
pub const AEAD_AES_256_GCM: u16 = 0x0002;
pub const AEAD_CHACHA20_POLY1305: u16 = 0x0003;

fn extract(salt: &[u8], ikm: &[&[u8]]) -> [u8; 32] {
    // An empty salt is HashLen zeros (RFC 5869 §2.2); HMAC pads keys with
    // zeros, so the two are the same key.
    let mut c = HmacSha256::new(salt);
    for p in ikm {
        c.update(p);
    }
    c.finalize()
}

fn expand(prk: &[u8; 32], info: &[&[u8]], out: &mut [u8]) {
    let k = HmacSha256::new(prk);
    let mut t: Vec<u8> = Vec::new();
    let mut done = 0;
    let mut i = 1u8;
    while done < out.len() {
        let mut c = k.clone();
        c.update(&t);
        for p in info {
            c.update(p);
        }
        c.update(&[i]);
        t = c.finalize().to_vec();
        let n = (out.len() - done).min(32);
        out[done..done + n].copy_from_slice(&t[..n]);
        done += n;
        i += 1;
    }
}

fn labeled_extract(suite: &[u8], salt: &[u8], label: &[u8], ikm: &[u8]) -> [u8; 32] {
    extract(salt, &[b"HPKE-v1", suite, label, ikm])
}

fn labeled_expand(suite: &[u8], prk: &[u8; 32], label: &[u8], info: &[u8], out: &mut [u8]) {
    let l = (out.len() as u16).to_be_bytes();
    expand(prk, &[&l, b"HPKE-v1", suite, label, info], out)
}

/// An X25519 HPKE key pair of the server's.
pub struct HpkeKey {
    private: PrivateKey,
    public: [u8; 32],
}

impl HpkeKey {
    pub fn generate() -> Option<HpkeKey> {
        let private = PrivateKey::generate(&agreement::X25519).ok()?;
        HpkeKey::from_private(private)
    }

    /// From the 32-byte X25519 private key.
    pub fn from_bytes(sk: &[u8]) -> Option<HpkeKey> {
        HpkeKey::from_private(PrivateKey::from_private_key(&agreement::X25519, sk).ok()?)
    }

    fn from_private(private: PrivateKey) -> Option<HpkeKey> {
        let pk = private.compute_public_key().ok()?;
        let mut public = [0u8; 32];
        public.copy_from_slice(pk.as_ref());
        Some(HpkeKey { private, public })
    }

    pub fn public(&self) -> &[u8; 32] {
        &self.public
    }

    /// SetupBaseR(enc, skR, info) then Open(aad, ct) at sequence 0
    /// (RFC 9180 §5.1, §5.2): the plaintext, or `None`.
    pub fn open(&self, kdf: u16, aead_id: u16, enc: &[u8], info: &[u8], aad: &[u8], ct: &[u8]) -> Option<Vec<u8>> {
        if kdf != KDF_SHA256 || enc.len() != 32 {
            return None;
        }
        // AES-GCM is verilith-aes's (Verus) where the CPU has the
        // instructions, else aws-lc's; ChaCha20-Poly1305 libcrux's (HACL*,
        // verified; CRYPTO.md).
        let (alg, nk): (Option<&'static aead::Algorithm>, usize) = match aead_id {
            AEAD_AES_128_GCM => (Some(&aead::AES_128_GCM), 16),
            AEAD_AES_256_GCM => (Some(&aead::AES_256_GCM), 32),
            AEAD_CHACHA20_POLY1305 => (None, 32),
            _ => return None,
        };
        // DHKEM Decap (§4.1).
        let dh = agreement::agree(&self.private, UnparsedPublicKey::new(&agreement::X25519, enc), (), |s| {
            let mut d = [0u8; 32];
            d.copy_from_slice(s);
            Ok(d)
        })
        .ok()?;
        let kem_suite = [b'K', b'E', b'M', 0x00, 0x20];
        let eae_prk = labeled_extract(&kem_suite, b"", b"eae_prk", &dh);
        let mut ctx = [0u8; 64];
        ctx[..32].copy_from_slice(enc);
        ctx[32..].copy_from_slice(&self.public);
        let mut shared = [0u8; 32];
        labeled_expand(&kem_suite, &eae_prk, b"shared_secret", &ctx, &mut shared);
        // KeySchedule, mode_base (§5.1).
        let mut suite = *b"HPKE\0\0\0\0\0\0";
        suite[4..6].copy_from_slice(&KEM_X25519_SHA256.to_be_bytes());
        suite[6..8].copy_from_slice(&kdf.to_be_bytes());
        suite[8..10].copy_from_slice(&aead_id.to_be_bytes());
        let psk_id_hash = labeled_extract(&suite, b"", b"psk_id_hash", b"");
        let info_hash = labeled_extract(&suite, b"", b"info_hash", info);
        let mut ksc = [0u8; 65];
        ksc[1..33].copy_from_slice(&psk_id_hash);
        ksc[33..].copy_from_slice(&info_hash);
        let secret = labeled_extract(&suite, &shared, b"secret", b"");
        let mut key = [0u8; 32];
        labeled_expand(&suite, &secret, b"key", &ksc, &mut key[..nk]);
        let mut nonce = [0u8; 12];
        labeled_expand(&suite, &secret, b"base_nonce", &ksc, &mut nonce);
        let Some(alg) = alg else {
            if ct.len() < 16 {
                return None;
            }
            let mut pt = vec![0u8; ct.len() - 16];
            libcrux_chacha20poly1305::decrypt(&key, &mut pt, ct, aad, &nonce).ok()?;
            return Some(pt);
        };
        if let Some(k) = verilith_aes::AesGcm::new(&key[..nk]) {
            let n = ct.len().checked_sub(16)?;
            let mut buf = ct[..n].to_vec();
            let tag: [u8; 16] = ct[n..].try_into().unwrap();
            return k.open(&nonce, aad, &mut buf, &tag).then_some(buf);
        }
        let k = LessSafeKey::new(UnboundKey::new(alg, &key[..nk]).ok()?);
        let mut buf = ct.to_vec();
        let n = k.open_in_place(Nonce::assume_unique_for_key(nonce), Aad::from(aad), &mut buf).ok()?.len();
        buf.truncate(n);
        Some(buf)
    }
}

/// The server's Encrypted Client Hello keys (RFC 9849 §4): one X25519
/// key, its ECHConfig, and the ECHConfigList to publish (DNS HTTPS record)
/// and to send as retry_configs.
pub struct EchKeys {
    config_id: u8,
    key: HpkeKey,
    /// The ECHConfig, version and length included: HPKE's info is
    /// "tls ech" || 0 || this (§6.1).
    config: Vec<u8>,
    list: Vec<u8>,
}

/// The HPKE suites an ECHConfig of ours offers, all with HKDF-SHA256.
const ECH_AEADS: [u16; 3] = [AEAD_AES_128_GCM, AEAD_AES_256_GCM, AEAD_CHACHA20_POLY1305];

impl EchKeys {
    /// A fresh key, for clients reaching the server under `public_name`
    /// (the name ClientHelloOuter carries; the certificate must be valid
    /// for it too, so a client can take retry_configs from it).
    pub fn generate(config_id: u8, public_name: &str) -> Option<EchKeys> {
        EchKeys::with_key(config_id, HpkeKey::generate()?, public_name)
    }

    /// From a 32-byte X25519 private key, so that the published config
    /// outlives a restart.
    pub fn from_private_key(config_id: u8, sk: &[u8], public_name: &str) -> Option<EchKeys> {
        EchKeys::with_key(config_id, HpkeKey::from_bytes(sk)?, public_name)
    }

    fn with_key(config_id: u8, key: HpkeKey, public_name: &str) -> Option<EchKeys> {
        let name = public_name.as_bytes();
        if name.is_empty() || name.len() > 255 {
            return None;
        }
        let mut c = vec![config_id];
        c.extend_from_slice(&KEM_X25519_SHA256.to_be_bytes());
        c.extend_from_slice(&32u16.to_be_bytes());
        c.extend_from_slice(key.public());
        c.extend_from_slice(&((ECH_AEADS.len() * 4) as u16).to_be_bytes());
        for a in ECH_AEADS {
            c.extend_from_slice(&KDF_SHA256.to_be_bytes());
            c.extend_from_slice(&a.to_be_bytes());
        }
        c.push(0); // maximum_name_length: let the client pad as it likes.
        c.push(name.len() as u8);
        c.extend_from_slice(name);
        c.extend_from_slice(&[0, 0]); // no extensions
        let mut config = 0xfe0du16.to_be_bytes().to_vec();
        config.extend_from_slice(&(c.len() as u16).to_be_bytes());
        config.extend_from_slice(&c);
        let mut list = (config.len() as u16).to_be_bytes().to_vec();
        list.extend_from_slice(&config);
        Some(EchKeys { config_id, key, config, list })
    }

    /// The ECHConfigList, length prefix included.
    pub fn config_list(&self) -> &[u8] {
        &self.list
    }

    /// Opens an ECH payload (§7.1).
    pub fn open(&self, config_id: u8, kdf: u16, aead: u16, enc: &[u8], aad: &[u8], payload: &[u8]) -> Option<Vec<u8>> {
        if config_id != self.config_id || !ECH_AEADS.contains(&aead) {
            return None;
        }
        let mut info = b"tls ech\0".to_vec();
        info.extend_from_slice(&self.config);
        self.key.open(kdf, aead, enc, &info, aad, payload)
    }
}
