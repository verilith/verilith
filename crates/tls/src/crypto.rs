//! The cryptography verilith-tls uses and does not prove: the AEADs, key
//! exchange, signatures and random numbers. Everything in this file is
//! trusted. The functions are uninterpreted: the proofs know only that
//! they are functions (the same inputs give the same output) and the
//! lengths stated here. The implementation is a separate crate,
//! `verilith-tls-aws-lc`, over aws-lc; any type that implements these
//! traits with these contracts can stand in for it.
use alloc::vec::Vec;
use verilith_x509::spec::{SpecAlgId, SpecSpki};
use verilith_x509::{AlgId, Spki, Time};
use vstd::prelude::*;

verus! {

/// The AEAD of `suite` (§5.2: AEAD-Encrypt(write_key, nonce,
/// additional_data, plaintext)).
pub uninterp spec fn aead_seal(suite: u16, key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, pt: Seq<u8>) -> Seq<
    u8,
>;

/// AEAD-Decrypt: the plaintext, or `None` if the tag does not verify.
pub uninterp spec fn aead_open(suite: u16, key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, ct: Seq<u8>) -> Option<
    Seq<u8>,
>;

/// The tag length of every TLS 1.3 cipher suite.
pub const TAG_LEN: usize = 16;

/// An AEAD key, ready to use.
pub trait AeadKey: Sized {
    spec fn suite(&self) -> u16;

    spec fn key(&self) -> Seq<u8>;

    /// Encrypts `buf[start..]` in place and appends the tag.
    fn seal_in_place(&self, nonce: &[u8; 12], aad: &[u8; 5], buf: &mut Vec<u8>, start: usize)
        requires
            start <= old(buf)@.len(),
        ensures
            final(buf)@ == old(buf)@.take(start as int) + aead_seal(
                self.suite(),
                self.key(),
                nonce@,
                aad@,
                old(buf)@.skip(start as int),
            ),
            aead_seal(self.suite(), self.key(), nonce@, aad@, old(buf)@.skip(start as int)).len()
                == old(buf)@.len() - start + TAG_LEN,
    ;

    /// Decrypts `buf` (ciphertext and tag) in place. `Some(n)`: the
    /// plaintext is `buf[..n]`.
    fn open_in_place(&self, nonce: &[u8; 12], aad: &[u8; 5], buf: &mut [u8]) -> (r: Option<usize>)
        ensures
            match r {
                Some(n) => n <= final(buf)@.len() && aead_open(
                    self.suite(),
                    self.key(),
                    nonce@,
                    aad@,
                    old(buf)@,
                ) == Some(final(buf)@.take(n as int)),
                None => aead_open(self.suite(), self.key(), nonce@, aad@, old(buf)@) is None,
            },
            final(buf)@.len() == old(buf)@.len(),
    ;

    /// QUIC packet protection (RFC 9001 §5.3): encrypts `buf[start..]` in
    /// place with `buf[aad_start..start]` (the header) as the additional
    /// data, and appends the tag.
    fn seal_after(&self, nonce: &[u8; 12], buf: &mut Vec<u8>, aad_start: usize, start: usize)
        requires
            aad_start <= start <= old(buf)@.len(),
        ensures
            final(buf)@ == old(buf)@.take(start as int) + aead_seal(
                self.suite(),
                self.key(),
                nonce@,
                old(buf)@.subrange(aad_start as int, start as int),
                old(buf)@.skip(start as int),
            ),
            aead_seal(
                self.suite(),
                self.key(),
                nonce@,
                old(buf)@.subrange(aad_start as int, start as int),
                old(buf)@.skip(start as int),
            ).len() == old(buf)@.len() - start + TAG_LEN,
    ;

    /// Removes QUIC packet protection: decrypts `buf[start..]` (ciphertext
    /// and tag) in place with `buf[..start]` as the additional data.
    /// `Some(n)`: the plaintext is `buf[start..start + n]`, and the header
    /// is unchanged.
    fn open_after(&self, nonce: &[u8; 12], buf: &mut [u8], start: usize) -> (r: Option<usize>)
        requires
            start <= old(buf)@.len(),
        ensures
            final(buf)@.len() == old(buf)@.len(),
            final(buf)@.take(start as int) == old(buf)@.take(start as int),
            match r {
                Some(n) => start + n <= final(buf)@.len() && aead_open(
                    self.suite(),
                    self.key(),
                    nonce@,
                    old(buf)@.take(start as int),
                    old(buf)@.skip(start as int),
                ) == Some(final(buf)@.subrange(start as int, start + n)),
                None => aead_open(
                    self.suite(),
                    self.key(),
                    nonce@,
                    old(buf)@.take(start as int),
                    old(buf)@.skip(start as int),
                ) is None,
            },
    ;
}

/// QUIC header protection (RFC 9001 §5.4): the five mask bytes from
/// `sample` with the header protection key `key` of `suite` (AES-ECB for
/// the AES suites, ChaCha20 for ChaCha20-Poly1305).
pub uninterp spec fn hp_mask(suite: u16, key: Seq<u8>, sample: Seq<u8>) -> Seq<u8>;

/// A QUIC header protection key, ready to use.
pub trait HpKey: Sized {
    spec fn suite(&self) -> u16;

    spec fn key(&self) -> Seq<u8>;

    /// The mask for a 16-byte sample.
    fn mask(&self, sample: &[u8]) -> (r: [u8; 5])
        requires
            sample@.len() == 16,
        ensures
            r@ == hp_mask(self.suite(), self.key(), sample@),
    ;
}

/// Whether `shared` is the key exchange's shared secret for `group`, the
/// peer's share `peer` and the share `ours` this side sent (§4.2.8,
/// §7.4). What this means (X25519, ECDH, ML-KEM encapsulation) is the
/// provider's: the proofs only carry it.
pub uninterp spec fn key_exchange(group: u16, peer: Seq<u8>, ours: Seq<u8>, shared: Seq<u8>) -> bool;

/// Whether `sig` is a signature by the server's key with `scheme` of `msg`.
pub uninterp spec fn signed(scheme: u16, msg: Seq<u8>, sig: Seq<u8>) -> bool;

/// Whether `ticket` is a session ticket this server (its ticket keys)
/// issued, holding `state`. Sealing tickets, and refusing tickets it did not
/// issue, is the provider's: an AEAD under keys only the server has.
pub uninterp spec fn ticket_issued(ticket: Seq<u8>, state: Seq<u8>) -> bool;

/// Whether the provider's anti-replay (RFC 8446 §8) accepted 0-RTT data
/// for ClientHello `ch`: the ticket's age is within the freshness window
/// and this ClientHello has not had its 0-RTT data taken before.
pub uninterp spec fn early_claimed(ch: Seq<u8>) -> bool;

/// Whether `sig` is a signature, with a certificate's signature algorithm
/// `alg` (RFC 5280 §4.1.1.2), of `msg` by the public key `key`.
pub uninterp spec fn x509_signed(alg: SpecAlgId, key: SpecSpki, msg: Seq<u8>, sig: Seq<u8>) -> bool;

/// Whether `sig` is a TLS 1.3 signature with `scheme` (§4.2.3) of `msg` by
/// the public key `key`, of a type `scheme` allows.
pub uninterp spec fn tls_signed(scheme: u16, key: SpecSpki, msg: Seq<u8>, sig: Seq<u8>) -> bool;
/// Whether `pt` is what the server's ECH key for `config_id` opens from
/// `payload` with HPKE suite `kdf`/`aead`, encapsulated key `enc` and
/// additional data `aad` (RFC 9849 §7.1, RFC 9180 §5.2).
pub uninterp spec fn ech_opened(config_id: u8, kdf: u16, aead: u16, enc: Seq<u8>, aad: Seq<u8>, payload: Seq<u8>, pt: Seq<u8>) -> bool;

/// The cryptography a server needs, and its keys.
pub trait Provider {
    type Key: AeadKey;

    /// A QUIC header protection key.
    type Hp: HpKey;

    /// The header protection of `suite` with `key` (16 or 32 bytes).
    fn hp_key(&self, suite: u16, key: &[u8]) -> (r: Self::Hp)
        ensures
            r.suite() == suite,
            r.key() == key@,
    ;

    /// The AEAD of `suite` with `key` (16 or 32 bytes).
    fn aead_key(&self, suite: u16, key: &[u8]) -> (r: Self::Key)
        ensures
            r.suite() == suite,
            r.key() == key@,
    ;

    /// The server's side of a key exchange for `group`, given the client's
    /// share: appends the server's share to `share` and writes the shared
    /// secret to `shared`, returning its length; `None` if the client's
    /// share is malformed (an `illegal_parameter` alert).
    fn key_exchange(&mut self, group: u16, peer: &[u8], share: &mut Vec<u8>, shared: &mut [u8; 64]) -> (r: Option<usize>)
        ensures
            r matches Some(n) ==> n <= 64 && final(share)@.len() > old(share)@.len()
                && key_exchange(
                group,
                peer@,
                final(share)@.skip(old(share)@.len() as int),
                final(shared)@.take(n as int),
            ),
            final(share)@.take(old(share)@.len() as int) == old(share)@,
            final(share)@.len() <= old(share)@.len() + 65536,
    ;

    /// Signs `msg` with the server's key and `scheme`, appending the
    /// signature to `out`; `false` if the scheme is not the key's.
    fn sign(&mut self, scheme: u16, msg: &[u8], out: &mut Vec<u8>) -> (r: bool)
        ensures
            r ==> signed(scheme, msg@, final(out)@.skip(old(out)@.len() as int)),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(out)@.len() <= old(out)@.len() + 65535,
    ;

    /// 32 random bytes.
    fn random(&mut self, out: &mut [u8; 32]);

    /// Whether the provider has session ticket keys.
    fn tickets(&self) -> bool;

    /// Seals `state` into a session ticket appended to `out`.
    fn seal_ticket(&mut self, state: &[u8], out: &mut Vec<u8>) -> (r: bool)
        ensures
            r ==> ticket_issued(final(out)@.skip(old(out)@.len() as int), state@),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(out)@.len() <= old(out)@.len() + state@.len() + 64,
    ;

    /// Opens a session ticket into `out` (empty): `true` only for a ticket
    /// this server issued, and then `out` is what it holds.
    fn open_ticket(&self, ticket: &[u8], out: &mut Vec<u8>) -> (r: bool)
        ensures
            r ==> ticket_issued(ticket@, final(out)@),
    ;

    /// Seconds since the Unix epoch, for ticket lifetimes.
    fn now(&mut self) -> u64;

    /// Anti-replay for 0-RTT data (§8): whether to take ClientHello
    /// `ch`'s early data, given its first PSK binder `binder` (unique to
    /// the ClientHello), the ticket's `obfuscated_ticket_age`, and when
    /// the ticket was issued and its `ticket_age_add`. `true` at most once
    /// for a binder within the freshness window, and only if the
    /// client's view of the ticket's age agrees with the server's.
    /// `antireplay::Register::claim` is a verified implementation.
    fn claim_early(&mut self, ch: &[u8], binder: &[u8], obfuscated_age: u32, issued: u64, age_add: u32) -> (r: bool)
        ensures
            r ==> early_claimed(ch@),
    ;

    /// Checks a certificate's signature (client authentication): `sig`
    /// over `msg` with signature algorithm `alg` by `key`. `false` for a
    /// wrong signature or an algorithm or key the provider does not take.
    fn verify_cert_sig(&self, alg: &AlgId, key: &Spki, msg: &[u8], sig: &[u8]) -> (r: bool)
        ensures
            r ==> x509_signed(alg@, key@, msg@, sig@),
    ;

    /// Checks a CertificateVerify signature (§4.4.3): `sig` over `msg`
    /// with `scheme` by `key`. `false` for a wrong signature, or a scheme
    /// that does not fit the key.
    fn verify_tls_sig(&self, scheme: u16, key: &Spki, msg: &[u8], sig: &[u8]) -> (r: bool)
        ensures
            r ==> tls_signed(scheme, key@, msg@, sig@),
    ;

    /// The time now, in UTC, for certificate validity periods.
    fn now_utc(&mut self) -> Time;
    /// ECH (RFC 9849 §7.1): opens `payload` with the server's ECH key for
    /// `config_id` and HPKE suite `kdf`/`aead` (RFC 9180 SetupBaseR with
    /// `enc` and the ECHConfig as info, then Open with `aad`), the
    /// plaintext into `out` (empty); `false` if there is no such key or it
    /// does not open.
    fn ech_open(&mut self, config_id: u8, kdf: u16, aead: u16, enc: &[u8], aad: &[u8], payload: &[u8], out: &mut Vec<u8>) -> (r: bool)
        ensures
            r ==> ech_opened(config_id, kdf, aead, enc@, aad@, payload@, final(out)@),
    ;
}

} // verus!
