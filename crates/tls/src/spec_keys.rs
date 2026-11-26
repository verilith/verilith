//! The specification of the TLS 1.3 key schedule (RFC 8446 §7), from
//! HKDF (RFC 5869) over HMAC and SHA-2 as verilith-sha2 specifies them
//! (FIPS 198-1, FIPS 180-4). Trusted, like `spec.rs`: read it against
//! §7.1 to §7.3 and §5.3. Nothing below HMAC is assumed: verilith-sha2's
//! HMAC and SHA-2 are themselves proven against those standards.
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_sha2::{spec::sha256, spec512::sha384, spec_hmac::{hmac_sha256, hmac_sha384}};

verus! {

/// The hash of a cipher suite (§B.4): SHA-256 for TLS_AES_128_GCM_SHA256
/// and TLS_CHACHA20_POLY1305_SHA256, SHA-384 for TLS_AES_256_GCM_SHA384.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HashAlg {
    Sha256,
    Sha384,
}

/// `Hash.length`.
pub open spec fn hash_len(a: HashAlg) -> nat {
    match a {
        HashAlg::Sha256 => 32,
        HashAlg::Sha384 => 48,
    }
}

pub open spec fn hash(a: HashAlg, m: Seq<u8>) -> Seq<u8> {
    match a {
        HashAlg::Sha256 => sha256(m),
        HashAlg::Sha384 => sha384(m),
    }
}

pub open spec fn hmac(a: HashAlg, k: Seq<u8>, m: Seq<u8>) -> Seq<u8> {
    match a {
        HashAlg::Sha256 => hmac_sha256(k, m),
        HashAlg::Sha384 => hmac_sha384(k, m),
    }
}

/// `n` zero bytes: §7.1's "0", "a string of Hash.length bytes set to
/// zeros".
pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

// ---------------------------------------------------------------------------
// HKDF (RFC 5869)
// ---------------------------------------------------------------------------

/// HKDF-Extract (§2.2): `PRK = HMAC-Hash(salt, IKM)`.
pub open spec fn hkdf_extract(a: HashAlg, salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8> {
    hmac(a, salt, ikm)
}

/// `T(i)` of HKDF-Expand (§2.3): `T(0)` is empty,
/// `T(i) = HMAC-Hash(PRK, T(i-1) | info | i)`.
pub open spec fn t_block(a: HashAlg, prk: Seq<u8>, info: Seq<u8>, i: nat) -> Seq<u8>
    decreases i,
{
    if i == 0 {
        Seq::empty()
    } else {
        hmac(a, prk, t_block(a, prk, info, (i - 1) as nat) + info + seq![i as u8])
    }
}

/// `T(1) | ... | T(n)`.
pub open spec fn t_concat(a: HashAlg, prk: Seq<u8>, info: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        t_concat(a, prk, info, (n - 1) as nat) + t_block(a, prk, info, n)
    }
}

/// HKDF-Expand (§2.3): the first `l` bytes of `T(1) | T(2) | ...`, for
/// `l <= 255 * HashLen`.
pub open spec fn hkdf_expand(a: HashAlg, prk: Seq<u8>, info: Seq<u8>, l: nat) -> Seq<u8> {
    let n = (l + hash_len(a) - 1) as int / hash_len(a) as int;
    t_concat(a, prk, info, n as nat).take(l as int)
}

// ---------------------------------------------------------------------------
// The labels (§7.1, §7.2, §7.3)
// ---------------------------------------------------------------------------

/// `"derived"`
pub open spec fn l_derived() -> Seq<u8> {
    seq![100, 101, 114, 105, 118, 101, 100]
}

/// `"c hs traffic"`
pub open spec fn l_c_hs() -> Seq<u8> {
    seq![99, 32, 104, 115, 32, 116, 114, 97, 102, 102, 105, 99]
}

/// `"s hs traffic"`
pub open spec fn l_s_hs() -> Seq<u8> {
    seq![115, 32, 104, 115, 32, 116, 114, 97, 102, 102, 105, 99]
}

/// `"c ap traffic"`
pub open spec fn l_c_ap() -> Seq<u8> {
    seq![99, 32, 97, 112, 32, 116, 114, 97, 102, 102, 105, 99]
}

/// `"s ap traffic"`
pub open spec fn l_s_ap() -> Seq<u8> {
    seq![115, 32, 97, 112, 32, 116, 114, 97, 102, 102, 105, 99]
}

/// `"exp master"`
pub open spec fn l_exp() -> Seq<u8> {
    seq![101, 120, 112, 32, 109, 97, 115, 116, 101, 114]
}

/// `"res master"`
pub open spec fn l_res() -> Seq<u8> {
    seq![114, 101, 115, 32, 109, 97, 115, 116, 101, 114]
}

/// `"key"`
pub open spec fn l_res_binder() -> Seq<u8> {
    seq![114u8, 101, 115, 32, 98, 105, 110, 100, 101, 114]
}

pub open spec fn l_resumption() -> Seq<u8> {
    seq![114u8, 101, 115, 117, 109, 112, 116, 105, 111, 110]
}

pub open spec fn l_key() -> Seq<u8> {
    seq![107, 101, 121]
}

/// `"iv"`
pub open spec fn l_iv() -> Seq<u8> {
    seq![105, 118]
}

/// `"finished"`
pub open spec fn l_finished() -> Seq<u8> {
    seq![102, 105, 110, 105, 115, 104, 101, 100]
}

/// `"traffic upd"`
pub open spec fn l_upd() -> Seq<u8> {
    seq![116, 114, 97, 102, 102, 105, 99, 32, 117, 112, 100]
}

/// `"tls13 "`
pub open spec fn l_tls13() -> Seq<u8> {
    seq![116, 108, 115, 49, 51, 32]
}

// ---------------------------------------------------------------------------
// HKDF-Expand-Label and Derive-Secret (§7.1)
// ---------------------------------------------------------------------------

/// The `HkdfLabel` structure, serialized:
///
/// ```text
/// struct {
///     uint16 length = Length;
///     opaque label<7..255> = "tls13 " + Label;
///     opaque context<0..255> = Context;
/// } HkdfLabel;
/// ```
pub open spec fn hkdf_label(l: nat, label: Seq<u8>, ctx: Seq<u8>) -> Seq<u8> {
    seq![(l / 256) as u8, (l % 256) as u8, (6 + label.len()) as u8] + l_tls13() + label + seq![
        ctx.len() as u8,
    ] + ctx
}

/// `HKDF-Expand-Label(Secret, Label, Context, Length)`.
#[verifier::opaque]
pub open spec fn expand_label(a: HashAlg, secret: Seq<u8>, label: Seq<u8>, ctx: Seq<u8>, l: nat) -> Seq<
    u8,
> {
    hkdf_expand(a, secret, hkdf_label(l, label, ctx), l)
}

/// `Derive-Secret(Secret, Label, Messages)`, with `Transcript-Hash` the
/// hash of the concatenated handshake messages (§4.4.1).
pub open spec fn derive_secret(a: HashAlg, secret: Seq<u8>, label: Seq<u8>, messages: Seq<u8>) -> Seq<
    u8,
> {
    expand_label(a, secret, label, hash(a, messages), hash_len(a))
}

// ---------------------------------------------------------------------------
// The key schedule (§7.1). `psk` is the PSK of a resumption, or
// `zeros(hash_len(a))` for a handshake without one.
// ---------------------------------------------------------------------------

/// Early Secret: `HKDF-Extract(0, PSK)`.
pub open spec fn early_secret(a: HashAlg, psk: Seq<u8>) -> Seq<u8> {
    hkdf_extract(a, zeros(hash_len(a)), psk)
}

/// binder_key for a resumption PSK: `Derive-Secret(Early, "res binder", "")`.
pub open spec fn binder_key(a: HashAlg, psk: Seq<u8>) -> Seq<u8> {
    derive_secret(a, early_secret(a, psk), l_res_binder(), Seq::empty())
}

/// The PSK a NewSessionTicket with `nonce` makes (§4.6.1):
/// `HKDF-Expand-Label(resumption_master_secret, "resumption", nonce,
/// Hash.length)`.
pub open spec fn ticket_psk(a: HashAlg, res_master: Seq<u8>, nonce: Seq<u8>) -> Seq<u8> {
    expand_label(a, res_master, l_resumption(), nonce, hash_len(a))
}

/// Handshake Secret: `HKDF-Extract(Derive-Secret(Early, "derived", ""),
/// (EC)DHE)`.
pub open spec fn handshake_secret(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>) -> Seq<u8> {
    hkdf_extract(a, derive_secret(a, early_secret(a, psk), l_derived(), Seq::empty()), dhe)
}

/// Master Secret: `HKDF-Extract(Derive-Secret(Handshake, "derived", ""),
/// 0)`.
pub open spec fn master_secret(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>) -> Seq<u8> {
    hkdf_extract(
        a,
        derive_secret(a, handshake_secret(a, psk, dhe), l_derived(), Seq::empty()),
        zeros(hash_len(a)),
    )
}

/// client_handshake_traffic_secret, `messages` being ClientHello to
/// ServerHello.
pub open spec fn client_hs_traffic(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, handshake_secret(a, psk, dhe), l_c_hs(), messages)
}

/// server_handshake_traffic_secret, ClientHello to ServerHello.
pub open spec fn server_hs_traffic(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, handshake_secret(a, psk, dhe), l_s_hs(), messages)
}

/// client_application_traffic_secret_0, ClientHello to server Finished.
pub open spec fn client_ap_traffic(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, master_secret(a, psk, dhe), l_c_ap(), messages)
}

/// server_application_traffic_secret_0, ClientHello to server Finished.
pub open spec fn server_ap_traffic(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, master_secret(a, psk, dhe), l_s_ap(), messages)
}

/// exporter_master_secret, ClientHello to server Finished.
pub open spec fn exporter_master(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, master_secret(a, psk, dhe), l_exp(), messages)
}

/// resumption_master_secret, ClientHello to client Finished.
pub open spec fn resumption_master(a: HashAlg, psk: Seq<u8>, dhe: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    derive_secret(a, master_secret(a, psk, dhe), l_res(), messages)
}

/// `application_traffic_secret_N+1` (§7.2).
pub open spec fn next_traffic_secret(a: HashAlg, secret: Seq<u8>) -> Seq<u8> {
    expand_label(a, secret, l_upd(), Seq::empty(), hash_len(a))
}

/// The traffic key and IV of a secret (§7.3).
pub open spec fn traffic_key(a: HashAlg, secret: Seq<u8>, key_len: nat) -> Seq<u8> {
    expand_label(a, secret, l_key(), Seq::empty(), key_len)
}

pub open spec fn traffic_iv(a: HashAlg, secret: Seq<u8>) -> Seq<u8> {
    expand_label(a, secret, l_iv(), Seq::empty(), 12)
}

/// `finished_key` (§4.4.4).
pub open spec fn finished_key(a: HashAlg, base_key: Seq<u8>) -> Seq<u8> {
    expand_label(a, base_key, l_finished(), Seq::empty(), hash_len(a))
}

/// `verify_data` (§4.4.4): `HMAC(finished_key, Transcript-Hash(Handshake
/// Context, Certificate*, CertificateVerify*))`.
pub open spec fn verify_data(a: HashAlg, base_key: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    hmac(a, finished_key(a, base_key), hash(a, messages))
}

// ---------------------------------------------------------------------------
// Record nonces (§5.3)
// ---------------------------------------------------------------------------

/// Byte `i` of the 64-bit record sequence number "padded to the left with
/// zeros to iv_length" (12).
pub open spec fn seq_byte(seq: u64, i: int) -> u8 {
    if i < 4 {
        0
    } else {
        ((seq as nat / pow256((11 - i) as nat)) % 256) as u8
    }
}

pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// The per-record nonce: the padded sequence number XORed with the IV.
#[verifier::opaque]
pub open spec fn record_nonce(iv: Seq<u8>, seq: u64) -> Seq<u8> {
    Seq::new(12, |i: int| iv[i] ^ seq_byte(seq, i))
}


// ---------------------------------------------------------------------------
// QUIC (RFC 9001 §5): the Initial secrets, and the packet protection keys
// and key updates of a TLS traffic secret.
// ---------------------------------------------------------------------------

/// `initial_salt` of QUIC version 1 (§5.2).
pub open spec fn quic_v1_salt() -> Seq<u8> {
    seq![0x38u8, 0x76u8, 0x2cu8, 0xf7u8, 0xf5u8, 0x59u8, 0x34u8, 0xb3u8, 0x4du8, 0x17u8, 0x9au8, 0xe6u8, 0xa4u8, 0xc8u8, 0x0cu8, 0xadu8, 0xccu8, 0xbbu8, 0x7fu8, 0x0au8]
}

/// `"client in"`
pub open spec fn l_client_in() -> Seq<u8> {
    seq![99u8, 108u8, 105u8, 101u8, 110u8, 116u8, 32u8, 105u8, 110u8]
}

/// `"server in"`
pub open spec fn l_server_in() -> Seq<u8> {
    seq![115u8, 101u8, 114u8, 118u8, 101u8, 114u8, 32u8, 105u8, 110u8]
}

/// `"quic key"`
pub open spec fn l_quic_key() -> Seq<u8> {
    seq![113u8, 117u8, 105u8, 99u8, 32u8, 107u8, 101u8, 121u8]
}

/// `"quic iv"`
pub open spec fn l_quic_iv() -> Seq<u8> {
    seq![113u8, 117u8, 105u8, 99u8, 32u8, 105u8, 118u8]
}

/// `"quic hp"`
pub open spec fn l_quic_hp() -> Seq<u8> {
    seq![113u8, 117u8, 105u8, 99u8, 32u8, 104u8, 112u8]
}

/// `"quic ku"`
pub open spec fn l_quic_ku() -> Seq<u8> {
    seq![113u8, 117u8, 105u8, 99u8, 32u8, 107u8, 117u8]
}

/// `initial_secret = HKDF-Extract(initial_salt, client_dst_connection_id)`.
pub open spec fn initial_secret(dcid: Seq<u8>) -> Seq<u8> {
    hkdf_extract(HashAlg::Sha256, quic_v1_salt(), dcid)
}

/// `client_initial_secret = HKDF-Expand-Label(initial_secret, "client in", "", 32)`.
pub open spec fn client_initial_secret(dcid: Seq<u8>) -> Seq<u8> {
    expand_label(HashAlg::Sha256, initial_secret(dcid), l_client_in(), Seq::empty(), 32)
}

pub open spec fn server_initial_secret(dcid: Seq<u8>) -> Seq<u8> {
    expand_label(HashAlg::Sha256, initial_secret(dcid), l_server_in(), Seq::empty(), 32)
}

/// The packet protection key of a secret (§5.1), `key_len` bytes.
pub open spec fn quic_key(a: HashAlg, secret: Seq<u8>, key_len: nat) -> Seq<u8> {
    expand_label(a, secret, l_quic_key(), Seq::empty(), key_len)
}

/// The packet protection IV (§5.1).
pub open spec fn quic_iv(a: HashAlg, secret: Seq<u8>) -> Seq<u8> {
    expand_label(a, secret, l_quic_iv(), Seq::empty(), 12)
}

/// The header protection key (§5.1), as long as the AEAD key.
pub open spec fn quic_hp(a: HashAlg, secret: Seq<u8>, key_len: nat) -> Seq<u8> {
    expand_label(a, secret, l_quic_hp(), Seq::empty(), key_len)
}

/// The next secret of a key update (§6.1): "quic ku".
pub open spec fn quic_next(a: HashAlg, secret: Seq<u8>) -> Seq<u8> {
    expand_label(a, secret, l_quic_ku(), Seq::empty(), hash_len(a))
}

/// The secret after `n` key updates.
pub open spec fn quic_updated(a: HashAlg, s: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        s
    } else {
        quic_next(a, quic_updated(a, s, (n - 1) as nat))
    }
}

} // verus!
