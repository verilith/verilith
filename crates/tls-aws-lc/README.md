# verilith-tls-aws-lc

The cryptography [verilith-tls](../tls) uses and does not prove, over
[aws-lc](https://github.com/aws/aws-lc) through aws-lc-rs: an
implementation of `verilith_tls::crypto::{Provider, AeadKey}`.

verilith-tls's proofs assume each function here meets the contract written
on the trait in `crates/tls/src/crypto.rs` (the AEAD seals and opens as
`aead_seal` and `aead_open`, the key exchange gives `key_exchange`'s shared
secret, the signature is `signed`, a ticket opens only if these keys sealed
it, `ticket_issued`). This crate is where that assumption is kept, in about
400 lines. It is not verified, and it is its own Cargo
project, outside the workspace and the Buck build, because aws-lc is C.

Not all of it is aws-lc. [CRYPTO.md](CRYPTO.md) lists every primitive
this crate calls, what proof stands behind each, and the benchmarks behind
the choice: HPKE's HMAC-SHA-256 is verilith-sha2's (Verus), and the
ChaCha20-Poly1305 that seals session tickets and opens ChaCha20 ECH
payloads is libcrux's (HACL*). The rest is aws-lc, where the verified
alternatives are several times slower.

- Cipher suites: TLS_AES_128_GCM_SHA256, TLS_AES_256_GCM_SHA384,
  TLS_CHACHA20_POLY1305_SHA256.
- Groups: X25519MLKEM768, x25519, secp256r1, secp384r1. An all-zero X25519
  output is refused (§7.4.2).
- Server keys (PKCS#8): ECDSA P-256 and P-384, Ed25519, RSA (PSS).
- Session tickets: `TicketKeys`, shared by a server's connections and
  threads (`Arc`), seal ticket state with ChaCha20-Poly1305 (libcrux's) under a random
  key, as `name(4) | nonce(12) | ciphertext | tag(16)` with the name as
  associated data. The key changes every `period` seconds and the previous
  one still opens, so a ticket opens for at least `period` seconds. Give
  `AwsLc::with_tickets` the same `Arc<TicketKeys>` on every connection.

`tests/` holds the interop tests with a rustls client and the record
protection tests; `examples/bench.rs` compares against a rustls server.
`tests/data` is a test CA and a leaf certificate for `localhost`, with its
key; they are for tests only.

## Licence

MIT or Apache-2.0, at your option.
