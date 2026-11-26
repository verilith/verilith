# verilith-tls

TLS 1.3 (RFC 8446) for the verified HTTP server, written in Rust and proven
with [Verus](https://github.com/verus-lang/verus): the wire formats first,
then the handshake state machine and the key schedule. The cryptographic
primitives (AEAD, HKDF, signatures, key exchange) stay in aws-lc and are
trusted; everything that decides what a byte from the peer means is proven.

**Status: a working TLS 1.3 server.** This release has the ClientHello
parser, negotiation, the key schedule, record protection and the server
handshake state machine, all proven, and talks to rustls clients with every
TLS 1.3 cipher suite and X25519, P-256, P-384 and X25519MLKEM768. It does a
full handshake with a certificate: no PSK resumption, no 0-RTT and no
client certificates yet ([plan](#plan)). The cryptography is
[`verilith-tls-aws-lc`](../tls-aws-lc), a separate crate.

```rust,ignore
use std::sync::Arc;
use verilith_tls::{server::Config, stream::ServerStream};
use verilith_tls_aws_lc::{AwsLc, SigningKey, GROUPS, SUITES};

let key = SigningKey::from_pkcs8(&key_der).unwrap();
let cfg = Arc::new(Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(),
                               b"\x02h2\x08http/1.1".to_vec(), &vec![cert_der]).unwrap());
let mut tls = ServerStream::new(cfg, AwsLc::new(Some(key)));
tls.read_tls(&bytes_from_socket);
tls.process()?;                       // plaintext in tls.plaintext()
socket.write_all(tls.pending())?;     // answers to send
```

ClientHello parsing is the part of a TLS server an unauthenticated peer
reaches first, with the most structure: nested length-prefixed vectors,
about a dozen extensions with their own formats, rules about duplicates
and order. verilith-tls parses it in one pass, without copying or
allocating, and returns spans of the input.

```rust
use verilith_tls::hello::ClientHello;

let body: &[u8] = &std::fs::read("tests/data/py-default-sni-alpn.bin").unwrap();
let hello = ClientHello::parse(body).unwrap();
assert_eq!(hello.server_name.unwrap().of(body), b"example.com");
```

## What is proven

`src/spec.rs` is the specification, as pure functions over the bytes,
written from RFC 8446, RFC 6066 (server_name) and RFC 7301 (ALPN). Every
definition names its section. The proofs show:

- **`ClientHello::parse` computes exactly `spec::parse_client_hello`**: it
  accepts exactly the ClientHellos the spec accepts, rejects the others
  with the alert the spec gives (`decode_error` or `illegal_parameter`),
  and every span it returns is the one the spec gives. The spec checks:
  - the syntax of §4.1.2: legacy_session_id of at most 32 bytes, an even,
    non-empty cipher_suites list, at least one compression method, the
    extensions vector (which may be absent, §4.1.2), and nothing after it;
  - §4.2: no two extensions of one type, and pre_shared_key last (§4.2.11),
    else `illegal_parameter`;
  - the contents of each extension it interprets, each a vector that must
    be exactly the extension's data, with the RFC's lower bounds:
    server_name (one host name at most, not empty), ALPN (non-empty names),
    supported_versions, supported_groups, signature_algorithms,
    signature_algorithms_cert, key_share, psk_key_exchange_modes,
    pre_shared_key (identities and binders, binders of at least 32 bytes,
    as many binders as identities), cookie, and early_data (empty);
  - §4.2.8: no two key shares for one group, else `illegal_parameter`.
- **Linear work**: `ClientHello::parse_counted` takes at most
  `12n + 2100` steps on an `n`-byte body, whatever the bytes. A step is a
  turn of a loop. The duplicate checks are what could have been quadratic:
  they use a set (`seen.rs`) that keeps values below 64 in one word and up
  to 16 others in an array, and moves to a 2^16-bit bitmap only past that,
  so `k` inserts cost at most `17k` steps plus the move, once.
- **Negotiation** (`negotiate.rs`): `negotiate` computes exactly
  `spec::negotiate`, a TLS 1.3 server's choices for a full handshake from
  a parsed ClientHello and its preferences: TLS 1.3 offered in
  supported_versions, else `protocol_version` (§4.2.1); a compression list
  of exactly `[0]`, else `illegal_parameter` (§4.1.2); signature_algorithms,
  supported_groups and key_share present, else `missing_extension` (§9.2);
  the server's first cipher suite and signature scheme the client offers,
  else `handshake_failure`; the server's first ALPN protocol the client
  offers, else `no_application_protocol` (RFC 7301 §3.2); and the server's
  first group the client sent a key share for, or failing that a
  HelloRetryRequest for its first group in supported_groups, or
  `handshake_failure` (§4.2.8). Its loops run over the ClientHello once per
  server preference, so its work is at most the ClientHello's length times
  the longest preference list.
- **Server names** (`negotiate::valid_host_name_x`) computes exactly
  `spec::valid_host_name`: what RFC 6066 allows in HostName (labels of 1 to
  63 letters, digits, hyphens and underscores, not starting or ending with
  a hyphen, at most 253 bytes, no final dot), with no IPv4 or IPv6
  literals.
- **The key schedule** (`keys.rs`) computes exactly `spec_keys.rs`, which
  is RFC 8446 §7 written over HKDF (RFC 5869) and HMAC: HKDF-Extract,
  HKDF-Expand with its T(i) blocks, the `HkdfLabel` encoding,
  HKDF-Expand-Label and Derive-Secret; the Early, Handshake and Master
  Secrets for a handshake without a PSK; the handshake and application
  traffic secrets, the exporter and resumption master secrets; traffic
  keys and IVs (§7.3); Finished's `verify_data` (§4.4.4); the next
  traffic secret of a KeyUpdate (§7.2); and the per-record nonce (§5.3),
  the IV XORed with the left-padded sequence number. The transcript hash
  is a running SHA-256 or SHA-384, proven to be the hash of every message
  given to it. HMAC and SHA-2 are verilith-sha2's, which are proven too
  (against FIPS 198-1 and FIPS 180-4), so the key schedule assumes nothing
  of its own. It does not allocate.
- **Record protection** (`protect.rs`) computes exactly `spec_record.rs`
  (§5.2, §5.3): the protected record header, which is also the AEAD's
  additional data; TLSInnerPlaintext as content, type and no padding when
  sealing; when opening, the 2^14 + 256 ciphertext and 2^14 + 1 plaintext
  limits (`record_overflow`), the padding stripped back to the last
  non-zero byte (`unexpected_message` if there is none), and the per-record
  nonce. Each direction's sequence number goes up by one per record and
  stops before it would wrap, and `lemma_nonce_injective` proves distinct
  sequence numbers give distinct nonces: no nonce is used twice under a key.
- **The server state machine** (`server.rs`, over `spec_server.rs`):
  - a connection is only ever in one of the states of Appendix A.2
    (`Phase`: Start, Retried, WaitFinished, Connected, Closed), and moves
    between them only forward;
  - every handshake message the server sends is exactly `spec_server.rs`'s
    encoding of it (ServerHello, HelloRetryRequest, EncryptedExtensions
    with the ALPN choice, Certificate, CertificateVerify, Finished,
    KeyUpdate); the flight after ServerHello is proven to be exactly those
    messages sealed in order under the server handshake keys from sequence
    number 0;
  - `SpecHs::valid`: each ClientHello negotiated (`spec::negotiate`)
    exactly the suite, group, signature scheme and ALPN protocol used; after
    a HelloRetryRequest the second ClientHello had to agree with it
    (§4.1.4), and the transcript starts with `message_hash` (§4.4.1); the
    shared secret is the provider's key exchange of the client's share; the
    CertificateVerify signature is over §4.4.3's content for the transcript
    through Certificate;
  - the transcript hash is over exactly the messages §4.4.1 says, and every
    secret and key is the key schedule's for it;
  - `lemma_connected`: once Connected, the client's Finished was exactly
    the one RFC 8446 defines for that transcript (compared in constant
    time);
  - application data is delivered (`Event::Data`) only when Connected, and
    only from a record that `spec_record::open_record` opens under the
    client's application traffic keys (after however many KeyUpdates);
    `write` seals under the server's;
  - change_cipher_spec records are dropped only between the ClientHello and
    the client's Finished, and only when they are the single byte 1;
    handshake messages may span records but not a change of keys; refused
    0-RTT data is skipped up to a bound (§4.2.10). Anything else is the
    alert §6 gives.
- **Record and handshake headers** (`record.rs`) read exactly
  `spec::record_header` and `spec::handshake_message`.
- No panics, no overflow, no out-of-bounds access, in all of the above. No
  allocation, except the bitmap above, which no real client causes.

`parse` does not decide whether the ClientHello can negotiate TLS 1.3
(`negotiate` does), or whether its server name is a valid host name
(`valid_host_name_x` does). A valid TLS 1.2 ClientHello parses.

## Trusted base

- **The spec** (`spec.rs`, `spec_keys.rs`, `spec_record.rs`,
  `spec_server.rs`). Read them against the RFCs.
- **The cryptography** (`crypto.rs`): the AEADs, key exchange, signatures
  and random numbers are uninterpreted functions, and the proofs assume the
  provider's implementation meets the contracts on the `AeadKey` and
  `Provider` traits. [`verilith-tls-aws-lc`](../tls-aws-lc) implements them
  over aws-lc; it is a separate crate, outside the workspace and Buck,
  because aws-lc is C.
- `stream.rs`, a byte-stream adapter that frames records and buffers
  bytes for `ServerConn`, is plain Rust and not verified; it decides
  nothing about what the bytes mean.
- Verus, vstd, Z3, rustc; verilith-core's `bytes::be16`, a spec function;
  and verilith-sha2's specifications of SHA-2 and HMAC (and its own
  trusted base: the SHA instructions' specifications and CPU detection).

There is no `external_body` in this crate.

## Tests

`../tls-aws-lc/tests/interop.rs` handshakes with a rustls 0.23 client in
memory: all three cipher suites with each of the four groups, ALPN
selection, a HelloRetryRequest, KeyUpdates both ways, close_notify, records
fed one byte at a time, a no-common-group and a no-common-ALPN failure, and
a tampered record (`bad_record_mac`, and nothing more is sent).
`../tls-aws-lc/tests/protect.rs` checks record protection against the AEAD
called directly with §5.3's nonce, with padding and each error.

`tests/keys.rs` checks the key schedule against RFC 8448's early and
derived secrets and, for both hashes and 100 random handshakes, against
a schedule built on RustCrypto's `hkdf` crate. `tests/negotiate.rs` negotiates with the real ClientHellos under several
server preferences (server preference wins, HelloRetryRequest, each
alert) and checks host names. `tests/hello.rs` parses real ClientHellos (`tests/data`, captured by
`tools/gen_hellos.py` from Python's OpenSSL, which offers X25519MLKEM768,
and from `openssl s_client`), hand-built ones for each rule above, every
prefix of the real ones, and 80,000 random mutations against a separate
reference parser.

`bench/` compares against rustls 0.23 (`cargo run --release`), and
`bench --agree` parses a million mutated ClientHellos with both. Every one
rustls accepts gives the same server name and ALPN list here. Where the two
disagree, verilith-tls is the stricter:

- **server_name**: rustls reads the first entry of the list and ignores the
  rest; verilith-tls reads the whole list as RFC 6066 defines it, so a list
  with trailing garbage, or a second host name, is `decode_error`.
- **signature_algorithms_cert** (§4.2.3): rustls does not interpret it in a
  ClientHello; verilith-tls checks its syntax.

In the other direction rustls rejects more, because it also checks values
(for example that the server name is a DNS name, and what a TLS 1.3
ClientHello must contain), which verilith-tls leaves to the caller and the
state machine.

## Speed

Cloud x86 VM (4 vCPU, shared), `bench/`, median of 31 runs of 20,000. The
task on both sides: one record holding a ClientHello in, the server name,
ALPN protocols, cipher suites and signature schemes out. rustls's API for
it is `Acceptor`, which also copies the fields it parses; verilith-tls
returns spans.

| ClientHello | verilith-tls | rustls 0.23 `Acceptor` | speedup |
|---|---:|---:|---:|
| Python/OpenSSL, X25519MLKEM768, SNI, ALPN (1536 B) | 99 ns | 2013 ns | 20x |
| Python/OpenSSL, TLS 1.2 only (185 B) | 64 ns | 1500 ns | 23x |
| openssl s_client, 3 ALPN protocols (341 B) | 93 ns | 1739 ns | 19x |
| openssl s_client, P-256 and P-384 (260 B) | 85 ns | 1178 ns | 14x |
| rustls client, SNI, ALPN (1490 B) | 95 ns | 1653 ns | 17x |

### Against a rustls server

`../tls-aws-lc/examples/bench.rs` (`cargo run --release --example bench`),
same VM. Both servers use aws-lc for their cryptography, so the difference
is the TLS layer; a rustls client drives both and only the server's own
work is timed. ECDSA P-256 certificate, TLS_AES_128_GCM_SHA256.

| full handshake, server side | verilith-tls | rustls 0.23 | speedup |
|---|---:|---:|---:|
| X25519 | 62.9 µs | 74.3 µs | 1.18x |
| P-256 | 91.9 µs | 103.6 µs | 1.13x |
| X25519MLKEM768 | 85.0 µs | 99.5 µs | 1.17x |

| 16 MiB in 16 KiB records | verilith-tls | rustls 0.23 | speedup |
|---|---:|---:|---:|
| server seals | 11.2 GB/s | 9.1 GB/s | 1.23x |
| server opens | 4.5 GB/s | 3.6 GB/s | 1.27x |

Most of a handshake is the signature and the key exchange, which are the
same aws-lc calls on both sides.

## Plan

1. ClientHello and extensions parser, record and handshake headers.
   *(done)*
2. Negotiation, verified: version, cipher suite, group and key share,
   signature scheme, ALPN choice, and server name validation. *(done)*
3. The server handshake state machine (§2, §4, Appendix A.2). *(done for
   the full handshake and HelloRetryRequest; PSK resumption, session
   tickets and client certificates next)*
4. The key schedule (§7). *(done, over verilith-sha2's proven HMAC, so
   no HKDF is trusted)*
5. Record protection (§5.2, §5.3). *(done)*
6. A drop-in under rustls's server API where the server needs it, and
   benchmarks of full handshakes against rustls.

## Licence

MIT or Apache-2.0, at your option.
