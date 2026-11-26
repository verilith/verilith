# verilith-tls

TLS 1.3 (RFC 8446) for the verified HTTP server, written in Rust and proven
with [Verus](https://github.com/verus-lang/verus): the wire formats first,
then the handshake state machine and the key schedule. The cryptographic
primitives (AEAD, HKDF, signatures, key exchange) stay in aws-lc and are
trusted; everything that decides what a byte from the peer means is proven.

**Status: first part.** This release has the ClientHello parser and the
record and handshake message headers. The server handshake state machine
and the key schedule come next ([plan](#plan)).

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
- **Record and handshake headers** (`record.rs`) read exactly
  `spec::record_header` and `spec::handshake_message`.
- No panics, no overflow, no out-of-bounds access, in all of the above. No
  allocation, except the bitmap above, which no real client causes.

What `parse` does not decide: whether the ClientHello can negotiate
TLS 1.3 (legacy_version, a compression list of exactly `[0]`,
supported_versions with 0x0304), which is the state machine's job, and
whether a server name is a valid DNS name, which is the caller's. A valid
TLS 1.2 ClientHello parses.

## Trusted base

- **The spec** (`spec.rs`). Read it against the RFCs.
- Verus, vstd, Z3, rustc; and verilith-core's `bytes::be16`, a spec
  function.

There is no `external_body` in this crate.

## Tests

`tests/hello.rs` parses real ClientHellos (`tests/data`, captured by
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

## Plan

1. ClientHello and extensions parser, record and handshake headers.
   *(this release)*
2. Negotiation, verified: version, cipher suite, group and key share,
   signature scheme, ALPN choice, and server name validation.
3. The server handshake state machine (§2, §4, Appendix A.2): full
   handshake, HelloRetryRequest, PSK resumption, proven to send and accept
   messages only in the order the RFC allows, with the transcript hash over
   exactly the messages §4.4.1 says.
4. The key schedule (§7.1) and record protection (§5.2, §5.3): the
   HKDF-Expand-Label inputs and the derivation order proven against the
   RFC, nonces proven never to repeat, with HKDF, HMAC and the AEADs from
   aws-lc, trusted.
5. A drop-in under rustls's server API where the server needs it, and
   benchmarks of full handshakes against rustls.

## Licence

MIT or Apache-2.0, at your option.
