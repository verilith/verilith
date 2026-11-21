# verilith-x509

A DER and X.509 certificate parser in Rust, formally verified with
[Verus](https://github.com/verus-lang/verus). The parser is proven to compute
exactly a specification of DER (X.690) and the RFC 5280 certificate profile,
written as pure functions in [`src/spec.rs`](src/spec.rs): it accepts a
certificate if and only if the spec does, and returns exactly the fields
the spec says. Verus also proves that it never reads out of bounds and
never overflows.

It is a drop-in for mbedTLS: with a 20-line patch, mbedTLS 3.6.4 decodes
every certificate it reads (`mbedtls_x509_crt_parse_der`, and so
`mbedtls_x509_crt_parse`, PEM files, the TLS handshake and PKCS#7) with
verilith-x509 and passes its own test suites, except for 18 synthetic test
certificates that break DER and RFC 5280 (see
[mbedtls/README.md](mbedtls/README.md)).

It is `no_std`, never allocates and never copies: a parsed certificate is a
set of slices of the input. It builds for bare-metal targets such as
`thumbv7em-none-eabihf`, where mbedTLS is mostly used.

It is fast: 8 to 12 times faster than x509-parser and x509-cert, the other
Rust parsers that decode a whole certificate (see Performance).

Every place where it reads X.690 or RFC 5280 strictly or loosely is listed
in [DEPARTURES.md](DEPARTURES.md), and [CVES.md](CVES.md) maps fourteen
certificate parsing CVEs in OpenSSL, NSS, Windows CryptoAPI and PolarSSL
to the proven property that rules out each bug class.

## Two speeds: drop-in and native

Swap verilith-x509 in under mbedTLS today and get the proofs at no cost in speed;
call `verilith_x509::parse` directly where certificate parsing is hot.

| | what you change | against mbedTLS 3.6.4 |
| --- | --- | --- |
| **Drop-in** (mbedTLS with the patch) | apply the patch, rebuild | 1.00x (0.94x to 1.03x) |
| **Native** (`verilith_x509::parse` and its accessors) | port the calling code | up to 3.15x (1.98x to 5.35x) |

The task is: parse a certificate in place
(`mbedtls_x509_crt_parse_der_nocopy`), read the serial, every issuer and
subject attribute, both validity times, key usage, the CA flag, the DNS
subjectAltNames and the extended key usages, then free it, on a leaf, two
roots and Mozilla's root bundle.
Measured with [vbench](https://github.com/verilith/verilith/tree/main/bench) on an
Apple M3 Pro (2026-11-20, 31 alternating pairs per case; speedup is mbedTLS's
time over ours, geometric mean and range over the cases). Both columns run
the same task against the same mbedTLS driver. The native number is what you
get after porting the calling code; relinking alone gets the drop-in
number.

**The native number is an upper bound, because the two sides do not do the
same work.** mbedTLS also decodes the public key into a
`mbedtls_pk_context` and allocates the name and extension lists, and its
API does not let a caller skip either. verilith-x509 checks the structure of the
SubjectPublicKeyInfo and returns the key bytes undecoded, and it returns
names and extensions as slices of the input. A caller that goes on to use
the key pays for decoding it on our side too.

## Usage

```rust
let cert = verilith_x509::parse(&der).ok_or("malformed")?;
// Or, to learn why a certificate was rejected:
// let cert = verilith_x509::try_parse(&der)?;   // Err says what, at which offset

for atv in cert.subject().attributes() {
    println!("{} = {:?}", verilith_x509::OidDisplay(atv.oid), atv.value_str());
}
for dns in cert.dns_names() {
    println!("DNS: {}", String::from_utf8_lossy(dns));
}
if let Some(bc) = cert.basic_constraints() {
    println!("CA: {}, path length: {:?}", bc.ca, bc.path_len);
}
let signed = cert.tbs_der;      // the exact bytes the signature covers
let signature = cert.signature;
```

### From C

The same API from C or C++, through `include/vx509.h`: build with
`cargo build --profile release-fat --features capi` and link
`target/release-fat/libverilith_x509.a`. Use it when you can change the calling code;
use the mbedTLS drop-in (`mbedtls/`) when you cannot.

```c
vx509_cert c;
if (vx509_cert_parse(der, len, &c, NULL) == VX509_OK) {
    vx509_span names;
    vx509_general_name g;
    if (vx509_get_subject_alt_names(&c, &names))
        while (vx509_general_name_next(&names, &g))
            if (g.kind == VX509_GN_DNS) fwrite(g.value.p, 1, g.value.len, stdout);
    /* c.tbs is what the signature covers; c.signature is the signature */
}
```

`vx509_cert_parse` fills a caller-provided struct of spans that point into
the certificate. Nothing is allocated, nothing is copied and there is
nothing to free, where the mbedTLS shape has to build `mbedtls_x509_crt`'s
linked lists. Names, extensions and lists are read with cursor functions
(`vx509_rdn_next`, `vx509_ext_next`, ...), and every decoded extension of
the Rust API has a getter. It is `no_std` and allocation-free like the
parser.

## What is proven

- **Exactness.** `verilith_x509::parse(b)` returns `Some(c)` if and only if
  `parse_certificate(b)` in the spec returns `Some`, and then `c` is the
  spec's value. The same holds for every typed extension accessor
  (BasicConstraints, KeyUsage, ExtendedKeyUsage, SubjectAltName,
  IssuerAltName, SubjectKeyIdentifier, AuthorityKeyIdentifier,
  certificatePolicies, NameConstraints) and every iterator (RDNs,
  attributes, GeneralNames, OIDs, extensions), which yield exactly the
  spec's lists.
- **Safety.** No out-of-bounds index, no arithmetic overflow, no panic and
  no unbounded loop in the verified code.
- **The spec** checks DER framing (minimal lengths, at most 4 length octets,
  single-octet tags where X.509 uses them), minimal INTEGERs and OIDs,
  times, Names, every field of TBSCertificate, version rules (unique IDs
  only from v2, extensions only in v3), distinct extensions, the contents
  of every extension listed above, and signatureAlgorithm equal to the
  TBSCertificate's signature.

The trusted base is the spec, Verus, Z3 and rustc. `src/api.rs`
(`Iterator` impls, text, timestamps), `src/error.rs` (rejection reasons),
and the mbedTLS adapter (`src/mbedtls.rs`, `src/mbedtls_err.rs`,
`mbedtls/vx509_mbedtls.c`) are unverified. None of them decides whether a
certificate is accepted.

So is the native C API, `src/native.rs` (feature `capi`, 393 lines of code
for 20 functions, against 964 for the mbedTLS adapter). Each function turns
its arguments into slices, calls the verified function of the same name
and writes the result out as spans. What it adds to the trusted base is
its own `unsafe` and the contract in `include/vx509.h`: the caller keeps
the certificate's bytes alive and passes back only spans this API wrote.

## How this differs from Verdict

[Verdict](https://github.com/secure-foundations/verdict) (USENIX Security
2025) is a verified X.509 parser and chain validator, also in Verus, built
on the [Vest](https://github.com/secure-foundations/vest) parser
combinators, and it validates chains under Chrome, Firefox and OpenSSL
policies. verilith-x509 does less, a parser and no chain validation, and aims at a
different place:

- **It replaces the parser inside an existing C library.** mbedTLS
  applications get a verified certificate decoder by relinking, with the
  same API and structures, and mbedTLS's test suites check the result.
- **Embedded targets.** `no_std`, no allocator and no copies, so it runs
  where mbedTLS runs.
- **Hand-written code against a direct spec**, rather than combinators,
  which is what makes it zero-copy and fast.

Verdict has not been benchmarked against verilith-x509 yet.

## Performance

From the benchmark harness in `bench/` (`bench/run.sh`), in ns per
certificate, lower is better. Each row ran on its own in three separate
processes, each taking the best of 30 runs of 20k iterations after a
warm-up; the table gives the best of the three. Rust is built with
`lto = "fat"`, mbedTLS 3.6.4 with CMake's Release flags (`-O2`). One
machine (Intel Xeon @ 2.1 GHz), not reproduced independently.

| What is measured | leaf (1,473 B, 8 extensions) | RSA root (1,391 B) | ECDSA root (543 B) |
| --- | --- | --- | --- |
| **Rust, whole certificate decoded and checked** | | | |
| verilith-x509 `parse` | **422** | **235** | **220** |
| verilith-x509 `parse`, then read every field and list | 1,006 | 488 | 461 |
| x509-parser 0.18 `parse_x509_certificate` | 3,534 | 2,048 | 1,833 |
| x509-cert 0.2 `Certificate::from_der` | 4,564 | 3,323 | 2,819 |
| **Less work** (Names and times not decoded; most extension contents checked only when used) | | | |
| rustls-webpki 0.103 `EndEntityCert::try_from` | 182 | 103 | 103 |
| **C, into `mbedtls_x509_crt`** (includes decoding the public key and allocating the name lists) | | | |
| mbedTLS 3.6.4 `mbedtls_x509_crt_parse_der` | 1,250 | 955 | 1,416 |
| vx509-backed mbedTLS, same call | 1,581 | 1,162 | 1,561 |
| mbedTLS 3.6.4 `mbedtls_x509_crt_parse_der_nocopy` | 1,064 | 782 | 1,363 |
| vx509-backed mbedTLS, same call | 1,386 | 964 | 1,440 |
| **Other** | | | |
| OpenSSL 3.0.13 `X509::from_der` | 126,506 | 122,662 | 123,705 |

The two vx509-backed mbedTLS rows above were measured before the adapter
was reworked (the verified parser now hands each attribute and extension
to the adapter as it checks it, instead of filling records that were
copied twice more). Measured since, on an Apple M3 Pro with the
[vbench](https://github.com/verilith/verilith/tree/main/bench) harness
(`mbedtls_x509_crt_parse_der` + free, both sides Apple clang 21 `-O3`,
31 pairs per case, three sittings, 2026-11-19), vx509-backed mbedTLS
against stock mbedTLS 3.6.4:

| Case | vx509-backed | stock | speed vs stock |
| --- | ---: | ---: | --- |
| leaf (8 extensions) | 595 ns | 580 ns | 0.96x to 0.99x |
| RSA root | 420 ns | 441 ns | 1.04x to 1.07x |
| ECDSA root | 803 ns | 818 ns | 1.01x to 1.03x |
| 118 Mozilla roots, one chain | 89.3 µs | 88.1 µs | 0.985x to 0.987x |

So inside mbedTLS it is level with mbedTLS's own parser (geometric mean
1.01x), while checking more than mbedTLS does (times, OIDs, IA5 names,
every extension's contents, duplicates). Before the rework the same
harness on the same machine gave 0.84x, 0.95x, 0.96x and 0.91x. For
scale, one RSA-2048 signature check takes about 20 µs.
OpenSSL 3's `d2i_X509` is dominated by looking up a key decoder for the
public key in its provider framework.

The certificates are ISRG Root X1 and X2 and a RapidSSL leaf for
cryptography.io, in `bench/data/`.

## Testing

- `tests/cves.rs`: certificates shaped like fourteen CVEs (see CVES.md).
- `tests/differential.rs`: against OpenSSL, x509-parser, x509-cert and
  webpki on about 31,000 certificates from x509-limbo, pyca/cryptography's
  vectors and the system trust store, with 0 disagreements on decoded
  fields (see [corpus/README.md](corpus/README.md)).
- `tests/capi.rs` (`cargo test --features capi`): the native C API against
  the Rust API, field by field, on the corpus and on every truncation and
  single-byte change of four certificates. `scripts/test-c.sh` runs
  `tests/c/native.c` under ASan and UBSan.
- `mbedtls/run-tests.sh`: mbedTLS's own test suites with verilith-x509 as its parser.
  `examples/mbedtls_cases.rs` lists where verilith-x509 and stock mbedTLS disagree
  on mbedTLS's X.509 test vectors.

## Fuzzing

`fuzz/` has two cargo-fuzz targets, for the code the proofs do not cover.

| Target | What it checks |
| --- | --- |
| `parse` | Every accessor and iterator, text output, timestamps, and that `try_parse` agrees with `parse` |
| `mbedtls` | The vx509-backed `mbedtls_x509_crt_parse_der` and `_nocopy`, then `mbedtls_x509_crt_info` on every accepted certificate and `mbedtls_x509_crt_free`, with mbedTLS built with AddressSanitizer. mbedTLS must never accept a certificate verilith-x509 rejects |

```sh
git -C mbedtls apply ../verilith/crates/x509/mbedtls/mbedtls-use-vx509.patch
CC=clang cmake -S mbedtls -B mbedtls/build-asan -DCMAKE_C_COMPILER_WORKS=1 \
  -DENABLE_TESTING=OFF -DENABLE_PROGRAMS=OFF -DMBEDTLS_VX509_DIR=$PWD/verilith/crates/x509 \
  -DMBEDTLS_VX509_LIB=$PWD/verilith/target/release-fat/libverilith_x509.a \
  -DCMAKE_C_FLAGS="-fsanitize=address,fuzzer-no-link -g"
cmake --build mbedtls/build-asan --target mbedx509 mbedcrypto
cd vx509/fuzz && MBEDTLS_LIB_DIR=$PWD/../../mbedtls/build-asan/library \
  cargo +nightly fuzz run -s address mbedtls corpus/mbedtls seeds
```

Seeded with about 3,600 certificates from the differential corpus and
mbedTLS's test data, ten minutes per target ran 32.7M inputs of `parse` and
9.1M of `mbedtls` with no crash, leak, sanitizer report or mismatch.

## Continuous integration

`.github/workflows/ci.yml` is a manual workflow (automatic runs are off; start it from the Actions tab). It runs:

- **verify**: builds Verus from source at the pinned commit (cached) and
  checks every proof;
- **test**: the bare-metal `no_std` build, the CVE tests and the
  differentials on the fetched corpus, the native C API's tests, and
  `cargo publish --dry-run`;
- **mbedtls**: mbedTLS 3.6.4's test suites with the patch, which must pass
  except for the 18 documented x509parse cases;
- **fuzz**: five minutes per fuzz target under AddressSanitizer.

## Verifying

Install Verus at commit `8bf68ee` (release 0.2026.11.02.8bf68ee; Rust
1.99.1), then:

```sh
cargo verus verify
```

## Next steps

1. Benchmark against Verdict.
2. Prove the mbedTLS adapter's field copies, so that the spans it hands to
   mbedTLS are the spec's.
3. Report upstream that mbedTLS accepts a `[2]`-tagged serial number and an
   explicit v1 version.
4. CRLs and CSRs, which mbedTLS still parses itself.
