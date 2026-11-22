# verilith-x509 inside mbedTLS

This directory makes verilith-x509 the certificate decoder behind mbedTLS's
`mbedtls_x509_crt_parse_der` (and so behind `mbedtls_x509_crt_parse`,
`_parse_file`, `_parse_path`, the TLS handshake and PKCS#7). The C API and
`mbedtls_x509_crt` struct are unchanged, so applications relink and nothing
else.

Tested against mbedTLS 3.6.8.

## Build

```sh
# 1. The static library with the C ABI.
cd verilith/crates/x509
cargo build --profile release-fat --features mbedtls

# 2. mbedTLS with the 20-line patch.
cd ../../../mbedtls
git apply ../verilith/crates/x509/mbedtls/mbedtls-use-vx509.patch
cmake -B build-vx -DMBEDTLS_VX509_DIR=$PWD/../verilith/crates/x509 \
  -DMBEDTLS_VX509_LIB=$PWD/../verilith/target/release-fat/libverilith_x509.a
cmake --build build-vx -j
cd build-vx && ctest
```

Without `-DMBEDTLS_VX509_DIR` the patched tree builds stock mbedTLS.

`run-tests.sh <mbedtls checkout>` does all of this and checks that the only
failures are the ones listed in `expected-x509parse-failures.txt` (with test
names cut where mbedTLS's runner cuts them).

## What runs where

| Step | Code |
|---|---|
| Framing, every length, tag and DER rule; TBSCertificate structure; version, serial, validity times, Names, unique IDs; every extension's syntax (BasicConstraints, KeyUsage, EKU, SAN, SKI, AKI, certificatePolicies, NameConstraints, IAN) and duplicate detection; signatureAlgorithm equality | verilith-x509, verified (`src/cert.rs` and below). Proven to compute exactly the spec in `src/spec.rs`. |
| Picking out each field the adapter copies: every Name attribute (and whether it continues a multi-valued RDN), every extension's OID, criticality and value, and the decoded contents of BasicConstraints, KeyUsage, EKU, SAN, IAN, SKI, AKI and certificatePolicies | verilith-x509, verified. As it checks the certificate, the parser hands each attribute and each extension to a sink (`AtvSink`, `ExtSink`), and is proven to hand over exactly the spec's attributes and extensions, in order, each extension with what its value decodes to (`parse_rec`'s postcondition, `ext_log_ok`). The adapter's sinks (`src/mbedtls.rs`, unverified) store them as pointer and length pairs for the C code: up to 10 extensions and 8 attributes per Name. Beyond that the adapter falls back to walking the spans itself. |
| Copying those slices into `mbedtls_x509_crt` (name lists, sequences, bit masks) | `vx509_mbedtls.c`, C, and the C ABI in `src/mbedtls.rs`, which turns slices into pointer and length pairs and frames list items (the entries of ExtKeyUsage, SubjectAltName and certificatePolicies, up to 24 per certificate in one go) inside values the verified parser accepted. |
| Public key decoding (`mbedtls_pk_parse_subpubkey`), signature algorithm table (`mbedtls_x509_get_sig_alg`), per-SAN-entry policy (`mbedtls_x509_parse_subject_alt_name`), extension and policy callbacks | mbedTLS, unchanged, called on spans verilith-x509 already validated. |
| Error codes when a certificate is rejected | `src/mbedtls_err.rs`, unverified safe Rust that reproduces mbedTLS's error for the input. It runs only after the verified parser has said no, so it can change *which* error is returned but never *whether* a certificate is accepted. |

## Test results (mbedTLS 3.6.8, `ctest` in `build-vx`)

Every suite passes except `x509parse`, at 870 of 888. `x509write` (80),
`pkcs7` (821), `ssl` (999) and `debug` (36) all pass, and so does every
error-code test in `x509parse`.

The 18 remaining cases are certificates mbedTLS accepts and verilith-x509 rejects on
purpose. They are built from one synthetic template in the test data that is
not valid X.509:

| Vectors | Why verilith-x509 rejects |
|---|---|
| `X509 CRT ASN1 (well-formed)`, the two mixed `GeneralizedTime`/`UTCTime` cases, the nine `Name with X520 …`/`PKCS9 …` cases | `version` is written explicitly as v1 (`a0 03 02 01 00`). DER forbids encoding a DEFAULT value (X.690 §11.5), and RFC 5280 §4.1.2.1 says v1 omits it. The same template also has an empty OID (`06 00`) and UTCTime without seconds or `Z`, both invalid under RFC 5280 §4.1.2.5.1. |
| `X509 CRT (TBS, valid v3Ext in v3 CRT)`, `empty Signature`, `dummy 24-bit Signature`, and the three `Unsupported … policy … by callback` cases | The serial number is tagged `[2]` (`82 04 de ad be ef`) instead of INTEGER. mbedTLS accepts that tag; RFC 5280 §4.1.2.2 requires INTEGER. |

`examples/mbedtls_cases.rs` reproduces this list from the test data:

```sh
cargo run --profile release-fat --example mbedtls_cases mbedtls/tests/suites/test_suite_x509parse.data
```

The two cases it lists as "verilith-x509 accepts where mbedTLS rejects" (unsupported
critical extensions) are rejected by the adapter, which applies mbedTLS's
policy of failing on a critical extension it does not know, so the suite
passes them.

See [`../DEPARTURES.md`](../DEPARTURES.md) for the rest of verilith-x509's strict and
lenient choices.
