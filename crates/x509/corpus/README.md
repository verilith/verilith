# Differential corpus

`tests/differential.rs` compares verilith-x509 with OpenSSL, x509-parser, x509-cert
and webpki on every certificate in a directory named by `VX509_CORPUS`:

```sh
corpus/fetch.sh /tmp/vx509-corpus
VX509_CORPUS=/tmp/vx509-corpus/der cargo test --profile release-fat --test differential -- --nocapture
```

The corpus is every certificate in

- [x509-limbo](https://github.com/C2SP/x509-limbo)'s `limbo.json`, a test
  suite for path validation with many deliberately malformed certificates,
- pyca/cryptography's test vectors (`cryptography_vectors` 50.0.2), including
  NIST PKITS,
- the system trust store,

deduplicated, about 31,000 certificates. `sources.json`, written next to
`der/`, says where each file came from.

The `fields_agree` test checks that on every certificate verilith-x509 and the other
parsers both accept, they decode the same version, serial, names, validity,
key, signature and extensions. On the 30,433 certificates where that applies
there are 0 disagreements. `accept_reject` prints which parsers accept which
certificates; the certificates only verilith-x509 rejects are listed, with reasons,
in [`DEPARTURES.md`](../DEPARTURES.md).
