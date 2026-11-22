# Departures

Where verilith-x509 is stricter or more lenient than "whatever parses", and why. Each
choice is part of the spec in `src/spec.rs`, so the proofs cover it.

## Stricter than common parsers

- **DER lengths are minimal.** Short form below 128; long form `81`–`84` with
  no leading zero octet and no long form for short lengths. No indefinite
  lengths.
- **INTEGERs are minimal** (no redundant leading `00` or `FF`), including the
  serial number.
- **OIDs are non-empty with minimal arcs** (no leading `80` octet).
- **version is omitted for v1.** An explicit `[0] INTEGER 0` is a DEFAULT
  value encoded, which DER forbids. Only v2 and v3 may be explicit.
- **Unique IDs are not allowed in v1**, and extensions only in v3. The
  extensions list, when present, is non-empty.
- **signatureAlgorithm must equal TBSCertificate.signature**, byte for byte
  (RFC 5280 §4.1.1.2).
- **Extension OIDs are distinct** (RFC 5280 §4.2).
- **Times** are `YYMMDDHHMMSSZ` (UTCTime) or `YYYYMMDDHHMMSSZ`
  (GeneralizedTime), with valid month, day (leap years included), hour,
  minute and second (RFC 5280 §4.1.2.5).
- **IA5String names** (rfc822Name, dNSName, URI) reject NUL and octets above
  127.
- **iPAddress** is 4 or 16 octets, or 8 or 32 inside NameConstraints.
- **RelativeDistinguishedNames are non-empty.**
- **Decoded extensions must be well formed**: BasicConstraints,
  KeyUsage, ExtKeyUsage (non-empty), SubjectAltName and IssuerAltName
  (non-empty), SubjectKeyIdentifier, AuthorityKeyIdentifier,
  certificatePolicies (non-empty), NameConstraints (at least one of
  permitted or excluded, each non-empty, no minimum or maximum). Other
  extensions are kept as opaque OCTET STRINGs.

## More lenient than strict DER

- **BOOLEAN accepts any non-zero octet as TRUE**, and an explicit FALSE for
  `critical` and `cA`. X.690 §8.2 (BER) allows both; DER does not. mbedTLS's
  own test certificates use `cA = 01` and explicit `critical FALSE`, and
  OpenSSL and mbedTLS accept them.
- **KeyUsage may carry zero octets past the second.** Some issuers pad it.
  The mask is unchanged.
- **Serial numbers have no length limit.** RFC 5280 says 20 octets, but real
  certificates exceed it and every parser in the differential test accepts
  them.
- **Attribute values in Names are kept raw**, whatever their string type. The
  `api` layer decodes the common ones.

## mbedTLS drop-in

The mbedTLS adapter rejects 18 test-suite certificates mbedTLS accepts. They
come from one synthetic template that is not valid X.509 (explicit v1, a
`[2]`-tagged serial, an empty OID, UTCTime without seconds). See
[`mbedtls/README.md`](mbedtls/README.md).
