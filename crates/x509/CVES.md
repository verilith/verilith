# verilith-x509 against X.509 and DER parsing CVEs

Each CVE below is a bug in another certificate parser: OpenSSL, NSS, Windows
CryptoAPI, or PolarSSL (now mbedTLS). For each one, the table gives the
proven verilith-x509 property that rules out that bug class for every input, and a
test in `tests/cves.rs` that builds a certificate of the attack's shape and
checks how verilith-x509 handles it, including the reason it gives for rejecting it.
Run them with `cargo test --profile release-fat --test cves`.

Two properties hold for every input and cover several rows at once:

- **No out-of-bounds access and no arithmetic overflow.** Verus checks every
  index and every addition in the verified parser.
- **No allocation and no copies.** The parser returns slices of the input.
  The crate builds `no_std` without `alloc` (it is checked on
  `thumbv7em-none-eabihf`), so it has no heap to corrupt and no buffer to
  overflow.

| CVE | Where | Bug | Why verilith-x509 is not affected (proven) | Test |
| --- | --- | --- | --- | --- |
| CVE-2014-1569 | NSS < 3.17.3 | `definite_length_decoder` accepted non-minimal long-form lengths, so data could be smuggled into signed structures to forge certificates | Lengths must be minimal: short form below 128, long form only with no leading zero octet, at most 4 octets, never indefinite (`parse_len` in the spec) | `cve_2014_1569_and_2012_2110_lengths` |
| CVE-2012-2110 | OpenSSL | Length arithmetic in `asn1_d2i_read_bio` overflowed, then a heap buffer overflowed | Length arithmetic is overflow-checked, every length is checked against the input before use, and nothing is allocated | same test: lengths up to 2³²−1 and 5-octet lengths |
| CVE-2009-2511 | Windows CryptoAPI (MS09-056) | An OID arc padded with `0x80` octets, or too large for 32 bits, decoded to a different OID such as commonName, so a CA-signed certificate could spoof a name | OIDs must have minimal arcs (no `0x80` at the start of an arc) and are compared as bytes, never converted to integers, so two OIDs are equal exactly when their encodings are | `cve_2009_2511_oid_arcs`: a padded `2.5.4.3` is rejected; `2.5.4.(2⁶⁴+3)` is its own OID |
| CVE-2009-2408, CVE-2009-2510 | NSS; Windows CryptoAPI | A NUL in a name (`www.bank.com\0.evil.com`) matched as the part before it | rfc822Name, dNSName and URI must be 7-bit with no NUL (`valid_ia5_name`) | `cve_2009_2408_and_2510_nul_in_names` (see the CN caveat below) |
| CVE-2020-1971, CVE-2023-0286 | OpenSSL | `GENERAL_NAME_cmp` handled EDIPartyName (NULL dereference) and x400Address (type confusion) as the wrong type | Each GeneralName choice decodes to its own variant of an enum, and the context tags must be in the form the choice requires | `cve_2020_1971_and_2023_0286_general_name_choices` |
| CVE-2021-3712 | OpenSSL | Code assumed ASN.1 strings were NUL-terminated and read past their end | Strings are slices with their own length; no read goes past a TLV's contents | `cve_2021_3712_and_2015_1182_truncations`: every prefix of a certificate is rejected |
| CVE-2015-1182 | PolarSSL ≤ 1.3.9 | An error inside a SEQUENCE OF in a certificate freed an uninitialized pointer | Nothing is allocated or freed; a malformed list is a rejection | same test: an error in the middle of ExtendedKeyUsage, SubjectAltName and certificatePolicies |
| CVE-2015-1789 | OpenSSL | `X509_cmp_time` read out of bounds on a malformed time | Times must be exactly `YYMMDDHHMMSSZ` or `YYYYMMDDHHMMSSZ`, with a valid month, day (leap years included), hour, minute and second | `cve_2015_1789_times` |
| CVE-2016-2108 | OpenSSL | A negative-zero INTEGER corrupted memory when re-encoded | INTEGERs must be minimal, and verilith-x509 never re-encodes | `cve_2016_2108_and_2014_8275_non_der` |
| CVE-2014-8275 | OpenSSL | Non-DER encodings changed a certificate's fingerprint without breaking its signature | signatureAlgorithm must equal the TBSCertificate's signature byte for byte, BIT STRING padding must be zero, lengths and INTEGERs minimal, v1 not encoded. BOOLEAN is the exception: see DEPARTURES.md | same test |
| CVE-2023-2650 | OpenSSL | `OBJ_obj2txt` took super-linear time on very long OIDs | OIDs are checked in one pass and never converted in the verified parser | `cve_2023_2650_long_oids`: a 200 KB OID |
| CVE-2021-43527 | NSS ("BigSig") | An oversized signature was copied into a fixed-size stack buffer | The signature is a slice of the input; nothing is copied | `cve_2021_43527_big_signature`: a 64 KB signature |

Not tied to one CVE, but `duplicate_extensions` checks that a repeated
extension is rejected (RFC 5280 §4.2), since parsers that keep the first and
parsers that keep the last disagree on what the certificate says.

## What this does not cover

- **commonName.** Attribute values in Names are kept as raw bytes, so a NUL
  in a CN is accepted. Match host names against subjectAltName, as RFC 6125
  says; verilith-x509 checks those.
- **Public keys.** verilith-x509 checks that the SubjectPublicKeyInfo is well formed
  but does not decode keys. Bugs in key parsing, such as CurveBall
  (CVE-2020-0601, explicit curve parameters in CryptoAPI), belong to
  whatever decodes the key. In the mbedTLS drop-in that is still mbedTLS's
  `mbedtls_pk_parse_subpubkey`.
- **Chain validation.** Name constraints, policy trees (OpenSSL
  CVE-2023-0464), punycode in name constraints (CVE-2022-3602, CVE-2022-3786)
  and signature checks happen after parsing.
- **Other parsers in mbedTLS.** The drop-in replaces certificate parsing
  only. CRLs (CVE-2020-36426 was a one-byte over-read in
  `mbedtls_x509_crl_parse_der`), CSRs, PEM and `mbedtls_x509_string_to_names`
  are unchanged. Code that walks `crt->v3_ext` itself, as Trusted Firmware-A
  did (CVE-2022-47630), gets a list verilith-x509 has proven well formed, but its own
  decoding is outside verilith-x509.
- **The trusted base.** The guarantees assume the spec (`src/spec.rs`) says
  what X.690 and RFC 5280 say, and that Verus, Z3 and rustc are correct.
  `src/api.rs`, `src/error.rs`, `src/mbedtls.rs`, `src/mbedtls_err.rs` and
  `mbedtls/vx509_mbedtls.c` are unverified. None of them decides whether a
  certificate is accepted.

## Sources

- CVE-2014-1569: <https://bugzilla.mozilla.org/show_bug.cgi?id=1064670>
- CVE-2012-2110: <https://www.openssl.org/news/secadv/20120419.txt>
- CVE-2009-2511: <https://learn.microsoft.com/en-us/security-updates/securitybulletins/2009/ms09-056>
- CVE-2009-2408: <https://nvd.nist.gov/vuln/detail/CVE-2009-2408>
- CVE-2009-2510: <https://nvd.nist.gov/vuln/detail/CVE-2009-2510>
- CVE-2020-1971: <https://www.openssl.org/news/secadv/20201208.txt>
- CVE-2023-0286: <https://www.openssl.org/news/secadv/20230207.txt>
- CVE-2021-3712: <https://www.openssl.org/news/secadv/20210824.txt>
- CVE-2015-1182: <https://security-tracker.debian.org/tracker/CVE-2015-1182>
- CVE-2015-1789: <https://www.openssl.org/news/secadv/20150611.txt>
- CVE-2016-2108: <https://www.openssl.org/news/secadv/20160503.txt>
- CVE-2014-8275: <https://www.openssl.org/news/secadv/20150108.txt>
- CVE-2023-2650: <https://www.openssl.org/news/secadv/20230530.txt>
- CVE-2021-43527: <https://www.mozilla.org/en-US/security/advisories/mfsa2021-51/>
- CVE-2020-36426: <https://bugzilla.redhat.com/show_bug.cgi?id=1984521>
- CVE-2022-47630: <https://trustedfirmware-a.readthedocs.io/en/v2.9/security_advisories/security-advisory-tfv-10.html>
