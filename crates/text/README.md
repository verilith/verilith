# verilith-text

Text encodings and Unicode in Rust, formally verified with
[Verus](https://github.com/verus-lang/verus):

- **Unicode normalization**: NFC, NFD, NFKC and NFKD (UAX #15), Unicode 18.0.
- **IDNA**: Punycode (RFC 3492) and UTS #46 ToASCII and ToUnicode, with the
  URL Standard's domain to ASCII.
- **Base64** (RFC 4648 §4 and §5), **hex** and **percent-encoding**, with
  AVX2 kernels for base64 and hex, and WHATWG forgiving-base64 decoding.
- **Transcoding** between UTF-8, UTF-16 and Latin-1, with UTF-8 validation
  and output-length counts, with AVX2 kernels. Behind a C API and verilith-bind's
  `simdutf.h`, this replaces simdutf in Node.js.

Each one has a spec written from its standard, and the implementation is
proven to compute exactly that spec on every input. Unlike a fast path that
was only tested, a proven fast path cannot get an input wrong. The public
APIs follow the crates they replace: `unicode-normalization` and
`icu_normalizer`, `idna`, `base64`, `hex` and `percent-encoding`. The
transcoding C API follows simdutf.

## Using it from Rust

```rust
use verilith_text::{base64, hex, idna, percent, unicode};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Unicode normalization, as unicode-normalization or icu_normalizer.
    assert_eq!(unicode::nfc("e\u{301}"), "\u{e9}");
    assert!(unicode::is_nfd("e\u{301}"));

    // IDNA, as the idna crate.
    assert_eq!(idna::domain_to_ascii("bücher.example")?, "xn--bcher-kva.example");
    assert_eq!(idna::domain_to_unicode("xn--bcher-kva.example").0, "bücher.example");

    // base64, hex and percent-encoding, as the crates of the same names.
    assert_eq!(base64::STANDARD.encode(b"hello"), "aGVsbG8=");
    assert_eq!(base64::STANDARD.decode("aGVsbG8=")?, b"hello");
    assert_eq!(hex::encode(b"hi"), "6869");
    assert_eq!(hex::decode("6869")?, b"hi");
    assert_eq!(percent::percent_encode(b"a b\n", percent::CONTROLS).to_string(), "a b%0A");
    assert_eq!(percent::percent_decode_str("a%20b").decode_utf8()?, "a b");
    Ok(())
}
```

The transcoding functions (`utf8_to_utf16` and the rest) are a C API with
simdutf's names, `include/vtext_utf.h`.

## What is proven

**Normalization** (`src/unicode`). `spec.rs` transliterates UAX #15:

- full canonical or compatibility decomposition;
- the canonical ordering algorithm as a stable insertion fold;
- canonical composition with the "blocked" rule (D115, D117);
- algorithmic Hangul.

`norm::normalize_into` is proven to append `enc(nf(cs, compose, compat))`,
where `cs` are the input's scalars. `norm::quick_check` returning true is
proven to imply `nf(cs) == cs`, which is what lets `normalize` return the
input borrowed.

The implementation works on UTF-8 directly. It skips runs of ASCII eight
bytes at a time, copies through characters whose data says they are stable,
and splits the text into segments at boundary characters. The theorem that
makes that sound is `lemma_nf_split`: `nf(x + y) == nf(x) + nf(y)` when `y`
starts with a boundary character, proven from the spec.

**Punycode** (`src/idna/punycode.rs`). The spec is RFC 3492 sections 6.2 and
6.3. Integers are bounded by `u32::MAX`, as in the `idna` crate: any step
that would overflow fails. `decode_into` and `encode_into` are proven equal
to the spec, failures included, and every decoded code point is proven to be
a scalar.

**UTS #46** (`src/idna/spec.rs`, `src/idna/uts46.rs`). The spec transliterates
sections 4 to 4.2:

- Map, including Transitional_Processing.
- Normalize, reusing the NFC spec above.
- Break, then Convert/Validate, with every validity criterion.
- CheckJoiners, as RFC 5892 Appendix A.1 and A.2.
- CheckBidi, as RFC 5893 section 2 over Bidi domain names.
- ToASCII, including VerifyDnsLength.

`process_exec` (ToUnicode) and `to_ascii_exec` are proven equal to the spec.

`lemma_fast_checked` proves that an ASCII domain name passing every check
that the flags turn on is only lowercased by both. The checks cover:

- no `--` anywhere;
- labels that do not begin or end with a hyphen;
- only letters, digits and hyphens;
- 1 to 63 characters per label, 253 in all.

`ascii_checked` makes those checks, and is the fast path that
`to_ascii_fast` and the C API take for any flags. `lemma_fast` is the
special case for the URL Standard's flags, where only `--` matters, and
`ascii_unchanged` uses it.

`url_domain_to_ascii_exec` is proven to compute the URL Standard's host
parser step, which lowercases ASCII domains and runs ToASCII on all others.

Two limits differ from UTS #46, as they do in the `idna` crate, because
Punycode is quadratic (whatwg/url#824). A label whose Punycode part is over
2000 bytes is an error, and so is a non-ASCII label of over 1000 code points
in ToASCII.

**Base64, hex, percent-encoding**:

- Base64: `decode` is proven to accept exactly the canonical encodings
  (`lemma_decode_iff_encode`). The scalar and AVX2 codecs are proven to
  compute `encode` and `decode`.
- Hex: `decode(encode(x)) == Some(x)` in both cases is proven, and whatever
  `decode` accepts is an encoding of its result up to the case of each
  digit.
- Percent-encoding: when the set contains `%`, `decode(encode(set, x)) == x`
  is proven, and no byte that `encode` leaves alone is in the set or
  non-ASCII.
- The AVX2 kernels are proven against verilith-simd's specifications of the
  intrinsics.

**Transcoding** (`src/utf`). `spec.rs` defines UTF-8 decoding one character
at a time (`dec8_at`, Unicode Table 3-7, so overlongs, surrogates and values
above U+10FFFF are rejected), UTF-16 decoding with surrogate pairs, and
Latin-1, then each conversion as a fold over the input: `u8to16`, `u16to8`,
`u8tol1`, `l1to8`, and their lengths `cnt8`, `cnt16`, `cnt8l1`, `cnt_l1`.
`lemma_dec8_roundtrip` and `lemma_dec16_roundtrip` prove the decoders invert
the encoders.

- `valid8::utf8_valid` is proven to return exactly whether the input is
  UTF-8. Its AVX2 kernel is the three-table lookup validator that simdjson
  and simdutf use, proven against verilith-simd's intrinsic specs (`lemma_lookup`
  ties the tables to the byte classes of Table 3-7).
- `conv::utf8_to_utf16`, `utf16_to_utf8`, `utf8_to_latin1`, `latin1_to_utf8`,
  `latin1_to_utf16` and `utf16_to_latin1` are proven to fail exactly on
  invalid input and otherwise to write exactly the spec's output, given an
  output buffer of the spec's length. `latin1_to_utf8_safe` writes the
  longest prefix that fits.
- `count_utf8`, `count_utf16` and `count_latin1_utf8` are proven to compute
  the output lengths, which is what makes buffers sized by them safe.
- ASCII runs take AVX2 kernels (`avx2.rs`: 32-byte ASCII checks, widening
  bytes to 16-bit units and narrowing back), proven like the rest. Other
  characters are converted one at a time.

**Forgiving base64** (`src/base64/forgiving.rs`). `forgiving` transliterates
the WHATWG Infra forgiving-base64 decode (which `atob` and Node's base64
decoding follow): ASCII whitespace is removed, up to two trailing `=` are
allowed only where they complete a group, a single leftover character is
an error, and the bits left over at the end are ignored. `decode_forgiving`
is proven to return its bytes or its error (invalid character or remainder),
and never "buffer too small" for a buffer of `max_len` bytes. Whitespace-free
input goes through the verified AVX2 decoder above.

**Everywhere.** The verified code is memory safe: every index is proven in
bounds and no arithmetic can overflow. Every loop and recursion is proven
to terminate. There are no `admit`s or `assume`s.

## C API

`include/vtext_icu.h` declares a C API shaped like ICU4C's `unorm2.h` and
the UTS #46 part of `uidna.h`: `unorm2_getNFCInstance` (and NFD, NFKC,
NFKD), `unorm2_normalize`, `unorm2_isNormalized`, `unorm2_quickCheck`,
`uidna_openUTS46`, `uidna_close`, `uidna_nameToASCII`, `uidna_nameToUnicode`
and their `_UTF8` forms. They take ICU's arguments and options and follow its
conventions: -1 for NUL-terminated input, preflighting with
`U_BUFFER_OVERFLOW_ERROR`, NUL termination when there is room, and doing
nothing when `*pErrorCode` is already a failure.

Each function is exported as `vtext_` plus its ICU name. With the `icu-abi`
feature, the static library also exports ICU's own names, so a program built
against ICU with `U_DISABLE_RENAMING=1` can link verilith-text instead.

The C layer in `src/capi.rs` is not verified. It converts between UTF-16 or
UTF-8 and the verified functions, which compute the results. Some behavior
follows ICU rather than UTS #46:

- ICU always checks hyphens, and checks DNS lengths in ToASCII.
- It allows a trailing root label under VerifyDnsLength.
- It reports an empty label in ToUnicode too.

`unorm2_quickCheck` never answers `UNORM_MAYBE`. The `UIDNAInfo.errors` bits
are worked out per label and match ICU's in 87% of error cases. Whether
there is an error at all always matches.

`./scripts/icu_diff.sh` diffs the C API against the system's ICU 74 (Unicode
15.1). It first runs every assigned character through both on its own. The
71 characters whose IDNA data changed after Unicode 15.1 (for example the
Georgian capitals U+10A0..U+10C5, and Hangul fillers that are now ignored)
are printed and left out of the random part. On 2 million random strings,
which is 8 million normalizations and 16 million IDNA calls, there is no
difference.

One ICU quirk is skipped: ICU looks for `--` in the third and fourth UTF-16
code units of a label rather than code points. The two disagree when a
supplementary character comes first.

Speed, against ICU 74's C library (`bench/c/capi_bench.c`, same machine as
below):

| | ICU 74 | verilith-text |
|---|---:|---:|
| `uidna_nameToASCII_UTF8` `www.example.com` | 42 ns | 49 ns |
| `uidna_nameToASCII_UTF8` `münchen.de` | 429 ns | 391 ns |
| `uidna_nameToASCII_UTF8` `例子.测试` | 468 ns | 437 ns |
| `unorm2_normalize` NFC, French, 64 KB | 4.66 GB/s | 3.85 GB/s |
| `unorm2_normalize` NFC, Vietnamese | 3.76 GB/s | 0.91 GB/s |
| `unorm2_normalize` NFC, Greek | 0.70 GB/s | 0.28 GB/s |
| `unorm2_normalize` NFD, French | 0.86 GB/s | 0.30 GB/s |
| `unorm2_normalize` NFD, Korean | 0.21 GB/s | 0.08 GB/s |

IDNA is level with ICU. UTF-16 normalization is 2.5 to 4 times slower,
because the verified code works on UTF-8 and the C layer converts in both
directions. Those conversions are now the verified transcoders above, with
AVX2 for ASCII runs, instead of hand-written loops; the figures are from
before that change. Through the C API,
UTF-8 normalization is the faster option, as the Rust table below shows.

### The simdutf API

`include/vtext_utf.h` declares simdutf's validation, length, conversion and
base64 functions, the ones Node.js and V8 call, under a `vtext_` prefix
(`vtext_validate_utf8_with_errors`, `vtext_convert_utf8_to_utf16`,
`vtext_base64_to_binary_safe`, and so on). A `simdutf::result` comes back as
its error code, with the count written through a pointer. verilith-bind's
`include/simdutf.h` wraps them in simdutf 7.7's C++ signatures, so Node 26
builds against verilith-text with `--shared-simdutf` and no patch.

The glue in `src/capi_utf.rs` is not verified. Most of it makes slices of the
caller's buffers, sized by the verified counts, calls the verified
functions, and reproduces simdutf's error reports: the position and kind of
the first UTF-8 error (`utf8_error`, transliterated from simdutf's scalar
code) and of the first non-Latin-1 character. Three parts of it do work of
their own, with no proof behind them:

* **Base64 outside the forgiving decoder.** A `loose` decode of valid text
  into a buffer that holds it is the verified decoder's, and that is every
  decode Node's `Buffer` and `atob` make. The `strict` and
  `stop_before_partial` last-chunk modes of `Uint8Array.fromBase64`,
  decoding the bytes before an invalid character (which V8 asks for), and
  decoding into a buffer that is too small (`setFromBase64` on a short
  array) go through `b64_details`, a transliteration of simdutf's scalar
  decoder.
* **UTF-16 well-formedness**: `validate_utf16`, `to_well_formed_utf16` and
  `utf8_length_from_utf16_with_replacement`, loops that look for unpaired
  surrogates.
* **`convert_utf32_to_utf8`**, which Node's CommonJS lexer calls one code
  point at a time; it is Rust's `char::encode_utf8`.

verilith-bind's `tests/cpp/run.sh` diffs every one of these functions against
simdutf 7.7.0 on 50,000 seeded cases (3.6 million calls). The only
differences are 42 base64 texts that both sides reject, with a `=` in the
wrong place: simdutf's chunked path calls that `BASE64_INPUT_REMAINDER`
where its own one-pass decoder, and verilith-text, call it
`INVALID_BASE64_CHARACTER`. The bytes written before the error are the same.

simdutf's `accept_garbage` options are not there. Node does not use them.

**CPU support.** The kernels are AVX2 on x86-64 and NEON on AArch64
(Apple Silicon, Graviton). The NEON kernels (`src/utf/neon.rs` and the
NEON half of `src/utf/valid8.rs`) cover UTF-8 validation and the ASCII,
widening and narrowing paths of the transcoders, built from verilith-simd's NEON
specs and proven under the same contracts as the AVX2 ones. Base64, hex
and the remaining paths take their verified scalar code on ARM, as does
every function on other CPUs.

## The trusted base

These are what the proofs take on trust:

- **Unicode data.** The tables in `src/unicode/tables.rs` and
  `src/idna/tables.rs` are generated from the Unicode 18.0 UCD by
  `tools/gen_unicode.py` and `tools/gen_idna.py`. The proofs see each table
  as an uninterpreted function, read through a one-line `external_body`
  accessor (`*_at`).
- **Axioms about that data.** These are the `axiom_*` functions in
  `unicode/data.rs`, `unicode/spec.rs` and `idna/data.rs`. Examples are "the
  trie's blocks are in bounds", "decompositions are scalars in canonical
  order" and "ASCII characters are stable".
  `tests/unicode_data.rs` and `tests/idna_data.rs` check every table entry
  against the UCD files, parsed again independently, and check every axiom
  for every code point.
- **Glue.** The C APIs in `capi.rs` and `capi_utf.rs`, as described above. The `&str`
  wrappers in `unicode/mod.rs` and `idna/mod.rs` pass `Ghost::assume_new()`
  for the scalars a `&str` holds, which is the UTF-8 guarantee of `&str`.
  They also turn verified ASCII or UTF-8 output back into `String`s.
- **Target-feature trampolines.** Verus rejects `#[target_feature]` on
  verified code (verus-lang/verus#3362). Each AVX2 entry point (the
  `*_avx2` transcoders and counters in `utf/conv.rs`, `utf8_avx2` in
  `utf/valid8.rs`, and `encode_bulk`/`decode_bulk` in `base64/avx2.rs` and
  `hex/avx2.rs`) is an `external_body` wrapper that, on x86-64, calls a
  one-line `unsafe` trampoline in its file's `mod tf`, which carries the
  attribute and calls the verified `*_body` function. The contract is
  `*_body`'s, checked by Verus, and requires `avx2()`, so callers prove the
  CPU check. What is trusted is that the two calls forward.
- **Dependencies.** verilith-core's `prims` (unchecked reads and `extend`) and
  verilith-simd's intrinsic specifications, plus Verus, Z3 and rustc.

## Tests

`cargo test --profile release-fat` runs:

- `tests/normalization.rs`: all of NormalizationTest.txt, through both the
  fast implementation and the reference one. It also diffs against
  `unicode-normalization` (300k random strings, all four forms and the
  `is_*` checks) and `icu_normalizer` (100k strings).
- `tests/idna.rs`: all of IdnaTestV2.txt, twice:
  - with the conformance flags (everything checked);
  - with the URL Standard's flags, ignoring the status codes of the checks
    that are off, as the file says.

  It also runs all of WPT's `toascii.json`, and diffs against the `idna`
  crate on 300k random domain names. The one difference the diff skips is
  criterion V4: a decoded label must not begin with `xn--`. The `idna` crate
  does not check V4 when CheckHyphens is off, but IdnaTestV2 lists V4
  separately from the CheckHyphens codes.
- `tests/punycode.rs`: RFC 3492's samples, plus 200k random labels against
  the `idna` crate, round trips, and mutated encodings.
- `tests/encodings.rs`: base64 (every engine, encode, decode and the error
  kinds), hex and percent-encoding against their crates on random and
  near-valid inputs.
- `tests/unicode_data.rs` and `tests/idna_data.rs`: the tables and axioms,
  as above.
- `tests/utf.rs`: every converter, validator and count against the standard
  library's UTF-8 and UTF-16 handling, on random and mutated text in each
  encoding.
- `tests/forgiving.rs`: forgiving base64 against a separate transcription
  of the WHATWG algorithm on 300k random and damaged inputs.
- `tests/capi.rs`: the C API's conventions. It also checks the facts behind
  its UTF-16 fast path against the UCD: below U+0300 (NFC), U+00C0 (NFD) or
  U+00A0 (NFKC, NFKD), a character is stable and never ends a composition.

`./scripts/icu_diff.sh` diffs the C API against the system's ICU, as
described above.

## Speed

Measured with `cd bench && cargo run --profile release-fat` (plus `-- norm` and
`-- idna`). Each figure is the best of 15 runs, on a shared 4-vCPU Intel
Xeon at 2.8 GHz with rustc 1.97.0. The VM is noisy, so differences under
about 10% are not meaningful.

The reference crates are `base64` 0.22.1, `base64-simd` 0.8.0, `hex` 0.4.3,
`faster-hex` 0.10.1, `percent-encoding` 2.3.2, `unicode-normalization`
0.1.26, `icu_normalizer` 2.4.0 and `idna` 1.1.0.

**Normalization**, 64 KB of text, GB/s:

| sample     | form | verilith-text | icu_normalizer | unicode-normalization |
|------------|------|------:|---------------:|----------------------:|
| ASCII      | NFC  | 16.8  | 1.38 | 0.07 |
| French     | NFC  | 2.19  | 1.37 | 0.06 |
| French     | NFD  | 0.46  | 0.42 | 0.09 |
| French NFD | NFC  | 0.30  | 0.20 | 0.07 |
| French NFD | NFD  | 1.82  | 0.56 | 0.11 |
| Vietnamese | NFC  | 1.38  | 1.49 | 0.06 |
| Greek      | NFC  | 1.11  | 0.69 | 0.09 |
| Korean     | NFC  | 1.23  | 0.89 | 0.09 |
| Korean     | NFD  | 0.18  | 0.19 | 0.12 |
| Hindi      | NFC  | 0.53  | 0.41 | 0.15 |
| Hindi      | NFD  | 1.22  | 0.63 | 0.21 |

verilith-text is ahead or level everywhere except Vietnamese NFC, where it is 7%
behind.

**IDNA**, nanoseconds per call:

| domain | verilith-text `domain_to_ascii_cow` | idna | verilith-text `domain_to_unicode` | idna |
|--------|------:|------:|------:|------:|
| `www.example.com` | 10 | 16 | 22 | 23 |
| `static-assets.cdn.subdomain.example-company.co.uk` | 27 | 78 | 45 | 85 |
| `WWW.Example.COM` | 32 | 129 | 38 | 128 |
| `münchen.de` | 277 | 242 | 230 | 181 |
| `例子.测试` | 342 | 292 | 170 | 187 |
| `مثال.إختبار` (bidi) | 460 | 437 | 239 | 302 |
| `ｅｘａｍｐｌｅ．ｃｏｍ` | 272 | 363 | 242 | 362 |

For ASCII `xn--` domains, `domain_to_ascii` follows the current URL
Standard and only lowercases, while `idna` 1.1.0 still decodes and validates
them. So `xn--mnchen-3ya.de` takes 22 ns against 180 ns, which compares
different work.

**Encodings**, GB/s at 1 KB / 64 KB:

| | verilith-text | reference | SIMD reference |
|---|---:|---:|---:|
| base64 encode (`encode_slice`) | 9.3 / 10.6 | 2.3 / 2.3 | 8.9 / 9.4 (base64-simd) |
| base64 decode (`decode_slice`) | 11.9 / 14.1 | 2.4 / 2.4 | 8.8 / 9.2 (base64-simd) |
| hex encode | 9.8 / 11.9 | 0.36 / 0.37 | 8.5 / 10.7 (faster-hex) |
| hex decode | 13.3 / 17.9 | 0.48 / 0.52 | 6.3 / 6.9 (faster-hex) |
| percent encode | 0.96 / 0.99 | 0.77 / 0.97 | |
| percent decode | 1.15 / 1.21 | 0.96 / 1.11 | |

At 64 bytes, base64-simd is still ahead: 2.6 against 1.8 GB/s to encode, and
4.7 against 3.4 to decode.

## Verifying

`./scripts/verify.sh` runs `cargo verus verify`. It needs Verus at commit
`8bf68ee741df833ea5d0fe6a2255126fdea87e47`, whose vstd matches the one
pinned in `Cargo.toml`. The proofs take about 40 seconds.

To regenerate the tables after a Unicode update, run
`tools/gen_unicode.py UCD_DIR` and `tools/gen_idna.py UCD_DIR`. Then copy
the UCD files that the tests read into `tests/data`.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/text/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/text/LICENSE-MIT), at your option.

The Unicode Character Database files in `tests/data` and the tables
generated from them (`src/unicode/tables.rs`) are under the Unicode License
v3; see [LICENSE-UNICODE](https://github.com/verilith/verilith/blob/main/crates/text/LICENSE-UNICODE).
