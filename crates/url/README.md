# verilith-url

A WHATWG URL parser in Rust, formally verified with [Verus](https://github.com/verus-lang/verus).
It ships a C API that drops in for [ada](https://github.com/ada-url/ada)'s `ada_c.h`.

## Using it from Rust

`verilith_url::compat::Url` follows the `url` crate's API (`parse`, `join`,
`options().base_url(..)`, `scheme`, `host_str`, `host`, `port_or_known_default`,
`path_segments`, `query_pairs`, `query_pairs_mut`, the `set_*` methods,
`ParseError`, and `Display`/`FromStr`/`Eq`/`Ord`/`Hash`), so most code
moves over by changing an import. `tests/compat.rs` checks that every
accessor returns what the `url` crate returns on each WPT input where the two
crates produce the same href (562 inputs; on the other 65 the `url` crate
departs from the Standard). On a 20,000-URL corpus the hrefs agree on
19,997 and the accessors on all of those.

```rust
use verilith_url::compat::Url;

fn main() -> Result<(), verilith_url::compat::ParseError> {
    let base = Url::parse("https://example.com/a/b?x=1")?;
    let u = base.join("../c?q=v%20w#top")?;
    assert_eq!(u.as_str(), "https://example.com/c?q=v%20w#top");
    assert_eq!(u.host_str(), Some("example.com"));
    assert_eq!(u.port_or_known_default(), Some(443));
    assert_eq!(u.query_pairs().next(), Some(("q".into(), "v w".into())));
    Ok(())
}
```

The verified parser decides whether an input is accepted. When it is
rejected, the `ParseError` reason comes from a separate diagnostic pass in
plain Rust: the reason is best effort, the rejection is not. It matches the
`url` crate's reason on 262 of the 269 WPT inputs both crates reject.

The lower-level `verilith_url::Url` exposes the URL Standard's getters (`href`,
`protocol`, `hostname`, `search`, ...) directly.

## Which URL standard

verilith-url implements the [WHATWG URL Standard](https://url.spec.whatwg.org/)
only: the parser browsers, `fetch`, Node and the `url` crate use. It is
not an RFC 3986 parser, and the two standards read some inputs
differently:

| Input | RFC 3986 | WHATWG (verilith-url) |
| --- | --- | --- |
| `http://good.example\@evil.example/` | not a URI (`\` is not allowed) | host `good.example` (`\` reads as `/`) |
| `http:/evil.example/x`, `http:evil.example/x` | no authority; path `/evil.example/x` or `evil.example/x` | host `evil.example` |
| `http://0x7f.1/` | host `0x7f.1`, a name | host `127.0.0.1` |
| `http://a.example/b/%2e%2e/c` | path `/b/%2e%2e/c` | path `/c` |

**Use one parser for checking and fetching.** When an allowlist, proxy
or SSRF filter reads a URL with one standard and the code that fetches it
uses the other, inputs like these get past the check. If part of your
stack follows RFC 3986, either parse with the same library on both sides
or accept only URLs on which both standards agree.
[vuri](https://github.com/verilith/vuri) is a verified
RFC 3986 parser that proves such a class: for `http` and `https` URIs with
a lowercase ASCII domain, no userinfo, no dot segments and a port up to
65535, it proves that RFC 3986 and verilith-url's model of the WHATWG parser give
the same scheme, host, port, path, query and fragment. Its README gives
the exact conditions and an example of each class of disagreement.

## What is proven

Verus checks the following for every input byte string and every base URL
that verilith-url itself produced:

- **Conformance.** `api::parse` returns exactly the URL record that
  `spec::parse_url` returns, with `href` equal to `spec::serialize` of it.
  When the spec reports failure, `parse` returns `None`. `spec.rs`
  transliterates the Standard's algorithms (the URL record, the host parser
  with IPv4, IPv6 and opaque hosts, every state of the basic URL parser, and
  the serializer) into a byte-level state machine; the places where it
  narrows the Standard are listed [below](#where-the-model-differs-from-the-standard).
  The exec parser in `parse.rs` is proven to compute that machine's result,
  though it works differently: it uses bulk scans (some eight bytes at a
  time in a `u64`, with each lane's formula proven exact by Verus's
  bit-vector solver, in `swar.rs`), fast paths for an
  `http://` or `https://` prefix and for plain paths, and writes `href` and
  the component offsets in a single pass.
- **Setters.** Each of the Standard's setters (protocol, username,
  password, host, hostname, port, pathname, search, hash) is proven to
  leave exactly the record that the Standard's setter leaves
  (`spec::set_protocol`, ... `spec::set_hash`, which run the basic URL
  parser with the Standard's state override, `spec::run_url`). `set.rs`
  runs the override's states on the setter's input, then builds the new
  `href` from the old URL's other components and the new one, proven to
  be the new record's serialization, so no setter parses its result
  again. The href setter is the parser itself.
- **IDNA.** Non-ASCII domains go through verilith-text's UTS #46
  (`verilith_text::idna::uts46::url_domain_to_ascii_exec`), which verilith-text proves
  equal to its transliteration of UTS #46. `idna.rs` proves the UTF-8
  decoding that connects the two.
- **Well-formedness.** Every URL that is returned satisfies `Url::wf`: its
  component offsets lie inside `href` and delimit the spec's components.
  The getters depend on this.
- **ASCII output.** Every URL the Standard's parser returns has only ASCII
  components, so its serialization is ASCII (`ascii::lemma_parse_url_ascii`,
  proven over the spec state machine for every state). `api::parse` ensures
  `Url::ok`, so the getters hand out `href` as `&str` without checking it.
  `Url::ok` also says that a URL without a host has no credentials and no
  port (`creds::lemma_parse_url_creds`), which the host setter relies on
  when it gives such a URL a host.
- **Memory safety.** The verified code is safe Rust with every index
  proven in bounds, so it cannot panic on an index and its arithmetic
  cannot overflow.
- **Termination.** Every loop and every recursive function has a proven
  `decreases` measure.
- **Linear time.** `api::parse_metered` carries a ghost step counter
  (`spec::Meter`). It ticks once per iteration of every loop whose trip
  count is not bounded by a constant, and once per byte that a bulk copy
  moves. The theorem is

  ```text
  steps(parse(input, base)) <= parse_cost(n, m) = 3n + 32 + 20 * 128 * (n + m + 2) + 128n
  ```

  where `n = input.len()` and `m` is the length of the base URL's href.
  The proof runs on a potential function, `parse::pot`. Every byte the
  parser consumes pays 128 steps. Every drop in the state's level pays
  `128 * (n + m + 2)`, and no transition raises the level. That covers the
  two places the Standard moves the pointer backwards: the scheme state
  restarting in "no scheme", and the authority state rewinding to the
  start of the host. Bytes written to `href` are counted in the potential,
  so the `..` segment, which shortens `href`, is paid for by the earlier
  writes it undoes.

  The meter runs through every state handler in `parse.rs`, the host
  parser in `host.rs`, the percent-encoding and byte-class scans in
  `encode.rs`, and the input cleanup in `api.rs`. A step is a loop
  iteration, not a machine instruction: the bound also assumes `Vec::push`
  is amortized O(1) and that the IDNA call is linear (see below).

`cargo verus focus` reports 529 verified, 0 errors. The crates it builds on,
[verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) and
[verilith-text](https://github.com/verilith/verilith/tree/main/crates/text), are verified
as their own crates in this repository. CI (`.github/workflows/ci.yml` at the repository root) verifies the proofs and runs `ci.sh` on every pull request and push to `main` that touches this crate or a crate it depends on.

### Where the model differs from the Standard

| Standard | verilith-url's model | Why it is safe or what it costs |
|---|---|---|
| Input is a string of Unicode scalar values. | Input is its UTF-8 bytes, one per step. | Every parser decision compares against ASCII, and every percent-encode set contains all non-ASCII code points, so the two agree on valid UTF-8 (argued at the top of `spec.rs`). The Rust API takes `&str`. Through the C API or `parse_bytes`, invalid UTF-8 has no counterpart in the Standard; verilith-url gives the model's bytewise result. |
| UTS #46 (`domain to ASCII`) for non-ASCII domains, after UTF-8 decode without BOM. | verilith-text's specification of UTS #46 (`spec::domain_to_ascii`). Ill-formed UTF-8 fails. | verilith-text's spec transliterates UTS #46 and is part of verilith-text's trusted base. Ill-formed UTF-8 decodes to U+FFFD, which UTS #46 disallows, so failing is what the Standard does; this step is argued, not proven. ASCII domains never reach UTS #46 and are fully specified. Passes WPT `toascii.json`. |
| ToASCII's result may be any length. | A result over 8 bytes per input byte fails (`spec::domain_to_ascii`). | Keeps the parser's output, and so its running time, linear without assuming anything about verilith-text. No input is known to reach the limit: over every code point the largest ratio is 5.67 (U+337F, 3 bytes, becomes 17). |
| Validation errors are reported. | Not modelled. | They never change the result. |
| Non-UTF-8 query encodings (HTML documents in legacy encodings). | The query is always UTF-8. | Matches every non-HTML caller; a browser would need its own query encoder. |
| Blob URL entries. | Not modelled. | They are a lookup outside URL parsing. |
| The setters change the URL in place, and keep what the parser changed even when it then returns failure. | `spec::run_url` returns the URL as the failing state found it. | Exact: no state changes the URL in the step that returns failure. |
| The setters also update the URLSearchParams object. | Not modelled. | `searchparams.rs` reads the query again. |
| The setters return nothing. | The Rust and C APIs return ada's booleans (`setters.rs`). | The booleans are not specified; the URL is. |
| `URLSearchParams` and `application/x-www-form-urlencoded`. | The parser and serializer are specified (`searchparams::form_parse`, `form_serialize`) and proven: `UrlSearchParams::parse`/`reset` equal `params_init`, `to_bytes` equals `form_serialize`, and every list serializes to bytes that parse back to it (`theorem_serialize_parse`). Names and values are bytes: the Standard's UTF-8 decode (which turns invalid sequences into U+FFFD) is left out, as in ada. The list edits and the UTF-16 `sort` are not modelled. | The edits and `sort` are unverified; fuzzed and diffed against ada. |
| `origin`. | Computed in plain Rust from the verified components (`public.rs`). | Unverified; checked against WPT and the `url` crate. |

### Trusted computing base

- **`spec.rs`**, which has to be read against the Standard (see the table
  above and the notes at the top of the file).
- **IDNA cost (`idna.rs`).** verilith-text's ToASCII is proven correct but not
  metered, so it is assumed to run in time linear in its input. Only the
  linear-time theorem depends on this. (Its output length is not assumed:
  a result over 8 bytes per input byte fails; see the table above.)
- **verilith-text's trusted base** for UTS #46: its specification, the Unicode
  tables and the axioms about them (see verilith-text's README).
- **Verus, Z3, rustc,** and the `vstd` library (the published
  `vstd = "=0.0.0-2026-11-01-0251"` crate, matching Verus commit `8bf68ee7`).
- **Glue outside the proof**, plain Rust:
  - `public.rs`: getters that slice the verified `href` at the verified
    offsets.
  - `setters.rs`: the `&mut self` setters, which call the verified ones in
    `set.rs` and compute ada's booleans.
  - `searchparams.rs`: URLSearchParams's list edits (`append`, `set`,
    `remove`, ...) and `sort`. Its parser and serializer are verified.
  - `capi.rs`: the C ABI.
  - `compat.rs`: the `url`-crate-shaped API and its error diagnosis.

## Testing

Everything below runs in the CI workflow (`.github/workflows/ci.yml`, manual runs only),
alongside the Verus proof check.

- The WPT `urltestdata.json` suite passes in full (896/896), as do
  `setters_tests.json` (278/278) and `toascii.json`: `cargo test`.
- `tests/compat.rs` compares the `url`-crate-shaped API with the `url`
  crate (accessors, setters and error reasons).
- The C API is differentially tested against ada (`tests/capi/run.sh`).
  The test runs every `ada_c.h` function, including the setters,
  URLSearchParams and IDNA, on the WPT inputs plus a 20,000-URL corpus,
  72,303 cases in all, and finds no differences. Valgrind reports no leaks.
- The verified setters were diffed against the previous ones (which
  reparsed their result and were diffed against ada) on 8.2 million setter
  calls and setter pairs over every WPT URL. The only differences are one
  case the old setters got wrong: after setting the path of a special URL
  to start with "C|", setting the protocol to "file" now gives
  "file://host/C|/", as the Standard does, where the old setter refused
  because that href reparses as "file://host/C:/".
- Three `cargo fuzz` targets run under AddressSanitizer: `parse` (parse with
  and without a base, every getter, and reparse-of-href is a fixed point),
  `setters` (random setter sequences, reading every component after each) and
  `capi` (random sequences of C ABI calls, including frees, copies, search
  params iterators and null handles). Each ran for over a million inputs
  locally with no failures; CI runs each for two minutes.

## Speed

Parsing the 100,025 URLs of ada's
[url-dataset](https://github.com/ada-url/url-various-datasets) (`out.txt`,
8.7 MB) on one core of a cloud Intel Xeon vCPU (2.1 GHz nominal). `bench/run.sh` runs each
parser in its own process, five rounds in rotating order, 40 sustained
iterations each, and reports each parser's best (so no parser inherits
another's frequency boost or warm caches). Everything is built with
`-march=x86-64-v3` / `target-cpu=x86-64-v3`, LTO for Rust, and `-O3` for
C++. Each parser's href is read after the parse.

| parser | ns/URL | MB/s | vs verilith-url |
|---|---:|---:|---:|
| ada 4.0.0 | 59.6 | 1457 | 0.92x |
| **verilith-url** | **64.5** | **1346** | 1x |
| curl 8 URL API, set only | 197.9 | 439 | 3.1x |
| `url` crate 2.5.8 | 316.2 | 275 | 4.9x |
| curl 8 URL API, set + get href | 894.3 | 97 | 13.9x |

verilith-url runs at 1.08x ada's time per URL (the previous release measured the
same way: 1.12x). It is 4.9x faster than the `url` crate and 3.1x faster
than curl, even before curl writes out an href. The gains over earlier
versions came from proving the output ASCII (the getters used to
re-validate `href` as UTF-8 on every read, about 20 ns per URL), from
finding the first stopping byte of a block without a byte loop (a
branch-free flag vector read back as two words and a trailing-zero count),
from scanning hosts eight bytes at a time in a `u64`, and from deciding
`http` versus `https` without a branch the predictor would lose half the
time. Every one of these is inside the proof.

The ratio depends on the machine. On a second cloud VM (Intel Xeon @ 2.8
GHz with AVX-512, the same harness, dataset and flags, ada 4.0.0 built from
the amalgamation bundled in the `ada-url` 4.0.0 crate), three separate
runs on two different cores agreed within 1%:

| parser | ns/URL | vs verilith-url |
|---|---:|---:|
| **verilith-url** | **110.4** | 1x |
| ada 4.0.0 | 146.5 | 1.33x |
| curl 8 URL API, set only | 283.0 | 2.6x |
| `url` crate 2.5.8 | 477.9 | 4.3x |
| curl 8 URL API, set + get href | 1376.9 | 12.5x |

There verilith-url takes 0.75x ada's time. So verilith-url is within 10% of ada on one
machine and ahead of it on another; neither result should be read as a
general ranking.

The harness in `bench/` is a small Rust crate that links ada and libcurl
through a C++ shim. It expects ada and the dataset to be cloned under
`$EXT`: `EXT=~/ext bench/run.sh`.

## Building

```text
cargo build --profile release-fat          # rlib + staticlib exporting vurl_* symbols
cargo build --profile release-fat --features ada-abi   # export ada_* symbols instead
cargo verus focus              # verify (needs Verus at the commit pinned in ci.yml)
```

The C header is ada's `ada_c.h`. With `ada-abi`, linking `libverilith_url.a` in
place of ada needs no source changes.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/url/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/url/LICENSE-MIT), at your option.

The URL test data in `tests/data` comes from web-platform-tests
(BSD-3-Clause); see [LICENSE-wpt](https://github.com/verilith/verilith/blob/main/crates/url/LICENSE-wpt).
