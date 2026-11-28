# verilith-css

A CSS tokenizer in Rust, proven with
[Verus](https://github.com/verus-lang/verus) to compute exactly the
tokens of [CSS Syntax Module Level 3](https://www.w3.org/TR/css-syntax-3/)
(Candidate Recommendation Draft, 1 October 2026): §3.3, preprocessing the
input stream, and §4, tokenization. It is the first piece of the browser
engine layer: the HTML parser's `<style>` elements, `style` attributes and
every stylesheet go through it before any CSS parsing.

`cargo verus verify` (or `scripts/verify.sh`) checks 65 functions and
lemmas with no errors, no `assume`, no `external_body` and no axioms in
this crate. The proofs are checked once per pointer width: `scripts/verify-narrow.sh`
runs Verus compiling for `wasm32-unknown-unknown`, where `usize` is 32
bits.

```rust
use verilith_css::{Kind, tokenize_str};

let t = tokenize_str("a { width: -1.5em; background: url(x.png) }");
let kinds: Vec<Kind> = t.tokens.iter().map(|k| k.kind).collect();
assert_eq!(kinds[0], Kind::Ident);
assert_eq!(kinds[2], Kind::LeftBrace);

let em = &t.tokens[7];
assert_eq!(em.kind, Kind::Dimension { integer: false });
assert_eq!(t.number(em), Some(-1.5));
assert_eq!(t.sign(em), Some('-'));
assert_eq!(t.value(em), "em");

let url = t.tokens.iter().find(|k| k.kind == Kind::Url).unwrap();
assert_eq!(t.value(url), "x.png");
```

## What is proven

For every input, with no exceptions:

- `preprocess(s)` returns `spec::preprocess(s@)`: CR LF, CR and FF
  become LF, and NUL and surrogates become U+FFFD (§3.3).
- `tokenize(s)` returns `spec::tokens(s@)`: the token sequence of §4,
  without the final `<EOF-token>`. Each token's kind and flags (the hash
  token's "id" type, the numeric tokens' "integer" type), its value after
  escapes are resolved (an ident's name, a string's contents, a url, a
  dimension's unit), and the positions of the text it was consumed from
  are those of the specification.
- No panics, no out-of-bounds access and no integer overflow, and every
  loop terminates. Every token is at least one code point long and
  within the input, so the tokens (with the comments between them) cover
  the input in order.

`spec.rs` states the standard's algorithms as functions over the code
points, one per algorithm, named after its section: "consume a token"
(§4.3.1) is `next_token`, "consume an ident sequence" (§4.3.12) is
`ident_seq`, and so on. That file is the one to review.

## Where it departs from the standard

- **Non-ASCII ident code points.** This crate counts every code point from
  U+0080 as an ident code point, as the 2021 Candidate Recommendation
  defined it and as browsers (and Servo's cssparser) still do. The current
  draft narrows "non-ASCII ident code point" to the ranges of XML names
  (U+00B7, U+00C0 to U+00D6, and so on), so that, for example, U+00D7 ×
  is a delim there and part of an ident here. The definition is one
  function, `is_non_ascii`, in `spec.rs`.
- **Unicode-range tokens.** The tokenizer runs with the draft's "unicode
  ranges allowed" flag false, which is how stylesheets are tokenized. The
  draft sets it only while consuming the value of a `unicode-range`
  descriptor; `U+0-7F` here is tokenized as an ident, a number and so on,
  as in every other context.
- **Numeric values.** The standard gives a number token the exact decimal
  value of its text. The verified tokenizer gives the text (`start` to
  `repr_end`) and the type flag. `Tokens::number` reads the text with
  Rust's correctly rounded `f64` parser (unverified), and a value too large
  for `f64` is infinite. `Tokens::sign` gives the sign character, which is
  the first code point of the text when it is `+` or `-`.
- **Input.** The verified functions take code points. `tokenize_str` turns
  a `&str` into code points (no decoding step is needed for valid UTF-8);
  decoding bytes in another encoding, or the `@charset` rule, is the
  caller's.

## Layout

- `src/spec.rs`: the specification (trusted).
- `src/lex.rs`: `preprocess` and `tokenize`, proven equal to it.
- `src/api.rs`: `tokenize_str` and `Tokens`, plain Rust convenience over
  the verified functions (not verified).

## Trusted base

- The specification, `src/spec.rs`.
- Verus, `vstd`, Z3 and the Rust compiler.
- `src/api.rs`: `&str` to code points, code points back to `String`, and
  the `f64` parse of a number's text. It is short and has no `unsafe`.

There are no `external_body` functions, axioms or `assume`s in this crate.

## Tests

- `tests/tokens.rs`: small inputs whose tokens are worked out by hand from
  the standard: escapes, strings, urls and bad urls, numbers, hashes,
  CDO and CDC, preprocessing.
- `tests/differential.rs`: compares the tokens, values, flags and numbers
  with Servo's [cssparser](https://crates.io/crates/cssparser) (the
  tokenizer Firefox uses), on a corpus and on 2,000,000 random inputs
  built from the code points that matter to the tokenizer. They agree,
  except in two places where cssparser departs from the standard, which
  the test skips (under 1% of the random inputs):
  - `-` followed by `\` and a newline: §4.3.9 says this does not start an
    ident sequence, as `\` and a newline are not a valid escape, so `-` is
    a delim; cssparser returns an ident `-`.
  - An unquoted url with whitespace followed by `\)`: §4.3.6 only looks at
    the code point after the whitespace, and the remnants of the bad url
    (§4.3.15) then read `\)` as an escape that does not end it.
    cssparser consumes that code point first and ends the bad url at the
    `)`.

## Not here yet

- Parsing (§5): rules, declarations, blocks and component values. The
  tokenizer is the first half of it.
- Speed. The tokenizer works one code point at a time on a `Vec<u32>`
  and has not been tuned or measured against cssparser.
- Positions in the original text: token positions count the
  preprocessed code points, so a CR LF counts as one.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/css/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/css/LICENSE-MIT), at your option.
