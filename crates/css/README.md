# verilith-css

A CSS tokenizer and parser in Rust, proven with
[Verus](https://github.com/verus-lang/verus) to compute exactly
[CSS Syntax Module Level 3](https://www.w3.org/TR/css-syntax-3/)
(Candidate Recommendation Draft, 1 October 2026): §3.3, preprocessing the
input stream, §4, tokenization, and §5, parsing into rules, declarations
and component values. It is the first piece of the browser engine layer:
`<style>` elements, `style` attributes and every stylesheet go through it
before selectors and property values are read.

`cargo verus verify` (or `scripts/verify.sh`) checks 134 functions and
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

Parsing gives rules, with nested rules and declarations inside them:

```rust
use verilith_css::{Item, parse_stylesheet_str};

let p = parse_stylesheet_str("a { color: red !important; &:hover { color: blue } }").unwrap();
let Item::Rule { declarations, children, .. } = &p.tree[0] else { panic!() };
assert_eq!(p.tokens.name(&declarations[0]), "color");
assert!(declarations[0].important);
assert!(matches!(children[0], Item::Rule { at: false, .. }));
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

For parsing, for every sequence of tokens:

- `parse_stylesheet(ts)` returns `parse_spec::parse_stylesheet(ts@)`
  (§5.4.4, "parse a stylesheet's contents"), `parse_block_contents(ts)`
  returns `parse_spec::parse_block_contents(ts@)` (§5.4.5, used for a
  `style` attribute), and `parse_component_values(ts)` returns
  `parse_spec::parse_component_values(ts@)` (§5.4.9): the same rules,
  preludes, declarations (name, value, `!important`), nested rules and
  component value trees, with the same token positions.
- The same freedom from panics, overflow and non-termination, and the
  stack is bounded: the code recurses only to go one nesting level
  deeper, at most `MAX_DEPTH` (128) levels.

`spec.rs` and `parse_spec.rs` state the standard's algorithms as functions,
one per algorithm, named after its section: "consume a token" (§4.3.1) is
`next_token`, "consume an ident sequence" (§4.3.12) is `ident_seq`,
"consume a qualified rule" (§5.5.3) is `q_rule`, "consume a block's
contents" (§5.5.5) is `contents`, and so on. Those two files are the ones
to review.

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
- **Nesting depth.** A parse that would nest blocks, functions and rules'
  blocks more than `MAX_DEPTH` (128) levels deep fails as a whole
  (`None`, or `TooDeep` from the `_str` functions). The standard has no
  limit; the limit is what bounds the stack. In an optimized build a
  parse at the limit needs under 128 KiB of stack (`tests/depth.rs` runs
  one on a 256 KiB thread).
- **Declarations at the end of a block.** In "consume a block's contents"
  (§5.5.5), the published text only says "Return rules." when the block
  ends, so the declarations not yet appended to the rules would be
  dropped, including all of `a { color: red }`'s. They are appended
  first here, as every implementation does.
- **Validity.** Where the standard asks whether a rule or declaration is
  "valid in the current context" (§5.5.2, §5.5.3, §5.5.6), the answer
  depends on the grammar of what is being parsed, which is the caller's:
  here everything is valid, and the caller checks the grammar.
- **`unicode-range`.** §5.5.6 re-tokenizes the value of a declaration
  named `unicode-range` with unicode ranges allowed. That is not done: its
  value is the ordinary tokens.
- **Custom property names.** A custom property name is any name starting
  with `--`, as CSS Typed OM defines the "custom property name string"
  that §5.5.6 uses; that includes `--` alone, which CSS Variables reserves.
- **Input.** The verified functions take code points. `tokenize_str` turns
  a `&str` into code points (no decoding step is needed for valid UTF-8);
  decoding bytes in another encoding, or the `@charset` rule, is the
  caller's.

## Layout

- `src/spec.rs`: the specification (trusted).
- `src/lex.rs`: `preprocess` and `tokenize`, proven equal to it.
- `src/parse_spec.rs`: the specification of parsing (trusted).
- `src/parse.rs`: `parse_stylesheet`, `parse_block_contents` and
  `parse_component_values`, proven equal to it, and the tree types
  (`Item`, `Declaration`, `ComponentValue`).
- `src/api.rs`: `tokenize_str`, `parse_stylesheet_str` and the other
  `_str` functions, and `Tokens`, plain Rust convenience over the verified
  functions (not verified).

## Trusted base

- The specifications, `src/spec.rs` and `src/parse_spec.rs`.
- Verus, `vstd`, Z3 and the Rust compiler.
- `src/api.rs`: `&str` to code points, code points back to `String`, and
  the `f64` parse of a number's text. It is short and has no `unsafe`.
- The `Clone`, `PartialEq` and `Debug` implementations of the tree types,
  written out at the end of `src/parse.rs` (Verus does not accept a derive
  on a recursive type).

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

- `tests/parse.rs`: stylesheets, block contents and component values
  parsed by hand from §5: declarations and `!important`, nested rules
  and nested declarations, custom properties with `{}` blocks, at-rules
  with and without blocks, stray `}`, CDO and CDC, positions.
- `tests/depth.rs`: the nesting limit, exactly, and a parse at the limit
  on a small stack.
- `tests/random.rs`: 300,000 random inputs parse without panicking, into
  trees whose positions are in order and within the tokens.

The parser has not yet been compared with another implementation; the
tokens it reads have.

## Not here yet

- A differential test of the parser, against cssparser's rule and
  declaration parsers or the WPT `css-syntax` tests.
- Grammars on top of the parser: selectors, media queries and property
  values.
- Speed. The tokenizer works one code point at a time on a `Vec<u32>`,
  and the parser, as the standard describes, tries each item of a block
  as a declaration before reparsing it as a rule, so a token nested in
  `n` rules is read about `n + 1` times. Neither has been tuned or
  measured against cssparser.
- Positions in the original text: token positions count the
  preprocessed code points, so a CR LF counts as one.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/css/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/css/LICENSE-MIT), at your option.
