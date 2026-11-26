# verilith-json

A fast JSON parser for Rust, with a cJSON-compatible C ABI, whose parser is
formally verified with [Verus](https://github.com/verus-lang/verus). For
every input, the parser is proven to return exactly what an executable
statement of the RFC 8259 grammar returns, and it is proven never to panic
or overflow, to terminate, and to recurse at most 1000 deep. Strings the
writer emits are proven to read back as the same bytes. Its parse speed is
in the same range as [simdjson](https://github.com/simdjson/simdjson)'s
(see [Performance](#performance) for where it is ahead and where behind).

* **Rust:** `verilith_json::parse`, borrowed `Value` views, a `Writer`, and with
  the `serde` feature `from_slice`/`to_vec` for any serde type.
* **C:** the `cjson` feature builds `libvjson.{a,so}`, a drop-in for
  cJSON 1.7.19: every function in `cJSON.h` is implemented. Parsing goes
  through the verified parser, so it is stricter than cJSON's (see
  [Differences from cJSON](#differences-from-cjson)); the rest follows
  cJSON's code and is fuzzed against it.

**Status:** early, not yet published. What is proven and what is trusted is
listed below; read [What is not proven](#what-is-not-proven) before relying
on it.

## Two speeds: drop-in and native

Swap verilith-json in for cJSON today and get the proofs at no cost in speed; move
hot paths to `verilith_json::Parser` when you want the speed too.

| | what you change | against cJSON 1.7.19 |
| --- | --- | --- |
| **Drop-in** (cJSON ABI, the `cjson` feature) | relink | 1.30x (1.01x to 1.80x) |
| **Native** (`verilith_json::Parser`) | port the calling code | 6.48x (5.44x to 7.50x) |

The task is: parse a document, read every value (numbers as doubles, the
length of every string and key), free it, on simdjson's six example files.
Measured with [vbench](https://github.com/verilith/verilith/tree/main/bench) on an
Apple M3 Pro (2026-11-20, 31 alternating pairs per case; speedup is cJSON's
time over ours, geometric mean and range over the cases). Both columns run
the same task against the same cJSON driver. The native number is what you
get after porting the calling code; relinking alone gets the drop-in
number.

The gap is the API's shape, not the parser, which is the same code in both
rows. cJSON's API hands back a tree with one allocated node per value, so
the drop-in has to build and free that tree; the native API parses into a
flat index inside a `Parser` the caller reuses. Against simdjson, which has
a flat design like ours, the same native parser is at 1.01x on the same
files (see [Performance](#performance)).

## Design

`verilith_json::parse` and `Parser` use a two-pass design in the style of
[simdjson](https://github.com/simdjson/simdjson):

1. **Stage 1** (`src/index.rs`) reads the input 64 bytes at a time and
   writes the position of every structural byte (brackets, braces, commas,
   colons, quotes, the first byte of each number or literal, and each
   backslash or control character inside a string) to an index. The index
   is a window: it covers 64 KiB of input at a time, in a buffer of the
   same fixed size whatever the input's length, and stage 1 resumes where
   it stopped when stage 2 reads past the window's end. It finds string interiors with a
   carry-less multiply (prefix XOR) over the unescaped quotes. It
   uses AVX-512 (with VBMI2 compress) or AVX2 when the CPU has them, NEON
   on AArch64 (Apple Silicon and other ARM64 CPUs; `src/neon.rs`), and a
   scalar kernel otherwise. On NEON the prefix XOR is the scalar shift
   ladder, and UTF-8 validation checks 64-byte ASCII runs with NEON and
   runs simdjson's lookup check with `tbl` on any non-ASCII run, as the
   x86 kernels do with `pshufb`.
2. **Stage 2** (`src/stage2.rs`) walks the index and writes a flat *tape*:
   one token per value, key and bracket, in pre-order. Strings and numbers
   are byte spans into the input, so parsing allocates nothing per value.
   On AArch64 the eager parser reads the digits of a number with a
   branchless NEON kernel (`digit_run_acc16_neon` in `src/neon.rs`): it
   classifies 16 bytes, shifts the leading run of digits to the end of the
   vector with `tbl`, and turns them into an integer with three multiply
   and pairwise-add steps. Its result is proven equal to the decimal value
   of the run.

Stage 1 rejects nothing on its own. A control character inside a string
is in the index, so stage 2 rejects it where it reaches it, and a string
left open runs out of index. The one-pass parser in `src/parser.rs` is
used by `parse_prefix` and by the C API. It scans strings, whitespace and digits 16
bytes at a time with SSE2 (`src/simd.rs`).

The one-pass parser emits tokens to a `Sink`. Two sinks exist:

* `Tape` stores the tokens and backs the Rust API.
* `TreeSink` (in `src/ffi.rs`) builds cJSON's linked `cJSON` nodes while
  parsing, in one pass with no intermediate tape. This is what the C API
  uses.

### Rust API

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let doc = verilith_json::parse(br#"{"name": "verilith-json", "n": 2}"#)?;
    let root = doc.root();
    assert_eq!(root.get("name").unwrap().as_str().as_deref(), Some("verilith-json"));
    assert_eq!(root.get("n").unwrap().as_i64(), Some(2));
    Ok(())
}
```

`Value` is a borrowed view with `kind`, `as_bool`, `as_f64`, `as_i64`,
`as_number_str`, `as_bytes`/`as_str` (borrowed unless the string has
escapes), `elements`, `members`, `get`, `at` and `len`. `parse_prefix`
accepts trailing bytes and returns where the value ended. `Parser` keeps its
token buffer between documents.

A failed parse returns an `Error` with an `ErrorKind` (unexpected byte,
unexpected end, unterminated string, invalid escape, control character,
invalid number or literal, nesting too deep, trailing data, invalid UTF-8)
and its byte offset, line and column, e.g. `unexpected ']' at line 3
column 3 (byte 11)`.

Inputs may be up to 2^48 - 1 bytes (256 TiB), more than a 64-bit address
space holds today: token positions are 48 bits, so a token is 16 bytes.
On 32-bit targets (wasm32 for browsers and Cloudflare Workers) any slice
fits. The index takes the same fixed memory at any input size.
Parsing recurses once per nesting level, so the full 1000 levels take
about 400 KiB of stack under wasmtime; give a wasm host at least 512 KiB
(wasmtime's default is just that, browsers give about 1 MiB).

### On-demand reading

`verilith_json::ondemand::Reader` reads values straight from the stage 1 index and
builds no tape. It moves forward only: enter a container, step through it,
read the values you want and pass over the rest.

```rust
use verilith_json::ondemand::Reader;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let src = br#"{"skipped": [1, {"x": "y"}], "id": 7, "name": "verilith-json"}"#;
    let (mut idx, mut buf) = (Vec::new(), Vec::new());
    let mut r = Reader::new(src, &mut idx).unwrap();
    r.obj_begin()?;
    assert!(r.find(b"id")?);
    assert_eq!(r.i64()?, 7);
    assert!(r.find(b"name")?);
    assert_eq!(r.str(&mut buf)?, b"verilith-json");
    Ok(())
}
```

`arr_begin`/`arr_next` and `obj_begin`/`obj_next` step through containers
(a value that was not read is passed over), `key`, `key_is` and `find` read
member names, `str`, `f64`, `i64`, `bool` and `null` read scalars, `skip`
passes over a value and `leave` closes the container the reader is in from
anywhere inside it. A call that does not fit what is at the cursor returns
`Mismatch` and never panics.

The guarantee is the one of simdjson's On Demand front end, not the tape
parser's. Everything that is read is checked against RFC 8259: a number,
string, literal, key, comma, colon or bracket the reader hands back or
steps over one at a time is exactly the grammar's token. What is passed
over (`skip`, `leave`, an unread value before `arr_next`/`obj_next`,
everything after the last read) is only bracket-counted, so `[1, nul]` can
be skipped as an array. `Reader::new` checks that the whole input is
UTF-8 before the first read. A string is checked to be terminated when
the reader reaches it, and to be free of control characters when it is
read. Use `verilith_json::parse` when the whole text must be valid.
On a valid text, the reader is proven to read what the tape parser
would: each value, key and container end it returns is the tape's token
at the same place (see [What is proven](#what-is-proven)).

### C API (native)

The same zero-copy views from C or C++, through `include/vjson.h` (build
with `--features capi`). Use this one when you can change the calling code;
use the cJSON ABI when you cannot.

```c
vjson_parser *p = vjson_parser_new();          /* reusable; keeps its buffers */
vjson_value root, v, e;
vjson_iter it;
if (vjson_parse(p, buf, len, &root, NULL) == VJSON_OK &&
    vjson_object_get(root, "tags", 4, &v) && vjson_array_iter(v, &it)) {
    while (vjson_array_next(&it, &e)) {
        const char *s; size_t n;
        if (vjson_get_string(e, &s, &n)) fwrite(s, 1, n, stdout);
    }
}
vjson_parser_free(p);
```

A `vjson_value` is two words passed by value: a view into the parser's last
document. Reading it allocates nothing and copies nothing, where the cJSON
ABI has to allocate a node per value and copy every string and key. Strings
come as a pointer and a length (decoded UTF-8, not NUL-terminated), valid
until the parser parses again or is freed, and only while the input buffer
is alive: strings without escapes point into the input itself. The header
has the full rules.

`bench/native_c.c` measures parse-and-read-every-value through this API,
the same work as the second column of `examples/like_for_like.rs`.

### Writing

`Writer` builds a JSON text one value at a time (compact, or pretty with
`Writer::pretty`), and `Document::to_vec` writes a parsed document back
out. Calls out of order (a value where a member name is due, a mismatched
close, a second top-level value) are refused rather than written.

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut w = verilith_json::Writer::new();
    w.begin_object()?;
    w.key("name")?;
    w.string("say \"hi\"\n")?;
    w.key("n")?;
    w.f64(2.5)?;
    w.end_object()?;
    assert_eq!(w.finish()?, br#"{"name":"say \"hi\"\n","n":2.5}"#);
    Ok(())
}
```

### serde

With the `serde` feature, `verilith_json::from_slice`/`from_str` deserialize any
`Deserialize` type through the verified parser (borrowing strings that have
no escapes), and `verilith_json::to_vec`/`to_string`/`to_vec_pretty` serialize
through `Writer`. The output is byte for byte what serde_json writes, which
the tests check.

## What is proven

Everything in `src/spec.rs`, `src/parser.rs`, `src/index.rs`,
`src/stage2.rs`, `src/ondemand.rs`, `src/protocol.rs`, `src/utf8.rs`, `src/write.rs`, `src/simd.rs`, `src/float.rs`,
`src/diag.rs` and `src/lemmas.rs` is checked by Verus (`./scripts/verify.sh`, which runs `cargo verus verify`,
880 items, 0 errors). The proofs are checked once per pointer width:
also for `wasm32-unknown-unknown` at a 32-bit `usize`
(`./scripts/verify-narrow.sh`, 794 items, without the x86 and Arm
kernels, which that build does not have).
The trusted base is listed under [What is not proven](#what-is-not-proven).

* **Conformance.** `src/spec.rs` states the RFC 8259 grammar as Verus spec
  functions: `value`, `array`/`elements`, `object`/`members`, `string`,
  `number_end`, and `document` for a whole JSON text. Each one turns the
  input into a *tape*, which is the pre-order list of the tree's tokens.
  Every executable function in `src/parser.rs` is proven to return exactly
  what its spec function returns. The two-pass parser is proven against the
  same spec: `parse2_with` returns exactly `document(s, true)`. Stage 1 is
  proven to produce exactly the structural positions defined in
  `src/index.rs`, window by window (each window resumes stage 1's state
  and the UTF-8 check's where the last one stopped), and stage 2 is proven
  to read the spec's tokens through that windowed index. This holds for accepted and rejected
  inputs, and covers the decoded string bytes (UTF-8 for `\u` escapes and
  surrogate pairs), the byte range of each number, and the end position.
* **Error reasons and positions.** `doc_fail` in `src/diag.rs` says what
  error a rejected text gets: it reads the text with the grammar, rule for
  rule, and reports the first byte where no rule applies (or the end of the
  input, if more was needed), with the reason; ill-formed UTF-8 at or before
  that byte wins, reported at its first ill-formed sequence.
  `lemma_doc_fail` proves that it reports an error exactly when `document`
  rejects the text. `explain` is proven to return `doc_fail`'s error and
  `line_col` its line and column, so the `Error` that `parse` and
  `parse_prefix` return is the specified one. (`cJSON_GetErrorPtr` keeps
  cJSON's own idea of the error position, which is not specified.)
* **Numbers, from text to `f64`.** `number_value` in `src/spec.rs` says
  what a number lexeme means, as integers: a sign, a significand (every
  digit of the integer and fraction parts read as one integer) and a power
  of ten. The scanner `ex_number_scan` is proven to return exactly that
  whenever it reports the value as exact (at most 19 significant digits
  and an exponent below 100000), including the 16-digits-at-once SSE2
  kernel `digits_value16`. `is_round` in `src/float.rs` defines the correctly
  rounded double (round to nearest, ties to even, with subnormals, zero
  and infinity) for `w * 10^q` using only integer and rational arithmetic:
  a candidate bit pattern is the right one when `w * 10^q` lies between
  the midpoints to its neighbours. `to_bits`, the Eisel-Lemire algorithm
  over a 128-bit table of powers of five (every entry checked by
  evaluation), is proven to return a bit pattern satisfying `is_round`, or
  to give up (`None`) in cases so close to a midpoint that the table's
  precision cannot decide them. No such case came up in 520 000 random
  inputs, and the reader then falls back to `f64::from_str`. Before it,
  Clinger's fast path (`clinger`) takes significands below `2^53` with
  `|q| <= 22`, where one IEEE 754 multiplication or division of two exact
  doubles is already correctly rounded. It is proven to satisfy
  `is_round` too, against verilith-core's model of binary64
  (`verilith_core::binary64`): what each bit pattern is worth as an exact
  rational, and what rounding to nearest, ties to even, means. The proof
  shows that `w as f64` is exact below `2^53`, that the table of `10^k`
  holds those values exactly (checked by evaluation), and that rounding the
  exact product or quotient is `is_round`. What it assumes is the model's
  statement of the three hardware operations it uses (`u64 as f64`, `*`
  and `/` each return their exact result correctly rounded), three
  one-line wrappers in verilith-core, on the same footing as the SIMD instruction
  specs. A test still checks the path bit for bit against `f64::from_str`
  for every `q` it takes. The other
  trusted step is `f64::from_bits`, the reinterpretation of those 64 bits
  as a double.
* **Writing strings.** `escape` in `src/write.rs` says how the writer
  spells a string's bytes, and `lemma_escape_parses` proves the round trip:
  wherever the escaped bytes appear, followed by a quote, the parser reads
  one string that ends at that quote and decodes to exactly the original
  bytes. So no string, whatever it holds, can end early or inject JSON.
  `write_escaped` is proven to emit `escape`, copying runs that need no
  escape 16 bytes at a time. Every number the writer emits is first checked
  against the verified number grammar.
* **UTF-8.** `document` also requires the text to be well-formed UTF-8
  (RFC 8259 §8.1), with `utf8_from` in `src/spec.rs` read straight off
  Unicode's table of well-formed byte sequences (Table 3-7). The validator
  in `src/utf8.rs` uses simdjson's lookup algorithm: three 16-entry table
  lookups per byte, on 32 or 64 bytes at once. Two theorems connect it to
  the table: `lemma_utf8_local` shows that a check on each byte and the
  three before it accepts exactly the well-formed texts, and
  `lemma_lookup` shows, by evaluating all 4096 cases, that the tables
  compute that check (both in verilith-core's `utf8`, shared with
  verilith-text's validator). Stage 1 runs the validator on each 128-byte chunk
  as it indexes it.
* **Panic freedom.** Verus checks that no index is out of bounds and no
  arithmetic overflows or underflows anywhere in the parser.
* **Reading without bounds checks.** `lemma_document_in_bounds` in
  `src/lemmas.rs` proves that every tape `document` accepts lies within
  the input: each number, string and key token has
  `start <= end <= input length`. Every parser states this in its
  `ensures`, and the reader in `src/value.rs` (ordinary Rust) relies on it
  to slice the input for strings, keys and numbers without a bounds check.
  That cut the instructions spent reading twitter.json, citm_catalog.json
  and small.json by about 10%. The same lemma proves that the tape is not
  empty and does not end with a key (`ends_value`), so the root and the
  value after each key are read without a bounds check either (another 6%
  to 7% of reading).
* **Termination.** Every loop and recursive call has a decreasing measure
  that Verus checks, in both the spec and the executable code.
* **Bounded recursion.** Recursion happens only when entering an array or
  object, and the measure is the remaining nesting depth, which starts at
  `MAX_DEPTH` (1000, cJSON's `CJSON_NESTING_LIMIT`). Long arrays, objects
  and strings are parsed by loops, so stack use does not grow with input
  size.
* **The spec says what it appears to say.** Termination checking is purely
  syntactic, so the spec contains a few `if !(i < n <= len) { None }` guards.
  `src/lemmas.rs` proves that these guards are never taken. It also proves
  that every successful parse step consumes at least one byte and stays
  inside the input.
* **Every sink sees the same tokens.** The parser is generic over `Sink`, and
  its spec says the tokens pushed to the sink are exactly the spec tape. That
  holds for `TreeSink` as well as `Tape`.
* **Container links.** Each `ArrStart` and `ObjStart` token holds the
  index of its matching end token, so readers skip a whole container in
  one step. The links are part of the spec: `value` in `src/spec.rs` sets
  a container's start token to point at the end token it finishes with
  (`close_at`), and the parsers are proven to return exactly that tape.
  `lemma_document_links` proves that every start token in a document's
  tape links to a later token of the matching kind (`links_from`).
* **Stored values.** By default `Parser` is eager: while parsing it stores
  each number's significand and power of ten, and each escaped string's
  decoded bytes, in side arrays (`Tape::aux` and `Tape::strs`), and tags
  the token so the reader can skip rescanning the input. `stored_ok` in
  `src/parser.rs` says that every tagged token's slot holds its value: a
  number's slot and tag hold exactly its `number_value`, and an escaped
  string's slot holds a range of `strs` equal to its `decode`. The eager
  parser (`parse2_eager_into`) is proven to return a tape satisfying it.
  `src/value.rs` reads those slots back as ordinary Rust.
* **Memory.** `lemma_document_size` proves that a document's tape has at
  most one token per input byte. It also proves that the tokens together
  with the raw bodies of the strings weigh at most the input's length, and
  a decoded body is never longer than its source (`lemma_decode_len`). The
  parsers state `toks.len() <= input length` in their `ensures`, and the
  eager parser also states that the decoded strings take at most the
  input's length. The side array of stored values grows only to the token
  buffer's capacity (`set_aux`). Recursion depth is at most 1000 (above).
* **On-demand reading.** `src/ondemand.rs` proves three things about the
  cursor under `Reader`, against the same grammar functions as the parsers.
  (1) Safety on every input: each operation keeps the cursor between two
  tokens and outside any string (`Cursor::wf`), so no index or input read
  is out of bounds, nothing panics and every loop ends, whatever the
  bytes are and in whatever order the operations are called. `Reader`'s
  own methods are proven to keep that invariant in every state. (2) Each
  read is the grammar's token at the cursor: `num` succeeds exactly when
  `number_end` accepts there and a delimiter follows, with the scanner's
  exact `number_value`; `string` succeeds exactly when `string` does and
  appends exactly `decode` of its body; `lit` and `eat` likewise; each
  leaves the cursor right after the token and leaves it in place on
  failure. (3) Skipping agrees with the grammar: `skip` is specified as a
  walk over the index (`skip_to`: a string to its closing quote, a
  container to the bracket that returns the depth to where it started,
  anything else one entry), and `lemma_skip_value` proves that whenever
  `value` accepts at the cursor, that walk ends exactly where the value
  ends. `leave` is the same walk started inside a container. The walk
  that looks at eight entries at a time is proven equal to the one that
  looks at one (`lemma_block`).
* **The on-demand protocol.** `src/protocol.rs` and `Reader`'s contracts
  prove that the reader's sequencing of those operations reads a JSON text
  the way the tape does. The reader carries, as ghost state, the tape of
  everything before the cursor and the containers it is in, and on any
  input that `document(s, true)` accepts it is `synced`: finishing the
  parse from its place the grammar's way (`finish`, a continuation made of
  what is left of the innermost container, `rest`, then of each one around
  it, `unwind`) gives exactly the document's tape. `Reader::new` is synced
  at tape index 0. Each call is then specified against the tape token at
  the reader's index `pos()`: `null`, `bool`, `num_raw`, `str_raw`,
  `arr_begin` and `obj_begin` succeed exactly when a value is expected and
  the tape has that kind of token there, and return its contents (the
  string's range and escape flag and decoded bytes, the number's lexeme
  and exact value); `key_is` compares with the tape's key and `key_skip`
  passes it; `skip` moves to the index after the value
  (`next_val`, through the start token's link); `arr_next` and `obj_next`
  pass over an unread value, then return `false` exactly at the innermost
  container's end token, the one its start token links to, and `true`
  otherwise; `leave` moves past that end token from anywhere in the
  container; `find` stops at the first member of the same object from the
  cursor on with the key asked for (`none_before`: every key it passed
  differs), or past the object's end when none has it; `at_end` holds exactly once the
  document's value has been read, and then the reader is at the tape's
  end. Each leaves the reader synced at the place it says, so by induction
  any sequence of calls that fits reads what the tape holds, in order. A
  call that does not fit (a number where the tape has a string, a key
  where a value is expected, `arr_next` in an object, `obj_next` or
  `find` in an array, `leave` at the top) returns `Mismatch` and changes
  nothing: the reader keeps the kinds of the containers it is in, and
  checks them. The scalar readers are verified too: `str` and `key` give
  the token's bytes (`str_bytes`, `key_bytes`: the body, decoded if it
  has escapes); `i64` gives the number's value exactly when the lexeme is
  an integer that fits (`int_value`); `num_bits`, under `f64`, gives the
  bits of the nearest double, ties to even (`float::is_round` of the
  lexeme's exact `number_value`), with its sign. The
  lemmas say that each move leaves `finish` unchanged
  (`lemma_value_step`, `lemma_open_step`, `lemma_key_step`,
  `lemma_comma_step`, `lemma_start_step`, `lemma_leave_step`), that tokens
  already on the tape stay there (`lemma_finish_keeps`), and that the
  bracket walk `leave` does stops where the grammar ends the container
  (`lemma_rest_body`).

### What is not proven

* **The native C API** (`src/native.rs`, 350 lines of code for 18
  functions, feature `capi`) is unverified glue, like the cJSON ABI but a
  quarter of its size. It makes no decision about the input: each function
  checks its pointers, checks that the value's index is inside the tape,
  and calls the `value.rs` method of the same name. What it adds to the
  trusted base is its own `unsafe`: the parser handle (a document's view
  kept next to the parser that owns its buffers, and dropped before the
  parser is used again), and the contract in `include/vjson.h` that the
  caller keeps the input alive and passes back only values this API
  returned. `tests/capi.rs` checks it against the Rust API on every
  document it parses, and `tests/c/native.c` runs under ASan and UBSan,
  JSONTestSuite included.

* **Single-instruction specs** come from
  [verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd). Verus has no
  model of SIMD registers, so `__m128i`, `__m256i` and `__m512i` are opaque
  types with a ghost view of their lanes, and each x86 instruction the
  parser uses (`pcmpeqb`, `pshufb`, `por`, `pand`, `pxor`, `pmaxub`,
  `psubusb`, `psrlw`, `ptest`, `pmovmskb`, `vpcmpub`, `vpcompressb`,
  `vpmovzxbd`, `pclmulqdq`, `popcnt`, `pmaddwd`, `packssdw`, `punpcklbw`,
  `movq`, the loads and stores, and so on) has a trusted specification
  there, which verilith-simd's tests check against the CPU through a verified
  reference implementation. `src/lanes.rs` no longer trusts anything about
  them: its wrappers (`eq16`, `shuffle32`, `compress64`, `clmul_lo`, ...)
  are verified code that calls verilith-simd, and their contracts, which the rest
  of the parser is proven against, are proven from verilith-simd's. Every AVX2 and
  AVX-512 wrapper requires verilith-simd's CPU-feature predicate, so Verus checks
  that a kernel is reached only after its features were detected.
  Everything built from them, including the 64-byte classifier, the
  prefix XOR, writing out the set bits of a mask and the 16-byte SSE2
  scans, is verified. Scalar unchecked stores go through
  vstd's spec of `get_unchecked_mut` and need no trust. A unit test checks each
  kernel against a scalar version, and another checks that the scalar,
  AVX2 and AVX-512 stage 1 kernels agree.
* **The on-demand reader, outside the protocol.** On input the grammar
  rejects nothing is claimed beyond safety, and skipped parts are not
  validated, by design.
  `tests/ondemand.rs` and the `ondemand` fuzz target still read every
  accepted text through the reader and compare it with the tape, and
  check that partial reads end at its end. `Reader::new` is proven to
  return `None` only for input that is not UTF-8. `Reader::f64` is two
  lines of glue over the verified `num_bits`: `f64::from_bits` of its bits,
  or, for more than 19 significant digits, `f64::from_str` of the lexeme.
* **NEON specs** come from verilith-simd (`verilith_simd::neon`), on the same footing:
  each intrinsic is a one-line wrapper with a trusted spec, checked against
  the real instructions by verilith-simd's `tests/neon.rs` on AArch64. The NEON
  classifier (`src/neon.rs`) and verilith-simd's `movemask64` are verified against
  the same contracts as the AVX2 kernels. The NEON digit kernel uses seven
  more of these wrappers (`mul` and `uaddlp` at 8, 16 and 32 bits, and the
  high 64-bit lane), added to verilith-simd for it. Off AArch64 the wrappers run an
  emulation, so the NEON kernels are also tested on x86
  (`cargo test neon`) and, under qemu, on AArch64.
  Off x86-64 the 16-byte scans (`classify_special`, `classify_non_ws`,
  `classify_non_digit`, `digit_run_acc16`, `copy_plain16`) choose, in
  verified code, between the NEON kernels and verified scalar loops (for
  WebAssembly without SIMD128); `cargo test portable_kernels` runs the
  scalar loops on x86-64.
* **Vec capacity.** vstd does not model a `Vec`'s capacity, so
  verilith-core's `spare` (re-exported by `src/lanes.rs`) declares it as an
  uninterpreted `spare` and wraps
  `reserve`, a `push` into reserved space without the capacity check, and
  element assignment with specs saying how each changes it. Stage 2
  reserves a token per index entry and proves that every push has room.
* **Target-feature trampolines.** Verus rejects `#[target_feature]` on
  verified code (verus-lang/verus#3362), so each kernel entry point
  (`utf8_avx2`, `utf8_avx512`, `index_avx2`, `index_avx512`) is an
  `external_body` wrapper that calls a one-line `unsafe` trampoline in
  `mod tf`, which carries the attribute and calls the verified `*_body`
  function. The wrapper's contract is copied from `*_body`, whose proof
  Verus checks; what is trusted is only that the two calls forward. Each
  wrapper requires the CPU features its trampoline enables.
* **CPU feature detection** is verilith-simd's (`has_avx2`, `has_avx512vbmi2`,
  `has_pclmul`, `has_popcnt`, `has_bmi2`, which wrap
  `is_x86_feature_detected!`, and `has_neon`, true exactly on AArch64,
  where NEON is baseline). Running a kernel on a CPU that lacks its
  instructions is undefined behaviour, so these are trusted to be
  accurate. That each kernel and each trampoline is called only when the
  features it needs were detected is proven: the trampolines require the
  predicates for every feature they enable.
* A fuzz run of 2 million mutated inputs (`examples/proto2 --fuzz`)
  checks that the two-pass parser and the one-pass parser agree token for
  token.
* `src/ffi.rs`, the C ABI, is ordinary unsafe Rust. Its `TreeSink` methods
  are trusted (`external_body`): they turn tokens into `cJSON` nodes. The
  rest of the C ABI (building, editing, printing, comparing and freeing
  trees) is a port of cJSON 1.7.19's code and makes no syntax decisions.
  String decoding calls the verified decoder, printing strings calls the
  verified escaper, and `cJSON_Minify` is the verified
  `minify::minify_in_place` (proven to leave exactly `spec_minify` of the
  input, in place, without reading or writing past the string's NUL).
* **Vec capacity as a number.** `len_spare` in verilith-core's `spare` wraps
  `Vec::capacity` with the spec that it is the length plus the spare
  room. `set_aux` uses it to size the side array of stored values.
* **Reading stored values back.** `src/value.rs` reads a tagged token's
  slot (proven right, above) as ordinary Rust. Tests check eager reads
  against lazy ones and against `f64::from_str` bit for bit, and the
  `parse` fuzzer checks every number it reads, eager and lazy, against
  `f64::from_str`. Allocation is Rust's: how much capacity a `Vec` keeps
  beyond its length is up to the standard library.
* `src/number.rs`: `lexeme_bits`, which calls `ex_number_scan` and
  `to_bits` and sets the sign bit, is verified to return the correctly
  rounded bits of the lexeme's `number_value` whenever it returns any,
  and `parse_i64` to return an integer lexeme's value exactly when it
  fits in `i64`. What is left unverified is `f64::from_bits` of those
  bits, and lexemes with more than 19 significant digits, or that
  `to_bits` cannot decide, which go to `f64::from_str`.
* `src/writer.rs` (the `Writer` state machine: brackets, commas and colons)
  and `src/serde_support.rs` are ordinary Rust, tested by parsing what they
  write. Floats are formatted by the `zmij` crate, as in serde_json; its
  output is checked against the verified grammar before it is written.
* `src/value.rs`, the Rust API, is ordinary Rust over the tape; its
  unchecked accesses rely only on the proven facts above.
* `cJSON_GetErrorPtr`'s position is the one the parser reports, as in
  cJSON, and is not specified. The `Error` of the Rust and native C APIs is
  (see "Error reasons and positions" above); `src/error.rs` only converts
  it to the public types.

## How verilith-json reads RFC 8259

RFC 8259 leaves some choices to the parser. verilith-json's are in the verified
spec (`document` in `src/spec.rs`), so the parser is proven to follow them:

| Input | RFC 8259 | verilith-json |
|---|---|---|
| A UTF-8 byte order mark at the start | may be ignored (§8.1) | skipped |
| Text that is not UTF-8 | not JSON (§8.1) | rejected |
| A lone surrogate escape, e.g. `"\ud800"` | allowed by the grammar, meaning undefined (§8.2) | rejected (it cannot be decoded to UTF-8) |
| Nesting deeper than 1000 | limits allowed (§9) | rejected |
| Inputs of 256 TiB or more | limits allowed (§9) | rejected |
| Numbers beyond `f64` range, e.g. `1e400` | limits allowed (§9) | accepted; `as_f64` gives ±infinity |
| Duplicate member names | should be unique, behavior unpredictable (§4) | all kept, in order; `get` returns the first |
| `parse_prefix`: data after the value | (not a JSON text) | allowed, except a top-level number directly followed by a byte that could continue it (`01`, `1.`, `2e`), which is rejected rather than read as a shorter number |

serde_json differs from verilith-json on three of these: it rejects a BOM, numbers
beyond `f64` range, and nesting deeper than 128.

## Differences from cJSON

verilith-json follows RFC 8259. cJSON is more permissive in a few places:

| Input | cJSON | verilith-json |
|---|---|---|
| Leading zeros, `-01`, `1.`, `.5`, `2.e3` | accepted | rejected |
| Raw control characters inside strings (tab, newline, ...) | accepted | rejected |
| Any byte `<= 0x20` as whitespace (e.g. form feed) | accepted | only space, tab, CR, LF |
| Some invalid `\u` escapes, e.g. `"\uqqqq"` | accepted | rejected |
| Invalid UTF-8 (stray continuation bytes, overlong forms, surrogates, ...) | accepted | rejected |

The behaviors that callers depend on are kept:

* trailing data after the value is allowed unless `require_null_terminated`
  is set, and `return_parse_end` points just past the value (but a number
  followed by a digit, as in `01`, is rejected: cJSON reads it as 1, and
  reading it as 0 would silently disagree);
* a leading UTF-8 BOM is skipped (cJSON skips it only when more than 4
  bytes follow from the start);
* the nesting limit is 1000;
* duplicate keys are kept in order;
* `\u0000` truncates the C string.

## Test results

* **JSONTestSuite** (`test_parsing`, 318 files), Rust API: every `y_` file is
  accepted and every `n_` file is rejected.
* **JSONTestSuite on the spec itself.** The tests above run the parser,
  which is proven equal to `spec::document`, so they speak for the spec
  only through the proofs. `spec-tests/` checks the spec with no parser
  and no proof involved: each file becomes an
  `assert(document(bytes, true) is Some) by (compute_only)` (or `is None`),
  which Verus proves by running `spec::document` on the file's bytes in
  its own evaluator. All 315 files it can evaluate agree with the suite:
  every `y_` file accepted, every `n_` file rejected, and each `i_` file
  as the table above says. The three files nested 500 levels deep or
  more go past the evaluator's recursion limit and are left out
  (`scripts/spec-tests.sh json`, run in CI).
* **JSONTestSuite through the C API**, `cJSON_ParseWithLengthOpts(...,
  require_null_terminated=1)`, built with ASan and UBSan:
  * verilith-json gets 1 file wrong: `n_multidigit_number_then_00.json`. That file
    has an embedded NUL, which any NUL-terminated C API stops at.
  * cJSON 1.7.19 gets 17 files wrong under the same harness.
* **Upstream cJSON tests**, built with ASan and UBSan: `parse_with_opts`,
  `parse_value`, `parse_array`, `parse_object`, `parse_number`,
  `parse_examples` (which checks parse+print round trips byte for byte),
  `compare_tests`, `print_array`, `print_number`, `print_object`,
  `print_string`, `print_value`, `misc_tests`, `cjson_add` (which includes
  allocation failures through `cJSON_InitHooks`), `minify_tests` and
  `readme_examples` all pass. `parse_string` passes except for one case that
  feeds raw control characters inside a string, which is the difference in
  the table above. Three `misc_tests` cases test cJSON internals that verilith-json
  does not have (its buffer growth and its BOM helper) and are left out.
  `tests/c/cjson_tests/common.h` is a shim for upstream's `common.h`, which
  `#include`s cJSON.c to reach those internals.

* **Differential fuzzing** (`fuzz/`, cargo-fuzz, under ASan; also run in
  CI):
  * `cjson_ops` runs random sequences of cJSON calls (create, add, insert,
    replace, detach, delete, duplicate, parse, print, minify, compare,
    lookups) on verilith-json's C ABI and on upstream cJSON side by side, and
    checks that every result and every printed tree is the same.
  * `cjson_parse` checks that verilith-json accepts only what cJSON accepts, with
    the same printed tree, and that printing and reparsing round-trips.
  * `parse` checks that the Rust API accepts what serde_json accepts (apart
    from the documented differences above), that writing and reparsing
    round-trips, and that serde deserialization gives the same values.
  * `ondemand` checks the on-demand reader against the tape parser: a
    full read through the reader accepts exactly the texts the tape
    accepts and reads the same values, partial reads of an accepted text
    (reading some values, skipping others, leaving containers early,
    searching for keys) end at its end, and calls in no sensible order
    never panic. The same checks run in `tests/ondemand.rs` over
    JSONTestSuite, the benchmark files and mutated inputs (3 million
    mutations and 1.8 million fuzz runs so far, no failure). An earlier
    version of the check found one bug, in the wrapper and not in the
    proven cursor: a NUL byte after the document was taken for the end of
    the input.

  The fuzzers found two mismatches, both now fixed: `01` with trailing data
  allowed (read as 0, where cJSON reads 1), and case-sensitive lookup
  skipping unnamed members where cJSON stops.

## Performance

### Apple M3 Pro (AArch64, NEON)

Speed against simdjson 5.1.1 on an Apple M3 Pro (macOS, Apple clang
`-O3 -mcpu=native`, rustc with `target-cpu=native` and fat LTO), measured
with vbench's json-simdjson runners: 31 interleaved pairs per file, three
sittings. The ratio is simdjson's time over verilith-json's for a parse plus a
read of every value, so above 1 means verilith-json is faster. `99523e5` is before
the NEON digit kernel, `742bee9` has it (and the fast path in
`float::to_bits`), and `f008de7` adds the index writes from a reversed
mask described below.

| File | `99523e5` | `742bee9` | `f008de7` |
|---|---|---|---|
| canada.json | 0.82 | 0.96 to 0.98 | 0.99 to 1.02 |
| mesh.json | 0.86 to 0.88 | 1.04 to 1.06 | 1.04 to 1.07 |
| citm_catalog.json | 0.90 | 0.90 to 0.91 | 0.94 |
| twitter.json | 0.94 to 0.95 | 0.96 | 0.98 to 0.99 |
| github_events.json | 0.96 to 0.97 | 0.98 to 1.01 | 1.03 to 1.06 |
| gsoc-2018.json | 0.95 to 0.98 | 0.97 | 1.04 to 1.08 |

The geometric mean went from 0.91 to 0.97 to 0.98 and then to 1.01 to
1.02. The first column is from an earlier sitting than the other two,
which were measured together.

* **Digit kernel.** On canada.json a parse plus read went from 54.6 to
  43.1 million instructions (simdjson: 44.1 million). Both parsers run at
  about 6 instructions per cycle on this CPU, so the instruction count
  tracks time closely.
* **Index writes.** Stage 1 writes the position of each set bit of a
  64-bit mask. AArch64 has no trailing-zero count, so `trailing_zeros` is
  `rbit` then `clz` for every bit. The NEON path reverses the mask once,
  then takes a leading-zero count and clears the top bit for each
  position, four at first and then two at a time while any are left
  (`put_top` and `put_rev` in `src/simd.rs`).
  The reversal is a shift-and-mask ladder in plain Rust, which rustc
  compiles to one `rbit`, and it is proven that bit `q` of the result is
  bit `63 - q` of the mask. This saved 1% to 3% of instructions and 3% to
  6% of cycles on five of the six files.
* **The NEON loop's shape.** Stage 1's main loop on NEON loads each
  64-byte block once and uses those vectors for the ASCII test of the
  UTF-8 check as well as for the classes. It makes each class mask where
  the bit logic first needs it (backslashes, then quotes, then the rest)
  rather than all five up front, and it writes the positions of both
  blocks of a turn one whole turn later. A later sitting timed stage 1
  alone before and after, with simdjson's stage 1 beside it
  (`examples/ondemand_bench/simdjson_stage1.cpp`), in microseconds:

  | file | before | after | simdjson stage 1 |
  |---|---:|---:|---:|
  | twitter | 82.5 | 79.1 | 69.8 |
  | citm_catalog | 200.2 | 183.8 | 163.5 |
  | canada | 288.4 | 272.4 | 317.4 |
  | github_events | 7.42 | 6.83 | 5.9 |
  | gsoc-2018 | 343.8 | 351.8 | 303.4 |
  | mesh | 113.6 | 101.5 | 105.0 |

  Cycles fell 8.0% on citm_catalog, 4.1% on twitter and 9.7% on canada
  with instruction counts within 3% either way: the gain is in how much
  of the work overlaps, not in doing less. (The gsoc-2018 figure in the
  "before" column did not reproduce: rebuilt clean, "before" is 343 and
  "after" 324.)
* **The ASCII test for free.** The control-character mask is made with a
  compare that also marks the bytes from 0x80 up. Where that mask has no
  bit outside whitespace the block is ASCII and the mask is exactly its
  control characters, so the UTF-8 check's ASCII test needs no vector
  work of its own, and one branch covers 128 bytes. Otherwise an
  out-of-line function finds the high bytes, runs the UTF-8 check on both
  blocks and takes the high bytes out of the error masks. Index writes
  became six at first, then two at a time. Stage 1 alone, microseconds:

  | file | before | after | simdjson stage 1 |
  |---|---:|---:|---:|
  | twitter | 79.0 | 82.1 | 69.8 |
  | citm_catalog | 183.7 | 168.2 | 163.5 |
  | canada | 268.2 | 238.7 | 317.4 |
  | github_events | 6.79 | 6.38 | 5.9 |
  | gsoc-2018 | 324.4 | 299.2 | 303.4 |
  | mesh | 101.4 | 96.0 | 105.0 |

  Five files are 5% to 11% faster. twitter, where a third of the
  128-byte turns hold non-ASCII text and take the out-of-line path, is 4%
  slower. simdjson's stage 1 is now level on gsoc-2018, 3% faster on
  citm_catalog, 8% on github_events and 15% on twitter.
* Converting each number to its `f64` bits during the parse, as simdjson
  does, was proven and measured too, and was slower on this CPU (0.76 to
  0.78 on canada.json) although it ran fewer instructions, so the
  conversion stays in the read.

#### On-demand reader

`examples/ondemand_bench` times each access pattern three ways: a full
parse to the tape and a read from it (eager and lazy), and the on-demand
reader, which runs stage 1 and reads from its index. Microseconds per
document, best of many interleaved runs, median of three sittings; the
last column is the faster tape mode over on-demand. The Mac was lightly
loaded during these sittings (about two other busy cores); a second pass
agreed within about 2%.

| file | pattern | eager | lazy | on-demand | stage 1 alone | on-demand speedup |
|---|---|---:|---:|---:|---:|---:|
| twitter | 8 fields of every tweet (simdjson's partial_tweets) | 167.0 | 164.8 | 131.7 | 88.5 | 1.25 |
| twitter | user ids of tweets and retweets | 162.5 | 155.9 | 132.2 | 90.0 | 1.18 |
| twitter | find one tweet by id (halfway) | 154.1 | 148.0 | 108.1 | 90.0 | 1.37 |
| twitter | one field at the end | 151.8 | 145.6 | 112.6 | 90.0 | 1.29 |
| citm_catalog | performances: ids, start, prices | 411.4 | 398.2 | 294.0 | 218.3 | 1.35 |
| citm_catalog | events: id and name | 384.3 | 371.6 | 226.5 | 218.4 | 1.64 |
| github_events | type, time, actor, repo per event | 14.8 | 14.3 | 11.2 | 8.1 | 1.28 |
| gsoc-2018 | project and sponsor names | 603.9 | 514.8 | 457.8 | 369.3 | 1.12 |
| canada | feature names only | 1092.1 | 848.9 | 414.3 | 310.2 | 2.05 |
| canada | sum every coordinate | 1587.4 | 2201.7 | 1744.2 | 310.5 | 0.91 |
| mesh | positions and indices | 692.6 | 634.3 | 359.5 | 124.0 | 1.76 |
| twitter | read everything | 192.5 | 238.7 | 189.5 | 90.0 | 1.02 |
| citm_catalog | read everything | 510.3 | 547.5 | 481.2 | 218.2 | 1.06 |
| github_events | read everything | 16.9 | 20.8 | 16.5 | 8.1 | 1.02 |
| gsoc-2018 | read everything | 643.5 | 1652.2 | 609.2 | 374.4 | 1.06 |
| canada | read everything | 1834.8 | 2400.0 | 2033.5 | 310.5 | 0.90 |
| mesh | read everything | 651.1 | 827.8 | 651.2 | 124.1 | 1.00 |

The geometric mean over the eleven partial reads is 1.35, and 1.01 over
the six full reads. The gain is bounded by stage 1, which the reader still
runs over the whole input: it is 67% to 96% of the on-demand time on the
text-heavy partial reads. Where every number is read (canada), on-demand
is about 10% slower than the eager tape, whose stage 2 scans numbers in a
tighter loop.

Against simdjson 5.1.1's On Demand front end on the same patterns
(`examples/ondemand_bench/simdjson_od.cpp`, same sittings):

| file | pattern | verilith-json on-demand | simdjson On Demand | simdjson DOM | simdjson On Demand / verilith-json |
|---|---|---:|---:|---:|---:|
| twitter | 8 fields of every tweet | 131.7 | 104.7 | 157.1 | 0.80 |
| twitter | find one tweet by id | 108.1 | 86.4 | 145.9 | 0.80 |
| twitter | one field at the end | 112.6 | 94.0 | 145.2 | 0.84 |
| canada | sum every coordinate | 1744.2 | 1659.4 | 1537.1 | 0.95 |

simdjson is 16% to 20% faster on twitter. A later sitting timed its
stage 1 alone (`iterate` with nothing read) to split the difference:

| twitter | verilith-json stage 1 | simdjson stage 1 | verilith-json reading | simdjson reading |
|---|---:|---:|---:|---:|
| 8 fields of every tweet | 87 | 72 | 42 | 23 |
| find one tweet by id | 84 | 75 | 17 | 11 |
| one field at the end | 84 | 75 | 22 | 19 |

So the gap has two parts. Stage 1 is about 12 microseconds slower than
simdjson's on this file (on canada it is faster, 305 against 341). And
key lookup costs about twice simdjson's: verilith-json's index holds both quotes
of every string where simdjson's holds one, and `find` reads each key as
a string before comparing it.

### x86-64 cloud VM

MB/s on a cloud VM (Intel Xeon @ 2.10GHz, AVX2 and AVX-512), against
simdjson built from source with `g++ -O3 -march=native` through its DOM
API. Both parsers are reused and both check UTF-8. verilith-json uses one
`Parser`, switched to lazy mode for parse alone and to eager mode for
parse and read (simdjson's side also uses one parser for both), built
with the default target (no `-C target-cpu`). `bench/sustained.sh` runs
each tool alone in its own process, pinned to one core with `taskset`,
five times back to back before the other takes its turn, for three
rounds, and keeps the best run of each. Each run takes the best of 200
timings. Both tools were measured in the same sitting, because this VM's
clock drifts over a day, and runs on this VM vary by up to 10%.

| File | simdjson parse | verilith-json parse | ratio | simdjson parse + read | verilith-json parse + read | ratio |
|---|---|---|---|---|---|---|
| twitter.json | 5468 | 5600 | 1.02 | 4073 | 3544 | 0.87 |
| citm_catalog.json | 5269 | 5244 | 1.00 | 3831 | 3040 | 0.79 |
| canada.json | 1471 | 2756 | 1.87 | 1127 | 1016 | 0.90 |
| small.json (escape-heavy) | 3320 | 3724 | 1.12 | 2729 | 2308 | 0.85 |

Interleaved runs (`cmp.sh`-style, ten rounds) in the same session gave
parse + read ratios of 0.87 (twitter), 0.89 (citm_catalog), 0.95 (canada)
and 0.85 (small). After the number and escape changes at the end of
"Since then" below, three interleaved sessions of 25 to 30 rounds gave
0.93 to 0.97 (twitter), 0.94 to 0.99 (citm_catalog), 0.94 to 0.95
(canada) and 0.83 to 0.87 (small); simdjson's own speed moved by up to 8%
between sessions. Counted with callgrind, verilith-json now runs about 10% more
instructions than simdjson in each of its two stages on twitter.json, and
3% to 18% more on parse plus a full walk across the four files. The
previous table, before the changes listed under "Since then" below, had
0.84, 0.80, 0.79 and 0.79.

Here every step from the number's text to its `f64` bits is verified
except `f64::from_bits` (and, on the fast path, verilith-core's statement of IEEE
754 `*`, `/` and `u64 as f64`). Before the conversion was verified (with an
unverified Eisel-Lemire and Clinger's floating-point fast path), canada.json
read at 916 MB/s against simdjson's 1093 in an earlier sitting (0.84x); the
proven version costs about 4% there. Rounding in it is branchless: with
a branch, the round-up decision mispredicted on about half of all numbers
and canada.json read at 636 MB/s.

Before escaped strings were decoded in one pass (below), parse + read was
3055 MB/s on twitter.json (0.78x) and 1782 on small.json (0.65x).

In an earlier sitting, before the read-path changes below, verilith-json's parse +
read was 2642 MB/s on twitter.json (0.67x simdjson), 2817 on citm_catalog.json
(0.79x), 893 on canada.json (0.81x) and 1680 on small.json (0.60x).

The two parsers do different amounts of work while parsing, so the table has
two halves:

* **Parse** is what a lazy parse costs. simdjson converts every number and
  unescapes every string during the parse. `Parser::lazy` checks the
  number and escape grammar but leaves the bytes where they are, which is
  most of its lead on canada.json (almost all numbers).
* **Parse + read** also visits every value: every number as an `f64`, and
  every string and key decoded. This is the like-for-like comparison.
  **verilith-json does not beat simdjson on parse + read for any of these files**:
  it is at 0.93 to 0.99 of simdjson's speed on twitter.json,
  citm_catalog.json and canada.json, and 0.83 to 0.87 on small.json.

`Parser::new` (and `parse`) works eagerly, like simdjson. While lexing a
number the verified parser also accumulates its digits, so reading it is
only the final Eisel-Lemire step. It decodes strings with escapes into
one shared buffer, so reading them does not allocate. The payloads go in a
side array indexed like the tape, so tokens stay 12 bytes, and the eager
and lazy modes are separate `Sink` types, so each gets its own compiled
parse loop and the lazy one does no eager bookkeeping. Eager reading is
about 10% faster than lazy on canada.json and small.json and level on the
others. `\uXXXX` escapes are decoded through a 256-entry hex table whose
every entry the verifier checks by evaluation.

Digits are accumulated 16 at a time: an SSE2 compare finds the length of
the digit run (verified), and the run's value is combined in-register
with multiply-add instructions, so the end of a run costs no branch
misprediction. This replaced a one-digit-at-a-time loop, which mispredicted
at the end of almost every number. (An earlier eight-at-a-time SWAR attempt
measured no faster; the difference is that the run length now comes from
one vector compare instead of a branch per digit.)

The read path was then made cheaper in three ways:

* A `Value` is two words: a reference to the document's slices (input,
  tokens and side arrays) and a token index. Reading no longer goes
  through the tape's `Cow` for every access. This cut reading instructions
  by 5% to 8%.
* Strings, keys and numbers are sliced from the input without a bounds
  check, which the proof above justifies. This cut another 4% to 11%.
* The digit kernel no longer checks for SSSE3 on every call. That check,
  and the out-of-line call it led to, cost about 1 million instructions
  (3%) per canada.json parse. The SSE2 kernel is always used, and is now
  verified.

At that point, counted with callgrind, verilith-json spent 9% to 16% more instructions than
simdjson on parse plus a full walk of twitter.json, citm_catalog.json and
canada.json. The time gap is larger than that, so some of it is
instruction-level parallelism, not instruction count. small.json is mostly
`\uXXXX` escapes; verilith-json's verified decoder spends about 37 instructions
on each in a run of them (down from 70), against about 35 for simdjson.

Escaped strings are validated and decoded in one pass. Stage 2 used to
check each escape while walking the string's index entries, and the eager
sink then decoded the whole body again. Now the eager sink's `scan_str`
calls `ex2_string_dec`, which decodes each escape as it checks it, and
proves that the bytes it appends are `decode` of the body that `string`
accepts. Strings without escapes take an inline path that only looks at
the first index entry; the rest is out of line. This cut small.json's
eager parse from 35.6k to 30.0k instructions and its time by about a
third.

Since then:

* Integer parts of up to three digits take a scalar path instead of the
  16-digit kernel (canada.json parse -14%).
* Arrays whose elements are numbers are parsed in line in stage 2, so
  canada.json's coordinate pairs cost no call each (parse -9%).
* The byte after a scalar is checked by a 256-entry table, verified by
  evaluation, rather than by a chain of compares.
* `true`, `false` and `null` are matched with one four-byte compare
  (twitter.json parse -4% instructions).
* The reader takes tokens by reference and, given `ends_value`, reads the
  root and every member's value without a bounds check.
* Stage 1 writes structural positions eight at a time, deciding each group
  by the count of set bits. One branch per eight writes instead of per
  four cut stage 1's simulated branch mispredictions on citm_catalog.json
  by a quarter.
* Stage 2's out-of-line functions return their results in registers.
  `ex2_elements` returned a 24-byte `Option<(usize, usize)>`, which went
  through memory, and LLVM then kept every value result of the inlined
  parse loop in that stack slot too. It now returns the index count alone
  (the end is read back from the index), and the escaped-string path
  packs its result into two words. Together these cut parse instructions
  by 3% to 4% on twitter.json, citm_catalog.json and small.json.
* The UTF-8 check is written in terms of stage 1's block position, so
  LLVM reuses the classification loads instead of loading the same bytes
  again at unaligned offsets (-1%).
* The benchmark uses one parser for both modes, as simdjson's side does.
  With two parsers, the read loop cycled through twice the buffers, which
  cost up to 7% on citm_catalog.json.
* The AVX-512 UTF-8 check tests its 131-byte ASCII window from the two
  blocks stage 1 has already loaded plus one four-byte load, instead of a
  third 64-byte load that always split a cache line. Stage 1 got 4% to 7%
  faster and is now level with simdjson's (twitter.json 43 vs 42 us,
  citm_catalog.json 115 vs 120, canada.json 149 vs 152).
* Numbers that are values in objects take a shorter verified path: an
  optional sign, an integer part of 1 to 15 digits read by one step of the
  16-digit kernel, then the end or a fraction. Anything else falls back to
  the general scanner. Array elements keep the general scanner, whose scalar
  loop for short integer parts has less latency on canada.json's
  coordinates. This cut citm_catalog.json's parse by 5% of its instructions,
  and parse + read got about 3% faster.
* Simple escapes (`\n`, `\"` and so on) are looked up in a 256-entry table,
  verified by evaluation. The chain of compares had become a jump table,
  whose target changed from one escape to the next; callgrind's branch
  simulation showed half of small.json's indirect mispredictions there.
  twitter.json parse + read got about 4% faster.

These were measured and dropped because they were slower or no faster:
* in the one-pass decoder, decoding straight through to the closing quote
  after the first escape (with SIMD copies of plain runs) instead of
  following the index entries: no faster on small.json or twitter.json;
* inlining one level of array parsing into its caller, so that arrays of
  arrays (canada.json's coordinates) take one call per outer array. LLVM
  then outlined the value parser itself, and parsing got 10% slower on
  canada.json and 35% slower on twitter.json;
* converting numbers fully during the parse, or in a separate pass after
  it. This is the same Eisel-Lemire work either way, and simdjson does it
  during the parse.
* caching the token in `Value` (a four-word handle, which spills
  registers in a recursive walk);
* storing a number's sign in its token, which made the parse slower by
  about as much as it made reading faster;
* trying the `\uXXXX` run decoder before the general escape decoder
  (more instructions on twitter.json, where many escapes are surrogate
  pairs);
* writing each token with two stores (8 and 4 bytes) instead of one per
  field: fewer stores, more instructions, no measurable change;
* stage 1 one block per iteration instead of two, or classifying each
  block just before indexing it: more instructions or no change;
* a stage 2 restructuring that stopped LLVM from peeling the first member
  of each object: 2% fewer instructions, but twice the simulated branch
  mispredictions on citm_catalog.json, whose objects share shapes;
* building the UTF-8 check's shifted inputs in registers (`valignq` and
  `vpalignr`) instead of unaligned loads: slower on all four files;
* integer parts by eight-digit SWAR (verified, three multiplies per
  eight digits) instead of the 16-byte kernel: the same instruction count
  for citm_catalog.json's nine-digit ids, and no faster;
* copying the plain runs between escapes with one 16-byte move instead of
  `memcpy`: 0.4% fewer instructions on small.json, within noise;
* a denser layout for number values: no change, so the parse is not
  waiting on memory there;
* stage 2 as one loop with an explicit stack instead of recursion
  (prototyped without proofs first): 4% more instructions on twitter.json
  and 11% more on canada.json, and timings within noise. The recursive
  version's specialized paths (number arrays in line, objects peeled) are
  worth more than the calls cost;
* `\uXXXX` decoding through a 32-bit hex table, so that one compare checks
  all four digits: 3% fewer instructions on small.json but 4% slower,
  measured in both orders;
* testing `[` and `{` with one compare so that the value dispatch is no
  longer a jump table: callgrind's simulated mispredictions on
  citm_catalog.json fell by 17%, but parse + read got 4% to 7% slower on
  small.json and twitter.json. The hardware predicts the jump table better
  than the simulation does;
* jumping over a decoded `\uXXXX` run's index entries in one checked step
  instead of one at a time: fewer simulated mispredictions on small.json,
  but 3% slower there, measured in both orders.

Against serde_json (`examples/serde_speed.rs`, `serde_json::Value` as the
target type, best of 30, microseconds):

| File | verilith-json read | serde_json read | verilith-json write | serde_json write |
|---|---|---|---|---|
| twitter.json | 2500 | 2570 | 503 | 435 |
| citm_catalog.json | 4320 | 4114 | 1119 | 730 |
| canada.json | 9267 | 10060 | 5610 | 3395 |
| small.json | 14 | 9 | 3 | 2 |

Reading is at parity except on small documents. Writing numbers is slower:
every number is checked against the verified grammar before it is written,
and that check costs about as much as formatting it.

The one-pass parser (used by `parse_prefix` and the C ABI) runs at about
40% of the two-pass one. cJSON and verilith-json's C ABI, which keeps cJSON's
one-allocation-per-node layout, run at 300 to 500 MB/s.

## Building

```sh
cargo build --profile release-abort                   # Rust library
cargo build --profile release-abort --features serde  # with serde support
cargo build --profile release-abort --features cjson  # also target/release-abort/libvjson.{a,so} with the cJSON ABI
cargo build --profile release-abort --features capi   # ... with the native C API (include/vjson.h)
cc app.c -Iinclude target/release-abort/libverilith_json.a -lm -lpthread -ldl
```

`include/cJSON.h` is cJSON's header, unmodified. `include/vjson.h` is the
native C API. The two features can be enabled together.

## Verifying and testing

```sh
./scripts/verify.sh            # needs `cargo-verus` on PATH, matching vstd in Cargo.toml
JSON_TEST_SUITE=/path/to/JSONTestSuite/test_parsing cargo test --profile release-abort
cargo test --profile release-abort --features capi --test capi   # the native C API against the Rust API
./scripts/test-c.sh            # both C APIs; clones cJSON and JSONTestSuite at pinned commits
../../scripts/spec-tests.sh json   # spec::document itself on JSONTestSuite, evaluated by Verus
```

## API coverage

Every function declared in `cJSON.h` 1.7.19 is implemented: parsing
(`cJSON_Parse*`, `cJSON_GetErrorPtr`), printing (`cJSON_Print*`), reading
(`cJSON_Get*`, `cJSON_HasObjectItem`, the `cJSON_Is*` predicates),
`cJSON_Compare`, building (`cJSON_Create*`, `cJSON_Add*`), editing
(`cJSON_Detach*`, `cJSON_Delete*From*`, `cJSON_Insert*`, `cJSON_Replace*`,
`cJSON_SetNumberHelper`, `cJSON_SetValuestring`), `cJSON_Duplicate`,
`cJSON_Minify`, `cJSON_Delete`, `cJSON_InitHooks`, `cJSON_malloc`,
`cJSON_free` and `cJSON_Version`. The building and editing functions follow
cJSON's code line for line, including its handling of references, constant
keys and allocation failure. cJSON_Utils (JSON Pointer and Patch) is not
included.

## Layout

```text
src/spec.rs      RFC 8259 grammar as Verus spec functions
src/parser.rs    verified one-pass parser and the Sink trait
src/index.rs     verified stage 1: the structural index
src/stage2.rs    verified stage 2: parsing through the index
src/ondemand.rs  verified on-demand cursor and the Reader over it
src/protocol.rs  the Reader's protocol against the tape (verified)
src/lanes.rs     single-instruction SIMD wrappers, verified over verilith-simd (the 16-byte SSE2 ones are
                 verilith_simd::sse2, shared with verilith-xml), and two stores into a Vec's
                 reserved space (the capacity model is verilith_core::spare)
src/simd.rs      verified classification and bit-mask kernels built from them
src/utf8.rs      verified SIMD UTF-8 validation (the UTF-8 spec, its local
                 condition, the lookup tables' proof and the scalar validator
                 are in verilith_core::utf8)
src/lemmas.rs    proofs about the spec
src/value.rs     Rust API over the tape
src/native.rs    native C API over src/value.rs (unverified, feature `capi`; include/vjson.h)
src/diag.rs      error reasons and positions (verified)
src/error.rs     the public error types
src/write.rs     verified string escaping and number checks for the writer
src/writer.rs    Writer (unverified state machine over src/write.rs)
src/serde_support.rs  serde Serializer/Deserializer (feature `serde`)
src/float.rs     verified correctly rounded conversion of w * 10^q to f64 bits
src/number.rs    verified glue from the scanner to src/float.rs (src/pow5.rs is its table)
src/minify.rs    verified in-place cJSON_Minify
src/ffi.rs       cJSON-compatible C ABI (unverified)
examples/        benchmark and debugging drivers
bench/           like-for-like benchmark against simdjson
fuzz/            differential fuzzing against cJSON and serde_json
scripts/         verification, C tests, table generation
include/cJSON.h  cJSON's public header
tests/parse.rs   Rust tests, including JSONTestSuite
tests/ondemand.rs  the on-demand reader against the tape parser
tests/c/         C harnesses and the upstream-test shim
```

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/json/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/json/LICENSE-MIT), at your option.

`include/cJSON.h` and the tree-building functions in `src/ffi.rs`, which
are ported from cJSON 1.7.19, are under cJSON's MIT license, whose notice
is at the top of `include/cJSON.h`.
