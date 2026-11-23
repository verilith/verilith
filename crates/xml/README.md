# verilith-xml

An XML 1.0 parser for Rust whose parser is formally verified with
[Verus](https://github.com/verus-lang/verus). For every input, the parser is
proven to return exactly what an executable statement of the
well-formedness rules of XML 1.0 (Fifth Edition) returns: the same verdict,
and the same tape of the document's items. It is proven never to panic or
overflow, to terminate, to use no recursion (an element nested a million
deep needs no stack), and to write at most one token per input byte.
Crafted input cannot make it slow: the checks on entities are linear in
the input, and attribute names and entity references go through hash
tables seeded at random for each document, whose results are proven equal
to the spec's. It reads UTF-8, UTF-16, ISO-8859-1 and US-ASCII through
verified decoders.

On thirteen documents it checks one 3.1 to 18.6 times as fast as expat
2.10.0 (geometric mean 5.7x) and 2.4 to 17 times as fast as libxml2 2.15.4
(4.2x), and parses and reads one through its API 1.2 to 14 times as fast
as expat (2.2x) and 1.1 to 9 times as fast as libxml2's SAX2 interface
(1.8x), measured with the repository's benchmark harness on an x86-64
cloud VM (see [Performance](#performance)). On an Apple M3 Pro the gaps
are smaller: 2.23x and 1.72x checking, 1.35x and 1.14x reading.

**Status:** early, not yet published. What is proven and what is trusted
is listed below; read [What is not proven](#what-is-not-proven) before
relying on it. With the feature `expat-abi` it is a drop-in for libexpat:
a C program built against expat 2.10.0's `expat.h` links
`libverilith_xml.a` in place of `libexpat.a` and runs unchanged, 1.2 to 9
times as fast reading a document through expat's callbacks (see
[The expat C ABI](#the-expat-c-abi)). There is no libxml2 ABI yet.

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let doc = verilith_xml::parse(br#"<?xml version="1.0"?>
    <book id="b1"><title>Verified &amp; fast</title></book>"#)?;
    let book = doc.root();
    assert_eq!(book.name(), "book");
    assert_eq!(book.attribute("id").as_deref(), Some("b1"));
    assert_eq!(book.elements().next().unwrap().text(), "Verified & fast");
    Ok(())
}
```

## Design

`parse` runs four verified steps and then hands out borrowed views:

1. **Encoding** (`src/enc.rs`). A UTF-16 byte order mark means UTF-16;
   otherwise the XML declaration, read as ASCII, may name ISO-8859-1 or
   US-ASCII; otherwise the input is UTF-8. UTF-16 and ISO-8859-1 are
   decoded to UTF-8 (proven against `utf16_dec` and `latin1_dec`), and
   ASCII runs of ISO-8859-1 are copied sixteen bytes at a time.
2. **Characters** (`src/chars.rs`). One pass checks that the text is
   well-formed UTF-8 and that every character is a `Char`, sixteen ASCII
   bytes at a time.
3. **The document** (`src/lex.rs`, `src/dtd.rs`, `src/content.rs`,
   `src/doc.rs`). One pass writes a *tape*: a 32-byte token per item, in
   document order, with byte ranges into the text for every name, value
   and run of text, so nothing is copied. Elements are a loop with an
   explicit stack of the open elements, not a recursion. A start tag's
   token holds the index of the token that closes it, so a reader skips
   an element in one step. Character data, attribute values, comments,
   CDATA sections and processing instructions are scanned sixteen bytes
   at a time with SSE2 (`src/scan.rs`). Names go through a 256-entry
   table for ASCII and are decoded otherwise.
4. **Entities** (`src/ent.rs`). After the internal subset, the
   replacement text of each internal entity is computed once, and the
   parser works out which entities may be referred to in content and in
   attribute values: the least fixed point of "its replacement text is
   right, and so is every entity it refers to", computed with a worklist
   (`src/fix.rs`) in time linear in the entities and their references.
   The document's references are then checked against it as they are
   met.

The API (`src/api.rs`) reads the tape: `Document::root`, and
`Element::name`, `attrs` (an iterator) and `attributes`, `attribute`,
`children`, `elements` and `text`. A reference to an internal entity is
expanded where it is read: the entity's replacement text is parsed as
content by the verified parser the first time it is needed, and its tape
is then read in place, so a reference costs nothing to expand twice and a
"billion laughs" document parses in microseconds. Character data comes
back with line ends normalized, attribute values normalized (§3.3.3, with
the DTD's defaults and declared types), both through verified decoders
(`src/decode.rs`). A rejected document gives an `Error` with its kind and
its line, column and byte offset.

## What is proven

Everything in `src/spec.rs`, `src/chars.rs`, `src/lex.rs`, `src/dtd.rs`,
`src/content.rs`, `src/doc.rs`, `src/ent.rs`, `src/enc.rs`, `src/decode.rs`,
`src/uniq.rs`, `src/index.rs`, `src/scan.rs`, `src/lanes.rs` and
`src/tape.rs` is checked by Verus (`./scripts/verify.sh`, which runs
`cargo verus verify`: 358 verified, 0 errors, in a few minutes on x86-64;
fewer for an AArch64 target, which has no SSE2 code. The SSE2 wrappers are
verified in verilith-simd). The trusted base is listed under
[What is not proven](#what-is-not-proven).

* **Conformance.** `src/spec.rs` states XML 1.0 (Fifth Edition)
  well-formedness for a document as Verus spec functions over its bytes,
  one per production, with the production numbers of the Recommendation:
  the prolog and the XML declaration, the document type declaration and
  every declaration the internal subset can hold (element types with
  their content models, attribute lists, general and parameter entities,
  notations), elements, attributes, references, comments, processing
  instructions, CDATA sections and character data. Each well-formedness
  constraint is in it where it applies: Element Type Match, Unique Att
  Spec, No External Entity References, No < in Attribute Values, Legal
  Character, Entity Declared, Parsed Entity, No Recursion and PEs in
  Internal Subset, and that a referenced internal entity's replacement
  text is well-formed content (§4.3.2). `document` turns the text into a
  tape, and `parse` adds the encodings. `enc::ex_parse` is proven to
  return exactly what `spec::parse` returns, for every input: the same
  verdict, the same decoded text, and the same tape, token for token.
  Each function under it is proven against the spec function of the same
  name.
* **Characters.** Name characters are the Fifth Edition's ranges, read
  from code points that `utf8_len` (verilith-core, Unicode Table 3-7)
  decodes. The table that classifies ASCII bytes is checked for all 256
  entries by evaluation.
* **Panic freedom and termination.** No index is out of bounds and no
  arithmetic overflows or underflows anywhere in the verified code; every
  loop and recursive call has a measure Verus checks.
* **No recursion.** Content is a loop over items with an explicit stack,
  in the spec and in the code, so there is no nesting limit and stack use
  does not grow with the input. The attribute-value decoder, which follows
  references into replacement texts, keeps an explicit stack of frames
  too, so a chain of references 100 000 deep reads like a short one.
* **Memory.** The tape has at most one token per input byte (`ex_document`
  ensures `tape.len() <= s.len()`), and an entity's replacement text is
  no longer than its literal value (`ex_repl`).
* **Entities, with no limit on nesting, in linear time.** Which entities
  may be referred to where is a fixed point (`oka_seq`, `okc_seq`): an
  entity may be referred to in content if its replacement text parses as
  content whose own references may be, at one level less; a reference
  cycle never gets there, which is how the spec says No Recursion. The
  spec takes as many levels as there are entities, and
  `lemma_oka_settled` and `lemma_okc_settled` prove that more levels
  allow nothing more (a longer chain names some entity twice), so the
  depth of nesting has no limit. The code does not go level by level,
  which would be quadratic on a long chain: `lemma_oka_hlev` and
  `lemma_okc_hlev` prove each table is the least fixed point of Horn
  clauses (each entity's own verdict, and the entities it refers to,
  from one pass over the replacement texts), and `fix::ex_hfix` is proven
  to compute that fixed point with a worklist, in time linear in the
  entities and their references.
* **Entity lookup in constant time.** A reference finds its entity
  through an index of the entities by name (`src/index.rs`): a table of
  chains, seeded at random, that holds only the first declaration of each
  name, the binding one (§4.2). The lookup is proven to return exactly
  `find_ent`, the spec's first declaration among those processed, also
  when it is limited to the entities declared before an attribute
  default. A linear search would make a document of n bytes with many
  declarations and many references cost about n²/600 comparisons.
* **Attribute names in linear time.** A start tag with more than sixteen
  attributes is checked for duplicates with a hash table of chains
  (`src/uniq.rs`), proven to give exactly the spec's verdict that no two
  names are equal: equal names hash alike, so a duplicate meets its
  original in one chain. The hash is seeded at random for each tag, as
  expat's is since CVE-2012-0876, so no input can put many names in one
  chain. (The quadratic check this replaced took 3.6 s on a tag of 50 000
  attributes.)
* **Reading back.** `decode::eol` (line ends, §2.11) and
  `decode::att_norm` (the normalized value of an attribute, §3.3.3, with
  entity references expanded) state what the text means, and the
  decoders are proven to produce it.
* **SIMD.** Each scanner in `src/scan.rs` is proven, from verilith-simd's
  specifications of the SSE2 instructions it uses, to skip only bytes its
  loop's spec passes over the same way (a lemma per loop shows that), so
  the loops are proven against the same byte-at-a-time spec.
* **The spec says what it appears to say.** Termination checking is
  syntactic, so the spec has a few guards of the form
  `if !(i < e <= s.len()) { None }` before it continues; each step moves
  forward and stays in the input, so they are not taken.

### What is not proven

* **The API** (`src/api.rs`, 690 lines, no `unsafe`) is ordinary Rust over
  the verified tape and decoders: navigation, the table of attribute
  definitions built from the DTD's tokens (which ones apply, defaults,
  and the collapsing of white space for declared types other than CDATA),
  and the conversion of byte spans to `&str` (checked, with
  `str::from_utf8`). It is tested: the W3C suite's 262 output tests that
  need no external entity produce the expected canonical form byte for
  byte, and the differential tests against expat below compare canonical
  forms on millions of documents. Its tables of attribute definitions are
  hash maps, so that supplying defaults stays proportional to an element's
  own definitions.
* **The expat ABI** (`src/api/expat.rs`, 2930 lines, feature `expat-abi`)
  is ordinary Rust with `unsafe` at the C boundary: it calls the caller's
  handlers with pointers into the document and into its own buffers, and
  trusts the pointers and lengths the caller passes, as a C library does.
  It is tested by libexpat's own tests under ASan and UBSan (see
  [The expat C ABI](#the-expat-c-abi)).
* **Error positions** (`Tape::err`, and the line and column in `Error`)
  are diagnostics outside the spec: the verified parser decides whether
  the document is well-formed, and records where the step that failed
  started.
* **The spec itself.** Read it against the Recommendation; the W3C suite
  checks it (below).
* **The trusted base:** verilith-simd's specifications of the six SSE2
  instructions the scanners use (`_mm_loadu_si128`, `_mm_set1_epi8`,
  `_mm_cmpeq_epi8`, `_mm_or_si128`, `_mm_min_epu8`, `_mm_movemask_epi8`),
  tested there against the CPU. The wrappers proven from them are
  verilith-simd's `sse2` module, shared with verilith-json; vstd's specifications of `Vec` and
  slices; the two `external_body` functions in the crate: `uniq::seed`,
  which reads random words for the hashes (any value gives the same
  result), and `tape::slice_len_bound`, which states that a slice is at
  most `isize::MAX` bytes long, as Rust guarantees of every object, so
  that positions cannot overflow; Verus, Z3 and the Rust compiler.
* **Other targets.** The scanners use SSE2 on x86-64. Elsewhere they skip
  nothing and the scalar loops do the work (verified the same); there are
  no NEON kernels yet, so AArch64 runs slower than the numbers below.

## How verilith-xml reads XML 1.0

The Recommendation leaves some choices to a non-validating processor.
verilith-xml's are in the verified spec, so the parser is proven to follow
them:

| Input | XML 1.0 | verilith-xml |
|---|---|---|
| The external DTD subset, external entities | need not be read (§5.1) | not read; a reference to an external parsed entity in content is `Child::Unexpanded` |
| A parameter entity reference in the internal subset | need not be read (§5.1) | not read (expat's default too); later entity and attribute-list declarations are checked but not processed, unless the document is standalone |
| A reference to an undeclared entity where "Entity Declared" does not apply (an unread declaration may declare it) | the processor cannot expand it | `Child::Unexpanded` in content; kept as written in an attribute value (expat drops it); `Document::has_unread_declarations` says when this can happen |
| Encodings | UTF-8 and UTF-16 required, others optional (§4.3.3) | UTF-8, UTF-16 (with its byte order mark, which §4.3.3 requires), ISO-8859-1, US-ASCII; the declaration must name the encoding the document is in |
| `version="1.1"` and other `1.x` | may be read as 1.0 (§2.8) | read as 1.0 |
| Names | the Fifth Edition's characters | the Fifth Edition's characters |
| Entity references nested through replacement texts | no limit | no limit (libxml2 rejects past 40 by default); a cycle is recursion, rejected where it is referred to |
| A reference cycle among entities that are not referred to | not an error | not an error |
| Element nesting | | no limit |
| Expanding a "billion laughs" entity | | parsing is linear; content expands lazily as it is read; an attribute value is read whole, which for the classic document is 3 GB (`try_attributes(limit)` refuses a value past `limit` bytes, for untrusted input) |
| Namespaces | a separate Recommendation | not processed: a name with a colon is a name |

## Differences from expat

expat is the reference for the differential tests (below). Where the two
disagree, it is on a rule of XML 1.0 that expat does not check, in each
case found by fuzzing:

* **Names outside ASCII.** expat's name tables are those of XML 1.0
  before the Fifth Edition (from Unicode 2.0), give or take: it rejects
  names the Fifth Edition allows (`<\u{EFFFF}/>`, U+0E5C) and takes `µ`
  (U+00B5) for a letter, which no edition does.
* **Version numbers.** expat accepts `version="1"`, `"1."`, `"10"`, `""`;
  VersionNum is `'1.' [0-9]+`.
* **Byte order marks.** expat accepts a UTF-8 BOM before
  `encoding="ISO-8859-1"` (the W3C suite's hst-lhs-007 is not
  well-formed), and UTF-16 without a BOM.
* **The internal subset.** expat stops checking declarations after a
  parameter entity reference it does not read (a `<` in an attribute default there
  is still not well-formed), and decides whether an attribute default's
  entity must be declared before it has seen the rest of the internal
  subset, where a later parameter entity reference lifts the constraint.

## The expat C ABI

`cargo build --profile release-abort --features expat-abi` adds expat's C
API to the library (`src/api/expat.rs`, not verified): all 83 functions
libexpat 2.10.0 exports, with the struct layouts of its `expat.h`
(`XML_GetUserData` reads the parser's first field, as the header's macro
does). Build the caller against libexpat's own `expat.h` and
`expat_external.h`, and link `libverilith_xml.a` (with `-lpthread -ldl -lm`)
instead of `-lexpat`.

The verified parser decides whether the document is well-formed and writes
its tape; the ABI turns the tape into expat's callbacks in document order:
the XML declaration, the document type declaration and every declaration
in the internal subset (entities, notations, attribute lists, element
types with their content models as `XML_Content` trees), elements with
their attributes (defaults from the DTD after the specified ones, as
`XML_GetSpecifiedAttributeCount` counts them; `XML_GetIdAttributeIndex`),
character data, CDATA sections, comments, processing instructions, skipped
entities, and the default handler (with `XML_SetDefaultHandler` an internal
entity reference is reported instead of expanded, as expat does). Internal
entities are expanded from the replacement text's tape, without a copy.
`XML_ParserCreateNS` processes namespaces over the names the verified parser
read, with expat's errors for unbound and reserved prefixes and its
triplets. `XML_StopParser` and `XML_ResumeParser` stop and resume between
callbacks. Line, column and byte positions are those of the item being
reported, and of the error. An `ExternalEntityRefHandler` is called for a
reference to an external parsed entity, and the parser it makes with
`XML_ExternalEntityParserCreate` reads the entity as content, with the
parent's internal subset in scope; nested references to the same entity
are rejected as recursion. An `UnknownEncodingHandler` is called for an
encoding the parser does not read, and its map converts the input to UTF-8
first. The encoding passed to `XML_ParserCreate` or `XML_SetEncoding`
(UTF-8, UTF-16, UTF-16LE, UTF-16BE, ISO-8859-1, US-ASCII) takes precedence
over the document's declaration, as external information does (§4.3.3).
With no handler set and no namespaces, `XML_Parse` runs the verified check
alone and builds nothing.

Where it departs from libexpat:

* **The document is checked whole.** `XML_Parse` keeps the input until the
  call with `isFinal` set, then parses it and calls the handlers. No
  handler runs before the last buffer arrives, and an error is found then,
  not in the call whose buffer holds it. Memory is the whole document plus
  its tape (32 bytes per item).
* **No handler runs for a rejected document.** expat reports the items
  before an error; here the verdict comes first.
* **The external DTD subset and external parameter entities are offered to
  the `ExternalEntityRefHandler` but not read**, as verilith-xml does not
  read them (see [How verilith-xml reads XML 1.0](#how-verilith-xml-reads-xml-10)).
  `XML_UseForeignDTD` calls the handler and has no other effect.
* **Error codes** are worked out from the place the verified parser
  stopped; on the common errors they and their positions are expat's
  (mismatched tag, junk after the root, undefined, recursive and binary
  entity references, duplicate attributes, unclosed tokens and CDATA
  sections, misplaced XML declarations, unknown encodings), and otherwise
  the code is `XML_ERROR_INVALID_TOKEN`.
* **Memory.** `XML_Memory_Handling_Suite` allocates what the caller frees
  (`XML_MemMalloc`, content models); the parser's own memory comes from
  Rust's allocator.
* **The amplification limits** (`XML_SetBillionLaughsAttackProtection*`,
  `XML_SetAllocTracker*`) are accepted and kept, and have nothing to limit:
  content expands lazily and parsing is linear. `XML_SetHashSalt` is
  accepted; the hash tables are seeded at random for each document.
* **The default handler** gets the markup of the items that have no
  handler of their own, in content and around the root; the DTD's
  declarations and the white space of the prolog are not reported to it.
* **What the parser accepts** is XML 1.0 Fifth Edition, where libexpat
  differs (see [Differences from expat](#differences-from-expat)): UTF-16
  without a byte order mark is rejected, unless the caller names the
  encoding.

**libexpat's own tests**, built from its 2.10.0 sources with ASan and UBSan
and linked against `libverilith_xml.a` (`scripts/test-expat.sh`, run by
`ci.sh`):

* `tests/runtests`, its unit tests, each at six chunk sizes with reparse
  deferral on and off: 238 of 443 tests pass in every mode. Of the 205 that
  fail, 86 test failing allocators, 33 need handlers to run (or errors to be
  found) before the final buffer, 34 feed UTF-16 without a byte order mark,
  14 need the external subset or external parameter entities read, 9 test
  libexpat's internals, 17 expect another error code or position, and 12
  the default handler's view of the DTD, encoding details or expat's
  amplification accounting.
* `tests/xmltest.sh`: libexpat's `xmlwf` over the W3C suite, comparing
  verdicts and canonical output with expat's expected files: 1402 of 1811
  pass (libexpat itself passes 1803). Of the 409 that fail, 302 are names
  the Fifth Edition allows and the suite's older tests reject, 55 have
  their error in the external subset or an external or parameter entity,
  44 have output that needs the external subset's declarations, and 7 fail
  with libexpat too.

`tests/c/expat-known-failures.txt` lists each failing test and its reason;
CI fails if any other test fails, or if a listed one passes.

## Test results

* **W3C XML Conformance Test Suite** (20130923, through the npm package
  `xml-conformance-suite` 1.2.0, pinned by SHA-256): the 1871 tests that
  apply to XML 1.0 Fifth Edition without namespaces. All 918 valid and
  invalid (well-formed) documents are accepted, UTF-16 ones included.
  Of the 932 not-wf documents, 872 are rejected; the other 60 have their
  error in an external entity or the external subset, or (one,
  not-sa-002) in a parameter entity, none of which are read, and are
  accepted. Of the 21 `error` tests (an error, not a fatal one: the
  document is well-formed), 15 are accepted, and the 6 in EUC-JP,
  ISO-2022-JP and Shift_JIS are rejected, as encodings this processor
  does not read (§4.3.3); `tests/xmlconf.rs` fails if any other is
  rejected. 0 failures.
* **Canonical outputs.** The suite's 262 output tests that need no
  external entity: each document read through `verilith_xml::parse` and
  written in James Clark's canonical form is the expected output, byte for
  byte (`tests/canonical.rs`): references and entities expanded, attribute
  values normalized, defaults supplied, line ends normalized.
* **Differential testing against expat 2.10.0** (`fuzz/`, expat built from
  source): the verdict on each document, and when both accept it, the
  canonical form of what each reads (expat's SAX events against
  verilith-xml's API), on the suite's files, Silesia's XML and the Rust
  parsers' benchmark documents, and mutations of them (byte changes,
  markup inserted and deleted, splices). Over 3.1 million documents, every
  difference is one of those listed under
  [Differences from expat](#differences-from-expat); `ci.sh` runs 310 000
  of them on every change.
* **Coverage-guided fuzzing** (cargo-fuzz, under ASan): `expat` (the same
  comparison) and `api` (reading every part of an accepted document, twice,
  without a panic), from the suite's files. `api` ran 17.2 million inputs
  in ten minutes with no failure. `expat` found one difference in its first
  ten minutes, the last in the list above (now allowed, narrowly, and a
  test in `tests/parse.rs`), and a second ten minutes, 13.3 million
  inputs, found nothing more. Neither found a crash.
* **API tests** (`tests/parse.rs`): a "billion laughs" document parses in
  well under a second, and with a limit refuses the 3 GB attribute value;
  a 3 MiB value is read whole; chains of references 65, 1000 and 100 000
  deep parse and expand, in content and in attribute values, the longest
  in milliseconds; a cycle 1000 long is rejected; a million
  nested elements parse and walk; a tag of 50 000 attributes is checked in
  milliseconds and a duplicate among them is found; 20 000 entities and
  100 000 references to them parse in milliseconds; UTF-16 and
  ISO-8859-1; error positions.

## Performance

The figures below were measured before positions widened from 32 to 64
bits (tokens from 16 to 32 bytes) and before the limits on entity nesting
and input size went. On the same thirteen files, `bench/` (best of 15,
two sittings each, the same cloud VM, 2026-11-22) puts the build after
those changes at 1.03x the build before them for checking (0.97x to
1.09x per file) and 1.02x for reading (0.96x to 1.07x).

### Against expat and libxml2 (vbench)

Measured with the repository's [vbench](https://github.com/verilith/verilith/tree/main/bench) harness
(`bench/run.sh --only xml`) on a cloud VM (Intel Xeon @ 2.10GHz, 4 cores,
x86-64 with AVX-512; Linux; gcc 13.3 at `-O3` and rustc 1.97 with fat LTO,
neither with `-march` or `-C target-cpu`), 2026-11-22: 31 interleaved pairs
per case, expat 2.10.0 and libxml2 2.15.4 built from source by the harness
with the same flags. Speedup is the other parser's time over
verilith-xml's, with its 95% confidence interval. The inputs are six of
Silesia's XML files and the seven files of roxmltree's benchmarks, pinned by
commit and SHA-256. The comparisons below are native, verilith-xml's own API
against each library's; the expat drop-in, the same driver linked against
the expat ABI, follows them.

On an Apple M3 Pro (macOS, Apple clang, the root README's run of the same
day) the gaps are smaller: checking is 1.14x to 6.69x expat (geometric mean
2.23x) and 0.92x to 6.85x libxml2 (1.72x), reading 0.80x to 2.17x expat
(1.35x) and 0.69x to 2.03x libxml2 (1.14x). The slowest reading case
against both is w3c5.xml, the closest case on the VM too.

**Checking** whether a document is well-formed: expat's `XML_Parse` with no
handlers; libxml2's `xmlCtxtReadMemory` on a reused context, with its SAX2
handlers for the DTD and none for content; `verilith_xml::check` into a
reused tape (the verified parser alone). MB/s:

| file | KB | verilith-xml | expat | libxml2 | vs expat | vs libxml2 |
|---|---:|---:|---:|---:|---|---|
| elts.xml | 110 | 966 | 192 | 300 | 5.04x (4.95–5.18) | 3.28x (3.23–3.29) |
| play1.xml | 245 | 948 | 273 | 384 | 3.46x (3.28–3.57) | 2.42x (2.35–2.50) |
| stats1.xml | 653 | 708 | 168 | 276 | 4.20x (4.09–4.29) | 2.50x (2.41–2.58) |
| tal1.xml | 717 | 616 | 126 | 180 | 4.87x (4.76–4.95) | 3.36x (3.34–3.41) |
| tpc.xml | 281 | 740 | 184 | 274 | 4.00x (3.95–4.04) | 2.42x (2.31–2.62) |
| w3c5.xml | 241 | 812 | 262 | 227 | 3.13x (3.08–3.17) | 3.29x (3.07–3.46) |
| attributes.xml | 264 | 578 | 70 | 210 | 8.31x (7.85–9.01) | 2.90x (2.32–3.01) |
| cdata.xml | 99 | 3444 | 484 | 205 | 7.21x (6.54–7.53) | 17.23x (16.72–17.61) |
| gigantic.svg | 1304 | 5159 | 283 | 436 | 18.55x (18.09–19.77) | 12.39x (11.85–12.95) |
| huge.xml | 815 | 1293 | 207 | 301 | 6.44x (6.04–6.52) | 4.41x (4.32–4.51) |
| large.plist | 313 | 1020 | 268 | 394 | 3.76x (3.61–3.85) | 2.56x (2.48–2.63) |
| medium.svg | 151 | 1325 | 190 | 354 | 6.97x (6.87–7.21) | 3.87x (3.80–3.93) |
| text.xml | 126 | 614 | 79 | 65 | 7.81x (7.73–7.89) | 9.31x (8.93–9.68) |

**Reading** a document: parse it and visit every element, every
attribute's normalized value and every run of character data. expat's SAX
callbacks; libxml2's SAX2 callbacks, with entities substituted and DTD
defaults added; `verilith_xml::parse` and a walk with `Element::attrs` and
`children`. MB/s:

| file | KB | verilith-xml | expat | libxml2 | vs expat | vs libxml2 |
|---|---:|---:|---:|---:|---|---|
| elts.xml | 110 | 378 | 187 | 282 | 2.02x (1.96–2.06) | 1.36x (1.34–1.38) |
| play1.xml | 245 | 434 | 269 | 380 | 1.61x (1.60–1.61) | 1.13x (1.13–1.14) |
| stats1.xml | 653 | 352 | 164 | 253 | 2.13x (2.10–2.16) | 1.36x (1.34–1.38) |
| tal1.xml | 717 | 250 | 122 | 187 | 2.05x (2.00–2.08) | 1.34x (1.31–1.37) |
| tpc.xml | 281 | 318 | 175 | 149 | 1.82x (1.77–1.86) | 1.96x (1.26–2.22)\* |
| w3c5.xml | 241 | 246 | 206 | 215 | 1.19x (1.18–1.20) | 1.08x (0.99–1.21)\* |
| attributes.xml | 264 | 120 | 68 | 78 | 1.74x (1.63–1.89) | 1.68x (1.64–1.70) |
| cdata.xml | 99 | 692 | 482 | 202 | 1.43x (1.39–1.48) | 3.41x (3.34–3.45) |
| gigantic.svg | 1304 | 3920 | 284 | 442 | 13.74x (13.41–14.53) | 9.18x (8.84–9.66) |
| huge.xml | 815 | 505 | 208 | 302 | 2.45x (2.37–2.47) | 1.70x (1.67–1.73) |
| large.plist | 313 | 407 | 265 | 367 | 1.53x (1.52–1.54) | 1.10x (1.07–1.12) |
| medium.svg | 151 | 569 | 190 | 354 | 2.99x (2.97–3.01) | 1.59x (1.57–1.61) |
| text.xml | 126 | 148 | 75 | 62 | 2.00x (1.98–2.02) | 2.30x (2.17–2.36) |

The vxml column is its median in the expat comparison; in the libxml2 one
it is within 10%. Geometric means: checking **5.69x** expat and **4.22x**
libxml2, reading **2.17x** expat and **1.80x** libxml2. Four sittings of
the same build that day gave 5.25–5.69x, 3.84–4.22x, 2.12–2.17x and
1.67–1.80x, and every case was faster in every sitting but one: the starred
w3c5 above, the closest case, whose interval in this sitting includes 1.00
(1.05–1.12 in the other three). The starred tpc was disturbed in this
sitting (libxml2 at 149 MB/s, 255 to 262 in the other three, which give
1.18x to 1.23x); with those, reading is 1.73x libxml2.

* The walk costs about as much as the parse (play1: 265 µs to check, 592
  µs to parse and read). Part of that is turning each span into a `&str`
  with `str::from_utf8` (8% to 10% of the instructions): the verified
  parser proves the text is UTF-8 but not yet that every span ends on a
  character boundary, so the API checks rather than assumes it.
* The largest speedups are where the SIMD scanners skip the most:
  gigantic.svg's long path attributes and cdata.xml's one long CDATA
  section. attributes.xml and text.xml are dense with entity and character
  references.
* w3c5 is in ISO-8859-1, so every parser decodes it to UTF-8 first.
* On attributes.xml libxml2's attribute values come to 691 bytes more than
  expat's and verilith-xml's (the harness shows both check values for that
  comparison): libxml2 keeps a CR LF in an entity's literal value as two
  characters, so a reference to the entity in an attribute value gives two
  spaces where XML 1.0 (§2.11, §3.3.3) gives one.
* libxml2 is measured through its fastest API that does the job. Its
  deprecated SAX1 callbacks are faster on most of these files, but do not
  receive the DTD's attribute defaults (on w3c5, 789 attributes against
  1112), and entity substitution makes its check slower, so the check runs
  without it.

### Drop-in for expat (vbench)

`bench/run.sh --only xml-expat-dropin-read,xml-expat-dropin-check`: the
harness's expat driver (`bench/suites/xml/expat.c`), unchanged, linked
against libexpat and against verilith-xml's expat ABI. The same VM,
2026-11-23, 11 interleaved pairs per case, gcc 13.3 `-O3 -march=native` and
rustc 1.97 with fat LTO and `-C target-cpu=native`. MB/s:

| file | read: vxml | read: expat | read: speedup | check: speedup |
|---|---:|---:|---|---|
| elts.xml | 223 | 127 | 1.62x (1.53–1.77) | 4.72x (4.30–5.19) |
| play1.xml | 363 | 241 | 1.50x (1.48–1.55) | 3.48x (3.38–3.64) |
| stats1.xml | 262 | 151 | 1.72x (1.50–1.77) | 4.07x (3.94–4.27) |
| tal1.xml | 176 | 116 | 1.51x (1.46–1.54) | 3.89x (3.70–4.10) |
| tpc.xml | 243 | 150 | 1.58x (1.51–1.68) | 4.06x (3.83–4.22) |
| w3c5.xml | 195 | 173 | 1.15x (1.03–1.24) | 3.23x (3.11–3.33) |
| attributes.xml | 82 | 61 | 1.28x (0.86–1.54)\* | 8.18x (7.02–8.62) |
| cdata.xml | 514 | 438 | 1.17x (1.06–1.50) | 7.44x (7.28–7.99) |
| gigantic.svg | 2511 | 274 | 9.22x (8.40–10.03) | 15.02x (13.34–16.19) |
| huge.xml | 458 | 187 | 2.40x (2.37–2.54) | 6.02x (5.20–6.27) |
| large.plist | 383 | 235 | 1.61x (1.51–1.67) | 3.78x (3.61–3.98) |
| medium.svg | 402 | 176 | 2.26x (2.19–2.40) | 6.08x (5.76–6.35) |
| text.xml | 163 | 74 | 2.21x (1.66–2.51) | 6.79x (6.55–7.12) |

Geometric means: reading **1.85x** expat, checking **5.35x**. The starred
interval includes 1.00. Reading through the ABI costs more than through
the Rust API (2.12x expat in the same sitting): each element's name and
attributes are copied out as NUL-terminated strings, as expat's callbacks
take them. Checking with no handlers runs the verified check alone, as the
native comparison does.

### Against the Rust XML parsers

`bench/` (a separate project) times verilith-xml against the Rust XML
parsers on the same thirteen files, in one process: best of 15 timings,
MB/s, the same VM and day. roxmltree 0.21 builds its tree and counts the
nodes; quick-xml 0.38 reads every event (it checks end tag names, and does
not check characters, names or references, nor expand references); xml-rs 1
reads every event.

| file | KB | verilith-xml check | verilith-xml read | roxmltree | quick-xml | xml-rs |
|---|---:|---:|---:|---:|---:|---:|
| elts.xml | 110 | 1029 | 405 | 164 | 675 | 42 |
| play1.xml | 245 | 1010 | 452 | 271 | 585 | 35 |
| stats1.xml | 653 | 754 | 368 | 253 | 396 | 29 |
| tal1.xml | 717 | 609 | 257 | 160 | 263 | 23 |
| tpc.xml | 281 | 767 | 331 | 207 | 391 | 27 |
| w3c5.xml | 241 | 847 | 269 | 143 | 819 | 42 |
| attributes.xml | 264 | 651 | 126 | 84 | 1599 | 48 |
| cdata.xml | 99 | 4425 | 986 | 538 | 29943 | 87 |
| gigantic.svg | 1304 | 5273 | 3994 | 889 | 2487 | 66 |
| huge.xml | 815 | 1380 | 531 | 247 | 910 | 40 |
| large.plist | 313 | 1086 | 421 | 237 | 614 | 36 |
| medium.svg | 151 | 1056 | 577 | 478 | 838 | 49 |
| text.xml | 126 | 666 | 154 | 33 | 830 | 13 |

roxmltree, which like verilith-xml checks the whole document and expands
references, reads 1.2 to 4.7 times slower. quick-xml reads faster than
verilith-xml's parse-and-read on all but gigantic.svg, and is slower than
the verified check on all but the three files dense with what it skips:
attributes.xml and text.xml (references, which it leaves unexpanded and
unchecked) and cdata.xml (one long CDATA section, whose characters it does
not check).

### What makes it fast

* **One pass, sixteen bytes at a time.** Character data, attribute values,
  comments, CDATA sections and processing instructions are scanned with
  SSE2 for the bytes that can end or change them; the check that every
  character is a `Char` skips sixteen ASCII bytes at a time. Each scanner's
  stop set may be larger than what matters (a byte up to 0x0D stands for
  tab, line feed and carriage return in attribute values, one compare for
  three), since the scalar step after it handles any byte. This took
  Silesia's files from 300–650 MB/s to 580–1100 MB/s, and gigantic.svg (long
  path attributes) from 673 to 5400 MB/s.
* **Nothing copied.** The tape holds spans, and an attribute value that
  needs no normalization (most do not) is handed out as a borrowed slice.
* **Entities once.** A replacement text is parsed once, when first read,
  and read in place for every reference after that.
* **Linear worst cases.** Attribute uniqueness, entity lookup and the
  entity checks stay linear on crafted input (see What is proven).

Smaller changes, measured: reserving the tape at one token per 16 input
bytes (1% to 6%); an allocation-free attribute iterator and `children`,
and ISO-8859-1 copied by ASCII runs (w3c5's parse and read went from 32
to 23 million instructions, and from 0.82x to 1.20x expat).

**Not done yet:** NEON scanners (AArch64 runs the scalar loops), and a
fast path for end tags that compares the name directly instead of scanning
it first.

## Building, verifying and testing

```sh
cargo build --profile release-abort
cargo build --profile release-abort --features expat-abi   # with the expat C ABI
./scripts/verify.sh            # needs cargo-verus on PATH (see the repository's README)
./ci.sh                        # the tests: fetches the W3C suite and libexpat
scripts/test-expat.sh XMLCONF  # libexpat's tests against the expat ABI
XMLCONF=/path/to/xmlconf cargo test --profile release-abort
./ci.sh fuzz                   # the libFuzzer targets (nightly, cargo-fuzz)
../../bench/run.sh --only xml  # vbench: against expat and libxml2, built from pinned sources
(cd bench && cargo run --release -- DIR...)   # against roxmltree, quick-xml, xml-rs
```

## Layout

```text
src/spec.rs      XML 1.0 (Fifth Edition) well-formedness as Verus spec functions
src/chars.rs     Char and Name characters: spec, tables, verified code
src/lex.rs       white space, literals, references, values, comments, PIs, CDATA, text, Misc
src/dtd.rs       the XML declaration and the document type declaration
src/content.rs   start tags, the content loop, replacement text as content
src/doc.rs       the prolog, attribute defaults, the document
src/ent.rs       replacement text, and which entities may be referred to where
src/fix.rs       the least fixed point of Horn clauses, with a worklist
src/enc.rs       encodings: choosing, UTF-16 and ISO-8859-1 decoders, parse
src/decode.rs    line-end and attribute-value normalization
src/uniq.rs      Unique Att Spec in linear time
src/index.rs     the entities by name, for references
src/scan.rs      SSE2 scanners
src/lanes.rs     SSE2 wrappers proven over verilith-simd
src/tape.rs      the tokens
src/api.rs       the Rust API (not verified)
src/api/expat.rs expat's C ABI, feature expat-abi (not verified)
tests/           the W3C suite, its output tests, API tests
tests/c/         libexpat's test suite against the ABI: internals stub, known failures
fuzz/            differential fuzzing against libexpat
bench/           against the Rust XML parsers (expat and libxml2 are in vbench)
scripts/         verification, fetching libexpat, libexpat's tests
```

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/xml/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/xml/LICENSE-MIT), at your option.
