# What verilith-font's proofs assume

The theorems are: every font `sanitize` returns satisfies
`spec::wf_font`; it draws the same as the input's tables
(`spec_same::draws_same`); a valid input (`spec_same::valid_tables`) is
never refused; and the verified code cannot read or write out of bounds,
overflow an integer, or panic. This file lists everything those theorems
take on trust.

## The specification

- `src/spec.rs`: `wf_font` and the per-table predicates for the sfnt
  container, `head`, `maxp`, `hhea`, `hmtx`, `OS/2`, `cmap`, `name`,
  `post`, `glyf`, `loca`, `kern`, `gasp`, `cvt `, `vhea`, `vmtx`.
- `src/spec_cff.rs`: the `CFF ` table (INDEX, DICT, charset, encoding,
  FDSelect, Private DICT).
- `src/spec_cs.rs`: Type 2 charstrings.
- `src/spec_layout.rs`: the layout tables `GDEF`, `GSUB` and `GPOS`.
- `src/spec_same.rs`: what the input's table set is for a plain sfnt
  file and a TrueType Collection (`input_tables`), what it means for the
  output to draw the same as it (`draws_same`), and which table sets
  are valid fonts (`valid_tables`).

These five files are definitions, with no proofs to check them against.
If a predicate is weaker than the OpenType specification intends, the
theorem is weaker in the same way. Review them against the OpenType
specification and Adobe Technical Notes #5176 and #5177. Places where
the specification makes a choice of its own are marked in comments
there and listed in the README under "Differences from OTS".

Two things the specification deliberately does not say:

- Nothing about the contents of TrueType instructions (`fpgm`, `prep`,
  glyph instructions). They are bytes of bounded length.
- In the layout tables, no more than OTS checks about values that are
  not offsets, counts or indices. Glyph ids inside the ranges of a
  format 2 coverage or class definition table are not compared with the
  glyph count, class values are not compared with the class counts of
  the subtables that use them, and lookup flags, script, language and
  feature tags and feature parameters are not interpreted. A shaper must
  still treat a glyph id or class it reads from those places as a number
  that may match nothing.
- `draws_same` treats the bytes of a glyph, a `CFF ` table, a `cmap`
  subtable or a hinting program as what determines how it draws. It
  does not interpret them, so two fonts that draw alike but are encoded
  differently do not count as the same. That is stricter than needed and
  never weaker.
- `draws_same` does not cover `name` when the input's is malformed,
  `maxp`'s outline limits, the `OS/2` version field, or the tables that
  are dropped (README, "Which tables are kept"). Changes the sanitizer
  makes to the layout tables are listed one by one in `layout_fix`.

## Trusted code

- `src/prims.rs`, `rd8`: one `get_unchecked` read. Its `requires` is the
  bounds check, which Verus proves at every call. Every other read in
  the crate goes through it. `src/lib.rs` states the size of `usize`
  for the target being built (8 or 4 bytes), and the proofs are checked
  for both.
- `src/capi.rs`: the C interface, about 60 lines, not verified. It turns
  the caller's pointer and length into a slice, calls the verified
  `sanitize_index`, and hands the output buffer over as a boxed slice.
  It is correct only if the caller keeps the contract in
  `include/vfont.h`.
- `include/opentype-sanitiser.h`, `include/ots-memory-stream.h`: C++
  headers that offer OTS's interface on top of the C interface. Not
  verified. Tested by `scripts/test-capi.sh`.

There is no `assume`, `admit` or `external_body` in the crate.

## Verified, but only for safety

Rebuilding the tables (`build::build_tables` and what it calls) and
decoding WOFF and WOFF2 (`build.rs`, `src/woff2.rs`) are verified to be
free of out-of-bounds access, overflow and panics, and nothing more.
Theorems 1 and 2 do not depend on the rebuilding being right, because
`sanitize` returns its output only after the verified checkers have
accepted it, and theorem 3 does not either, because a valid font
refused there is laid out again by the proven fallback.

The decoders are different: for a WOFF or WOFF2 input, `draws_same` and
`valid_tables` are about the tables the decoder produced. If a decoder
produced the wrong tables, the output would draw like those, and still
be well formed. The tests and the differential runs against OTS are the
evidence that it does not.

Reading a plain sfnt file or a collection (`read_sfnt`, `read_ttc`) and
laying out the file (`assemble`) are fully verified against
`input_tables` and `wf_font`'s directory rules.

## Dependencies

- [verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib) (WOFF) and
  [verilith-brotli](https://github.com/verilith/verilith/tree/main/crates/brotli) (WOFF2),
  path dependencies in this repository, with their own trusted bases (their
  READMEs list them, including
  [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s memory
  primitives). verilith-font uses only their memory safety: what they
  decompress is treated as untrusted bytes and checked like any other
  input.
- `vstd`, Verus's standard library, and its specifications of `Vec` and
  slices.
- Verus, Z3 and the Rust compiler.
- The Rust allocator. Running out of memory aborts the process.
