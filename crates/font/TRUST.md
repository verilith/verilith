# What verilith-font's proofs assume

The theorem is: every font `sanitize` returns satisfies `spec::wf_font`,
and the verified code cannot read or write out of bounds, overflow an
integer, or panic. This file lists everything that theorem takes on
trust.

## The specification

- `src/spec.rs`: `wf_font` and the per-table predicates for the sfnt
  container, `head`, `maxp`, `hhea`, `hmtx`, `OS/2`, `cmap`, `name`,
  `post`, `glyf`, `loca`, `kern`, `gasp`, `cvt `, `vhea`, `vmtx`.
- `src/spec_cff.rs`: the `CFF ` table (INDEX, DICT, charset, encoding,
  FDSelect, Private DICT).
- `src/spec_cs.rs`: Type 2 charstrings.
- `src/spec_layout.rs`: the layout tables `GDEF`, `GSUB` and `GPOS`.

These four files are definitions, with no proofs to check them against.
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
- Nothing that relates the output to the input. `wf_font` is a property
  of the output alone.

## Trusted code

- `src/prims.rs`, `rd8`: one `get_unchecked` read. Its `requires` is the
  bounds check, which Verus proves at every call. Every other read in
  the crate goes through it. The same file states `size_of usize == 8`:
  the proofs are for 64-bit targets.
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

`src/build.rs` and `src/woff2.rs` (reading the containers, rebuilding
tables, laying out the file) are verified to be free of out-of-bounds
access, overflow and panics, and nothing more. The theorem does not
depend on them doing the right thing, because `sanitize` returns their
output only after the verified checker has accepted it. Whether they
accept the fonts they should is a matter for the tests.

## Dependencies

- [verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib) (WOFF) and
  [verilith-brotli](https://github.com/verilith/verilith/tree/main/crates/brotli) (WOFF2),
  pinned by commit in `Cargo.toml`, with their own trusted bases (their
  READMEs list them, including
  [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s memory
  primitives). verilith-font uses only their memory safety: what they
  decompress is treated as untrusted bytes and checked like any other
  input.
- `vstd`, Verus's standard library, and its specifications of `Vec` and
  slices.
- Verus, Z3 and the Rust compiler.
- The Rust allocator. Running out of memory aborts the process.
