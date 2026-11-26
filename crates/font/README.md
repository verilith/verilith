# verilith-font

An OpenType font sanitizer written in Rust and verified with
[Verus](https://github.com/verus-lang/verus). It does the job of
[OTS](https://github.com/khaledhosny/ots), the OpenType Sanitizer that
Chrome and Firefox run on every web font: it takes font bytes nobody
trusts, parses them, and either refuses the font or writes a new one that
is safe to hand to a rasterizer. It is a sanitizer and not a rasterizer.

It reads OpenType with TrueType or CFF outlines, WOFF, WOFF2 and TrueType
Collections, and always writes a plain OpenType font. WOFF and WOFF2 are
unpacked with [verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib) and
[verilith-brotli](https://github.com/verilith/verilith/tree/main/crates/brotli), which are
verified too.

**Status:** `cargo verus verify` checks 481 functions with 0 errors. On
OTS's own test corpus verilith-font accepts 245 of the 277 fonts that OTS accepts,
never crashes, and OTS accepts every font verilith-font writes. The layout tables
`GDEF`, `GSUB` and `GPOS` are sanitized and kept. Variation, colour and
bitmap tables are dropped, and `CFF2` fonts are refused. See
[which tables are kept](#which-tables-are-kept) before using this in
place of OTS.

**Speed:** 1.17 times as fast as OTS overall (geometric mean, verilith-font at
`89a9cbf`). [vbench](https://github.com/verilith/verilith/tree/main/bench)'s
`font-sanitize` comparison drives both through OTS's C++ API on Source
Serif 4 Regular, on vbench's reference Mac, 31 pairs per case, noise about
±0.02:

| Input | Speed against OTS |
| --- | ---: |
| TTF | 1.42x |
| OTF | 1.38x |
| OTF as WOFF | 1.17x |
| TTF as WOFF | 1.16x |
| OTF as WOFF2 | 1.08x |
| TTF as WOFF2 | 0.88x |

verilith-font runs 0.89 times the instructions and 0.86 times the cycles of OTS.
Its lead shrinks as decompression takes a larger share of the work, and
it loses on TrueType WOFF2, where it runs 32% more instructions. The two
write slightly different bytes for the same tables, so this compares the
same job and not identical output.

## What is proven

```rust,ignore
pub fn sanitize(input: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@),
        r matches Some(out) ==> (spec_same::input_tables(input@, 0) matches Some(t)
            ==> spec_same::draws_same(t, out@)),
        (spec_same::input_tables(input@, 0) matches Some(t) && spec_same::valid_tables(t))
            ==> r is Some,
```

Three theorems, for every input:

1. **Every font that `sanitize` returns is well formed** (`wf_font`).
2. **It draws the same as the input** (`draws_same`).
3. **A valid font is never refused** (`valid_tables`).

Verus also proves that none of the verified code can read or write out
of bounds, overflow an integer, or panic. `sanitize_tables`, which takes
the tables a container reader found, has the same three theorems for
any table set, and is what `sanitize` calls.

Theorems 2 and 3 are about the input's *table set*: the known tables the
container holds, as (tag, bytes) pairs. For a plain OpenType file and a
TrueType Collection, `spec_same::input_tables` says exactly what that set
is, and the reader is proven to find it. For WOFF and WOFF2 the set is
whatever the decoders produce, which is not specified, so for those
inputs the theorems hold relative to the decoded tables and the
fidelity of decompression rests on the tests (see
[TRUST.md](https://github.com/verilith/verilith/blob/main/crates/font/TRUST.md)).

`wf_font` is the specification, written from the OpenType specification
and Adobe's Technical Notes #5176 and #5177. It is about 3,100 lines in
`src/spec.rs`, `src/spec_cff.rs`, `src/spec_cs.rs` and
`src/spec_layout.rs`, and it is what a reviewer needs to read. It says:

- **The file.** The header's search fields are right. The table records
  are sorted by tag with no duplicates. The tables follow the directory
  one after another in that order, each starting on a 4-byte boundary,
  with zero padding and nothing else between or after them, so no two
  tables overlap and no byte of the file is unaccounted for. Every table
  checksum is right and so is the checksum of the whole file.
- **The table set.** Only tables this specification knows are present.
  `head`, `hhea`, `hmtx`, `maxp`, `OS/2`, `cmap`, `name` and `post` are all
  there, with either `glyf` and `loca` or `CFF `, never both.
- **Agreement between tables.** `hhea` and `hmtx` (and `vhea` and `vmtx`)
  agree with `maxp` on how many metrics and glyphs there are. `loca` has
  one more entry than the font has glyphs, its offsets never decrease and
  all lie inside `glyf`, and its format is the one `head` names.
- **Glyphs (`glyf`).** Every glyph parses to exactly its own bytes, with
  fewer than four bytes of padding: contour end points increase, the
  flags and coordinates are all present, a composite's component records
  are complete. Every component is a glyph that exists. No glyph contains
  itself, directly or through other glyphs. Components may nest as deep
  as the glyphs allow, as in OTS; they are followed with a stack on the
  heap. `maxp` tells the truth: no glyph has more points, contours,
  instruction bytes, components or nesting than `maxp` says, counting a
  composite glyph's points and contours through all its components.
- **Character map (`cmap`).** Encoding records are sorted and each leads
  to a subtable inside the table, of format 0, 4, 12, 13 or 14, used with
  an encoding OTS also keeps. Segments and groups are in order and do not
  overlap, and every glyph a character can map to exists, including the
  ones reached through format 4's glyph id array. In format 14, variation
  selectors are real ones and in order, and their tables do not overlap.
- **`name`, `post`, `OS/2`, `kern`, `gasp`, `cvt `.** Every string, glyph
  name index, kerning pair and range lies inside its table, and glyph
  indices are below the glyph count.
- **CFF.** The header, the four INDEXes and everything the Top DICT
  points to lie inside the table and cover exactly the font's glyphs.
  Every DICT holds only known operators with the operands they take, real
  numbers are well formed, and string ids name strings that exist. Every
  glyph's charstring runs cleanly: every byte decodes, the stack never
  holds more than 48 numbers, each operator finds the operands it takes,
  every subroutine call names a subroutine that exists, calls nest at
  most 10 deep, hint masks have the bytes their stems need, and the
  program ends with `endchar`. Each glyph's charstring executes at most
  2^26 operators, as in OTS, so a consumer's work is bounded.
- **Layout (`GDEF`, `GSUB`, `GPOS`).** Every offset a shaper can follow,
  from the table header down to the last device table, leads to a
  structure that lies inside the table and is itself well formed: script,
  language system and feature lists; lookups of every type, directly or
  through an extension; coverage and class definition tables; sequence
  and chained sequence rules in all three formats; value records, anchors,
  mark and ligature arrays; attachment points, ligature carets and mark
  glyph sets. Counts fit the bytes they count. Glyph ids in coverage
  lists, substitutions, ligatures, rules and pair sets are glyphs that
  exist. Every feature index names a feature in the feature list, every
  lookup index (in features and in sequence lookup records) names a
  lookup in the lookup list, and a lookup's mark filtering set is one
  `GDEF` defines. Coverage ranges are in order and their indices add up.

### Draws the same

`draws_same(t, out)`, in `src/spec_same.rs` (about 600 lines), says
that a renderer given the output draws every glyph and maps every
character it maps exactly as it would with the input, and that a
shaper sees the same layout data but for named repairs:

- **Glyphs.** The output has TrueType outlines exactly when the input
  does, and then every glyph's outline (its contours or components and
  its instructions, cut at the end its own structure gives) is the
  input's. A `CFF ` table is the input's byte for byte.
- **Metrics.** `hhea`, `hmtx`, and `vhea` and `vmtx` when kept, are
  prefixes of the input's, so every advance and side bearing is the
  input's. `head` is the input's first 54 bytes, except for
  `checkSumAdjustment` and `indexToLocFormat`. `maxp` has the same glyph
  count and, for TrueType, the same limits a hinting interpreter
  allocates by, with `maxZones` clamped to 1 or 2. `OS/2` is a prefix of
  the input's.
- **Hinting.** `fpgm`, `prep`, `cvt `, `gasp` and `kern` are the input's
  when present. In a TrueType font the first four are dropped only when
  empty or malformed, and `kern` in any font only when malformed.
- **Characters.** Every `cmap` encoding record of the output is one of
  the input's, with the same platform, encoding and subtable bytes, or
  the bytes after OTS's repair of a format 4 last segment (which only
  changes U+FFFF to map to glyph 0).
- **Layout.** `GDEF`, `GSUB` and `GPOS` are present exactly when in the
  input, the same length, and differ only where a link to variation data
  is cleared or a script's default language system is repaired or
  removed.
- **`name` and `post`.** `name` is the input's if well formed. `post`
  keeps the input's italic angle, underline metrics and fixed-pitch flag,
  and is the whole input table if well formed.

It does not say: that `name` survives when malformed; that `maxp`'s
outline limits are the input's (they are recomputed); that dropped
`cmap` records or a dropped `vhea`/`vmtx` were unusable (only that what
is kept is unchanged); that a CFF font keeps `fpgm`, `prep`, `cvt ` or
`gasp` (they are TrueType-only); or anything about the dropped tables.

### Valid fonts are accepted

`valid_tables(t)` holds when the input's known tables, laid out as a
file of their own, would satisfy `wf_font`, and together take at most
1 GiB. Nothing is asked of the input's directory beyond what the reader
needs: its order, packing, padding and checksums, its unknown tables and
`head.checkSumAdjustment` may all be anything. A font whose known tables
need repair (a malformed `cmap` subtable, a too-long `hmtx`, a `glyf`
with padding after a glyph, a default language system that must be
fixed) is outside the theorem; the builder may still accept it, and the
differential tests below are the evidence that it usually does.

### How the theorems are proved

The sanitizer has two halves.

The **builder** reads the container, rebuilds or copies each table, and
lays out the new file. It is verified for memory safety only.

The **checkers** decide the specifications. `font::check_font` decides
`wf_font` exactly: Verus proves `check_font(s) == wf_font(s)` for all
bytes `s` (on a 32-bit target, for all `s` of at most `isize::MAX` bytes,
which is every slice). `same::check_same(t, s)` is proven sound for
`draws_same` (when it says yes, `draws_same` holds) and complete when the
output holds exactly the input's known tables. `sanitize` runs both on
what the builder produced and returns the font only if both say yes. So
theorems 1 and 2 do not rest on the builder being right. A bug there can
make the builder's output be refused, and cannot make verilith-font emit
a bad font or one that draws differently.

Theorem 3 needs one more piece. When the builder's output is refused,
`relay` lays out the input's known tables again, unchanged, in tag
order, with the file layout code (`build::assemble`), which is proven to
produce the directory, padding and checksums `wf_font` asks for. If the
input is valid, that file is well formed and holds exactly the input's
tables, so both checkers accept it. The fallback never changes the
answer for a font the builder handles; it catches the fonts the builder
would wrongly refuse.

The cost is a second pass over the output, and a third for the
comparison with the input. Proving the builder's output correct
directly, so that the checks can go, is future work.

### What is not proven

- That a font which needs repair is accepted. Theorem 3 covers fonts
  whose known tables are already well formed. For the rest, the
  differential test below is the evidence.
- That WOFF and WOFF2 decode to the right tables (see above).
- Anything about TrueType instructions. `fpgm`, `prep` and the
  instructions inside glyphs are copied as bytes (their lengths are
  bounded by `maxp`). OTS does the same. A rasterizer that executes
  hinting programs must defend itself.
- That the specification is the right one. See [TRUST.md](https://github.com/verilith/verilith/blob/main/crates/font/TRUST.md).

## Which tables are kept

**Sanitized** (specified in `wf_font`, checked on the way out):

| Table | What verilith-font does with it |
| --- | --- |
| `head` | Rebuilt: 54 bytes, checksum adjustment recomputed, `loca` format set to what was written. |
| `maxp` | Rebuilt: glyph limits raised to what the glyphs need, `maxZones` forced to 1 or 2. |
| `hhea`, `hmtx` | Cut to the lengths the glyph count calls for. |
| `OS/2` | Cut to the length its version calls for. |
| `cmap` | Rebuilt from the subtables that are well formed, after repairing a format 4 last segment whose `idRangeOffset` is 0xFFFF. A malformed subtable is dropped. The font is refused if none is left. |
| `name` | Kept if well formed, otherwise replaced by an empty one. |
| `post` | Kept if well formed, otherwise cut to a version 3 header (no glyph names). |
| `glyf`, `loca` | Rebuilt glyph by glyph: bytes after a glyph's end are cut, and `loca` is rewritten. |
| `CFF ` | Kept byte for byte if well formed, otherwise the font is refused. |
| `GDEF`, `GSUB`, `GPOS` | Kept if well formed, otherwise the font is refused, as OTS does. Before the check, links to variation data are cleared (the item variation store of a version 1.3 `GDEF`, the feature variations of a version 1.1 `GSUB` or `GPOS`), and a default language system OTS would not have looked at is repaired or removed. |
| `kern`, `gasp`, `cvt `, `vhea`, `vmtx` | Kept if well formed, otherwise dropped. |

**Passed through** without looking inside: `fpgm` and `prep` (TrueType
hinting programs), only in fonts with TrueType outlines.

**Dropped**, always: every other table. That includes

- the other layout tables `BASE`, `JSTF`, `MATH`;
- variations: `fvar`, `gvar`, `avar`, `cvar`, `HVAR`, `VVAR`, `MVAR`,
  `STAT` (a variable TrueType font comes out as its default instance);
- colour and bitmaps: `COLR`, `CPAL`, `SVG `, `CBDT`, `CBLC`, `sbix`,
  `EBDT`, `EBLC`, `EBSC`;
- `hdmx`, `LTSH`, `VDMX`, `VORG`, `DSIG`, `meta`, the Graphite and AAT
  tables, and any tag verilith-font does not know.

**Refused**: a font with neither `glyf` nor `CFF `. That covers fonts
whose only outlines are `CFF2` and bitmap-only fonts such as Noto Color
Emoji.

## Differences from OTS

Where verilith-font accepts less:

- The dropped tables above. OTS sanitizes the variation and colour
  tables and keeps them.
- In the layout tables: a script's default language system must be well
  formed (OTS does not look at it; verilith-font repairs a wrong lookup order
  offset or required feature, and otherwise removes it, which a `DFLT`
  script does not survive). `GDEF` must be version 1.0, 1.2 or 1.3 (OTS
  accepts any minor version but 1). Offsets in cursive attachment and
  mark glyph set tables must point past the whole record array (OTS
  computes a shorter array). A reverse chaining substitution must be
  format 1. Coverage indices are compared without 16-bit wraparound.
- `CFF2` fonts are refused.
- A WOFF2 file holding a collection is refused.
- A format 4 `cmap` subtable must have its segments in order, without
  overlap. OTS accepts some that do not; verilith-font drops the subtable. (Both
  repair the common case of a last segment whose `idRangeOffset` is
  0xFFFF.)
- Limits: input up to 1 GiB and 300 MiB after decompression (both OTS's).
- In CFF, a Font DICT may not hold the operators that describe the whole
  font, a font that is not CID-keyed may not have an FDArray or FDSelect,
  and charset ranges must not name string ids that do not exist.

Where verilith-font accepts more, or acts differently:

- OTS refuses a font when a `cmap` subtable, `kern`, or a table verilith-font
  drops is malformed. verilith-font drops that part and keeps the font.
- Variable fonts keep their layout tables but lose their variation data,
  so device tables of the variation index kind refer to a variation
  store that is no longer there. Shapers treat that as no adjustment.
- OTS trusts `maxp` and fixes a few fields. verilith-font recomputes the glyph
  limits from the glyphs.
- A TrueType Collection comes out as one font (the one `index` picks,
  0 by default), not as a collection.
- verilith-font does not say why it refused a font.

## Using it

Rust:

```rust,no_run
fn main() -> std::io::Result<()> {
    let bytes = std::fs::read("font.woff2")?;
    match verilith_font::sanitize(&bytes) {
        Some(font) => std::fs::write("font.ttf", font)?, // rebuilt, and proven well-formed
        None => eprintln!("refused"),
    }
    Ok(())
}
```

C (`include/vfont.h`, link `libverilith_font.a`):

```c
uint8_t *out; size_t out_len;
if (vfont_sanitize(data, len, 0, &out, &out_len)) {
    use_font(out, out_len);
    vfont_free(out, out_len);
}
```

C++ written for OTS: `include/opentype-sanitiser.h` and
`include/ots-memory-stream.h` provide `ots::OTSContext::Process`,
`ots::OTSStream`, `ots::MemoryStream` and `ots::ExpandingMemoryStream`
on top of the C interface, so code such as

```cpp
ots::OTSContext context;
ots::ExpandingMemoryStream output(length, limit);
if (context.Process(&output, data, length)) { ... }
```

compiles against verilith-font with the include path changed. `Message` and
`GetTableAction` overrides compile and are never called: there are no
messages, and the table policy is fixed.

Command line: `cargo run --release --example vfont-sanitize IN [OUT]`
exits with 0 if the font was accepted and 1 if it was refused.

## Tests

- `cargo test --release`: fonts built by hand in the test (TrueType,
  WOFF, collection, composites with and without cycles, and `GDEF`,
  `GSUB` and `GPOS` tables), every one-byte corruption and every
  truncation of them. Whatever comes out must pass the checker and be a
  fixed point of the sanitizer. `tests/fidelity.rs` checks that the
  output passes `check_same`, that changing a byte of a glyph, metric,
  `head` or `cmap` of the input is noticed, and that a valid font in a
  sloppy layout with unknown tables comes out the same as when laid out
  well.
- `scripts/test-capi.sh`: the C interface and the OTS-style C++ headers.
- `scripts/difftest.sh DIR...`: runs verilith-font and OTS on every file in the
  directories and reports where they differ. It also checks that OTS
  accepts every font verilith-font writes and that sanitizing verilith-font's output
  again changes nothing. `scripts/build-ots.sh` builds the `ots-sanitize`
  it needs. The fonts are not in this repository: use OTS's
  `tests/fonts`.

Results on OTS's corpus (OTS at `c5d249c`) and the fonts installed on the
development machine:

| Corpus | Files | Both accept | Only OTS | Only verilith-font | Both refuse | Crashes | Outputs OTS refuses |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tests/fonts/good` | 118 | 102 | 16 | 0 | 0 | 0 | 0 |
| `tests/fonts/bad` | 119 | 0 | 0 | 7 | 112 | 0 | 0 |
| `tests/fonts/fuzzing` | 201 | 143 | 16 | 0 | 42 | 0 | 0 |
| installed fonts | 108 | 106 | 1 | 1 | 0 | 0 | 0 |
| Source Serif 4 (OTF, TTF, variable) | 124 | 122 | 2 | 0 | 0 | 0 | 0 |
| layout mutations | 1800 | 819 | 4 | 40 | 937 | 0 | 0 |

The 16 good fonts only OTS accepts are 15 `CFF2` fonts and one
two-glyph collection whose only `cmap` subtable is a format 4 with
segments out of order, which OTS accepts and verilith-font's format 4 rules do
not. The 16 in the fuzzing set are variants of that same file. The bad
fonts only verilith-font accepts are malformed in a part verilith-font drops (`COLR`, a
Graphite table, or one `cmap` subtable). The installed font verilith-font refuses
is Noto Color Emoji, which has no outlines; the one OTS refuses has a
misaligned `FFTM` table, which verilith-font drops. The two Source Serif fonts
verilith-font refuses are the `CFF2` variable fonts.

The layout mutations are 1,800 copies of four fonts (DejaVu Sans,
FreeSerif, Source Serif 4 Regular, Source Serif 4 Variable Roman), each
with one byte of `GDEF`, `GSUB` or `GPOS` changed by
`scripts/mutate-layout.py`. The two sanitizers agree on 1,756 of them.
Of the 40 only verilith-font accepts, 36 are damaged in variation data verilith-font
drops and 4 in a language system verilith-font repairs. Of the 4 only OTS
accepts, 3 are damaged in a default language system and one has a
`GDEF` minor version of 131.

## Building and verifying

The proofs hold for 64-bit and for 32-bit targets (wasm32 included):
`scripts/verify.sh font` checks the first and `crates/font/scripts/verify-narrow.sh`
the second, and the tests pass on wasm32-wasip1. On a 32-bit target
`check_font` also asks that the font be at most `isize::MAX` bytes,
which every Rust slice is.

```sh
cargo build --release      # target/release/libverilith_font.a and the rlib
cargo test --release
scripts/test-capi.sh
scripts/verify.sh          # the proofs: needs cargo-verus on PATH
```

The proofs need the Verus release whose `vstd` matches the version pinned
in `Cargo.toml`. CI (`.github/workflows/ci.yml` at the repository root) verifies the proofs and runs `ci.sh` on every pull request and push to `main` that touches this crate or a crate it depends on.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/font/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/font/LICENSE-MIT), at your option.
