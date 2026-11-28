# What verilith-xml trusts

Verus checks every proof in verilith-xml, but a proof means something only
relative to what it starts from. This is everything assumed rather than
proven. [TRUST-LEDGER.md](../../TRUST-LEDGER.md) at the repository root
lists each trusted item mechanically; this file says why each one is there.

## The specification

What "correct" means here, so it has to be read against XML 1.0 (Fifth
Edition):

- `src/spec.rs`: well-formedness of a document, one spec function per
  production, with each well-formedness constraint where it applies.
- `src/pe_spec.rs`: the DTD read whole (parameter entities, conditional
  sections, the external subset, §5.1).
- `src/stream_spec.rs`, `src/items_spec.rs`: what the push parser emits.
- `src/walk.rs`: `items`, the order in which the C ABIs report content.
- `src/atts.rs`:
  - `decls`: the attribute-list declarations that apply. They are those
    before the end of the document type declaration and, unless the
    document is standalone, before the first parameter-entity reference
    that was not read (§5.1).
  - `binding`: the first definition of an attribute binds (§3.3).
  - `is_default`: a default applies to a start tag that does not specify
    the attribute (§3.3.2).
  - `collapse`: the normalization of a value whose declared type is not
    CDATA (§3.3.3).
- `src/reach.rs`:
  - `question`: the question the loader is asked for an external parsed
    entity. It is the base URI of the entity whose text holds the
    declaration, then the system and public identifiers.
  - `ext_rt`: the entity's replacement text. That is the answer decoded,
    after its text declaration, with line ends normalized.
  - `bad`: the replacement text is not content (§4.3.2).
  - `edge`: a reference in a replacement text names an entity (the first
    declaration binding, §4.2).
  - `reachable`: the entities a document reaches.
  - `on_cycle`: an entity lies on a cycle of references (§4.1, WFC: No
    Recursion).

The W3C conformance suite checks the spec through the code (README,
[Test results](README.md#test-results)), and the differential tests and
fuzzing compare it with libexpat.

A few spec functions are guarded so that Verus accepts their recursion:
`if !(i < e <= s.len()) { None }`, and the fuel of `pe_spec::flat`. Each
step moves forward and stays in the input, so the guards are never taken
on a real input.

## `external_body` items

- `tape::slice_len_bound` states that a slice is at most `isize::MAX`
  bytes long, as Rust guarantees of every object, so positions cannot
  overflow.
- `uniq::seed` reads random words for the hash tables of Unique Att Spec.
  Any value gives the same result. Only the time taken depends on it.
- `pe::Loader` is the caller's loader for `parse_with`. It is trusted in
  these ways:
  - `fetch`: its answers are a function of the question (`load_model`).
    It keeps each answer, so they are. Nothing else is known of them.
  - `count`, `bytes`: how many entities and bytes it has read. They
    enforce the limits of 4096 entities and 256 MiB. Nothing is proven of
    them. A wrong count can only refuse a document with
    `ErrorKind::Limit`, or let more be read. It cannot change which
    documents are accepted or what they contain.
  - `note_push`, `note_fetch`, `note_pop`: record where each parameter
    entity's text lies in the DTD read whole (the trace). Nothing is
    proven of the trace. It gives error positions and the base URI in the
    question for an external parsed entity (`reach::base_from`). A wrong
    trace can only change which base URI the loader is asked with.

## The unverified glue

`src/api.rs` (about 900 lines, no `unsafe`) is ordinary Rust. It is not
compiled when verifying, so the preconditions of the verified functions it
calls are trusted rather than checked at those calls:

- `AttTable::build(s, t, sa)` needs at most `isize::MAX` tokens, which
  Rust guarantees of a slice.
- `AttTable`'s other methods need `table_ok(s, self)`, that is, the DTD
  text the table was built from. The API keeps both in the `Document`.
- `next_default` needs a group number that `group_of` returned for the
  element type.
- `reach::ex_read_external` needs `args_ok`. That means the environment
  and the replacement texts of internal entities produced by the verified
  DTD parser, one text per entity, each under `tape::MAX_POS`.

Besides those calls, the API navigates the tape and converts byte spans to
`&str` (checked, with `str::from_utf8`). The expat and libxml2 ABIs
(`src/api/expat.rs`, `src/api/libxml2/`) are unverified too, and so is
everything they do at the C boundary: they trust every pointer and length
the caller passes, as a C library does. Which item of content they report
next is not theirs to decide: each takes it from the verified
`walk::Cursor`, which needs nothing of its caller (out-of-range arguments
to `Cursor::new` are cut to the tape, and its theorem holds for any tape).
What the ABIs keep about each open element is pushed on the cursor's
`Start` and popped on its `End`; that the two stay in step rests on the
cursor's balance theorem and on the ABIs pushing once per `Start`. The README's
[What is not proven](README.md#what-is-not-proven) describes how each is
tested.

## Tools

The other trusted pieces are:

- verilith-simd's specifications of the six SSE2 instructions the scanners
  use. They are tested there against the CPU.
- vstd's specifications of `Vec`, slices and the standard library.
- Verus, Z3 and the Rust compiler.
