# What verilith-archive trusts, and why

Verus checks every proof in verilith-archive, but a proof means something only
relative to the specifications it starts from and the code it does not
cover. This file lists everything that is assumed rather than proven.

## The short list

- **Tools**: Verus (pinned in `Cargo.toml` and CI), Z3, rustc.
- **vstd**, Verus's standard library, and its specifications of `Vec` and
  slices.
- **The format specification**, `src/spec.rs`: our reading of the format
  documents. If it is wrong, the parsers are faithfully wrong.
- **The extraction model and policy**, `src/policy.rs`: `comps_from`,
  `resolve` and `plan_safe`. The containment theorem is about this model of
  the file system.
- **verilith-zlib, verilith-zstd and verilith-checksum**: their specifications of DEFLATE, Zstandard
  and CRC-32 are part of ours (`unpack`, `entry_data`), and whatever their
  own TRUST files list is trusted here too.
- **Two unverified sorts**, whose results are checked by verified code.
- **Plain Rust around the verified core**: `src/api.rs`, `src/extract.rs`,
  `src/capi.rs`.

There is no `assume`, no `admit` and no `axiom` in the crate. The only
`external_body` functions are the two sorts.

## The format specification

`spec.rs` says what members an archive has. What a reader of the theorems
should check there:

- **zip** (`zip`, `zip_end`, `zip_entry`): the end-of-central-directory
  record is the last one whose comment ends exactly at the end of the file;
  zip64 values replace the 16- and 32-bit ones exactly where those are all
  ones; the central directory is authoritative for sizes, CRC and offsets,
  and the local header must agree on name, method and the encryption bit; a
  member's data must end before the central directory; and `zip` is `None`
  unless the members are pairwise disjoint. This is stricter than APPNOTE
  on purpose. Sizes and CRC in a local header or data descriptor are not
  compared with the central ones (they are never used).
- **tar** (`tar_header`, `tar_step`, `tar`): the checksum, octal and
  base-256 numbers, ustar prefix, pax `x` and `g` records (`path`,
  `linkpath`, `size`), GNU `L` and `K` long names. Sparse (`S`) and
  multi-volume (`M`) members make the archive unsupported, not misread.
  Other pax keys are ignored.
- **Data** (`entry_data`): method 0, 8 (raw DEFLATE, all of the compressed
  bytes used) or 93 (Zstandard), exactly the declared size, the declared
  CRC-32 where there is one (tar has none).

`src/reader.rs` chooses the format: tar if the bytes are a tar archive with
at least one member, otherwise zip, otherwise an empty tar. That order is a
choice, not a theorem about the formats.

## The extraction model

`resolve` models path resolution: components left to right, `..` to the
parent (escaping at the root), a component that is a symbolic link replaced
by the link's target, including in last position. The theorem then holds
for a real extraction under these assumptions, which are not proven:

1. **The model matches the system.** Paths are sequences of bytes split at
   `/`; names differing in bytes are different files. On a file system that
   folds case or normalises Unicode, two members the planner sees as
   different can be the same file, and one can be a symbolic link. The
   theorem does not cover that; extract onto a case-sensitive file system.
2. **The only symbolic links under the root are ones the plan created.**
   Extracting into a directory that already has links in it, or one that
   another process changes during extraction, is outside the theorem.
   `extract` creates files with `create_new`, so it never writes over an
   existing file, but that is tested, not proven.
3. **Links are relative.** The planner refuses absolute targets, so
   `resolve` has no case for them.
4. **Hard links** are not in `resolve`. The policy requires the target to
   be a regular file created earlier by the same plan, which is under the
   root by the theorem.

`plan_safe` is the policy; README.md states it in words. `plan_of`
(also in `src/policy.rs`) says which plan an archive has, so it is trusted
in the same way: one step per member not of kind `Other`, in member order,
each `item_of` its member. The planner is proven to return that plan when
it exists and satisfies `plan_safe`, and to refuse otherwise: every
refusal except `Why::Internal` comes with a proof that the archive has no
plan satisfying the policy. `Why::Internal` is returned only if the sort
below returns something `check_sorted` does not accept as a strictly
sorted permutation. The sort is proven to return a sorted permutation,
but that `check_sorted` then always accepts it is not proven, so
completeness rests on that step. Which of the other `Why`
values is returned, and for which member, is not proven: it names the
check that failed first.

## The two sorts

`order_by_offset` (`src/zip.rs`) and `order_by_path` (`src/plan.rs`) are
verilith-core's verified merge sort (`verilith_core::sort::order_by`),
which is proven to return a permutation in which each member is not after
the next. Nothing in them is trusted. `check_order` and `check_sorted`
still check the result before it is used (strictly increasing, for
paths), and if the zip check fails the reader falls back to a verified
comparison of every pair.

## Plain Rust

Not verified, kept thin, and where the tests concentrate:

- `src/api.rs` (about 150 lines): removes an outer gzip or Zstandard layer
  with verilith-zlib and verilith-zstd, calls `reader::parse`, and passes requests to
  `read_entry`, `stored_in_place` and `plan`. It is the code that
  establishes those functions' preconditions (archive below 2^48 bytes,
  members in bounds, which `parse` ensures).
- `src/extract.rs` (about 80 lines): turns a plan into `create_dir_all`,
  `File::create_new`, `symlink` and `hard_link` calls under the root. The
  theorem says where the plan's paths lead; this file is trusted to use
  exactly those paths.
- `src/capi.rs`: the libarchive-shaped C interface. It is `unsafe` at the
  boundary by nature: it trusts the caller's pointers, and after
  `archive_read_open_memory` it keeps reading the caller's buffer, which
  must stay valid and unchanged until the archive is closed (libarchive
  requires the same).

## Tests are evidence, not proof

The differential tests against libarchive, the attack tests and the
mutation test check the specification's reading of the formats and the
plain Rust above. They do not extend the theorems.
