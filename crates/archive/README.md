# verilith-archive

Zip and tar readers, and an extractor that cannot be made to write outside
its target directory, written in Rust and verified with
[Verus](https://github.com/verus-lang/verus).

Archive readers are parsers of attacker-controlled bytes followed by file
system writes at attacker-chosen names, and the same bugs keep coming back:
`../` in a name (zip-slip), a symbolic link planted by one member and
written through by the next, size and offset fields that lie or overflow,
members that overlap (zip bombs), data that runs past its declared size.
verilith-archive rules these out as theorems rather than by tests.

It builds on [verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib) (DEFLATE,
gzip), [verilith-zstd](https://github.com/verilith/verilith/tree/main/crates/zstd) (Zstandard) and
[verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (CRC-32).

## What is proven

Everything below is checked by Verus on every build of the proofs
(`scripts/verify.sh`: 135 verified, 0 errors). [TRUST.md](TRUST.md) lists
what the proofs assume.

**No panics, no out-of-bounds reads, no overflow** in the parsers, the
member reader and the planner, on any input.

**Parsing is exactly the specification.** `src/spec.rs` defines, in about
900 lines written from PKWARE's APPNOTE (including zip64) and from the
POSIX ustar and pax and the GNU tar formats, what members an archive has.
The parsers return exactly that:

```rust
pub fn parse_zip(b: &[u8]) -> (r: Option<Vec<Entry>>)
    ensures match r {
        Some(es) => zip(b@) == Some(views(es@)) && disjoint(views(es@)) && in_bounds(views(es@), b@.len()),
        None => zip(b@) is None,
    }
```

and the same for `parse_tar`. So the fields cannot lie: every member lies
inside the archive (`in_bounds`), the arithmetic that finds it cannot wrap,
and **no two members overlap** (`disjoint`: each member's bytes, from its
header to the end of its data, are its own). A zip whose local header
disagrees with the central directory about a member's name, compression
method or encryption is not an archive.

**A member's data is exactly what it declares.** `read_entry` returns
`entry_data`: the bytes that the member's own compressed range decompresses
to, only if that is exactly the declared size and, where the format has
one, the declared CRC-32. Nothing is returned, or allocated, past the
declared size, and a caller's limit is enforced before anything is
allocated.

**Extraction stays under the root.** `src/policy.rs` models how the
operating system walks a path, following symbolic links (`resolve`), and
states the policy (`plan_safe`). The planner's contract is

```rust
pub fn plan(b: &[u8], es: &Vec<Entry>) -> (r: Result<Vec<Item>, Rejected>)
    ensures r matches Ok(items) ==> plan_safe(sitems(items@)) && items_match(b@, views(es@), items@)
```

and the theorem is

```rust
pub proof fn theorem_contained(items: Seq<SItem>, i: int, sub: Map<Path, Path>, fuel: nat)
    requires plan_safe(items), 0 <= i < items.len(), sub.submap_of(links_of(items)),
    ensures
        !(resolve(sub, Seq::empty(), items[i].path, fuel) is Escaped),
        items[i].kind is Symlink ==> !(resolve(sub, items[i].path.drop_last(), items[i].target, fuel) is Escaped),
```

In words: for a plan the planner accepts, whatever subset of the plan's
symbolic links exists at the moment (so in any order of extraction, and
after a partial one), no path the extractor writes and no symbolic link it
creates resolves to a place outside the root. The policy that gives this:
names are relative, with no `..`, no NUL and no backslash; no two members
have the same path; no member's path passes through a symbolic link of the
archive; a symbolic link's target is relative and, walked from the link's
directory, stays under the root and passes through no other link; a hard
link's target is a regular file that an earlier member creates.

The planner is sound, not complete: when it refuses, it has not proven that
the archive is dangerous. It refuses some harmless archives on purpose (a
member stored twice, a file written through a symbolic link that points
inside the tree).

## Using it

```rust
let a = verilith_archive::Archive::open(&bytes)?;      // zip, tar, .tar.gz, .tar.zst
for (i, e) in a.entries().iter().enumerate() {
    let data = a.read(i)?;                      // exactly e.size bytes, CRC checked
}
verilith_archive::extract(&a, std::path::Path::new("out"))?;   // all of it, or nothing
```

`cargo run --release --example varc -- list|extract ARCHIVE [DIR]` is a
small command line around this.

## The C API: libarchive's read API

With the feature `libarchive-abi`, `libverilith_archive.a` exports the part of
libarchive's read API that readers use, under libarchive's names, so a C
program written against `<archive.h>` links against it unchanged (without
the feature the same functions are `varchive_*`).

Why libarchive, and not minizip or libzip: it is the only one of the three
that reads both formats, it is what the callers that matter use (bsdtar,
CMake, pacman, package managers and file managers on every Linux and BSD
and on macOS), and those callers use a small, uniform part of it:
`archive_read_new`, `archive_read_support_format_*` and `_filter_*`,
`archive_read_open_memory` / `_open_filename`, `archive_read_next_header`,
the `archive_entry_*` getters (pathname, size, filetype, perm, mode, mtime,
symlink, hardlink), `archive_read_data` / `_data_block` / `_data_skip`,
`archive_read_extract`, `archive_error_string`, `archive_read_free`. That
is what is implemented. minizip and libzip are zip-only, and their callers
lean on write and update calls that a reader cannot offer.

`tests/c/run.sh` builds one C program against the system's libarchive and
against verilith-archive and compares what they print for every test archive.

### Differences from libarchive

- A zip's end-of-central-directory record must end exactly at the end of
  the file, and local headers must agree with the central directory.
  libarchive reads zips in streaming mode too and accepts trailing data and
  disagreeing headers; these are the ambiguities that make two tools see
  two different archives, so verilith-archive refuses them. In the mutation test,
  libarchive accepts about 380 of 2,700 damaged archives that verilith-archive
  refuses, and verilith-archive accepts 7 that libarchive refuses.
- On macOS only, libarchive's tar reader treats a member named `._NAME`
  (AppleDouble: the extended attributes that macOS's tar stores beside a
  file) as metadata of the next entry and does not return it. verilith-archive
  returns it as an ordinary member, as libarchive does on every other
  system, so on macOS a tar made by macOS's own tar lists more members
  through verilith-archive than through libarchive.
- A member's data is checked (length and CRC-32) before any of it is
  returned, and `archive_read_data_block` returns it as one block.
  libarchive streams and reports a bad CRC after the last block.
- `archive_read_extract` plans the whole archive first and, if the planner
  refuses it, extracts nothing from it. Its flags are ignored: the secure
  behaviour is the only one, files are never overwritten, and owners and
  times are not restored.
- The archive is held in memory. `archive_read_open_filename` reads the
  whole file; there are no callbacks or file descriptors.
- Not supported: encrypted members; zip methods other than stored, DEFLATE
  and Zstandard; zips split over several disks; sparse and multi-volume tar
  members; other formats (cpio, 7z, rar, ...) and filters (bzip2, xz, ...).
  Device nodes and FIFOs are listed, never extracted.
- By default no decompression produces more than 1 GiB
  (`Archive::open_with_limit`).

## Tests

- `tests/attacks.rs`: hand-made hostile archives for each class above
  (zip-slip, absolute names, link escapes, duplicates, overlapping members,
  lying sizes and offsets, pax and GNU long names), and that a refused
  archive writes nothing.
- `tests/libarchive.rs`: every member of 18 archives made by GNU tar,
  bsdtar, Info-ZIP and Python (429 members) read through the C API and
  through libarchive itself, compared field by field and byte by byte;
  then 2,700 mutations of them through both, where neither may crash and
  whatever both accept must agree.
- `tests/extract.rs`: extraction compared with the archives' contents.

`cargo test --release` runs them (the differential tests need
`libarchive.so.13`). GitHub Actions is manual-only (`.github/workflows`).

## Speed

[vbench](https://github.com/verilith/verilith/tree/main/bench) runs one driver
written against `<archive.h>` with libarchive 3.8.9 (built with zlib 1.3.2)
and with verilith-archive (`./run.sh --only archive`). On an Apple Silicon Mac,
2026-11-20, verilith-archive f8296ff, as libarchive's time divided by verilith-archive's
(above 1 means verilith-archive is faster):

| archive | read every member | list (headers only) |
| --- | ---: | ---: |
| tar, 5 Silesia files (53 MB) | 1.30x | 4.1x |
| tar, 2000 files of 4 KiB | 2.45x | 2.47x |
| tar.gz, 2000 files of 4 KiB | 2.13x | 2.14x |
| zip (DEFLATE), Silesia | 1.82x | 43x |
| zip (DEFLATE), 2000 files | 1.96x | 54x |
| zip (stored), Silesia | 1.03x | 43x |

How to read it:

- The zip listing figures are not about speed of the same work. verilith-archive
  reads the central directory; libarchive, reading from memory through its
  streaming interface, walks the local headers.
- Reading a stored zip is nothing but CRC-32, so the two are level. (It
  was 0.39x until verilith-core's CRC-32 on ARM went from one chain of `crc32x`
  instructions to three interleaved ones.)
- Each figure is the mean of two sittings, which agreed within 2%.

## License

MIT.
