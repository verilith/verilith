# Releasing

How verilith versions relate to Verus and `vstd`, and what a release that
changes them has to do. The crates are not on crates.io yet; this is the
policy they will be published under.

## The pin

Every crate is verified with one Verus release, and depends on the `vstd`
cut from that release's commit. Both are pinned exactly:

| | Where | Now |
|---|---|---|
| Verus release | `scripts/verus-version` (`VERUS_RELEASE`) | `0.2026.11.02.8bf68ee` |
| Verus commit | `scripts/verus-version` (`VERUS_COMMIT`) | `8bf68ee741df833ea5d0fe6a2255126fdea87e47` |
| Rust toolchain Verus is built with | `scripts/verus-version` (`VERUS_TOOLCHAIN`) | `1.99.1` |
| `vstd`, `verus_builtin`, `verus_builtin_macros`, `verus_state_machines_macros` | `[workspace.dependencies]` in `Cargo.toml` | `=0.0.0-2026-11-01-0251` |

The Rust toolchain above is only for running Verus. Building the crates
needs Rust 1.89 or later (the `rust-version` in each `Cargo.toml`).

The pin is exact (`=`) because a proof is only checked against one `vstd`.
Its specifications and axioms change between releases, so code verified
with one release is not known to verify with the next, and vstd pins its
own `verus_builtin` crates exactly too.

## What the pin means for users

**Two verilith releases that pin different `vstd`s cannot be in one
dependency graph.** Every `vstd` release is versioned `0.0.0-<date>`, and
Cargo allows only one `0.0.0` of a crate in a build. A project that depends
on `verilith-json` built against `vstd =0.0.0-2026-11-01-0251` and on
`verilith-zlib` built against `vstd =0.0.0-2026-11-15-0327` fails to
resolve:

```
failed to select a version for `vstd` which could resolve this conflict
  previously selected package `vstd v0.0.0-2026-11-01-0251`
```

The same holds for a project that uses `vstd` itself, for its own proofs:
it has to use the `vstd` the verilith crates pin, and verify with the Verus
release in the table above.

So:

- Use verilith crates from the same release line (the same minor version,
  see below). They all pin the same `vstd`.
- To find which `vstd` a verilith release pins, look up its version in the
  table at the end of this file, or read `vstd` in its `Cargo.toml` on
  docs.rs or crates.io.

## Versions

All published crates share one version and are released together, from
one commit. While the crates are at 0.x:

- **A change to the Verus or `vstd` pin is a breaking release**: every
  crate's minor version goes up (0.1.x to 0.2.0), even a crate whose code
  did not change. A crate that kept the old minor version while depending
  on the new `vstd` would let Cargo pick a set that cannot resolve.
- **A patch release (0.1.x to 0.1.x+1) never changes the pin.** Bug fixes
  that need a newer Verus wait for the next minor release, or are made with
  the current one.
- After 1.0, a pin change is a major release, for the same reason.

The crates depend on each other with `version = "<x.y.z>"` (a caret
requirement), so within a minor version they mix freely.

## When to move the pin

Move it when there is a reason, not on every Verus release:

- a Verus or `vstd` fix the proofs need, or a soundness fix in either
  (these come first: release as soon as the proofs pass);
- a feature that removes trusted code or shortens proofs;
- the pinned release has fallen behind enough that the next move would be
  hard (more than about three months).

Several of these can wait for one minor release. Moving the pin only
in a minor release keeps the number of `vstd`s in use small.

## Moving the pin

One pull request, which changes the pin and nothing else that is not
needed for it:

1. `scripts/verus-version`: the new release, commit, toolchain and the four
   checksums of its release builds.
2. `Cargo.toml`: the four `[workspace.dependencies]` Verus crates, all at
   the `vstd` version cut from that commit. Then `cargo update -p vstd` and
   check that `Cargo.lock` has one `vstd`.
3. `scripts/buckify.py`, which regenerates `third-party/BUCK` (and each
   crate's `BUCK`) from `Cargo.lock`, so that Buck2 builds the new `vstd`.
   `scripts/buckify.py --check` then passes.
4. Whatever the proofs need for the new release (an API that moved, a
   lemma that is now in `vstd`). Say in the pull request what changed and
   why the proof still says what it said.
5. Every proof from nothing: run the CI workflow with "fresh", which also
   runs `scripts/crosscheck.sh`. On Apple Silicon, `scripts/verify.sh` with
   the new release.
6. `scripts/package.sh` and `scripts/wasm32.sh`.
7. This file: the table above.

## Making a release

1. Set the same `version` in every published crate, and the same version in
   the requirements between them.
2. `scripts/package.sh`, `scripts/trust-ledger.py --check`, and a fresh run
   of every proof on the release commit.
3. Publish in dependency order (`cargo publish --workspace` orders them),
   and tag the commit `v<version>`.
4. Add a row to the table below.

## Releases and their pins

| verilith | Verus release | `vstd` |
|---|---|---|
| unreleased (main) | `0.2026.11.02.8bf68ee` | `=0.0.0-2026-11-01-0251` |
