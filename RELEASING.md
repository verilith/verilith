# Releasing

How verilith versions relate to Verus and `vstd`, and what a release that
changes them has to do. The crates are not on crates.io yet; this is the
policy they will be published under.

## The pin

Every crate is verified with one Verus release, and depends on the `vstd`
cut from that release's commit. Both are pinned exactly:

| | Where | Now |
|---|---|---|
| Verus release | `scripts/verus-version` (`VERUS_RELEASE`) | `0.2026.11.22.1ce6a59` |
| Verus commit | `scripts/verus-version` (`VERUS_COMMIT`) | `1ce6a59bd72713cf486a7660097fe5ac57519617` |
| Rust toolchain Verus is built with | `scripts/verus-version` (`VERUS_TOOLCHAIN`) | `1.100.0` |
| `vstd`, `verus_builtin`, `verus_builtin_macros`, `verus_state_machines_macros` | `[workspace.dependencies]` in `Cargo.toml` | `=0.0.0-2026-11-22-0344` |

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
3. `scripts/publish.py` (a dry run), then publish: run the "Publish to
   crates.io" workflow with "dry_run" unticked, or `scripts/publish.py
   --publish` after `cargo login`. Then tag the commit `v<version>`.
4. Add a row to the table below.

## What is published

Every workspace member without `publish = false`, and `crates/tls-aws-lc`
(outside the workspace only because aws-lc is C and the workspace builds
only Rust). `scripts/publish.py --list` prints them in the order they are
published. Not published: `verilith-bind` and its Node.js and Python
crates, which ship through npm and PyPI.

`scripts/publish.py` skips a crate whose version is already on crates.io,
so a publish that stopped part way (a failure, or crates.io's limit on new
crates, about one every 10 minutes after the first 5) is finished by
running it again.

### Authentication

- **The first publish** of a crate needs a crates.io API token: on
  crates.io, Account Settings > API Tokens, with the `publish-new` and
  `publish-update` scopes, saved as the `CARGO_REGISTRY_TOKEN` secret of
  the `crates-io` environment: in the repository, Settings > Environments >
  New environment `crates-io`, then under Deployment branches and tags
  pick "Selected branches and tags" and add `main`, then Add environment
  secret.
- **After that, Trusted Publishing** (no token): on each crate's page on
  crates.io, Settings > Trusted Publishing > Add, with owner `verilith`,
  repository `verilith`, workflow `publish.yml` and environment
  `crates-io`. The
  workflow then gets a short-lived token from crates.io itself. Once every
  crate has it, the secret is only needed for new crates.
- A release that adds a crate needs the token again for that crate: run
  the workflow with auth "token".

## npm and PyPI

The Python and Node.js bindings (`crates/bind/python`, `crates/bind/node`)
are published as `verilith` on PyPI (imported as `vbind`; the name
`vbind` is taken there) and on npm, at the same version as the crates. Each
has a workflow run by hand, a dry run unless "dry_run" is unticked:

- **Publish to PyPI** (`.github/workflows/publish-pypi.yml`): seven abi3
  wheels (CPython 3.11 and later) for Linux x86_64 and aarch64 (glibc and
  musl), macOS arm64 and x86_64 and Windows x64, and the sdist. Each wheel
  is installed and tested before anything is uploaded.
- **Publish to npm** (`.github/workflows/publish-npm.yml`): the same seven
  platforms, napi-rs style. Each binary is its own package
  (`verilith-linux-x64-gnu`, ...), and `verilith` lists them as
  optional dependencies, so npm installs only the one that matches. Each
  binary is tested before anything is published.

A new version also needs, besides the `Cargo.toml`s: `version` in
`crates/bind/node/package.json` and its `optionalDependencies`, and
`npx napi version` in `crates/bind/node` for the platform packages.
`crates/bind/scripts/check-npm-packages.py` (which the npm workflow runs)
fails if any of them disagree. The PyPI version is read from `Cargo.toml`.

### Authentication

- **PyPI: Trusted Publishing only**, no token. Before the first publish,
  add a pending publisher (pypi.org > Account settings > Publishing): PyPI
  project `verilith`, owner `verilith`, repository `verilith`,
  workflow `publish-pypi.yml`, environment `pypi`. The first publish
  creates the project and turns it into an ordinary trusted publisher.
- **npm: a token the first time, then Trusted Publishing.** The first
  publish of each of the eight packages needs an npm granular access token
  (npmjs.com > Access Tokens > Generate New Token, read and write on
  packages, "bypass two-factor authentication" ticked), saved as the
  `NPM_TOKEN` repository secret. Then on each package's page, Settings >
  Trusted Publisher > GitHub Actions: owner `verilith`, repository
  `verilith`, workflow `publish-npm.yml`, environment `npm`. npm uses
  Trusted Publishing whenever it is set up, so the secret can then be
  deleted. A release that adds a platform needs it again for that package.

## Releases and their pins

| verilith | Verus release | `vstd` |
|---|---|---|
| unreleased (main) | `0.2026.11.22.1ce6a59` | `=0.0.0-2026-11-01-0251` |
