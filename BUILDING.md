# Buck2 in this repository

Cargo builds and tests the crates, and stays the way people who use them
build them. Buck2 sits beside it and, for now, does one job: it runs Verus.
It knows which files each crate's proofs are built from, so it can tell
when a proof needs checking again, and it can check a large crate as several
parts at once.

## Setting up

```sh
scripts/install-buck2.sh           # the pinned release, into ~/.local/bin
```

and Verus, built from the commit in `scripts/verus-version`, with its
`target-verus/release` directory on `PATH` (the same build `cargo verus`
needs). Then:

```sh
scripts/prove.sh zlib              # verify one crate
scripts/prove.sh                   # verify all of them
buck2 build //crates/zlib:zlib     # the same thing, as a Buck2 command
buck2 build '//crates/wasm:wasm[part2]'   # one part of a crate verified in parts
```

A second run does nothing: Buck2 sees that no input changed. Change a file
in `crates/core/src` and the crates that depend on core are checked again;
change a test or a README and nothing is. Buck2 keeps this knowledge in its
background process, so after `buck2 kill` or a reboot it verifies again
(see "A shared cache" below).

## What is where

| | |
|---|---|
| `verus/defs.bzl` | The rules: `verus_library` (a crate with proofs), `verus_vstd`, `rustc_library`. |
| `verus/verus.py` | Runs Verus for those rules, and decides whether a run counts as passed. |
| `crates/<name>/BUCK` | One `verus_library` per verified crate. Generated. |
| `third-party/BUCK` | vstd and the crates.io crates the verified crates use. Generated. |
| `toolchains/BUCK` | Where the rules find `verus.py` and the Verus pin. |
| `scripts/buckify.py` | Writes the generated files from `Cargo.toml` and `Cargo.lock`. |
| `scripts/buck2-version` | The Buck2 release, with checksums. |

**The BUCK files are generated, not written.** `Cargo.toml` and `Cargo.lock`
remain the one description of the crates. After changing a dependency, a
feature, a version, or adding a crate, run `scripts/buckify.py` and commit
the result. CI runs `scripts/buckify.py --check` and fails if they differ,
so the two cannot drift apart. `buckify.py` stops with an error on anything
it cannot reproduce exactly (a crate that asks for non-default features of
another, a new crates.io dependency with a build script, and so on).

## How a crate is verified

For each crate Buck2 runs what `cargo verus focus` runs in the crate's
directory, without Cargo in between:

1. **vstd** is compiled from the crates.io release in `Cargo.lock`, with
   the features the crate's `Cargo.toml` asks for (most crates use `std`;
   x509 uses none). It is not verified here, and is not under Cargo either.
2. **The crates it depends on** are compiled (`:name[export]`), not
   verified: each is verified by its own target.
3. **The crate** is verified with its default features (`:name[partK]`),
   and a last step checks the parts add up (`:name`). A crate whose
   `scripts/verify.sh` passes `--features` is verified with those as well:
   it names them in `[package.metadata.verilith] verify-features`, and
   `buckify.py` fails if the two disagree. json is the one such crate
   (`cjson`).

The crate names, the sources and their paths, the features and the Verus
build are the same as under Cargo. That matters because proofs here are
sensitive to all of them.

## What stops a proof from being silently skipped

Buck2 only knows whether a command exited with 0. Everything that makes
that mean "the proofs hold" is in `verus/verus.py`, and fails closed:

- **The right Verus.** Each run's output names the commit and Rust
  toolchain Verus was built from. They must match `scripts/verus-version`,
  which is an input of every proof, so changing it re-checks everything.
- **Verus's own verdict.** The result is read from Verus's JSON output: no
  errors, and at least one proof verified. A crate verified in one part
  must also be reported by Verus as "verifying the entire crate".
- **Parts cover the crate.** A crate in parts is divided by module. The
  list of modules is asked of Verus itself, each module is put in exactly
  one part, each part names its modules to Verus one by one (Verus rejects
  a name it does not know), the crate root goes with part 1, and the final
  step checks that the parts together are the whole list. Nobody maintains
  a list of modules by hand, so a new module cannot be left out of it.
- **Every verified crate has a target.** `buckify.py --check` fails if a
  crate with `verify = true` has no generated BUCK file, or a BUCK file was
  written by hand.
- **Buck2 against Cargo.** `scripts/crosscheck.sh` verifies a crate both
  ways and compares the number of verified proofs. CI does this for every
  crate once a week and whenever it is asked to. Pushes to main also run
  `cargo verus` on Apple Silicon. A mistake in the rules that drops a proof
  shows up as a count that is short.

## Verifying a crate in parts

Add to the crate's `Cargo.toml` and run `scripts/buckify.py`:

```toml
[package.metadata.verilith]
verify-parts = 4
```

The modules are spread over the parts by source size. Each part is its own
CI job, so a crate that takes 20 minutes takes about 5 of wall time. Splitting
does not change what any single proof sees: Verus builds the same query for
a function whether or not other modules are verified in the same run. A
crate whose time is in one module gains nothing: brotli is verified in 2
parts (16 minutes became 11), but wasm is not split, because 43 of its 44
minutes are a single proof, `run::execute`, and only rewriting that proof
as several smaller ones would shorten it.

## How CI skips proofs that already passed

`scripts/proof-plan.py` asks Buck2 for the files each proof is built from,
hashes them together with the BUCK files, the rules, the Buck2 version and
the platform, and names the proof after the hash. A job that passes saves an
empty GitHub cache entry under that name; the next run drops every proof
whose entry exists. Entries count only when saved by the same branch or by
main, which is also all GitHub lets a pull request read. The weekly run
ignores the entries.

## What Buck2 does not do yet

- **Building and testing.** `cargo build`, `cargo test` and each crate's
  `ci.sh` are unchanged. Moving them would mean Buck2 rules for the C
  reference libraries the tests compare against (zlib, c-ares, libpng,
  mbedTLS, RE2 and others), which today are built by shell scripts with
  whatever compiler the runner has.
- **A shared cache.** Buck2 can share results between CI and developers'
  machines through a remote cache. That needs a cache service; until there
  is one, CI uses the cache entries described above, and a fresh checkout
  or a restarted Buck2 verifies from nothing.
- **macOS.** Verification on Apple Silicon still goes through `cargo
  verus`. The rules should work there as they are, but no proof has been
  checked through them on a Mac.
