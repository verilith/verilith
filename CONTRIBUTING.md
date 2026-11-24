# Contributing

Thank you for helping. Bug reports, specification reviews and pull requests
are all welcome. Please report a security problem privately, as
[SECURITY.md](SECURITY.md) describes, not in a public issue.

## The one rule

**Every proof must still pass, with no new holes.** A pull request must not
add `assume(...)`, `admit()` or `#[verifier::external_body]` to verified
code, or weaken a specification, unless the change is the point of the pull
request and its description says why. If you add something to a crate's
trusted base, list it in that crate's `TRUST.md` or the "Trusted base"
section of its README.

## Setting up

You need:

- stable Rust (the crates build with stable Rust, and the proofs are erased
  in a normal build);
- for the proofs: the Verus release pinned in `scripts/verus-version`.
  `scripts/install-verus.sh` installs it into `~/verus-bin`; then put that
  directory on `PATH` and set `VERUS_Z3_PATH=~/verus-bin/z3`. A change
  to that pin follows [RELEASING.md](RELEASING.md);
- for the C API tests and the comparisons, a C compiler, `cmake` and
  `git`: each crate's `ci.sh` fetches and builds the original library
  at a pinned version.

## Checking a change

Work on one crate at a time:

```sh
cd crates/zlib
cargo test --release     # the Rust tests
./ci.sh                  # everything CI runs for this crate
cd ../.. && scripts/verify.sh zlib    # the proofs, with cargo verus
```

`scripts/prove.sh zlib` checks the same proofs through Buck2, which is what
CI uses ([BUILDING.md](BUILDING.md)). If you change a `Cargo.toml`, run
`scripts/buckify.py` and commit the BUCK files it writes.

If you add, remove or move anything Verus takes on trust (an
`external_body`, an `axiom fn`, an `assume_specification`, a
`Ghost::assume_new()`, an `exec_allows_no_decreases_clause`, or a `src/`
file with no `verus!` block), run `scripts/trust-ledger.py` and commit the
`TRUST-LEDGER.md` it writes; CI fails until you do. Say in the pull request
why the new item is needed, and add it to the crate's TRUST.md or "Trusted
base" section.

CI checks the crates your change touches and every crate that depends on
them. A pull request is ready to merge when the `CI` check passes.

## Writing it up

- One topic per pull request. Say what changed, what is now proven that was
  not before (or what is no longer proven, and why), and how you checked it.
- If a change affects speed, say how you measured it. `bench/` has the
  harness the published numbers come from.
- If a crate's behaviour now differs from the library it replaces, add the
  difference to the list in its README.

## Licence

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this repository by you, as defined in the
Apache-2.0 license, shall be dual licensed under the MIT license and the
Apache License 2.0, without any additional terms or conditions.
