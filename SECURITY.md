# Security policy

Verilith replaces libraries that parse untrusted input, so we treat a wrong
answer as seriously as a crash.

## Reporting a vulnerability

Please report privately, not in a public issue or pull request, in one of
two ways:

- Open the repository's **Security** tab and choose **Report a
  vulnerability** ([direct link](https://github.com/verilith/verilith/security/advisories/new)).
- Email **security@verilith.sh**.

Say which crate and commit, what input or sequence of calls triggers the
problem, and what you saw against what you expected. A file or a short
program that reproduces it is the most useful thing you can send.

We aim to acknowledge a report within a week and to keep you informed
while we work on it. Once a fix is released we publish an advisory and
credit you, unless you ask us not to.

## What counts

Because the crates are formally verified, some reports matter to us that
would not be security bugs elsewhere:

- **Memory unsafety, a panic, or a hang** reachable from a crate's public
  Rust API or C API, on any input.
- **A result that contradicts a crate's specification**: verified code that
  accepts what its `spec.rs` rejects, or returns different output.
- **A mistake in a specification**: a `spec.rs` that disagrees with the
  standard it was written from in a way a crate's README does not list.
  The proofs hold against the specification, so this is the kind of bug
  they cannot catch.
- **A mistake in the trusted base**: an `external_body` primitive or an
  assumed SIMD specification whose contract is false, or C glue that
  misuses the verified code. Each crate lists its trusted base in its
  `TRUST.md` or README.
- **A way to make the proofs pass without proving anything**, in the code
  or in the CI that checks them.

Not in scope: behaviour a crate's README documents as a deliberate
difference from the library it replaces, timing side channels (no crate
claims constant-time behaviour), and resource use within the bounds a
crate states.

## Supported versions

The crates are pre-release (0.1). Fixes go to `main`; there are no
maintained release branches yet.
