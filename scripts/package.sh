#!/usr/bin/env bash
# What crates.io and docs.rs will see, checked before anything is published:
#
# - `cargo package` builds every published crate from its own .crate file,
#   with plain rustc and vstd from crates.io (no Verus), so a file left out
#   of a package, or a path that only resolves inside the repository, fails
#   here rather than after `cargo publish`.
# - `cargo doc` builds the documentation the way docs.rs does (the features
#   in each crate's [package.metadata.docs.rs]) and fails on a broken link.
#   Spec functions and lemmas are compiled out of a normal build, so a doc
#   link to one is broken on docs.rs although Verus resolves it: name such
#   items in backticks, without brackets.
#
#   scripts/package.sh            both
#   scripts/package.sh doc        the documentation only
set -euo pipefail
cd "$(dirname "$0")/.."

# The bindings are not published (publish = false).
UNPUBLISHED=(--exclude verilith-bind --exclude verilith-bind-node --exclude verilith-bind-python)

if [ "${1:-}" != doc ]; then
  cargo package --workspace "${UNPUBLISHED[@]}"
fi

export RUSTDOCFLAGS="-D rustdoc::broken_intra_doc_links -D rustdoc::private_intra_doc_links -D rustdoc::invalid_html_tags -D rustdoc::bare_urls"
cargo doc --no-deps --workspace "${UNPUBLISHED[@]}"
# The crates whose docs.rs build turns features on.
cargo doc --no-deps -p verilith --all-features
cargo doc --no-deps -p verilith-json --features serde
