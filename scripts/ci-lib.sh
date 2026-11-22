# Shared setup for each crate's ci.sh. Sourced, not run.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[1]}")"
crate=$(basename "$PWD")
ROOT=$(cd ../.. && pwd)
# The Cargo profile this crate's release builds use.
P=$("$ROOT/scripts/profile" "$crate")
# The workspace's target directory.
T=${CARGO_TARGET_DIR:-$ROOT/target}
# Where downloads and builds of the original libraries go.
W=${CI_WORK:-$T/ci/$crate}
mkdir -p "$W"

# apt PACKAGE...: installs system packages, on CI only.
apt() {
  if [ -n "${CI:-}" ]; then sudo apt-get update -q && sudo apt-get install -y -q "$@"; fi
}

# Nightly Rust and cargo-fuzz.
fuzz_tools() {
  rustup toolchain install nightly --profile minimal
  command -v cargo-fuzz > /dev/null || cargo install cargo-fuzz --locked
}
