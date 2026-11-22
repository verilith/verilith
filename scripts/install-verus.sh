#!/usr/bin/env bash
# Installs the Verus release pinned in scripts/verus-version into DIR
# (default ~/verus-bin), after checking its checksum, and the Rust toolchain
# it needs. Then put DIR on PATH and set VERUS_Z3_PATH=DIR/z3.
#   scripts/install-verus.sh [DIR]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/verus-version"
dir=${1:-$HOME/verus-bin}
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) plat=x86-linux ;;
  Linux-aarch64 | Linux-arm64) plat=arm64-linux ;;
  Darwin-arm64) plat=arm64-macos ;;
  Darwin-x86_64) plat=x86-macos ;;
  *) echo "install-verus: no Verus release build for $(uname -s) $(uname -m)" >&2; exit 1 ;;
esac
want=VERUS_SHA256_${plat//-/_}
want=${!want}
rustup toolchain install "$VERUS_TOOLCHAIN" --profile minimal -c rustc-dev,llvm-tools
if [ -x "$dir/cargo-verus" ] && grep -qs "\"$VERUS_COMMIT\"" "$dir/version.json"; then
  echo "install-verus: $VERUS_RELEASE is already in $dir"
  exit 0
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
curl -sSfL --retry 3 -o "$tmp/verus.zip" \
  "https://github.com/verus-lang/verus/releases/download/release/$VERUS_RELEASE/verus-$VERUS_RELEASE-$plat.zip"
if command -v sha256sum > /dev/null; then got=$(sha256sum "$tmp/verus.zip"); else got=$(shasum -a 256 "$tmp/verus.zip"); fi
got=${got%% *}
[ "$got" = "$want" ] || { echo "install-verus: checksum of verus-$VERUS_RELEASE-$plat.zip is $got, expected $want" >&2; exit 1; }
unzip -q "$tmp/verus.zip" -d "$tmp"
rm -rf "$dir"
mkdir -p "$(dirname "$dir")"
mv "$tmp/verus-$plat" "$dir"
# A download made by curl carries no quarantine flag, but one moved here from a browser does.
[ "$(uname -s)" != Darwin ] || xattr -dr com.apple.quarantine "$dir" 2> /dev/null || true
echo "install-verus: $VERUS_RELEASE in $dir"
