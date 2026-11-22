#!/usr/bin/env bash
# install-buck2.sh [DIR]: downloads the Buck2 release pinned in
# scripts/buck2-version into DIR (default ~/.local/bin), after checking its
# checksum. Needs curl and zstd.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/buck2-version"
dir=${1:-$HOME/.local/bin}
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) triple=x86_64-unknown-linux-musl ;;
  Linux-aarch64) triple=aarch64-unknown-linux-musl ;;
  Darwin-arm64) triple=aarch64-apple-darwin ;;
  Darwin-x86_64) triple=x86_64-apple-darwin ;;
  *) echo "install-buck2.sh: no Buck2 build pinned for $(uname -s) $(uname -m)" >&2; exit 1 ;;
esac
var=BUCK2_SHA256_${triple//-/_}
want=${!var}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
curl -fsSL --retry 3 -o "$tmp/buck2.zst" \
  "https://github.com/facebook/buck2/releases/download/$BUCK2_RELEASE/buck2-$triple.zst"
if command -v sha256sum > /dev/null; then got=$(sha256sum "$tmp/buck2.zst" | cut -d' ' -f1)
else got=$(shasum -a 256 "$tmp/buck2.zst" | cut -d' ' -f1); fi
if [ "$got" != "$want" ]; then
  echo "install-buck2.sh: checksum mismatch for buck2-$triple.zst: got $got, want $want" >&2
  exit 1
fi
mkdir -p "$dir"
zstd -d -q -f "$tmp/buck2.zst" -o "$dir/buck2"
chmod +x "$dir/buck2"
echo "buck2 $BUCK2_RELEASE installed in $dir"
