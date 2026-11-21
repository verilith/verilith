#!/usr/bin/env bash
# Builds OTS's `ots-sanitize` by hand, for scripts/difftest.sh, without
# meson (whose wrap downloads may be blocked).
#   scripts/build-ots.sh OUTDIR
# Clones OTS and google/woff2 at the commits the README's numbers were
# measured with, unless OTS_SRC and WOFF2_SRC name existing checkouts.
# Needs a C++ compiler, zlib and brotli (headers and libraries).
set -euo pipefail
out=$(mkdir -p "$1" && cd "$1" && pwd)
ots=${OTS_SRC:-$out/ots}
woff2=${WOFF2_SRC:-$out/woff2}
if [ ! -d "$ots" ]; then
  git clone https://github.com/khaledhosny/ots "$ots"
  git -C "$ots" checkout c5d249ce90ab0aa3e76eb0dfad28746f407201d0
fi
if [ ! -d "$woff2" ]; then
  git clone https://github.com/google/woff2 "$woff2"
  git -C "$woff2" checkout 7b67e12355fe7da148db5c19d4261f0a498a9537
fi
cat > "$out/config.h" <<'CFG'
#define PACKAGE "ots"
#define VERSION "9.x"
#define OTS_COLR_CYCLE_CHECK 1
#define OTS_SYNTHESIZE_MISSING_GVAR 1
CFG
cxx=${CXX:-c++}
flags="-O2 -std=c++14 -DHAVE_CONFIG_H -I$out -I$ots/include -I$woff2/include"
objs=()
for f in "$ots"/src/*.cc "$woff2"/src/{table_tags,variable_length,woff2_common,woff2_dec,woff2_out}.cc \
         "$ots"/util/ots-sanitize.cc; do
  case "$(basename "$f" .cc)" in
    feat|glat|gloc|sile|silf|sill) continue ;;  # Graphite: off, and needs lz4
  esac
  o="$out/$(basename "${f%.cc}").o"
  $cxx $flags -c "$f" -o "$o" &
  objs+=("$o")
  while [ "$(jobs -r | wc -l)" -ge "$(nproc)" ]; do wait -n; done
done
wait
$cxx "${objs[@]}" -lbrotlidec -lbrotlicommon -lz -o "$out/ots-sanitize"
echo "$out/ots-sanitize"
