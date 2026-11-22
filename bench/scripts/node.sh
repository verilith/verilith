#!/usr/bin/env bash
# Node.js, as users would see it: Node's own benchmark/compare.js on two
# builds of the same Node source, same compiler and flags:
#
#   official  Node as shipped (bundled llhttp, ada, simdjson, zlib), except
#             c-ares: both builds use c-ares at the commit vdns's patch is
#             made for, so the c-ares version is not a difference.
#   hardened  the same, with our drop-ins swapped in (NODE_SWAPS):
#               llhttp   -> vhttp      (vhttp/compat/llhttp/node.sh)
#               ada      -> vurl       (vbind, --shared-ada)
#               simdjson -> vjson      (vbind, --shared-simdjson)
#               cares    -> c-ares + vdns (--shared-cares)
#               zlib     -> vzlib      (--shared-zlib)
#
# Then runs the benchmarks in NODE_BENCHES (file:--set options) with
# NODE_RUNS runs each, and summarizes them with harness/node_report.py.
#   scripts/node.sh RESULTS_DIR
# Each build takes 15-30 minutes on an M-series Mac (about an hour on four
# cores); both are reused on later runs.
. "$(dirname "$0")/lib.sh"
OUT=${1:?usage: scripts/node.sh RESULTS_DIR}
mkdir -p "$OUT/node"
OUT=$(cd "$OUT/node" && pwd)
V=$NODE_VERSION
NW=$WORK/node
: "${NODE_SWAPS:=llhttp ada simdjson cares zlib}"
: "${NODE_RUNS:=30}"
: "${NODE_BENCHES:=url/whatwg-url-parse.js:withBase=false url/whatwg-url-canParse.js url/whatwg-url-validity.js url/whatwg-url-get-prop.js url/whatwg-url-idna.js http/bench-parser.js zlib/inflate.js zlib/deflate.js}"
mkdir -p "$NW"

tarball=$NW/node-$V.tar.xz
if [ ! -f "$tarball" ]; then
  say "download Node.js $V"
  curl -sSfL -o "$tarball.part" "https://nodejs.org/dist/$V/node-$V.tar.xz"
  curl -sSfL "https://nodejs.org/dist/$V/SHASUMS256.txt" | grep " node-$V.tar.xz\$" | sed "s| node-$V.tar.xz| $tarball.part|" | $SHA256 -c - >/dev/null \
    || die "node-$V.tar.xz does not match nodejs.org's SHASUMS256.txt"
  mv "$tarball.part" "$tarball"
fi

# c-ares, stock and with vdns, as include + lib directories for --shared-cares.
[ -f "$BUILD/c-ares/lib/libcares.a" ] && [ -f "$BUILD/c-ares-vdns/lib/libcares.a" ] || "$ROOT/scripts/build.sh" dns
for k in c-ares c-ares-vdns; do
  rm -rf "$NW/$k"; mkdir -p "$NW/$k/include" "$NW/$k/lib"
  cp "$(orig c-ares)"/include/*.h "$BUILD/$k/ares_build.h" "$NW/$k/include/"
  cp "$BUILD/$k/lib/libcares.a" "$NW/$k/lib/"
done
lib=$("$ROOT/scripts/build.sh" --print-lib vdns cares,ares-abi); [ -f "$lib" ] || die "could not build vdns (cares,ares-abi)"
cp "$lib" "$NW/c-ares-vdns/lib/libvdns.a"   # the name --shared-cares-libname links

has() { case " $NODE_SWAPS " in *" $1 "*) return 0 ;; esac; return 1; }
ninja=""
command -v ninja >/dev/null && ninja="--ninja"

# build_node NAME CONFIGURE_ARGS...: unpacks a fresh tree once, configures and builds.
build_node() {
  local name=$1; shift
  local dir=$NW/$name
  local stamp="$V $*"
  if [ -x "$dir/out/Release/node" ] && [ "$(cat "$dir/.vbench-config" 2>/dev/null)" = "$stamp" ]; then
    say "Node $name: already built"
    return
  fi
  say "Node $name: unpack"
  rm -rf "$dir"; mkdir -p "$dir"
  tar xJf "$tarball" -C "$dir" --strip-components 1
  if [ "$name" = hardened ] && has llhttp; then
    "$(ours vhttp)/compat/llhttp/node.sh" "$dir"
  fi
  say "Node $name: configure ${*}"
  (cd "$dir" && CFLAGS="$CPUFLAG" CXXFLAGS="$CPUFLAG" python3 configure.py $ninja "$@" > "$NW/$name.configure.log")
  say "Node $name: build (log: $NW/$name.build.log)"
  if [ -n "$ninja" ]; then
    (cd "$dir" && ninja -C out/Release -j "$NPROC" node > "$NW/$name.build.log" 2>&1) || { tail -30 "$NW/$name.build.log"; die "Node $name failed to build"; }
  else
    (cd "$dir" && make -j "$NPROC" > "$NW/$name.build.log" 2>&1) || { tail -30 "$NW/$name.build.log"; die "Node $name failed to build"; }
  fi
  echo "$stamp" > "$dir/.vbench-config"
}

cares_args() {
  local k=$1 libs=cares
  [ "$k" = c-ares-vdns ] && libs=cares,vdns,cares
  echo "--shared-cares --shared-cares-includes=$NW/$k/include --shared-cares-libpath=$NW/$k/lib --shared-cares-libname=$libs"
}

build_node official $(cares_args c-ares)

hard=""
if has cares; then hard="$hard $(cares_args c-ares-vdns)"; else hard="$hard $(cares_args c-ares)"; fi
if has ada || has simdjson; then
  vb=$(ours vbind)
  if [ -f "$vb/Cargo.toml" ]; then
    say "build vbind (vurl + vjson behind ada's and simdjson's C++ API)"
    cargo build -q --profile "$(ours_profile vbind)" -p verilith-bind --manifest-path "$vb/Cargo.toml" --target-dir "$WORK/target/vbind"
    mkdir -p "$NW/vbind/lib"; cp "$WORK/target/vbind/$(ours_profile vbind)/libverilith_bind.a" "$NW/vbind/lib/libvbind.a"
    if has ada; then hard="$hard --shared-ada --shared-ada-includes=$vb/include --shared-ada-libpath=$NW/vbind/lib --shared-ada-libname=vbind"; fi
    if has simdjson; then hard="$hard --shared-simdjson --shared-simdjson-includes=$vb/include --shared-simdjson-libpath=$NW/vbind/lib --shared-simdjson-libname=vbind"; fi
  else
    warn "no vbind checkout at $vb: the hardened Node keeps ada and simdjson"
    NODE_SWAPS=$(echo " $NODE_SWAPS " | sed 's/ ada / /; s/ simdjson / /')
  fi
fi
if has zlib; then
  lib=$("$ROOT/scripts/build.sh" --print-lib vzlib zlib-abi); [ -f "$lib" ] || die "could not build vzlib (zlib-abi)"
  mkdir -p "$NW/vzlib/lib" "$NW/vzlib/include"
  cp "$lib" "$NW/vzlib/lib/libvzlib.a"
  cp "$(orig zlib)/zlib.h" "$(orig zlib)/zconf.h" "$NW/vzlib/include/"
  hard="$hard --shared-zlib --shared-zlib-includes=$NW/vzlib/include --shared-zlib-libpath=$NW/vzlib/lib --shared-zlib-libname=vzlib"
fi
build_node hardened $hard

OFF=$NW/official/out/Release/node
HRD=$NW/hardened/out/Release/node

say "check that the hardened build has our code in it"
{
  echo "swaps: $NODE_SWAPS"
  nm "$HRD" > "$OUT/hardened.nm" 2>/dev/null || true
  # Count rather than grep -q: with pipefail, grep -q closing the pipe early makes the check fail.
  check() { n=$(grep -c "$2" "$OUT/hardened.nm" || true); if [ "${n:-0}" -gt 0 ]; then echo "$1: yes ($n $2 symbols)"; else echo "$1: NO ($2 missing)"; fi; }
  for pair in llhttp:vhttp ada:vurl simdjson:vjson cares:vdns zlib:vzlib; do
    if has "${pair%%:*}"; then check "${pair#*:} in place of ${pair%%:*}" "${pair#*:}"; fi
  done
  for b in "$OFF" "$HRD"; do
    "$b" -e '
      const u = new URL("https://user@例え.テスト:8080/a/../b?q=1#f"); if (u.href !== "https://user@xn--r8jz45g.xn--zckzah:8080/b?q=1#f") throw new Error(u.href);
      const z = require("zlib"); const d = Buffer.from("hello ".repeat(1000)); if (!z.inflateSync(z.deflateSync(d)).equals(d)) throw new Error("zlib");
      const { HTTPParser } = require("_http_common"); if (typeof HTTPParser !== "function") throw new Error("http");
      console.log(process.execPath.includes("hardened") ? "hardened smoke test: ok" : "official smoke test: ok");'
  done
} 2>&1 | tee "$OUT/build-check.txt"
rm -f "$OUT/hardened.nm"
if grep -q ": NO " "$OUT/build-check.txt"; then warn "some swaps are not in the hardened binary; see $OUT/build-check.txt"; fi

say "Node benchmark/compare.js, $NODE_RUNS runs per configuration"
csv=$OUT/compare.csv
: > "$csv"
cd "$NW/official"
bench_lock node compare.js
for spec in $NODE_BENCHES; do
  file=${spec%%:*}
  sets=""
  if [ "$spec" != "$file" ]; then for s in $(echo "${spec#*:}" | tr ',' ' '); do sets="$sets --set $s"; done; fi
  cat=${file%%/*}; base=$(basename "$file" .js)
  say "  $file $sets"
  "$OFF" benchmark/compare.js --old "$OFF" --new "$HRD" --runs "$NODE_RUNS" --filter "$base.js" $sets "$cat" > "$OUT/part.csv"
  if [ -s "$csv" ]; then tail -n +2 "$OUT/part.csv" >> "$csv"; else cat "$OUT/part.csv" > "$csv"; fi
done
rm -f "$OUT/part.csv"
bench_unlock
python3 "$ROOT/harness/node_report.py" "$csv" "$OUT"
