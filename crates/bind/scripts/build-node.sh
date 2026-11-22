#!/bin/sh
# Builds Node.js with vurl in place of ada, vjson in place of simdjson,
# vtext in place of simdutf, vhttp in place of llhttp and vdns as c-ares's
# DNS message parser and writer, then runs the given Node test selectors
# with Node's test runner.
#
# The first four use Node's own --shared-ada / --shared-simdjson /
# --shared-simdutf / --shared-http-parser options, with no patch to Node.
# c-ares stays Node's bundled copy (vdns replaces its message parsing, not
# its resolver), so for vdns the script applies vdns/cares/c-ares-use-vdns.patch
# to deps/cares and defines CARES_WITH_VDNS in cares.gyp. Set VBIND_DNS=0
# to leave c-ares alone, and VBIND_HTTP=0 to keep Node's llhttp (vhttp
# rejects some messages llhttp's lenient modes accept; see README.md).
#
#   scripts/build-node.sh [node version] [test selectors...]
#   scripts/build-node.sh v26.13.1 parallel/test-url* wpt/test-url.js
#
# The source and build live in $WORK (default target/node). Building Node
# takes two to three hours on four cores.
set -e
here=$(cd "$(dirname "$0")/.." && pwd)
version=${1:-v26.13.1}
[ $# -gt 0 ] && shift
work=${WORK:-$here/target/node}
src=$work/node-$version
lib=$work/lib
mkdir -p "$work" "$lib"

dns=${VBIND_DNS:-1}
http=${VBIND_HTTP:-1}
features=url,json,text
[ "$http" = 1 ] && features=$features,http
[ "$dns" = 1 ] && features=$features,dns
(cd "$here" && cargo build --profile release-abort -p verilith-bind --features "$features")
cp "${CARGO_TARGET_DIR:-$here/../../target}/release-abort/libverilith_bind.a" "$lib/libvbind.a"

if [ ! -d "$src" ]; then
  curl -sSfL "https://nodejs.org/dist/$version/node-$version.tar.xz" | tar xJ -C "$work"
fi
cd "$src"
if [ "$dns" = 1 ] && [ ! -f deps/cares/cares.gyp.orig ]; then
  cp deps/cares/cares.gyp deps/cares/cares.gyp.orig
  patch -s -p1 -d deps/cares < "$here/../dns/cares/c-ares-use-vdns.patch"
  python3 - deps/cares/cares.gyp <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
old = "'target_name': 'cares',\n"
assert old in s
s = s.replace(old, old + "      'defines': [ 'CARES_WITH_VDNS' ],\n", 1)
open(p, 'w').write(s)
PY
fi
configure() {
  python3 configure.py --ninja "$@" \
    --shared-ada --shared-ada-includes="$here/include" \
    --shared-ada-libpath="$lib" --shared-ada-libname=vbind \
    --shared-simdjson --shared-simdjson-includes="$here/include" \
    --shared-simdjson-libpath="$lib" --shared-simdjson-libname=vbind \
    --shared-simdutf --shared-simdutf-includes="$here/include" \
    --shared-simdutf-libpath="$lib" --shared-simdutf-libname=vbind
}
if [ ! -f out/Release/build.ninja ]; then
  if [ "$http" = 1 ]; then
    configure --shared-http-parser \
      --shared-http-parser-includes="$here/../http/compat/llhttp/include" \
      --shared-http-parser-libpath="$lib" --shared-http-parser-libname=vbind
  else
    configure
  fi
fi
ninja -C out/Release node
ln -sf out/Release/node node
./node -p 'process.versions.node'
if [ $# -gt 0 ]; then
  python3 tools/test.py -j "$(nproc)" -p dots "$@"
fi
