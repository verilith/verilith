#!/usr/bin/env bash
# Builds a Node.js checkout with the verified parsers in place of three
# unverified ones:
#
#   - nghttp2's HPACK header decoder (HTTP/2, node:http2)  -> vhpack
#   - llhttp's generated parser (HTTP/1.1, node:http)       -> vhttp
#     (parsers with lenient flags, i.e. --insecure-http-parser, stay on it)
#   - undici's llhttp.wasm (fetch())                         -> vhttp as wasm
#
#   compat/node/node.sh NODE_DIR [VHTTP_DIR]
#
# NODE_DIR is a Node.js checkout (tested with v26.13.1: nghttp2 1.70.0,
# llhttp 9.4.4, undici 8.12.4; and v24.22.1). VHTTP_DIR is a vhttp checkout, needed only
# for fetch() (its compat/undici/build.sh makes the wasm; that needs clang,
# wasm-ld and the wasm32-unknown-unknown Rust target); without it, fetch()
# keeps undici's llhttp.wasm. Then build Node as usual:
#   ./configure --ninja && ninja -C out/Release node
#
# The Rust side is one static library (compat/node: vhpack and vhttp
# together), built with fat LTO, which makes it one object carrying its own
# copy of the Rust standard library. Two such libraries cannot be linked
# into one binary. Node 26 links a Rust library of its own (deps/crates), so
# for a checkout that has one, this library is built without LTO: then each
# std symbol is an archive member the linker takes once, from whichever
# library comes first (both must be built by the same rustc). Originals are
# kept as *.orig.
set -euo pipefail
node=$(cd "$1" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)

if [ -d "$node/deps/crates" ]; then
    export CARGO_PROFILE_RELEASE_LTO=off CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16
fi
cargo build --release -q --manifest-path "$here/Cargo.toml"
lib="$here/target/release/libvnode.a"

# nghttp2: the inflater on vhpack.
python3 "$root/compat/nghttp2/patch.py" "$node/deps/nghttp2/lib"
gyp="$node/deps/nghttp2/nghttp2.gyp"
[ -f "$gyp.orig" ] || cp "$gyp" "$gyp.orig"
python3 - "$gyp" "$lib" <<'PY'
import sys
p, lib = sys.argv[1], sys.argv[2]
s = open(p + ".orig").read()
a = "        'NGHTTP2_STATICLIB',\n        'HAVE_CONFIG_H',\n"
assert a in s, "unexpected nghttp2.gyp"
s = s.replace(a, a + "        'NGHTTP2_VHPACK',\n", 1)
b = "      'direct_dependent_settings': {\n        'defines': [ 'NGHTTP2_STATICLIB' ],"
assert b in s, "unexpected nghttp2.gyp"
s = s.replace(b, "      'link_settings': { 'libraries': [ '%s' ] },\n" % lib + b, 1)
open(p, "w").write(s)
PY
echo "patched $gyp"

# llhttp: api.c and http.c on vhttp's parser (as vhttp's compat/llhttp/node.sh).
gyp="$node/deps/llhttp/llhttp.gyp"
[ -f "$gyp.orig" ] || cp "$gyp" "$gyp.orig"
cat > "$gyp" <<GYP
{
  'variables': {
    'llhttp_sources': [
      'src/api.c',
      'src/http.c',
      'src/vhttp_lenient.c',
    ]
  },
  'targets': [
    {
      'target_name': 'llhttp',
      'type': 'static_library',
      'include_dirs': [ '.', 'include' ],
      'direct_dependent_settings': {
        'include_dirs': [ 'include' ],
      },
      'link_settings': {
        'libraries': [ '$lib' ],
      },
      'sources': [
        '<@(llhttp_sources)',
      ],
    },
  ]
}
GYP
# llhttp.c stays, under other names, for parsers with lenient flags set
# (--insecure-http-parser): vhttp's llhttp-lenient feature hands those to
# it. This is vhttp's compat/llhttp/src/lenient.c.
cat > "$node/deps/llhttp/src/vhttp_lenient.c" <<'C'
#define llhttp__internal_init vhttp_lenient_init
#define llhttp__internal_execute vhttp_lenient_execute
#include "llhttp.c"

void vhttp_lenient_start(llhttp__internal_t* state) {
  state->_current = (void*) (intptr_t) s_n_llhttp__internal__n_start;
}
C
echo "patched $gyp"

# undici (fetch()): the two wasm modules embedded in deps/undici/undici.js.
if [ $# -ge 2 ]; then
    vhttp=$(cd "$2" && pwd)
    "$vhttp/compat/undici/build.sh"
    js="$node/deps/undici/undici.js"
    [ -f "$js.orig" ] || cp "$js" "$js.orig"
    python3 - "$js" "$vhttp/target/undici/llhttp.wasm" <<'PY'
import base64, re, sys
p, wasm = sys.argv[1], sys.argv[2]
s = open(p + ".orig").read()
b64 = base64.b64encode(open(wasm, "rb").read()).decode()
s, n = re.subn(r'var wasmBase64 = "[A-Za-z0-9+/=]+";', 'var wasmBase64 = "%s";' % b64, s)
assert n == 2, "expected undici's two llhttp wasm modules, found %d" % n
open(p, "w").write(s)
PY
    echo "patched $js (both llhttp wasm modules)"
fi
