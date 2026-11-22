#!/usr/bin/env bash
# Builds Node.js with vhttp in place of llhttp's generated parser.
#
#   compat/llhttp/node.sh NODE_DIR
#
# NODE_DIR is a Node.js checkout (tested with v24.22.1, which bundles
# llhttp 9.4.3). Node keeps llhttp's api.c and http.c, and libverilith_http.a
# (built with the llhttp-lenient feature) takes llhttp.c's place; llhttp.c
# is kept under other names (src/lenient.c) only for parsers with lenient
# flags set. Then build as usual: ./configure --ninja && ninja -C out/Release node
set -euo pipefail
node=$(cd "$1" && pwd)
root=$(cd "$(dirname "$0")/../.." && pwd)
cargo build --profile release-abort --features llhttp-lenient --manifest-path "$root/Cargo.toml" -q
lib="${CARGO_TARGET_DIR:-$root/../../target}/release-abort/libverilith_http.a"
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
# llhttp.c stays, renamed, for parsers with lenient flags (--insecure-http-parser).
cp "$root/compat/llhttp/src/lenient.c" "$node/deps/llhttp/src/vhttp_lenient.c"
echo "patched $gyp to link $lib (original kept as llhttp.gyp.orig)"
