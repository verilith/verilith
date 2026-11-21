#!/usr/bin/env bash
# Builds llhttp.wasm for undici (the HTTP/1.1 client behind Node's fetch())
# with vhttp's verified parser in place of llhttp's generated one.
#
#   compat/undici/build.sh [UNDICI_DIR]
#
# Output: target/undici/llhttp.wasm, with exactly the imports and exports
# of undici's own build (build/llhttp.js in undici). llhttp's api.c and
# http.c (compat/llhttp/src) supply the C API; vhttp supplies
# llhttp__internal_init/execute and malloc/free. Needs clang and wasm-ld
# with a wasm32 backend, and `rustup target add wasm32-unknown-unknown`;
# no wasi-sdk.
#
# With UNDICI_DIR (an undici checkout, or Node's deps/undici/src), it then
# writes lib/llhttp/llhttp-wasm.js and llhttp_simd-wasm.js there, in the
# format undici's build writes. Node's bundled deps/undici/undici.js embeds
# the same base64; see node.sh for patching a Node checkout.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=$root/target/undici
mkdir -p "$out"

cargo build -q --release --target wasm32-unknown-unknown --manifest-path "$here/Cargo.toml"
CFLAGS="--target=wasm32-unknown-unknown -O3 -ffreestanding -nostdlib -fvisibility=hidden \
  -isystem $here/libc -I $root/compat/llhttp/include"
for f in api http; do
    ${CC:-clang} $CFLAGS -c "$root/compat/llhttp/src/$f.c" -o "$out/$f.o"
done

# undici's JavaScript imports these and calls these; the list is undici's
# own llhttp.wasm's exports (llhttp 9.3), plus memory and the table.
exports=(llhttp_init llhttp_should_keep_alive llhttp_alloc malloc llhttp_free free
  llhttp_get_type llhttp_get_http_major llhttp_get_http_minor llhttp_get_method
  llhttp_get_status_code llhttp_get_upgrade llhttp_reset llhttp_execute
  llhttp_settings_init llhttp_finish llhttp_pause llhttp_resume
  llhttp_resume_after_upgrade llhttp_get_errno llhttp_get_error_reason
  llhttp_set_error_reason llhttp_get_error_pos llhttp_errno_name llhttp_method_name
  llhttp_status_name llhttp_set_lenient_headers llhttp_set_lenient_chunked_length
  llhttp_set_lenient_keep_alive llhttp_set_lenient_transfer_encoding
  llhttp_set_lenient_version llhttp_set_lenient_data_after_close
  llhttp_set_lenient_optional_lf_after_cr llhttp_set_lenient_optional_crlf_after_chunk
  llhttp_set_lenient_optional_cr_before_lf llhttp_set_lenient_spaces_after_chunk_size
  llhttp_message_needs_eof)
imports=(wasm_on_message_begin wasm_on_url wasm_on_status wasm_on_header_field
  wasm_on_header_value wasm_on_headers_complete wasm_on_body wasm_on_message_complete)
printf '%s\n' "${imports[@]}" > "$out/imports.txt"
${WASM_LD:-wasm-ld} --no-entry --export-table --strip-all --gc-sections -O3 \
    "${exports[@]/#/--export=}" --allow-undefined-file="$out/imports.txt" \
    "$out/api.o" "$out/http.o" \
    "$here/target/wasm32-unknown-unknown/release/libvhttp_undici.a" \
    -o "$out/llhttp.wasm"
echo "built $out/llhttp.wasm ($(wc -c < "$out/llhttp.wasm") bytes)"

if [ $# -ge 1 ]; then
    dest=$1/lib/llhttp
    [ -d "$dest" ] || { echo "no $dest" >&2; exit 1; }
    for name in llhttp-wasm.js llhttp_simd-wasm.js; do
        [ -f "$dest/$name.orig" ] || cp "$dest/$name" "$dest/$name.orig"
        # vhttp has no wasm SIMD path, so both modules are the same.
        node -e '
const fs = require("fs");
const b64 = fs.readFileSync(process.argv[1]).toString("base64");
fs.writeFileSync(process.argv[2], `'"'"'use strict'"'"'

const { Buffer } = require('"'"'node:buffer'"'"')

const wasmBase64 = '"'"'${b64}'"'"'

let wasmBuffer

Object.defineProperty(module, '"'"'exports'"'"', {
  get: () => {
    return wasmBuffer
      ? wasmBuffer
      : (wasmBuffer = Buffer.from(wasmBase64, '"'"'base64'"'"'))
  }
})
`)' "$out/llhttp.wasm" "$dest/$name"
    done
    cp "$out/llhttp.wasm" "$dest/llhttp.wasm"
    cp "$out/llhttp.wasm" "$dest/llhttp_simd.wasm"
    echo "installed into $dest (originals kept as *.orig)"
fi
