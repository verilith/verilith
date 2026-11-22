#!/bin/sh
# Builds the C++ smoke test and the differential tests: the same programs
# compiled once against the real ada 2.9.2, simdjson 4.5.0 and simdutf 6.4.2
# (the versions Node.js 22 vendors) and once against vbind's headers, then compares what
# they print.
#
#   tests/cpp/run.sh [json files...]
#
# URL inputs are WPT's urltestdata.json from ../url. JSON inputs default to
# every *.json under $JSON_DIR (default: ../json).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$here/../..
out=${OUT:-$root/target/cpp}
ext=$out/ext
mkdir -p "$out" "$ext"
cd "$root"
cargo build --profile release-abort -q
lib="${CARGO_TARGET_DIR:-$root/../../target}/release-abort/libverilith_bind.a -lpthread -ldl -lm"

fetch() { [ -s "$ext/$2" ] || curl -sSfL -o "$ext/$2" "$1"; }
fetch https://github.com/ada-url/ada/releases/download/v2.9.2/ada.h ada.h
fetch https://github.com/ada-url/ada/releases/download/v2.9.2/ada.cpp ada.cpp
fetch https://raw.githubusercontent.com/simdjson/simdjson/v4.5.0/singleheader/simdjson.h simdjson.h
fetch https://raw.githubusercontent.com/simdjson/simdjson/v4.5.0/singleheader/simdjson.cpp simdjson.cpp
fetch https://github.com/simdutf/simdutf/releases/download/v6.4.2/singleheader.zip simdutf.zip
[ -s "$ext/simdutf/simdutf.cpp" ] || unzip -o -q "$ext/simdutf.zip" -d "$ext/simdutf"

CXX=${CXX:-c++}
$CXX -std=c++20 -O1 -Wall -Wextra -Iinclude "$here/smoke.cc" $lib -o "$out/smoke"
"$out/smoke" > /dev/null && echo "smoke: ok"

# URLs.
python3 - "$root/../url/tests/data/urltestdata.json" > "$out/urls.txt" <<'PY'
import json, sys
def esc(s): return s.replace('\\','\\\\').replace('\n','\\n').replace('\t','\\t').replace('\r','\\r')
for t in json.load(open(sys.argv[1], encoding='utf-8')):
    if isinstance(t, str): continue
    print(esc(t['input']) + ('\t' + esc(t['base']) if t.get('base') else ''))
PY
[ "$out/url_dump_ada" -nt "$ext/ada.cpp" ] || $CXX -std=c++20 -O1 -I"$ext" "$here/url_dump.cc" "$ext/ada.cpp" -o "$out/url_dump_ada"
$CXX -std=c++20 -O1 -Iinclude "$here/url_dump.cc" $lib -o "$out/url_dump_vbind"
"$out/url_dump_ada" < "$out/urls.txt" > "$out/url_ada.txt"
"$out/url_dump_vbind" < "$out/urls.txt" > "$out/url_vbind.txt"
echo "url: differences from ada 2.9.2 (see README for why):"
python3 "$here/compare.py" "$out/url_ada.txt" "$out/url_vbind.txt" 1 | grep -v "^    " | head -30

# Transcoding and base64: every simdutf call Node makes, over a seeded
# corpus. The one allowed difference is a safe base64 decode into a buffer
# smaller than maximal_binary_length_from_base64, where simdutf's chunked
# path fails on some valid inputs (whitespace after the padding) and vtext
# decodes them; Node falls back to its own decoder on any failure, which
# produces the same bytes.
[ "$out/utf_dump_simdutf" -nt "$ext/simdutf/simdutf.cpp" ] || $CXX -std=c++20 -O2 -I"$ext/simdutf" "$here/utf_dump.cc" "$ext/simdutf/simdutf.cpp" -o "$out/utf_dump_simdutf"
$CXX -std=c++20 -O2 -Iinclude "$here/utf_dump.cc" $lib -o "$out/utf_dump_vbind"
"$out/utf_dump_simdutf" ${UTF_CASES:-50000} > "$out/utf_simdutf.txt"
"$out/utf_dump_vbind" ${UTF_CASES:-50000} > "$out/utf_vbind.txt"
python3 - "$out/utf_simdutf.txt" "$out/utf_vbind.txt" <<'PY'
import sys, collections
a = open(sys.argv[1]).read().splitlines(); b = open(sys.argv[2]).read().splitlines()
assert len(a) == len(b), "different numbers of calls"
allowed = collections.Counter(); other = []
for x, y in zip(a, b):
    if x == y: continue
    fx, fy = x.split(), y.split()
    if fx[1].endswith('/small') and fx[2] == '0' and fy[2] == '2': allowed[fx[1]] += 1
    else: other.append((x, y))
print(f"utf: {len(a)} calls, {len(a) - sum(allowed.values()) - len(other)} identical, "
      f"{sum(allowed.values())} small-buffer base64 decodes simdutf fails and vtext gets right")
for x, y in other[:10]: print("  simdutf:", x, "\n  vtext:  ", y)
sys.exit(1 if other else 0)
PY

# JSON.
if [ $# -eq 0 ]; then
  find -L "${JSON_DIR:-$root/../json}" -name '*.json' -size -4M > "$out/json_files.txt"
else
  printf '%s\n' "$@" > "$out/json_files.txt"
fi
[ "$out/json_dump_sj" -nt "$ext/simdjson.cpp" ] || $CXX -std=c++20 -O1 -I"$ext" "$here/json_dump.cc" "$ext/simdjson.cpp" -o "$out/json_dump_sj"
$CXX -std=c++20 -O1 -Iinclude "$here/json_dump.cc" $lib -o "$out/json_dump_vbind"
xargs "$out/json_dump_sj" < "$out/json_files.txt" > "$out/json_sj.txt"
xargs "$out/json_dump_vbind" < "$out/json_files.txt" > "$out/json_vbind.txt"
python3 - "$out/json_sj.txt" "$out/json_vbind.txt" <<'PY'
import sys, collections
def recs(p):
    r = collections.OrderedDict(); cur = None
    for l in open(p, encoding='utf-8', errors='replace'):
        l = l.rstrip('\n')
        if l.startswith('# '): cur = l; r[cur] = []
        elif cur: r[cur].append(l)
    return r
a, b = recs(sys.argv[1]), recs(sys.argv[2])
diff = [k for k in a if a[k] != b.get(k)]
eager = [k for k in diff if b.get(k) == ['iterate-error']]
print(f"json: {len(a)} reads, {len(a) - len(diff)} identical, {len(eager)} where vjson "
      f"rejects invalid JSON that simdjson reads partway")
other = [k for k in diff if k not in eager]
for k in other[:10]:
    print("  differs:", k)
sys.exit(1 if other else 0)
PY
