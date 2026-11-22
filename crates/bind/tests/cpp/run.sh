#!/bin/sh
# Builds the C++ smoke test and the differential tests: the same programs
# compiled once against the real ada 4.0.0, simdjson 5.0.3 and simdutf 7.7.0
# (the versions Node.js 26 vendors) and once against vbind's headers, then compares what
# they print. It also checks that include/ada_url_pattern.h is what
# scripts/vendor-ada-url-pattern.py writes from that ada release.
#
#   tests/cpp/run.sh [json files...]
#
# URL inputs are WPT's urltestdata.json from ../url, and URLPattern inputs
# its urlpatterntestdata.json (tests/data). JSON inputs default to every
# *.json under $JSON_DIR (default: ../json).
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
fetch https://github.com/ada-url/ada/releases/download/v4.0.0/ada.h ada.h
fetch https://github.com/ada-url/ada/releases/download/v4.0.0/ada.cpp ada.cpp
fetch https://raw.githubusercontent.com/simdjson/simdjson/v5.0.3/singleheader/simdjson.h simdjson.h
fetch https://raw.githubusercontent.com/simdjson/simdjson/v5.0.3/singleheader/simdjson.cpp simdjson.cpp
fetch https://github.com/simdutf/simdutf/releases/download/v7.7.0/singleheader.zip simdutf.zip
[ -s "$ext/simdutf/simdutf.cpp" ] || unzip -o -q "$ext/simdutf.zip" -d "$ext/simdutf"

CXX=${CXX:-c++}
python3 scripts/vendor-ada-url-pattern.py "$ext" | cmp - include/ada_url_pattern.h
echo "ada_url_pattern.h: as generated from ada 4.0.0"
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
# (-O2: GCC 13 cannot compile ada 4's always-inline helpers at -O1.)
[ "$out/url_dump_ada" -nt "$ext/ada.cpp" ] || $CXX -std=c++20 -O2 -w -I"$ext" "$here/url_dump.cc" "$ext/ada.cpp" -o "$out/url_dump_ada"
$CXX -std=c++20 -O1 -Iinclude "$here/url_dump.cc" $lib -o "$out/url_dump_vbind"
"$out/url_dump_ada" < "$out/urls.txt" > "$out/url_ada.txt"
"$out/url_dump_vbind" < "$out/urls.txt" > "$out/url_vbind.txt"
echo "url: differences from ada 4.0.0 (see README for why):"
python3 "$here/compare.py" "$out/url_ada.txt" "$out/url_vbind.txt" 1 | grep -v "^    " | head -30

# URLPattern: ada's own code on both sides, over ada's URL parser and over
# vurl, with ada's std::regex provider. Every WPT case must give the same
# pattern strings, matches and groups.
python3 "$here/urlpattern_records.py" "$here/../data/urlpatterntestdata.json" > "$out/urlpatterns.txt"
def=-DADA_USE_UNSAFE_STD_REGEX_PROVIDER=1
[ "$out/urlpattern_dump_ada" -nt "$ext/ada.cpp" ] || $CXX -std=c++20 -O2 -w $def -I"$ext" "$here/urlpattern_dump.cc" "$ext/ada.cpp" -o "$out/urlpattern_dump_ada"
$CXX -std=c++20 -O1 -Wall -Wextra $def -Iinclude "$here/urlpattern_dump.cc" $lib -o "$out/urlpattern_dump_vbind"
"$out/urlpattern_dump_ada" < "$out/urlpatterns.txt" > "$out/urlpattern_ada.txt"
"$out/urlpattern_dump_vbind" < "$out/urlpatterns.txt" > "$out/urlpattern_vbind.txt"
cmp "$out/urlpattern_ada.txt" "$out/urlpattern_vbind.txt"
echo "urlpattern: $(grep -c '^end' "$out/urlpatterns.txt") WPT cases identical"

# Transcoding and base64: every simdutf call Node and V8 make, over a seeded
# corpus. Two differences are allowed, both on base64 that both sides
# reject. A safe decode into a buffer smaller than
# maximal_binary_length_from_base64 can fail in simdutf on valid input, since
# it decodes in chunks; Node falls back to its own decoder on any failure,
# which produces the same bytes. And for text with a "=" in the wrong place,
# simdutf's chunked path reports BASE64_INPUT_REMAINDER where its one-pass
# decoder, and vtext, report INVALID_BASE64_CHARACTER; the bytes written
# before the error are the same, and V8 throws a SyntaxError for both.
[ "$out/utf_dump_simdutf" -nt "$ext/simdutf/simdutf.cpp" ] || $CXX -std=c++20 -O2 -I"$ext/simdutf" "$here/utf_dump.cc" "$ext/simdutf/simdutf.cpp" -o "$out/utf_dump_simdutf"
$CXX -std=c++20 -O2 -Iinclude "$here/utf_dump.cc" $lib -o "$out/utf_dump_vbind"
"$out/utf_dump_simdutf" ${UTF_CASES:-50000} > "$out/utf_simdutf.txt"
"$out/utf_dump_vbind" ${UTF_CASES:-50000} > "$out/utf_vbind.txt"
python3 - "$out/utf_simdutf.txt" "$out/utf_vbind.txt" <<'PY'
import sys, collections
a = open(sys.argv[1]).read().splitlines(); b = open(sys.argv[2]).read().splitlines()
assert len(a) == len(b), "different numbers of calls"
small = collections.Counter(); padding = collections.Counter(); other = []
for x, y in zip(a, b):
    if x == y: continue
    fx, fy = x.split(), y.split()
    base64 = fx[1].startswith(('from_base64/', 'base64_to_binary_safe'))
    if fx[1].endswith('/small') and fx[2] == '0' and fy[2] == '2': small[fx[1]] += 1
    elif base64 and {fx[2], fy[2]} == {'7', '8'} and fx[4] == fy[4]: padding[fx[1]] += 1
    else: other.append((x, y))
same = len(a) - sum(small.values()) - sum(padding.values()) - len(other)
print(f"utf: {len(a)} calls, {same} identical, {sum(small.values())} small-buffer base64 decodes "
      f"simdutf fails and vtext gets right, {sum(padding.values())} invalid base64 texts where "
      f"the two name a different error")
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
