#!/usr/bin/env bash
# Fetches the original libraries and the input data, all pinned in pins.sh,
# into work/. Our libraries are the crates of this checkout. Safe to rerun.
. "$(dirname "$0")/lib.sh"
mkdir -p "$SRC" "$DATA" "$WORK/datasets"

echo "$ORIGINALS" | while read -r name url ref; do
  [ -n "$name" ] || continue
  say "fetch $name @ $ref"
  git_get "$SRC/$name" "$url" "$ref"
  # mbedTLS 4 keeps its crypto in the TF-PSA-Crypto submodule, which has submodules of its own.
  if [ "$name" = mbedtls ]; then git -C "$SRC/$name" submodule update -q --init --recursive --depth 1; fi
  # Verdict needs only its Verus fork (for vstd), not libcrux.
  if [ "$name" = verdict ]; then git -C "$SRC/$name" submodule update -q --init --depth 1 deps/verus; fi
done

echo "$DATASETS" | while read -r name url ref; do
  [ -n "$name" ] || continue
  say "fetch data set $name @ $ref"
  git_get "$WORK/datasets/$name" "$url" "$ref"
done

say "prepare inputs"
D=$WORK/datasets
# zlib: Silesia files, plus 4 KiB and 64 KiB prefixes of dickens (the sizes
# streaming callers such as Node's zlib often see).
mkdir -p "$DATA/zlib"
for f in $SILESIA_FILES; do
  [ -f "$DATA/zlib/$f" ] || unzip -o -q "$D/silesia/$f.zip" -d "$DATA/zlib"
done
head -c 4096 "$DATA/zlib/dickens" > "$DATA/zlib/dickens-4k"
head -c 65536 "$DATA/zlib/dickens" > "$DATA/zlib/dickens-64k"

# brotli: the same files as zlib.
mkdir -p "$DATA/brotli"
for f in $SILESIA_FILES dickens-4k dickens-64k; do cp "$DATA/zlib/$f" "$DATA/brotli/$f"; done

# lz4 and snappy: the same files again.
for d in lz4 snappy; do
  mkdir -p "$DATA/$d"
  for f in $SILESIA_FILES dickens-4k dickens-64k; do cp "$DATA/zlib/$f" "$DATA/$d/$f"; done
done

# sha2: short messages (the first 16, 64, 256 and 1024 bytes of dickens),
# then 4 KiB, 64 KiB and all of it.
mkdir -p "$DATA/sha2"
for n in 16 64 256 1024; do head -c $n "$DATA/zlib/dickens" > "$DATA/sha2/dickens-$n"; done
for f in dickens dickens-4k dickens-64k; do cp "$DATA/zlib/$f" "$DATA/sha2/$f"; done

# XML: six of the XML files in Silesia's xml (a tar of 20): plays, tagged
# corpora, statistics, a W3C page. Then the seven files of roxmltree's
# benchmarks: SVG drawings, a property list, a large data file, and files
# dense with attributes, with entity and character references, and with
# CDATA.
mkdir -p "$DATA/xml"
if [ ! -f "$DATA/xml/play1.xml" ]; then
  tar -xf "$DATA/zlib/xml" -C "$DATA/xml" play1.xml stats1.xml tal1.xml tpc.xml w3c5.xml elts.xml
fi
for f in attributes.xml cdata.xml gigantic.svg huge.xml large.plist medium.svg text.xml; do
  cp "$D/roxmltree/benches/$f" "$DATA/xml/"
done

# JSON: simdjson's standard examples (simdjson-data).
mkdir -p "$DATA/json"
for f in twitter citm_catalog canada github_events gsoc-2018 mesh; do
  cp "$D/simdjson-data/jsonexamples/$f.json" "$DATA/json/"
done

# URLs: ada's URL dataset (about 100k real URLs), plus its first 1000.
mkdir -p "$DATA/url"
cp "$D/url-dataset/out.txt" "$DATA/url/url-dataset.txt"
head -n 1000 "$D/url-dataset/out.txt" > "$DATA/url/url-dataset-1k.txt"

# Regex: English text (the start of dickens) and URLs.
mkdir -p "$DATA/regex"
cp "$DATA/zlib/dickens-64k" "$DATA/regex/dickens-64k"
head -c 1048576 "$DATA/zlib/dickens" > "$DATA/regex/dickens-1m"
cp "$DATA/url/url-dataset-1k.txt" "$DATA/regex/url-dataset-1k.txt"

# HTTP and DNS messages live in this repo (data/), made by data/*/make.py.
rm -rf "$DATA/http" "$DATA/dns"
cp -R "$ROOT/data/http" "$DATA/http"
cp -R "$ROOT/data/dns" "$DATA/dns"
rm -f "$DATA/http/make.py" "$DATA/dns/make.py"

# X.509: vx509's three benchmark certificates and every root in certifi's
# Mozilla bundle, as DER.
mkdir -p "$DATA/x509/roots"
cp "$(ours vx509)"/bench/data/*.der "$DATA/x509/"
python3 "$ROOT/data/x509/pem2der.py" "$D/certifi/certifi/cacert.pem" "$DATA/x509/roots"

# PNG: the 24 Kodak photos (768x512 RGB).
mkdir -p "$DATA/png"
for f in "$D"/kodak/PhotoCD_PCD0992/*.png; do cp "$f" "$DATA/png/kodim$(basename "$f")"; done

# Fonts: Source Serif 4 Regular as OpenType/CFF and TrueType, each also as
# WOFF and WOFF2 (Adobe's release files).
mkdir -p "$DATA/font"
ss=$D/source-serif
cp "$ss/OTF/SourceSerif4-Regular.otf" "$ss/TTF/SourceSerif4-Regular.ttf" \
   "$ss/WOFF/OTF/SourceSerif4-Regular.otf.woff" "$ss/WOFF/TTF/SourceSerif4-Regular.ttf.woff" \
   "$ss/WOFF2/OTF/SourceSerif4-Regular.otf.woff2" "$ss/WOFF2/TTF/SourceSerif4-Regular.ttf.woff2" "$DATA/font/"

say "check SHA-256 of every input"
if ! out=$(cd "$DATA" && $SHA256 -c "$ROOT/data/SHA256SUMS" 2>&1); then
  echo "$out" | grep -v ': OK$' >&2
  die "an input file does not match data/SHA256SUMS"
fi
say "inputs ready in $DATA"
