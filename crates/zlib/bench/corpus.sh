#!/bin/sh
# Builds the benchmark corpus in DIR from files found on a stock Ubuntu
# 24.04 machine with Go, Node and TypeScript installed. Any files will do;
# these are the ones the README's numbers use.
set -e
D=${1:-corpus}
mkdir -p "$D"
head -c 8000000 /usr/lib/x86_64-linux-gnu/libLLVM-17.so.1 > "$D/bin"
cp /usr/local/go1.25.1/src/internal/trace/traceviewer/static/trace_viewer_full.html "$D/html"
cp /opt/node-tools/node_modules/typescript/lib/typescript.js "$D/js"
cat /usr/share/vim/vim91/doc/version*.txt > "$D/text"
cp /usr/share/xml/iso-codes/iso_639-3.xml "$D/xml"
head -c 4096 "$D/text" > "$D/small"
ls -l "$D"
