#!/usr/bin/env python3
"""Writes copies of fonts with one byte of GDEF, GSUB or GPOS changed.

    scripts/mutate-layout.py OUTDIR FONT...

Makes 150 copies per layout table of each font, half of them damaged in
the table's first 2000 bytes, where the headers and lists are. Run
scripts/difftest.sh on OUTDIR to compare vfont with OTS on them.
"""
import random
import struct
import sys

out, fonts = sys.argv[1], sys.argv[2:]
random.seed(7)
k = 0
for src in fonts:
    d = open(src, "rb").read()
    n = struct.unpack(">H", d[4:6])[0]
    for i in range(n):
        tag, _, off, ln = struct.unpack(">4sIII", d[12 + 16 * i : 28 + 16 * i])
        if tag not in (b"GDEF", b"GSUB", b"GPOS"):
            continue
        for j in range(150):
            span = min(ln, 2000) if j % 2 else ln
            b = bytearray(d)
            b[off + random.randrange(span)] ^= random.choice([1, 2, 4, 0x10, 0x80, 0xFF])
            open(f"{out}/{k:05d}.ttf", "wb").write(b)
            k += 1
print(k, "files")
