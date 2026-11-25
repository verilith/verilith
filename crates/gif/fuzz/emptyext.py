#!/usr/bin/env python3
"""emptyext.py FILE: exits 0 if the GIF file has, before its trailer, an
extension with no data sub-blocks (its label then the block terminator),
which giflib misreads (README, "Departures from giflib")."""
import sys

b = open(sys.argv[1], "rb").read()
p = 13 + (3 * (2 << (b[10] & 7)) if len(b) > 10 and b[10] & 0x80 else 0)
while p < len(b):
    if b[p] == 0x21:
        if p + 2 < len(b) and b[p + 2] == 0:
            sys.exit(0)
        q = p + 2
    elif b[p] == 0x2C and p + 10 <= len(b):
        f = b[p + 9]
        q = p + 11 + (3 * (2 << (f & 7)) if f & 0x80 else 0)
    else:
        break
    while q < len(b) and b[q] != 0:
        q += 1 + b[q]
    p = q + 1
sys.exit(1)
