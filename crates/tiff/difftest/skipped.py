#!/usr/bin/env python3
"""skipped.py FILE: exits 0 if a field of the TIFF file's first IFD that the
decoder reads has a type other than BYTE, SHORT or LONG. TIFF 6.0 says to
skip such a field ("Readers should skip over fields containing an unexpected
field type", §2), and verilith-tiff does; libtiff converts the value when it
fits, and otherwise rejects the file (README, "Departures from libtiff").
Standard library only."""
import struct
import sys

READ = {256, 257, 258, 259, 262, 266, 273, 277, 278, 279, 284, 317, 320, 322, 323, 324, 325, 334, 338, 339}
f = open(sys.argv[1], "rb").read()
if len(f) < 8 or f[:2] not in (b"II", b"MM"):
    sys.exit(1)
e = "<" if f[:2] == b"II" else ">"
o = struct.unpack(e + "I", f[4:8])[0]
if o + 2 > len(f):
    sys.exit(1)
n = struct.unpack(e + "H", f[o:o + 2])[0]
for i in range(n):
    if o + 14 + 12 * i > len(f):
        sys.exit(1)
    t, ty = struct.unpack(e + "HH", f[o + 2 + 12 * i:o + 6 + 12 * i])
    if t in READ and ty not in (1, 3, 4):
        sys.exit(0)
sys.exit(1)
