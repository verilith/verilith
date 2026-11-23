#!/usr/bin/env python3
"""overlong.py FILE: exits 0 if a Deflate strip or tile of the TIFF file's
first image decompresses to more bytes than the strip or tile needs. libtiff
(through libdeflate) then leaves the last bytes of that strip or tile
unwritten (README, "Departures from libtiff"). Standard library only."""
import struct
import sys
import zlib

f = open(sys.argv[1], "rb").read()
e = "<" if f[:2] == b"II" else ">"
o = struct.unpack(e + "I", f[4:8])[0]
n = struct.unpack(e + "H", f[o:o + 2])[0]
ent = {}
for i in range(n):
    t, ty, c, v = struct.unpack(e + "HHII", f[o + 2 + 12 * i:o + 14 + 12 * i])
    if t in ent or ty not in (1, 3, 4):
        continue
    ts = {1: 1, 3: 2, 4: 4}[ty]
    pos = o + 10 + 12 * i if c * ts <= 4 else v
    if c > 1 << 20 or pos + c * ts > len(f):
        continue
    fmt = {1: "B", 3: "H", 4: "I"}[ty]
    ent[t] = [struct.unpack(e + fmt, f[pos + ts * k:pos + ts * (k + 1)])[0] for k in range(c)]
get = lambda t, d: ent.get(t, [d])[0]
w, h, bps, spp = get(256, 0), get(257, 0), get(258, 1), get(277, 1)
planar, rps = get(284, 1), get(278, 0xFFFFFFFF)
sc = 1 if planar == 2 else spp
tiled = 322 in ent
if tiled:
    tw, th = get(322, 1), get(323, 1)
    sizes = None
    need = lambda k: th * (tw * sc * bps // 8)
    offs, cnts = ent.get(324, []), ent.get(325, [])
else:
    rb = (w * sc * bps + 7) // 8
    s = max(1, (h + rps - 1) // rps)
    need = lambda k: min(rps, h - (k % s) * rps) * rb
    offs, cnts = ent.get(273, []), ent.get(279, [])
for k, (a, c) in enumerate(zip(offs, cnts)):
    try:
        if len(zlib.decompressobj().decompress(f[a:a + c])) > need(k):
            sys.exit(0)
    except zlib.error:
        pass
sys.exit(1)
