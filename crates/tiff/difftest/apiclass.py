#!/usr/bin/env python3
"""apiclass.py OURS LIBTIFF FILE: explains the differences between what
difftest/api.c prints linked with verilith-tiff (OURS) and with libtiff
(LIBTIFF) for FILE, a file both decode to the same samples. Prints the
reasons, one word each, and exits 0 if every line that differs is explained
by one of the libtiff behaviours the README lists; else prints what is not
and exits 1. Standard library only.

  edge         RGBA of a tiled greyscale image (16-bit, or with extra
               samples) whose width is not a multiple of the tile width:
               libtiff's put16bitbwtile, putgreytile and putagreytile do not
               scale the skew between tile rows by the size of a pixel.
  bytecounts   libtiff replaced StripByteCounts with its own estimate.
  extrasamples libtiff made up ExtraSamples for samples the file does not
               describe ("the default is no extra samples").
  unspecified  libtiff takes an extra sample of "unspecified data" (0) as
               alpha.
  colormap8    libtiff took a ColorMap as 8-bit ("white is represented by
               65535").
  skipped      a field of a type TIFF says to skip, which libtiff converts.
"""
import struct
import sys

ours = open(sys.argv[1]).read().splitlines()
ref = open(sys.argv[2]).read().splitlines()
data = open(sys.argv[3], "rb").read()


def first_words(a, b):
    sa, sb = set(a), set(b)
    return {l.split()[0] for l in (sa ^ sb) if l.split()}


keys = first_words(ours, ref) - {"warning"}
vals = {}
for l in ours:
    w = l.split()
    if w:
        vals.setdefault(w[0], w[1:])

# The IFD's entry types.
e = "<" if data[:2] == b"II" else ">"
o = struct.unpack(e + "I", data[4:8])[0]
n = struct.unpack(e + "H", data[o:o + 2])[0]
types = {}
for i in range(n):
    t, ty = struct.unpack(e + "HH", data[o + 2 + 12 * i:o + 6 + 12 * i])
    types.setdefault(t, ty)

reasons, allowed = set(), set()
if "warning bytecounts estimated" in ref:
    reasons.add("bytecounts")
    allowed |= {"rps", "bytecounts", "rgba", "rgbaok"}
if "warning extrasamples made up" in ref:
    reasons.add("extrasamples")
    allowed |= {"extrasamples", "rgba", "rgbaok"}
if "warning colormap taken as 8-bit" in ref:
    reasons.add("colormap8")
    allowed |= {"rgba"}


def dval(name):
    v = vals.get(name)
    return int(v[3]) if v and len(v) >= 4 else 0


spp, bps, ph = dval("spp"), dval("bps"), dval("photometric")
size = vals.get("size", [])
width, tiled = (int(size[0]), size[3] == "1") if len(size) >= 4 else (0, False)
ex = vals.get("extrasamples", ["0"])
extra = [int(x) for x in ex[1:]]
tw = dval("tilewidth")
grey = ph in (0, 1)
if tiled and grey and tw > 0 and width % tw != 0 and (bps == 16 or (bps == 8 and spp > 1)):
    reasons.add("edge")
    allowed.add("rgba")
if extra and extra[0] == 0 and spp > 3:
    reasons.add("unspecified")
    allowed.add("rgba")

TAG = {"bps": 258, "spp": 277, "compression": 259, "photometric": 262, "planar": 284, "fillorder": 266,
       "orientation": 274, "sampleformat": 339, "resunit": 296, "maxsample": 281, "rps": 278, "subfiletype": 254,
       "tilewidth": 322, "tilelength": 323, "xres": 282, "software": 305, "extrasamples": 338, "colormap": 320}
WANT = {282: {5}, 305: {2}}
for k in keys:
    t = TAG.get(k)
    if t in types and types[t] not in WANT.get(t, {1, 3, 4}):
        reasons.add("skipped")
        allowed.add(k)
        if k == "orientation":
            allowed.add("rgba")
        if k == "rps":
            # TIFFTileSize of a strip image is RowsPerStrip rows.
            allowed.add("scanline")

left = keys - allowed
print(" ".join(sorted(reasons)) if not left else "unexplained: " + " ".join(sorted(left)))
sys.exit(1 if left else 0)
