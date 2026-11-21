#!/usr/bin/env python3
"""Rewraps lossless WebP files in other containers: a raw VP8L bitstream,
RIFF + VP8X with ICCP/EXIF/XMP/unknown chunks, odd-sized chunks, wrong
sizes, truncations, and an animation flag."""
import os
import struct
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)


def chunk(tag, payload):
    c = tag + struct.pack("<I", len(payload)) + payload
    return c + (b"\0" if len(payload) % 2 else b"")


def riff(body):
    return b"RIFF" + struct.pack("<I", 4 + len(body)) + b"WEBP" + body


def vp8l_of(data):
    assert data[12:16] == b"VP8L"
    n = struct.unpack("<I", data[16:20])[0]
    return data[20:20 + n]


def dims(bs):
    v = int.from_bytes(bs[1:5], "little")
    return (v & 0x3fff) + 1, ((v >> 14) & 0x3fff) + 1


def vp8x(w, h, flags):
    return chunk(b"VP8X", struct.pack("<I", flags) + (w - 1).to_bytes(3, "little") + (h - 1).to_bytes(3, "little"))


for name in sorted(os.listdir(src)):
    if not name.endswith(".webp"):
        continue
    data = open(os.path.join(src, name), "rb").read()
    if data[12:16] != b"VP8L":
        continue
    bs = vp8l_of(data)
    w, h = dims(bs)
    b = name[:-5]
    variants = {
        "raw": bs,
        "vp8x": riff(vp8x(w, h, 0x10) + chunk(b"VP8L", bs)),
        "meta": riff(vp8x(w, h, 0x2c) + chunk(b"ICCP", b"icc!" * 5 + b"x") + chunk(b"VP8L", bs)
                     + chunk(b"EXIF", b"exif") + chunk(b"XMP ", b"<x/>")),
        "unknown": riff(vp8x(w, h, 0) + chunk(b"ABCD", b"123") + chunk(b"VP8L", bs) + chunk(b"WXYZ", b"")),
        "vp8x_badsize": riff(vp8x(w + 1, h, 0) + chunk(b"VP8L", bs)),
        "anim": riff(vp8x(w, h, 0x02) + chunk(b"VP8L", bs)),
        "trunc": data[:len(data) * 2 // 3],
        "trunc_hdr": data[:25],
        "riff_big": data[:4] + struct.pack("<I", len(data)) + data[8:],
        "riff_small": data[:4] + struct.pack("<I", len(data) - 9) + data[8:],
        "chunk_big": data[:16] + struct.pack("<I", len(bs) + 2) + data[20:],
        "trailing": data + b"\0\1\2\3garbage",
    }
    for k, v in variants.items():
        open(os.path.join(out, "%s.%s.webp" % (b, k)), "wb").write(v)
