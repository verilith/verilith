#!/usr/bin/env python3
"""gen.py DIR: writes a corpus of GIF files for the differential tests,
with Pillow: every palette size from 2 to 256 colours (so every LZW
minimum code size), sizes from 1x1 to 1200x900, noise (short strings, a
table that fills fast) and smooth images (long strings), interlaced or
not, and animations with graphic control extensions, transparency and
each disposal method. Deterministic."""
import math
import os
import random
import sys

from PIL import Image, ImageDraw

out = sys.argv[1]
os.makedirs(out, exist_ok=True)


def palette(r):
    return [r.randrange(256) for _ in range(768)]


def noise(w, h, ncol, seed):
    r = random.Random(seed)
    im = Image.new("P", (w, h))
    im.putpalette(palette(r))
    im.putdata([r.randrange(ncol) for _ in range(w * h)])
    return im


def smooth(w, h, ncol, seed):
    r = random.Random(seed)
    im = Image.new("P", (w, h))
    im.putpalette(palette(r))
    im.putdata([int((math.sin(x / 7.0 + seed) + math.cos(y / 5.0)) * ncol / 4 + ncol / 2) % ncol
                for y in range(h) for x in range(w)])
    return im


n = 0
for ncol in [2, 3, 4, 5, 8, 16, 17, 32, 64, 128, 200, 256]:
    for (w, h) in [(1, 1), (1, 7), (7, 1), (3, 5), (16, 16), (33, 17), (100, 75), (640, 480)]:
        for kind, f in [("noise", noise), ("smooth", smooth)]:
            im = f(w, h, ncol, n)
            for il in [0, 1]:
                im.save(os.path.join(out, f"p_{kind}_{ncol}_{w}x{h}_{il}.gif"), interlace=bool(il), optimize=False)
            n += 1
for kind, f in [("noise", noise), ("smooth", smooth)]:
    f(1200, 900, 256, 99).save(os.path.join(out, f"big_{kind}.gif"), optimize=False)
for k in range(16):
    r = random.Random(k)
    W, H = r.randrange(10, 200), r.randrange(10, 200)
    frames = []
    for i in range(r.randrange(2, 6)):
        im = smooth(W, H, r.choice([4, 16, 256]), k * 10 + i).convert("RGBA")
        x0, x1 = sorted([r.randrange(W), r.randrange(W)])
        y0, y1 = sorted([r.randrange(H), r.randrange(H)])
        ImageDraw.Draw(im).rectangle([x0, y0, x1, y1], fill=(0, 0, 0, 0))
        frames.append(im)
    frames[0].save(os.path.join(out, f"anim_{k}.gif"), save_all=True, append_images=frames[1:],
                   duration=[r.randrange(0, 500) for _ in frames], loop=0,
                   disposal=r.choice([0, 1, 2, 3]), optimize=r.choice([True, False]))
