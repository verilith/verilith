#!/usr/bin/env python3
"""Writes synthetic test images (PAM, RGBA) for the corpus: sizes from 1x1
up, noise, gradients, few-color images (palettes), and alpha variants."""
import os
import random
import sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
rng = random.Random(1)


def pam(name, w, h, px):
    with open(os.path.join(out, name + ".pam"), "wb") as f:
        f.write(b"P7\nWIDTH %d\nHEIGHT %d\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n" % (w, h))
        f.write(bytes(px))


def gen(kind, w, h, alpha):
    px = bytearray()
    pal = [tuple(rng.randrange(256) for _ in range(4)) for _ in range(256)]
    ncol = {"pal2": 2, "pal4": 4, "pal16": 16, "pal200": 200}.get(kind, 0)
    for y in range(h):
        for x in range(w):
            if kind == "noise":
                c = [rng.randrange(256) for _ in range(4)]
            elif kind == "grad":
                c = [(x * 255) // max(w - 1, 1), (y * 255) // max(h - 1, 1), ((x + y) * 3) & 255, (x * y) & 255]
            elif kind == "stripes":
                c = [255 * ((x // 3) % 2), 128, 255 * ((y // 5) % 2), 200]
            elif kind == "smooth":
                c = [(x // 4 + y // 7) & 255, (x * 2) & 255, (y * 3) & 255, 255 - ((x + y) & 63)]
            elif kind == "repeat":
                c = list(pal[(x % 7) + 7 * (y % 3)])
            else:
                c = list(pal[rng.randrange(ncol)] if rng.random() < 0.9 else pal[(x + y) % ncol])
            if alpha == "opaque":
                c[3] = 255
            elif alpha == "binary":
                c[3] = 0 if (x ^ y) & 4 else 255
            px += bytes(c)
    return px


sizes = [(1, 1), (1, 7), (9, 1), (2, 2), (3, 5), (16, 16), (17, 33), (64, 48), (127, 129), (256, 200), (513, 77)]
kinds = ["noise", "grad", "stripes", "smooth", "repeat", "pal2", "pal4", "pal16", "pal200"]
alphas = ["opaque", "binary", "full"]
n = 0
for (w, h) in sizes:
    for k in kinds:
        a = alphas[n % 3]
        n += 1
        if w * h > 20000 and k == "noise" and a == "full":
            continue
        pam("%s_%dx%d_%s" % (k, w, h, a), w, h, gen(k, w, h, a))
