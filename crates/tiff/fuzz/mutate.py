#!/usr/bin/env python3
"""mutate.py OUT N SEED FILES...: writes N mutants of the seed TIFF files to
OUT, for fuzz/run.sh to decode with verilith-tiff and libtiff.

Most mutations know the structure of IFD 0: an entry's value, count or type
changes (width, height, samples, bits, compression, rows per strip, planar
configuration, predictor, tile sizes, strip offsets and byte counts), an
entry is dropped, duplicated or moved, the strip or tile data gets bit
flips, is cut short or grows. The rest flip, insert, delete and truncate
bytes anywhere."""
import os
import random
import struct
import sys

TAGS = [256, 257, 258, 259, 262, 266, 273, 277, 278, 279, 284, 317, 322, 323, 324, 325, 338, 339]


def parse(b):
    if len(b) < 8 or b[:2] not in (b"II", b"MM"):
        return None
    e = "<" if b[:2] == b"II" else ">"
    o = struct.unpack(e + "I", b[4:8])[0]
    if o + 2 > len(b):
        return None
    n = struct.unpack(e + "H", b[o:o + 2])[0]
    if o + 2 + 12 * n > len(b):
        return None
    return e, o, n


def entries(b, e, o, n):
    return [list(struct.unpack(e + "HHII", b[o + 2 + 12 * i:o + 14 + 12 * i])) + [o + 2 + 12 * i] for i in range(n)]


def put(b, e, pos, ent):
    b[pos:pos + 12] = struct.pack(e + "HHII", *ent[:4])


def values_pos(b, e, ent):
    tag, ty, cnt, v, pos = ent
    ts = {1: 1, 3: 2, 4: 4}.get(ty, 4)
    return (pos + 8 if cnt * ts <= 4 else v), ts, cnt


def structured(b, r):
    p = parse(b)
    if p is None:
        return None
    e, o, n = p
    b = bytearray(b)
    ents = entries(b, e, o, n)
    if not ents:
        return None
    k = r.randrange(9)
    if k <= 2:  # an entry's value
        ent = r.choice([x for x in ents if x[0] in TAGS] or ents)
        if ent[2] == 1:
            v = r.choice([0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 24, 31, 32, 33, 255, 256, 32773, 32946,
                          65535, 0x7fffffff, 0xffffffff, ent[3] + 1, max(ent[3] - 1, 0), ent[3] * 2])
            if ent[1] == 3:
                v &= 0xffff
                ent[3] = v if e == ">" and False else v
                # SHORT values are left-justified in the value field.
                b[ent[4] + 8:ent[4] + 12] = struct.pack(e + "HH", v, 0)
                return bytes(b)
            if ent[1] == 1:
                b[ent[4] + 8] = v & 0xff
                return bytes(b)
            ent[3] = v & 0xffffffff
            put(b, e, ent[4], ent)
        else:  # one value of an array (offsets, byte counts, bits per sample)
            pos, ts, cnt = values_pos(b, e, ent)
            if cnt and pos + cnt * ts <= len(b):
                i = pos + ts * r.randrange(cnt)
                fmt = {1: "B", 2: "H", 4: "I"}[ts]
                old = struct.unpack(e + fmt, b[i:i + ts])[0]
                new = r.choice([0, 1, old + 1, max(old - 1, 0), old * 2, old // 2, len(b), len(b) + 10])
                b[i:i + ts] = struct.pack(e + fmt, new & ((1 << (8 * ts)) - 1))
    elif k == 3:  # an entry's count or type
        ent = r.choice(ents)
        if r.random() < 0.5:
            ent[2] = r.choice([0, 1, 2, 3, ent[2] + 1, max(ent[2] - 1, 0), 0xffffffff])
        else:
            ent[1] = r.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 16])
        put(b, e, ent[4], ent)
    elif k == 4:  # drop an entry
        i = r.randrange(n)
        rest = b[o + 2 + 12 * (i + 1):o + 2 + 12 * n]
        b[o + 2 + 12 * i:o + 2 + 12 * (n - 1)] = rest
        b[o + 2 + 12 * (n - 1):o + 2 + 12 * n] = b"\0" * 12
        b[o:o + 2] = struct.pack(e + "H", n - 1)
    elif k == 5:  # swap two entries, or make one a copy of another
        i, j = r.randrange(n), r.randrange(n)
        a, c = bytes(b[o + 2 + 12 * i:o + 14 + 12 * i]), bytes(b[o + 2 + 12 * j:o + 14 + 12 * j])
        b[o + 2 + 12 * i:o + 14 + 12 * i] = c
        if r.random() < 0.5:
            b[o + 2 + 12 * j:o + 14 + 12 * j] = a
    elif k <= 7:  # strip or tile data
        offs = [x for x in ents if x[0] in (273, 324)]
        if offs:
            pos, ts, cnt = values_pos(b, e, offs[0])
            if cnt and pos + ts <= len(b):
                fmt = {1: "B", 2: "H", 4: "I"}[ts]
                start = struct.unpack(e + fmt, b[pos:pos + ts])[0]
                for _ in range(r.randrange(1, 6)):
                    i = start + r.randrange(200)
                    if i < len(b):
                        b[i] ^= 1 << r.randrange(8)
    else:  # the header
        i = r.choice([2, 3, 4, 5, 6, 7])
        b[i] = r.randrange(256)
    return bytes(b)


def raw(b, r):
    b = bytearray(b)
    k = r.randrange(4)
    if k == 0:
        for _ in range(r.randrange(1, 5)):
            b[r.randrange(len(b))] = r.randrange(256)
    elif k == 1:
        del b[r.randrange(len(b)):]
    elif k == 2:
        i = r.randrange(len(b))
        del b[i:i + r.randrange(1, 4)]
    else:
        i = r.randrange(len(b) + 1)
        b[i:i] = bytes(r.randrange(256) for _ in range(r.randrange(1, 4)))
    return bytes(b)


def main():
    out, n, seed, files = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4:]
    r = random.Random(seed)
    seeds = [open(f, "rb").read() for f in files]
    seeds = [s for s in seeds if len(s) > 16]
    os.makedirs(out, exist_ok=True)
    for i in range(n):
        b = r.choice(seeds)
        for _ in range(r.choice([1, 1, 2, 3])):
            m = structured(b, r) if r.random() < 0.85 else None
            b = m if m is not None else raw(b, r)
            if len(b) < 9:
                break
        open(os.path.join(out, "m%06d.tif" % i), "wb").write(b)


main()
