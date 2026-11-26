#!/usr/bin/env python3
"""mutate.py OUT N SEED FILES...: writes N mutants of the seed GIF files to
OUT, for fuzz/run.sh to decode with verilith-gif and giflib.

Most mutations know the block structure, so they get past the parts that
are easy to reject: the image data is cut into new sub-blocks, its LZW
codes get bit flips, the descriptors change field by field, extensions are
added, dropped and duplicated (graphic control ones with odd lengths), the
trailer goes or gets company. The rest flip, insert, delete and truncate
bytes anywhere."""
import os
import random
import sys


def parse(b):
    """Splits a GIF into its header (with the global colour table) and its
    blocks, each as (kind, bytes). None if the structure is broken."""
    if len(b) < 13:
        return None
    n = 3 * (2 << (b[10] & 7)) if b[10] & 0x80 else 0
    p = 13 + n
    head, blocks = b[:p], []
    while p < len(b):
        t = b[p]
        if t == 0x3B:
            blocks.append(("trailer", b[p:p + 1]))
            blocks.append(("tail", b[p + 1:]))
            return head, blocks
        if t == 0x21:
            q = p + 2
        elif t == 0x2C:
            if p + 10 > len(b):
                return None
            f = b[p + 9]
            q = p + 10 + (3 * (2 << (f & 7)) if f & 0x80 else 0) + 1
        else:
            return None
        while q < len(b) and b[q] != 0:
            q += 1 + b[q]
        if q >= len(b):
            return None
        blocks.append(("ext" if t == 0x21 else "img", b[p:q + 1]))
        p = q + 1
    return head, blocks


def chain(data, r):
    """The data as sub-blocks of random sizes, with the terminator."""
    out, i = bytearray(), 0
    while i < len(data):
        n = min(len(data) - i, r.choice([1, 2, 3, 7, 100, 254, 255, 255]))
        out += bytes([n]) + data[i:i + n]
        i += n
    return bytes(out + b"\0")


def unchain(b, q):
    data = bytearray()
    while b[q] != 0:
        data += b[q + 1:q + 1 + b[q]]
        q += 1 + b[q]
    return bytes(data)


def image_parts(blk):
    f = blk[9]
    c = 10 + (3 * (2 << (f & 7)) if f & 0x80 else 0)
    return blk[:c], blk[c], unchain(blk, c + 1)


def mutate_image(blk, r):
    desc, m, data = image_parts(blk)
    desc = bytearray(desc)
    k = r.randrange(9)
    if k == 0:  # re-chunk only
        pass
    elif k == 1:  # flip bits in the codes
        data = bytearray(data)
        for _ in range(r.randrange(1, 4)):
            if data:
                data[r.randrange(len(data))] ^= 1 << r.randrange(8)
    elif k == 2:  # cut the codes
        data = data[:r.randrange(len(data) + 1)]
    elif k == 3:  # minimum code size
        m = r.choice([0, 1, 2, 3, 7, 8, 9, 12, 255, (m + 1) & 0xFF, (m - 1) & 0xFF])
    elif k == 4:  # width or height
        i = r.choice([5, 7])
        v = r.choice([0, 1, 2, desc[i] + 1, desc[i] - 1, 255, 0x7FFF, 0xFFFF]) & 0xFFFF
        desc[i:i + 2] = v.to_bytes(2, "little")
    elif k == 5:  # interlace flag
        desc[9] ^= 0x40
    elif k == 6:  # position
        i = r.choice([1, 3])
        desc[i:i + 2] = r.randrange(65536).to_bytes(2, "little")
    elif k == 7:  # random codes after the real ones
        data = data + bytes(r.randrange(256) for _ in range(r.randrange(1, 20)))
    else:  # a clear code, then the data again
        data = data + data
    return bytes(desc) + bytes([m]) + chain(data, r)


def gce(r):
    n = r.choice([4, 4, 4, 0, 3, 5, 1])
    body = bytes([r.randrange(256) for _ in range(n)])
    return b"\x21\xF9" + (bytes([n]) + body if n else b"") + b"\0"


def structured(b, r):
    pr = parse(b)
    if pr is None:
        return None
    head, blocks = pr
    head = bytearray(head)
    k = r.randrange(10)
    imgs = [i for i, (t, _) in enumerate(blocks) if t == "img"]
    if k <= 3 and imgs:
        i = r.choice(imgs)
        blocks[i] = ("img", mutate_image(blocks[i][1], r))
    elif k == 4:  # a graphic control extension somewhere
        blocks.insert(r.randrange(len(blocks) + 1), ("ext", gce(r)))
    elif k == 5 and blocks:  # drop a block
        del blocks[r.randrange(len(blocks))]
    elif k == 6 and blocks:  # duplicate a block
        i = r.randrange(len(blocks))
        blocks.insert(i, blocks[i])
    elif k == 7:  # another extension, any label
        blocks.insert(r.randrange(len(blocks) + 1),
                      ("ext", bytes([0x21, r.randrange(256)]) + chain(os.urandom(r.randrange(0, 300)), r)))
    elif k == 8:  # the screen
        i = r.choice([0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        head[i] = r.randrange(256)
    else:  # after the trailer
        blocks.append(("tail", bytes(r.randrange(256) for _ in range(r.randrange(1, 10)))))
    return bytes(head) + b"".join(x for _, x in blocks)


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
    seeds = [s for s in seeds if len(s) > 13]
    os.makedirs(out, exist_ok=True)
    for i in range(n):
        b = r.choice(seeds)
        for _ in range(r.choice([1, 1, 1, 2, 3])):
            m = structured(b, r) if r.random() < 0.8 else None
            b = m if m is not None else raw(b, r)
            if len(b) < 14:
                break
        open(os.path.join(out, "m%06d.gif" % i), "wb").write(b)


main()
