#!/usr/bin/env python3
"""Writes N mutants of the given PNG files to OUT, fixing chunk CRCs so the
mutations reach past the CRC check. Usage: mutate.py OUT N SEED FILES..."""
import os, random, struct, sys, zlib

def chunks(d):
    p, out = 8, []
    while p + 12 <= len(d):
        l = struct.unpack('>I', d[p:p+4])[0]
        if p + 12 + l > len(d): break
        out.append([d[p+4:p+8], bytearray(d[p+8:p+8+l])]); p += 12 + l
    return out

def build(cs):
    o = bytearray(b'\x89PNG\r\n\x1a\n')
    for t, c in cs:
        o += struct.pack('>I', len(c)) + t + c + struct.pack('>I', zlib.crc32(t + c))
    return bytes(o)

def mutate(d, r):
    cs = chunks(d)
    if not cs: return d
    k = r.randrange(6)
    if k == 0:   # flip bytes in a chunk's data
        t, c = r.choice(cs)
        for _ in range(r.randint(1, 4)):
            if c: c[r.randrange(len(c))] = r.randrange(256)
    elif k == 1: # mutate decompressed image data and recompress
        idat = b''.join(c for t, c in cs if t == b'IDAT')
        try: raw = bytearray(zlib.decompress(idat))
        except Exception: return build(cs)
        for _ in range(r.randint(1, 8)):
            if raw: raw[r.randrange(len(raw))] = r.randrange(256)
        if r.random() < 0.3: raw = raw[:r.randrange(len(raw) + 1)]
        if r.random() < 0.2: raw += bytes(r.randrange(256) for _ in range(r.randint(1, 50)))
        z = zlib.compress(bytes(raw))
        cs = [x for x in cs if x[0] != b'IDAT']
        at = next((i for i, x in enumerate(cs) if x[0] == b'IEND'), len(cs))
        cs.insert(at, [b'IDAT', bytearray(z)])
    elif k == 2: # change IHDR fields
        for t, c in cs:
            if t == b'IHDR' and len(c) == 13:
                c[r.choice([3, 7, 8, 9, 12])] = r.choice([0, 1, 2, 3, 4, 6, 8, 16, r.randrange(256)])
    elif k == 3: # duplicate, drop or swap chunks
        i = r.randrange(len(cs)); j = r.randrange(len(cs))
        op = r.randrange(3)
        if op == 0: cs.insert(j, [cs[i][0], bytearray(cs[i][1])])
        elif op == 1 and len(cs) > 2: del cs[i]
        else: cs[i], cs[j] = cs[j], cs[i]
    elif k == 4: # insert a PLTE or tRNS of random length
        t = r.choice([b'PLTE', b'tRNS'])
        cs.insert(r.randrange(1, len(cs) + 1), [t, bytearray(r.randrange(256) for _ in range(r.choice([0, 1, 2, 3, 6, 7, 30, 300, 768, 771])))])
    else:        # raw byte flips without CRC repair
        b = bytearray(build(cs))
        for _ in range(r.randint(1, 3)): b[r.randrange(len(b))] = r.randrange(256)
        return bytes(b)
    return build(cs)

out, n, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
r = random.Random(seed)
srcs = [open(f, 'rb').read() for f in sys.argv[4:]]
os.makedirs(out, exist_ok=True)
for i in range(n):
    d = r.choice(srcs)
    for _ in range(r.randint(1, 3)): d = mutate(d, r)
    open(os.path.join(out, f'm{i:05d}.png'), 'wb').write(d)
