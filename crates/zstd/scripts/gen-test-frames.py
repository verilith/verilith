#!/usr/bin/env python3
# Usage: scripts/gen-test-frames.py tests/data   (needs libzstd.so.1)
# Writes crates/zstd/tests/data/*.zst with the system libzstd: the inputs
# tests/frames.rs rebuilds and checks the decoder against.
import ctypes, sys
z = ctypes.CDLL("libzstd.so.1")
z.ZSTD_createCCtx.restype = ctypes.c_void_p
z.ZSTD_compressBound.restype = ctypes.c_size_t
z.ZSTD_compress2.restype = ctypes.c_size_t
z.ZSTD_compress2.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p, ctypes.c_size_t]
z.ZSTD_CCtx_setParameter.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
z.ZSTD_isError.argtypes = [ctypes.c_size_t]
WORDS = [b"the", b"quick", b"brown", b"fox", b"jumps", b"over", b"lazy", b"dog", b"zstd", b"frame", b"block", b"literal", b"sequence", b"offset", b"match", b"huffman"]
def sample(size, kind, seed):
    x = seed; out = bytearray()
    def nxt():
        nonlocal x
        x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        return x >> 33
    while len(out) < size:
        r = nxt()
        if kind == 0:
            out += bytes([r & 0xff])
        elif kind == 1:
            out += WORDS[r % 16] + b" "
        else:
            out += bytes([r & 0xff]) * (1 + (r >> 8) % 40) if r % 3 == 0 else WORDS[r % 16] + b" "
    return bytes(out[:size])
CASES = [  # name, size, kind, level, checksum, window log (0: default)
    ("random-4k", 4096, 0, 3, 1, 0),
    ("text-200k-l1", 200_000, 1, 1, 0, 0),
    ("text-200k-l19", 200_000, 1, 19, 1, 0),
    ("mixed-300k-l9", 300_000, 2, 9, 1, 0),
    ("mixed-300k-w10", 300_000, 2, 6, 0, 10),
    ("empty", 0, 1, 3, 1, 0),
]
for name, size, kind, level, cs, wl in CASES:
    src = sample(size, kind, 0x9e3779b97f4a7c15 + size)
    c = z.ZSTD_createCCtx()
    z.ZSTD_CCtx_setParameter(c, 100, level)   # ZSTD_c_compressionLevel
    z.ZSTD_CCtx_setParameter(c, 201, cs)      # ZSTD_c_checksumFlag
    if wl: z.ZSTD_CCtx_setParameter(c, 101, wl)  # ZSTD_c_windowLog
    cap = z.ZSTD_compressBound(size)
    dst = ctypes.create_string_buffer(cap)
    n = z.ZSTD_compress2(c, dst, cap, src, size)
    assert not z.ZSTD_isError(n), name
    open(f"{sys.argv[1]}/{name}.zst", "wb").write(dst.raw[:n])
    print(name, size, n)
