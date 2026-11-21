#!/usr/bin/env python3
"""Generate WebP/VP8L files that stress the code-length Huffman table builder.

CVE-2023-4863 was a heap buffer overflow in libwebp's BuildHuffmanTable while
building the Huffman table for the 19-symbol *code-length* alphabet (and the
subsequent symbol alphabets) from attacker-controlled code lengths. The fixed
allocation for the table's second level could be overrun by a code whose length
distribution needed more second-level entries than libwebp pre-sized for.

vwebp builds the same tables in `codes::build`, which is *proven* to either
return a valid table or reject the input, with every array write in bounds, for
*any* code-length configuration. These files exercise that path adversarially:

  * `cve_depth.webp`     -- a valid but maximally deep code-length code (the
                            second-level-table expansion the bug overran on).
  * `cve_oversub.webp`   -- an over-subscribed code-length code (must reject).
  * `cve_incomplete.webp`-- an incomplete code-length code (must reject).

VP8L packs bits LSB-first; this writer matches vwebp's bit reader exactly.
Run each through difftest/diff to confirm vwebp and libwebp agree (both reject,
or both decode) with no crash under ASan.
"""
import struct, sys, os

class BitWriter:
    def __init__(self):
        self.acc = 0; self.nbits = 0; self.out = bytearray()
    def put(self, value, n):
        # emit the low n bits of value, LSB first
        self.acc |= (value & ((1 << n) - 1)) << self.nbits
        self.nbits += n
        while self.nbits >= 8:
            self.out.append(self.acc & 0xff)
            self.acc >>= 8; self.nbits -= 8
    def finish(self):
        if self.nbits > 0:
            self.out.append(self.acc & 0xff)
            self.acc = 0; self.nbits = 0
        return bytes(self.out)

# The order in which the 19 code-length code lengths are transmitted (vwebp
# codes::CL_ORDER / RFC 9649 §5.4.2.1).
CL_ORDER = [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def vp8l_header(bw, w, h):
    bw.put(0x2f, 8)      # VP8L signature
    bw.put(w - 1, 14)    # width - 1
    bw.put(h - 1, 14)    # height - 1
    bw.put(0, 1)         # alpha_is_used
    bw.put(0, 3)         # version
    bw.put(0, 1)         # no transforms

def code_length_code(bw, lengths):
    """Emit the 19-symbol code-length code given lengths[sym] (0 = unused)."""
    bw.put(0, 1)         # color cache: off
    bw.put(0, 1)         # meta-huffman: off
    bw.put(0, 1)         # first symbol code: normal (not simple)
    bw.put(19 - 4, 4)    # num_code_lengths - 4  -> all 19 present
    for sym in CL_ORDER:
        bw.put(lengths[sym], 3)   # 3 bits each; the builder sees these verbatim

def wrap(payload):
    body = b"WEBP" + b"VP8L" + struct.pack("<I", len(payload)) + payload
    if len(body) & 1:
        body += b"\x00"
    return b"RIFF" + struct.pack("<I", len(body)) + body

def build(name, lengths, w=1, h=1):
    bw = BitWriter()
    vp8l_header(bw, w, h)
    code_length_code(bw, lengths)
    # Whatever follows is read with that table; truncation here is fine -- the
    # point is reaching and exercising the table builder on the code lengths.
    data = wrap(bw.finish())
    with open(name, "wb") as f:
        f.write(data)
    print(f"wrote {name} ({len(data)} bytes)")

def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else "."
    os.makedirs(outdir, exist_ok=True)
    j = lambda n: os.path.join(outdir, n)

    # A complete, maximally deep canonical code over the 19 symbols:
    # lengths 1,2,3,...,up to 7 with the tail filled so the Kraft sum is exact.
    # This is a *valid* code whose second level is the one buggy libwebp overran.
    depth = [1, 2, 3, 4, 5, 6, 7, 8, 8] + [0] * 10
    # Fix to a complete 8-deep code: 2^-1+2^-2+...+2^-7 = 1 - 2^-7; two 8s add
    # 2*2^-8 = 2^-7 -> exactly 1.
    build(j("cve_depth.webp"), depth)

    # Over-subscribed: three symbols of length 1 (Kraft sum 3/2 > 1). Must reject.
    oversub = [1, 1, 1] + [0] * 16
    build(j("cve_oversub.webp"), oversub)

    # Incomplete: a single symbol of length 2 (Kraft sum 1/4 < 1). Must reject.
    incomplete = [0, 0, 2] + [0] * 16
    build(j("cve_incomplete.webp"), incomplete)

if __name__ == "__main__":
    main()
