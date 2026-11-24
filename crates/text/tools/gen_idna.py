#!/usr/bin/env python3
"""Writes src/idna/tables.rs from the Unicode Character Database.

Usage: tools/gen_idna.py UCD_DIR

UCD_DIR holds IdnaMappingTable.txt, UnicodeData.txt, DerivedBidiClass.txt
and DerivedJoiningType.txt. The tables are trusted data: tests/idna_data.rs
checks every code point's word against the same files, parsed
independently, and tests/idna.rs runs IdnaTestV2.txt.

Layout. A three-level trie maps each code point to a word:

  bits 0-2    UTS #46 status (STATUS_*)
  bit 3       General_Category is a mark (Mn, Mc, Me)
  bits 4-7    Bidi_Class (BIDI_*; classes the rules do not name are OTHER)
  bits 8-10   Joining_Type (JT_*)
  bits 11-15  length of the mapping (mapped and deviation code points)
  bits 16-31  offset of the mapping in IDNA_POOL

IDNA_L1[cp >> 12] is the start in IDNA_L2 of a block of 64 entries, and
IDNA_L2[IDNA_L1[cp >> 12] + (cp >> 6 & 63)] the start in IDNA_DATA of the
block of 64 words that holds cp's word at (cp & 63).
"""
import sys
from collections import OrderedDict

UNICODE_VERSION = (18, 0, 0)
STATUS = {"valid": 0, "ignored": 1, "mapped": 2, "deviation": 3, "disallowed": 4}
BIDI = ["L", "R", "AL", "EN", "ES", "ET", "AN", "CS", "NSM", "BN", "ON"]  # then OTHER = 11
BIDI_LONG = {"Left_To_Right": "L", "Right_To_Left": "R", "Arabic_Letter": "AL", "European_Number": "EN",
             "European_Separator": "ES", "European_Terminator": "ET", "Arabic_Number": "AN",
             "Common_Separator": "CS", "Nonspacing_Mark": "NSM", "Boundary_Neutral": "BN", "Other_Neutral": "ON"}
JT = {"U": 0, "L": 1, "R": 2, "D": 3, "T": 4, "C": 5}
JT_LONG = {"Non_Joining": "U", "Left_Joining": "L", "Right_Joining": "R", "Dual_Joining": "D",
           "Transparent": "T", "Join_Causing": "C"}
N = 0x110000


def const_doc(k):
    """The doc comment of each generated constant."""
    if k.startswith("STATUS_"):
        return f"UTS #46 status `{k[7:].lower()}`."
    if k == "BIDI_OTHER":
        return "Bidi_Class: any class the bidi rule does not name."
    if k.startswith("BIDI_"):
        return f"Bidi_Class `{k[5:]}`."
    if k.startswith("JT_"):
        return f"Joining_Type `{k[3:]}`."
    if k.endswith("_LEN"):
        return f"The length of `{k[:-4]}`."
    raise KeyError(k)


def ranges(path):
    """(lo, hi, fields) of each data line, and the @missing lines."""
    data, missing = [], []
    for line in open(path, encoding="utf-8"):
        if line.startswith("# @missing:"):
            r, v = line[len("# @missing:"):].split(";")
            a, _, b = r.strip().partition("..")
            missing.append((int(a, 16), int(b or a, 16), v.strip()))
            continue
        line = line.split("#")[0].strip()
        if not line:
            continue
        f = [x.strip() for x in line.split(";")]
        a, _, b = f[0].partition("..")
        data.append((int(a, 16), int(b or a, 16), f[1:]))
    return data, missing


def parse(ucd):
    status = [None] * N
    mapping = [None] * N
    for a, b, f in ranges(f"{ucd}/IdnaMappingTable.txt")[0]:
        st = STATUS[f[0]]
        m = [int(x, 16) for x in f[1].split()] if len(f) > 1 and f[0] in ("mapped", "deviation") else []
        for cp in range(a, b + 1):
            status[cp] = st
            mapping[cp] = m
    assert all(s is not None for s in status)
    mark = [False] * N
    first = None
    for line in open(f"{ucd}/UnicodeData.txt"):
        f = line.split(";")
        cp = int(f[0], 16)
        if f[1].endswith(", First>"):
            first = cp
            continue
        lo = first if f[1].endswith(", Last>") else cp
        first = None
        if f[2] in ("Mn", "Mc", "Me"):
            for c in range(lo, cp + 1):
                mark[c] = True
    bidi = [None] * N
    data, missing = ranges(f"{ucd}/DerivedBidiClass.txt")
    for a, b, v in missing:
        for cp in range(a, b + 1):
            bidi[cp] = BIDI_LONG.get(v)
    for a, b, f in data:
        for cp in range(a, b + 1):
            bidi[cp] = f[0]
    jt = [0] * N
    data, missing = ranges(f"{ucd}/DerivedJoiningType.txt")
    assert missing == [(0, 0x10FFFF, "Non_Joining")]
    for a, b, f in data:
        for cp in range(a, b + 1):
            jt[cp] = JT[f[0]]
    return status, mapping, mark, bidi, jt


def main(ucd, out):
    status, mapping, mark, bidi, jt = parse(ucd)
    pool, pool_index = [], {}
    words = []
    for cp in range(N):
        m = mapping[cp]
        off = 0
        if m:
            key = tuple(m)
            if key not in pool_index:
                pool_index[key] = len(pool)
                pool.extend(m)
            off = pool_index[key]
        assert len(m) < 32
        b = BIDI.index(bidi[cp]) if bidi[cp] in BIDI else 11
        words.append(status[cp] | (int(mark[cp]) << 3) | (b << 4) | (jt[cp] << 8) | (len(m) << 11) | (off << 16))
    assert len(pool) < 65536

    data, data_index = [], {}
    l2, l2_index = [], {}
    l1 = []
    for hi in range(0, N, 4096):
        blk2 = []
        for lo in range(hi, hi + 4096, 64):
            blk = tuple(words[lo:lo + 64])
            if blk not in data_index:
                data_index[blk] = len(data)
                data.extend(blk)
            blk2.append(data_index[blk])
        key = tuple(blk2)
        if key not in l2_index:
            l2_index[key] = len(l2)
            l2.extend(blk2)
        l1.append(l2_index[key])
    assert len(data) < 65536 and len(l2) < 65536

    def arr(name, ty, vals, doc, per=16):
        rows = ",\n".join("    " + ", ".join(str(v) for v in vals[i:i + per]) for i in range(0, len(vals), per))
        return f"/// {doc}\npub static {name}: [{ty}; {name}_LEN] = [\n{rows},\n];\n"

    tables = [
        ("IDNA_L1", "u16", l1, "Start in `IDNA_L2` of the block of each 4096 code points.", 16),
        ("IDNA_L2", "u16", l2, "Start in `IDNA_DATA` of the block of each 64 code points.", 16),
        ("IDNA_DATA", "u32", words and data, "The word of each code point, by block.", 8),
        ("IDNA_POOL", "u32", pool, "Mapping sequences.", 8),
    ]
    consts = [(k.upper(), "u32", v) for k, v in [("status_" + s, n) for s, n in STATUS.items()]]
    consts += [("BIDI_" + b, "u32", i) for i, b in enumerate(BIDI)] + [("BIDI_OTHER", "u32", 11)]
    consts += [("JT_" + k, "u32", v) for k, v in JT.items()]
    consts += [(t[0] + "_LEN", "usize", len(t[2])) for t in tables]
    o = ["// Generated by tools/gen_idna.py from the Unicode Character Database",
         f"// {UNICODE_VERSION[0]}.{UNICODE_VERSION[1]}.{UNICODE_VERSION[2]}. Do not edit.",
         "use vstd::prelude::*;", "", "verus! {", ""]
    for k, t, v in consts:
        o += [f"/// {const_doc(k)}", f"pub const {k}: {t} = {v};"]
    o += ["", "} // verus!", ""]
    o += [arr(*t) for t in tables]
    open(out, "w").write("\n".join(o))
    print(f"l1 {len(l1)}, l2 {len(l2)}, data {len(data)}, pool {len(pool)}", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "src/idna/tables.rs")
