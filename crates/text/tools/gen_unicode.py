#!/usr/bin/env python3
"""Writes src/unicode/tables.rs from the Unicode Character Database.

Usage: tools/gen_unicode.py UCD_DIR

UCD_DIR holds UnicodeData.txt and DerivedNormalizationProps.txt of the
Unicode version the crate targets (see UNICODE_VERSION below). The tables
are trusted data: tests/unicode_data.rs checks every code point's entry
against the same files, parsed independently, and against the
unicode-normalization crate, and tests/normalization.rs runs
NormalizationTest.txt.

Layout. A two-level trie maps each code point below TRIE_LIMIT to its
FLAG_* bits and a record number (above it, every code point has PLAIN_WORD:
record 0, the record of a code point with no decomposition and combining
class 0, and the flags of such a code point). A record holds:

  ccc        canonical combining class
  fd, kd     canonical and compatibility full decomposition, as
             (offset << 5) | length into POOL; length 0 means none
  comp       (start << 8) | count: the composition pairs (second, result)
             in COMP_SECOND/COMP_RESULT with this code point first

Hangul syllables are algorithmic and have no fd/kd/comp entries.
"""
import sys
from collections import OrderedDict

UNICODE_VERSION = (18, 0, 0)
TRIE_SHIFT = 6
TRIE_LIMIT = 0x30000

S_BASE, L_BASE, V_BASE, T_BASE = 0xAC00, 0x1100, 0x1161, 0x11A7
L_COUNT, V_COUNT, T_COUNT = 19, 21, 28
N_COUNT = V_COUNT * T_COUNT
S_COUNT = L_COUNT * N_COUNT

FLAG_FAST_NFD = 1
FLAG_FAST_NFKD = 2
FLAG_FAST_NFC = 4
FLAG_FAST_NFKC = 8
FLAG_BB_NFD = 16
FLAG_BB_NFKD = 32
FLAG_BB_NFC = 64
FLAG_BB_NFKC = 128
FLAG_SECOND = 256


def const_doc(k):
    """The doc comment of each generated constant."""
    forms = {"NFD": "NFD", "NFKD": "NFKD", "NFC": "NFC", "NFKC": "NFKC"}
    if k == "UNICODE_VERSION":
        return "The Unicode version the tables are built from."
    if k == "TRIE_SHIFT":
        return "The trie's blocks are `1 << TRIE_SHIFT` code points."
    if k == "TRIE_LIMIT":
        return "Code points from here on are not in the trie: their word is `PLAIN_WORD`."
    if k == "PLAIN_WORD":
        return "The word of a code point with no decomposition, combining class 0 and no compositions."
    if k.startswith("FLAG_FAST_"):
        return f"Flag: the code point is in {forms[k[10:]]} on its own and starts a new segment."
    if k.startswith("FLAG_BB_"):
        return f"Flag: {forms[k[8:]]} can restart at the code point (a segment boundary before it)."
    if k == "FLAG_SECOND":
        return "Flag: the code point is the second of some composition pair."
    if k.endswith("_LEN"):
        return f"The length of `{k[:-4]}`."
    raise KeyError(k)


def parse(ucd):
    ccc = {}
    dm = {}
    for line in open(f"{ucd}/UnicodeData.txt"):
        f = line.split(";")
        cp = int(f[0], 16)
        if int(f[3]):
            ccc[cp] = int(f[3])
        if f[5]:
            parts = f[5].split()
            compat = parts[0].startswith("<")
            if compat:
                parts = parts[1:]
            dm[cp] = (compat, [int(p, 16) for p in parts])
    fce = set()
    for line in open(f"{ucd}/DerivedNormalizationProps.txt"):
        line = line.split("#")[0].strip()
        if not line:
            continue
        f = [x.strip() for x in line.split(";")]
        if f[1] == "Full_Composition_Exclusion":
            a, _, b = f[0].partition("..")
            for cp in range(int(a, 16), int(b or a, 16) + 1):
                fce.add(cp)
    return ccc, dm, fce


def is_hangul(cp):
    return S_BASE <= cp < S_BASE + S_COUNT


def hangul_decomp(cp):
    s = cp - S_BASE
    l, v, t = L_BASE + s // N_COUNT, V_BASE + (s % N_COUNT) // T_COUNT, T_BASE + s % T_COUNT
    return [l, v] if t == T_BASE else [l, v, t]


def main(ucd, out):
    ccc, dm, fce = parse(ucd)

    def full(cp, compat):
        if is_hangul(cp):
            return hangul_decomp(cp)
        if cp in dm and (compat or not dm[cp][0]):
            return [x for c in dm[cp][1] for x in full(c, compat)]
        return [cp]

    comp = {}
    for cp, (compat, m) in dm.items():
        if not compat and len(m) == 2 and cp not in fce:
            comp[(m[0], m[1])] = cp
    second = {b for (_, b) in comp} | set(range(V_BASE, V_BASE + V_COUNT)) | set(range(T_BASE + 1, T_BASE + T_COUNT))

    def compose_pair(a, b):
        if L_BASE <= a < L_BASE + L_COUNT and V_BASE <= b < V_BASE + V_COUNT:
            return S_BASE + ((a - L_BASE) * V_COUNT + (b - V_BASE)) * T_COUNT
        if is_hangul(a) and (a - S_BASE) % T_COUNT == 0 and T_BASE < b < T_BASE + T_COUNT:
            return a + (b - T_BASE)
        return comp.get((a, b))

    def cc(c):
        return ccc.get(c, 0)

    def reorder(d):
        out = []
        for c in d:
            if cc(c) == 0:
                out.append(c)
            else:
                p = len(out)
                while p > 0 and cc(out[p - 1]) > cc(c):
                    p -= 1
                out.insert(p, c)
        return out

    def compose(d):
        out = []
        for c in d:
            li = max((k for k in range(len(out)) if cc(out[k]) == 0), default=None)
            if li is not None and not any(cc(out[k]) == 0 or cc(out[k]) >= cc(c) for k in range(li + 1, len(out))):
                p = compose_pair(out[li], c)
                if p is not None:
                    out[li] = p
                    continue
            out.append(c)
        return out

    def flags(cp):
        fd = full(cp, False)
        kd = full(cp, True)
        f = 0
        if fd == [cp] and cc(cp) == 0:
            f |= FLAG_FAST_NFD
        if kd == [cp] and cc(cp) == 0:
            f |= FLAG_FAST_NFKD
        if cc(fd[0]) == 0:
            f |= FLAG_BB_NFD
            if fd[0] not in second:
                f |= FLAG_BB_NFC
                if compose(reorder(fd)) == [cp]:
                    f |= FLAG_FAST_NFC
        if cc(kd[0]) == 0:
            f |= FLAG_BB_NFKD
            if kd[0] not in second:
                f |= FLAG_BB_NFKC
                if compose(reorder(kd)) == [cp]:
                    f |= FLAG_FAST_NFKC
        if cp in second:
            f |= FLAG_SECOND
        return f

    plain = (0, 0, 0, 0, 0)  # the record of an unassigned code point
    plain_flags = flags(0x10FFFF - 2)
    assert plain_flags == 0xFF
    pool = []
    pool_index = {}

    def put(seq):
        key = tuple(seq)
        if key not in pool_index:
            pool_index[key] = len(pool)
            pool.extend(packed(seq))
        return (pool_index[key] << 5) | len(seq)

    def packed(seq):
        return [(cc(x) << 24) | x for x in seq]

    comp_second, comp_result = [], []
    firsts = {}
    for (a, b), c in sorted(comp.items()):
        firsts.setdefault(a, []).append((b, c))

    records = OrderedDict()
    records[plain] = 0
    trie_vals = []
    for cp in range(TRIE_LIMIT):
        fd = full(cp, False)
        kd = full(cp, True)
        fdv = 0 if (fd == [cp] or is_hangul(cp)) else put(fd)
        kdv = 0 if (kd == [cp] or is_hangul(cp)) else put(kd)
        cv = 0
        if cp in firsts:
            cv = (len(comp_second) << 8) | len(firsts[cp])
            for b, c in firsts[cp]:
                comp_second.append(b)
                comp_result.append(c)
        rec = (cc(cp), 0, fdv, kdv, cv)
        if rec not in records:
            records[rec] = len(records)
        trie_vals.append(records[rec] | (flags(cp) << 16))
    # Nothing above the trie needs a record.
    for cp in list(ccc) + list(dm) + [b for (_, b) in comp]:
        assert cp < TRIE_LIMIT, hex(cp)

    bs = 1 << TRIE_SHIFT
    blocks = OrderedDict()
    index = []
    data = []
    for i in range(0, TRIE_LIMIT, bs):
        blk = tuple(trie_vals[i:i + bs])
        if blk not in blocks:
            blocks[blk] = len(data)
            data.extend(blk)
        index.append(blocks[blk])
    assert len(records) < 65536 and len(data) < 65536 and records[plain] == 0 and len(pool) < (1 << 27)
    assert max(len(v) for v in firsts.values()) < 256 and len(comp_second) < (1 << 24)

    recs = list(records)

    def arr(name, ty, vals, doc, per=16):
        rows = ",\n".join("    " + ", ".join(str(v) for v in vals[i:i + per]) for i in range(0, len(vals), per))
        return f"/// {doc}\npub static {name}: [{ty}; {name}_LEN] = [\n{rows},\n];\n"

    tables = [
        ("TRIE_INDEX", "u16", index, "Start in `TRIE_DATA` of the block of each 64 code points.", 16),
        ("TRIE_DATA", "u32", data, "`record | flags << 16` of each code point, by block.", 8),
        ("REC_CCC", "u8", [r[0] for r in recs], "Canonical combining class, by record.", 16),
        ("REC_FD", "u32", [r[2] for r in recs], "Canonical full decomposition, `(offset << 5) | len` in `POOL`.", 8),
        ("REC_KD", "u32", [r[3] for r in recs], "Compatibility full decomposition, `(offset << 5) | len` in `POOL`.", 8),
        ("REC_COMP", "u32", [r[4] for r in recs], "Composition pairs with this first character, `(start << 8) | count`.", 8),
        ("POOL", "u32", pool, "Decomposition sequences, each character as `ccc << 24 | code point`.", 8),
        ("COMP_SECOND", "u32", comp_second, "Second character of each composition pair.", 8),
        ("COMP_RESULT", "u32", comp_result, "Primary composite of each composition pair.", 8),
    ]
    consts = [("TRIE_SHIFT", "u32", TRIE_SHIFT), ("TRIE_LIMIT", "u32", hex(TRIE_LIMIT)),
              ("PLAIN_WORD", "u32", hex(plain_flags << 16))]
    for k, v in [("FAST_NFD", FLAG_FAST_NFD), ("FAST_NFKD", FLAG_FAST_NFKD), ("FAST_NFC", FLAG_FAST_NFC),
                 ("FAST_NFKC", FLAG_FAST_NFKC), ("BB_NFD", FLAG_BB_NFD), ("BB_NFKD", FLAG_BB_NFKD),
                 ("BB_NFC", FLAG_BB_NFC), ("BB_NFKC", FLAG_BB_NFKC), ("SECOND", FLAG_SECOND)]:
        consts.append(("FLAG_" + k, "u16", v))
    consts += [(t[0] + "_LEN", "usize", len(t[2])) for t in tables]
    o = ["// Generated by tools/gen_unicode.py from the Unicode Character Database",
         f"// {UNICODE_VERSION[0]}.{UNICODE_VERSION[1]}.{UNICODE_VERSION[2]}. Do not edit.",
         "use vstd::prelude::*;", "", "verus! {", "",
         f"/// {const_doc('UNICODE_VERSION')}",
         f"pub const UNICODE_VERSION: (u8, u8, u8) = {UNICODE_VERSION};"]
    for k, t, v in consts:
        o += [f"/// {const_doc(k)}", f"pub const {k}: {t} = {v};"]
    o += ["", "} // verus!", ""]
    o += [arr(*t) for t in tables]
    open(out, "w").write("\n".join(o))
    print(f"records {len(recs)}, trie index {len(index)}, data {len(data)}, pool {len(pool)}, pairs {len(comp_second)}",
          file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "src/unicode/tables.rs")
