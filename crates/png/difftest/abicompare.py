#!/usr/bin/env python3
"""Runs abitest-libpng and abitest-vpng on every file given, in every read
mode, with each transformation alone and with every pair of them (and some
larger sets), and prints each case where the two outputs differ.
Exits 1 if any differ, other than in the departures the README lists
("The libpng API"), which are counted apart:
  - an error in the image data is reported with a different message (the
    verified decoder says only that the data is invalid), and at the first
    row rather than at the row where libpng meets it, so the rows a user
    transform saw before the error differ;
  - the progressive reader delivers rows only once all the image data has
    arrived, so a file that ends inside it gets no rows;
  - a zlib stream damaged after the last byte the image needs (bad
    Adler-32, truncated end) is an error, where libpng warns and decodes;
  - the progressive reader does not warn of extra data after the image,
    and image data that is short or damaged is an error, where libpng
    gives the rows before the damage and goes on;
  - damaged compressed text or profiles are reported as "bad compressed
    data", not with zlib's message.

Usage: difftest/abicompare.py [--quick | --light] FILES..."""
import itertools, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

here = os.path.dirname(os.path.abspath(__file__))
L, V = os.path.join(here, "abitest-libpng"), os.path.join(here, "abitest-vpng")
args = sys.argv[1:]
quick = "--quick" in args
light = "--light" in args
files = [a for a in args if a not in ("--quick", "--light")]
bits = [1 << i for i in range(21)]
singles = [0] + bits
pairs = [a | b for a, b in itertools.combinations(bits, 2)]
rng = random.Random(1)
triples = [rng.choice(bits) | rng.choice(bits) | rng.choice(bits) | rng.choice(bits) for _ in range(40)]
common = [0x1 | 0x2 | 0x10 | 0x20, 0x1 | 0x4 | 0x10 | 0x80, 0x1 | 0x2, 0x1 | 0x8000, 0x1000 | 0x2000 | 0x800, 0x1 | 0x10 | 0x20 | 0x2]


def cases():
    for f in files:
        if light:
            # A few cases per file, for large sets of damaged files.
            for t in [0] + common:
                yield (f, "seq", t)
            yield (f, "img", 0)
            yield (f, "prog", 0, 7)
            continue
        for t in (singles + common if quick else singles + pairs + triples + common):
            yield (f, "seq", t)
        for m in ("dsp", "nil", "img", "png"):
            for t in singles + common:
                if m == "png" and t & ~0x1ffff:
                    continue
                yield (f, m, t)
        for t in [0] + common + ([] if quick else bits):
            for chunk in (1, 7, 4096):
                yield (f, "prog", t, chunk)


def run(c):
    f, m, t = c[0], c[1], c[2]
    a = [f, m, "%x" % t] + ([str(c[3])] if len(c) > 3 else [])
    def go(b):
        try:
            r = subprocess.run([b] + a, capture_output=True, timeout=60)
            return r.stdout.decode("latin-1") + ("" if r.returncode == 0 else "exit %d\n" % r.returncode)
        except subprocess.TimeoutExpired:
            return "timeout\n"
    x, y = go(L), go(V)
    return c, x, y


import re


def departure(c, x, y):
    """Whether x (libpng) and y (vpng) differ only in a listed departure."""
    def norm(t):
        # Damaged compressed text or profile: vpng's decompressor does not
        # say why.
        t = re.sub(r"^W (iTXt|zTXt|iCCP): (bad compressed data|truncated|incorrect data check|"
                   r"invalid [a-z /]+(\(libpng\))?|incorrect header check|unknown compression method|"
                   r"invalid code -- missing end-of-block|too many length or distance symbols)$",
                   r"W \1: <compressed data error>", t, flags=re.M)
        t = re.sub(r"ERR IDAT: .*", "ERR IDAT: <image data error>", t)
        # libpng's errors in the image data that carry no chunk name.
        # A file that ends inside the image data: libpng meets the end of
        # the file reading on.
        t = re.sub(r"ERR (Not enough image data|bad adaptive filter value|Extra compressed data|Read Error)$",
                   "ERR IDAT: <image data error>", t, flags=re.M)
        # An error in the image data stops both; the rows hashed before it
        # differ, because libpng meets the error part way through.
        if re.search(r"ERR IDAT: ", t):
            t = re.sub(r"stage \d hash .*", "stage", t)
            # Nor the warnings libpng gave about the data before the error
            # (vpng checks an IDAT chunk's CRC before decoding it), nor the
            # rows a user transform saw.
            t = re.sub(r"^(W IDAT: .*|W (Truncated compressed|Extra compress(ed|ion)) data in IDAT|user \d+ \d+)\n", "", t, flags=re.M)
        return t
    if norm(x) == norm(y):
        return True
    # vpng stops at damaged image data, or (progressive) waits for the
    # rest of it, where libpng warns, or gives the rows before the damage,
    # and goes on, perhaps to another error.
    xl, yl = norm(x).splitlines(), norm(y).splitlines()
    i = next((k for k in range(min(len(xl), len(yl))) if xl[k] != yl[k]), None)
    if i is not None:
        stop = yl[i] == "ERR IDAT: <image data error>" or (c[1] == "prog" and yl[i] == "done=0")
        went_on = re.match(r"W (IDAT: |Extra compress|Truncated compressed)|ERR |user \d+ \d+$", xl[i]) or (
            c[1] == "prog" and yl[i] != "done=0")
        if stop and went_on:
            return True
    damaged = (r"W .*(ADLER32 checksum mismatch|Truncated compressed data|incorrect data check|Not enough image data|"
               r"IDAT: invalid [a-z /]+)$")
    if "ERR IDAT: invalid image data" in y and "ERR" not in x and re.search(damaged, x, re.M):
        return True
    if c[1] == "prog":
        # libpng's progressive reader warns of extra image data per call
        # with new data, so how often depends on how the caller splits the
        # input; vpng does not give these warnings.
        x2 = re.sub(r"^W Extra compress(ed|ion) data in IDAT\n", "", x, flags=re.M)
        if norm(x2) == norm(y):
            return True
    if c[1] == "prog" and "ERR IDAT: invalid image data" in y and "ERR" not in x and "done=1" in x:
        # Image data too short or damaged: libpng's progressive reader
        # gives the rows it could decode and goes on.
        return True
    if c[1] == "prog" and "done=0" in y:
        # A file that ends inside or just after its image data: vpng has
        # given no rows (nor their warnings), where libpng gave the rows
        # it had and may have met an error in them.
        strip = lambda t: [l for l in t.splitlines()
                           if not re.match(r"hash |W (IDAT: |Extra compress|Truncated compressed)|user \d+ \d+|ERR (IDAT: |bad adaptive)|stage ", l)
                           and l != "done=0"]
        if strip(x) == strip(y):
            return True
    return False


n = bad = dep = 0
with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
    for c, x, y in ex.map(run, cases()):
        n += 1
        if x != y and departure(c, x, y):
            dep += 1
        elif x != y:
            bad += 1
            print("DIFF", " ".join(str(v) if not isinstance(v, int) or v < 2 else hex(v) for v in c))
            xl, yl = x.splitlines(), y.splitlines()
            for i in range(max(len(xl), len(yl))):
                a = xl[i] if i < len(xl) else ""
                b = yl[i] if i < len(yl) else ""
                if a != b:
                    print("   libpng: %s\n   vpng:   %s" % (a, b))
                    break
print("%d cases, %d differ, %d differ only in a listed departure" % (n, bad, dep))
sys.exit(1 if bad else 0)
