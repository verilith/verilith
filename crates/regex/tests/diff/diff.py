#!/usr/bin/env python3
"""Runs the same patterns and texts through RE2 and vregex and compares.

Usage: tests/diff/diff.py RE2REF VRE [--fuzz N] [--seed S] [--show]

RE2REF is tests/diff/re2ref.cc built against RE2; VRE is the `vre` example.
Fixed cases come from tests/diff/cases.txt (pattern TAB text, Python escapes
in the text). --fuzz adds N random cases.
"""
import random
import subprocess
import sys


def run(binary, cases):
    inp = "".join(p.hex() + " " + t.hex() + "\n" for p, t in cases)
    out = subprocess.run([binary], input=inp.encode(), capture_output=True, check=True).stdout.decode()
    return out.splitlines()


ATOMS = ["a", "b", "c", "ab", ".", "[ab]", "[^a]", r"\d", r"\w", r"\s", r"\b", r"\B", "^", "$", "é", r"\pL", "[a-cé]",
         "()", "", "x", "(?i)a", "(?s).", "(?m)^", "(?m)$", r"\A", r"\z", "k", r"\x{212A}", "[[:alpha:]]", r"\PL",
         "[^\\n]", "0", " "]
TEXT = ["a", "b", "c", "ab", "x", "é", " ", "\n", "0", "A", "K", "K", "_", "ß", "\U0001F600", "-"]


def gen(rng, depth):
    r = rng.random()
    if depth <= 0 or r < 0.3:
        return rng.choice(ATOMS)
    if r < 0.5:
        return gen(rng, depth - 1) + gen(rng, depth - 1)
    if r < 0.62:
        return gen(rng, depth - 1) + "|" + gen(rng, depth - 1)
    if r < 0.75:
        return "(" + gen(rng, depth - 1) + ")"
    if r < 0.8:
        return "(?:" + gen(rng, depth - 1) + ")"
    op = rng.choice(["*", "+", "?", "*?", "+?", "??", "{2}", "{1,2}", "{0,2}", "{2,}", "{1,3}?", "{0}", "{0,1}"])
    return "(?:" + gen(rng, depth - 1) + ")" + op if rng.random() < 0.5 else "(" + gen(rng, depth - 1) + ")" + op


SYN = list("ab01(){}[]|*+?^$.\\-,:<>PpQEdDwWsSbBAzxiUms=!") + ["é", "\\p{L}", "\\pN", "[:alpha:]", "(?", "{2,3}", "\\x{", "\\0", "(?P<n>", "(?i)", "[^"]


def gen_syntax(rng):
    return "".join(rng.choice(SYN) for _ in range(rng.randint(1, 10)))


def main():
    re2ref, vre = sys.argv[1], sys.argv[2]
    cases = []
    for line in open(__file__.rsplit("/", 1)[0] + "/cases.txt", encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        p, _, t = line.partition("\t")
        cases.append((p.encode(), t.encode().decode("unicode_escape").encode("latin-1")))
    if "--fuzz" in sys.argv:
        n = int(sys.argv[sys.argv.index("--fuzz") + 1])
        seed = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 1
        rng = random.Random(seed)
        for _ in range(n):
            p = gen_syntax(rng) if rng.random() < 0.3 else gen(rng, rng.randint(1, 5))
            t = "".join(rng.choice(TEXT) for _ in range(rng.randint(0, 8)))
            cases.append((p.encode(), t.encode()))
    a = run(re2ref, cases)
    b = run(vre, cases)
    assert len(a) == len(b) == len(cases)
    bad = 0
    big = 0
    for (p, t), x, y in zip(cases, a, b):
        if y == "TOOBIG" or x == "TOOBIG":
            big += 1
            continue
        if "--show" in sys.argv:
            print(f"{p!r} on {t!r}: {y}")
        if x != y:
            bad += 1
            if bad <= 40:
                print(f"DIFF {p.decode()!r} on {t!r}: re2 {x} | vregex {y}")
    print(f"{len(cases)} cases, {bad} differ, {big} too big for vregex")
    sys.exit(1 if bad else 0)


main()
