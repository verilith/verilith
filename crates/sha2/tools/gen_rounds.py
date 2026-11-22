#!/usr/bin/env python3
"""Writes the eight-round loop bodies of src/compress.rs and
src/compress512.rs (between the GENERATED markers), so the register
renaming is not typed by hand. The two files get the same text: SHA-512's
rounds have SHA-256's shape, with other words and constants.

Round t updates d and h in place and the next round reads the variables
rotated by one: the call for round j of eight takes the names a..h rotated
right by j, and after eight rounds every name is back where it started.
The KW sections take K_t + W_t as one precomputed word (a vectorized
schedule's output). Each call is followed by the assertion that the eight names, in their
rotated order, are the working variables after round t + j + 1.

    tools/gen_rounds.py          rewrite both files
    tools/gen_rounds.py --check  fail if either would change
"""
import os
import sys

NAMES = "abcdefgh"
HERE = os.path.dirname(os.path.abspath(__file__))
PATHS = [os.path.join(HERE, "..", "src", f) for f in ("compress.rs", "compress512.rs")]


def rot(j):
    """The names playing a..h in round j of eight."""
    return [NAMES[(i - j) % 8] for i in range(8)]


def vars_of(ns):
    return "Vars { " + ", ".join(f"{f}: {n}" for f, n in zip(NAMES, ns)) + " }"


def body(kind, indent):
    out = []
    p = " " * indent
    for j in range(8):
        a, b, c, d, e, f, g, h = rot(j)
        tj = "t" if j == 0 else f"t + {j}"
        if kind == "SCHEDULED":
            out.append(f"{p}sched(w, {tj}, Ghost(m));")
        if kind == "KW":
            # K_t + W_t comes precomputed; K_t and W_t are only ghosts.
            out.append(f"{p}round_kw({a}, {b}, {c}, &mut {d}, {e}, {f}, {g}, &mut {h}, "
                       f"Ghost(K[({tj}) as int]), Ghost(spec::schedule(m, ({tj}) as int)), wk[{tj}]);")
        else:
            wv = f"w[({tj}) % 16]" if kind == "SCHEDULED" else f"w[{tj}]"
            out.append(f"{p}round({a}, {b}, {c}, &mut {d}, {e}, {f}, {g}, &mut {h}, K[{tj}], {wv});")
        out.append(f"{p}proof {{ lemma_round(v0, m, ({tj}) as nat); }}")
        out.append(f"{p}assert({vars_of(rot(j + 1))} == spec::rounds(v0, m, (t + {j + 1}) as nat));")
    return "\n".join(out)


def generate(src):
    for tag in ("ROUNDS", "SCHEDULED", "KW"):
        start = f"// GENERATED {tag} (tools/gen_rounds.py)\n"
        end = f"// END GENERATED {tag}\n"
        if start not in src:
            continue
        i = src.index(start) + len(start)
        k = src.index(end, i)
        line_start = src.rindex("\n", 0, k) + 1
        indent = k - line_start
        src = src[:i] + body(tag, indent) + "\n" + " " * indent + src[k:]
    return src


def main():
    for path in PATHS:
        src = open(path).read()
        new = generate(src)
        if "--check" in sys.argv:
            if new != src:
                sys.exit(f"{os.path.basename(path)} is out of date: run tools/gen_rounds.py")
            continue
        open(path, "w").write(new)


if __name__ == "__main__":
    main()
