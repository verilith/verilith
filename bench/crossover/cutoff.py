#!/usr/bin/env python3
"""Chooses a cutoff from `mca.py` output: `a` for n >= C, `b` below.

    python3 cutoff.py lat results/crc512-vs-crc256.tsv
    python3 cutoff.py tput results/memcpy-vs-wild-avx512.tsv results/memcpy-vs-wild-avx2.tsv

For each candidate C (each n in the tables), the cost of the choice at
every n and CPU model is divided by the cheaper kernel's there. The cutoff
printed is the one whose worst such ratio is smallest (ties: the smaller
mean), that is, the one that is never far from the better kernel on any of
the modelled CPUs.
"""
import sys


def load(paths):
    rows = {}
    for p in paths:
        cpus = None
        for l in open(p):
            l = l.rstrip("\n")
            if l.startswith("n\t"):
                cpus = l.split("\t")[3:]
                continue
            if not l[:1].isdigit():
                continue
            f = l.split("\t")
            for i, c in enumerate(cpus):
                lat, tput = f[3 + i].split(" ")
                rows.setdefault(int(f[0]), {})[c] = tuple(map(float, lat.split("/") + tput.split("/")))
    return rows


def main():
    k = {"lat": 0, "tput": 2}[sys.argv[1]]
    rows = load(sys.argv[2:])
    ns = sorted(rows)
    res = []
    for c in ns + [ns[-1] + 1]:
        rs = []
        for n in ns:
            for v in rows[n].values():
                a, b = v[k], v[k + 1]
                rs.append((a if n >= c else b) / min(a, b))
        res.append((max(rs), sum(rs) / len(rs), c))
    for worst, mean, c in res:
        print(f"C={c}\tworst {worst:.3f}\tmean {mean:.4f}")
    worst, mean, c = min(res)
    print(f"# best: C={c} (worst {worst:.3f}x, mean {mean:.4f}x of the better kernel)")


if __name__ == "__main__":
    main()
