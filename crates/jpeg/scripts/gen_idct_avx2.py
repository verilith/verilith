#!/usr/bin/env python3
"""Prints the generated part of src/idct_avx2.rs: one pass of the inverse
DCT over eight rows in the spread layout, and its proof, lane by lane,
from `lemma_vd16_lane` (src/idct16.rs).

A row of eight 16-bit values is spread over a 256-bit vector as
[c0 c1 c2 c3 * * * * | c4 c5 c6 c7 * * * *]: interleaving two such rows
(`vpunpcklwd`) puts the pair for column m in 32-bit lane m, and one
`vpmaddwd` multiplies both by their constants and adds them. A pass is 5
interleaves, 10 multiply-adds and 16 additions for all eight columns, in
the order of the steps `lemma_vd16_lane` takes."""

# The pass, as `lemma_vd16_lane` takes its steps: (kind, args).
X = lambda i: ("x%d" % i, "t%d[m]" % i)
PZ3 = ("pz3", "(t7[m] + t3[m])")
PZ4 = ("pz4", "(t5[m] + t1[m])")
ST = [
    ("dot", X(2), 10703, X(6), 4433),
    ("dot", X(2), 4433, X(6), -10704),
    ("dot", X(0), 8192, X(4), 8192),
    ("dot", X(0), 8192, X(4), -8192),
    ("add", 3, 1),
    ("sub", 3, 1),
    ("add", 4, 2),
    ("sub", 4, 2),
    ("dot", PZ3, -6436, PZ4, 9633),
    ("dot", PZ3, 9633, PZ4, 6437),
    ("dot", X(7), -4927, X(1), -7373),
    ("dot", X(7), -7373, X(1), 4926),
    ("dot", X(5), -4176, X(3), -20995),
    ("dot", X(5), -20995, X(3), 4177),
    ("add", 11, 9),
    ("add", 13, 10),
    ("add", 14, 9),
    ("add", 12, 10),
    ("add", 5, 18),
    ("add", 7, 17),
    ("add", 8, 16),
    ("add", 6, 15),
    ("sub", 6, 15),
    ("sub", 8, 16),
    ("sub", 7, 17),
    ("sub", 5, 18),
]
OUTS = list(range(19, 27))
V = "__m256i"


def kconst(c0, c1):
    x = (c0 & 0xFFFF) | ((c1 & 0xFFFF) << 16)
    return x


o = []
P = o.append
P("/// One pass over eight rows in the spread layout: 32-bit lane `m` of")
P("/// result `k` is output `k` of the pass over column `m`, modulo 2^32.")
P("#[inline(always)]")
P("#[verifier::spinoff_prover]")
P("#[verifier::rlimit(100)]")
P("fn pass8(" + ", ".join("x%d: %s" % (i, V) for i in range(8)) + ", " + ", ".join("Ghost(t%d): Ghost<Seq<int>>" % i for i in range(8)) + ") -> (r: (" + ", ".join([V] * 8) + "))")
P("    requires")
P("        avx2(),")
for i in range(8):
    P("        xs(x%d, t%d)," % (i, i))
P("        forall|m: int| 0 <= m < 8 ==> -0x8000 <= (#[trigger] t7[m]) + t3[m] < 0x8000,")
P("        forall|m: int| 0 <= m < 8 ==> -0x8000 <= (#[trigger] t5[m]) + t1[m] < 0x8000,")
P("    ensures")
for k in range(8):
    P("        py(r.%d, t0, t1, t2, t3, t4, t5, t6, t7, %d)," % (k, k))
P("{")
P("    hide(idct_1d);")
P("    hide(cong);")
P("    hide(w32);")
P("    let pz3 = addy(x7, x3, Ghost(t7), Ghost(t3));")
P("    let pz4 = addy(x5, x1, Ghost(t5), Ghost(t1));")
for n, s in enumerate(ST, 1):
    if s[0] == "dot":
        P("    let v%d = dx(%s, %s, kp(%d, %d), Ghost(%d), Ghost(%d));" % (n, s[1][0], s[3][0], s[2], s[4], s[2], s[4]))
    else:
        P("    let v%d = %s(v%d, v%d);" % (n, "ad" if s[0] == "add" else "sb", s[1], s[2]))
P("    proof {")
for k in range(8):
    P("        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v%d, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[%d]) by {" % (OUTS[k], k))
    P("            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);")
    P("            lemma_vd16_lane(" + ", ".join("t%d[m]" % i for i in range(8)) + ", " + ", ".join("w32(v%d, m)" % n for n in range(1, len(ST) + 1)) + ");")
    P("        }")
P("    }")
P("    (" + ", ".join("v%d" % n for n in OUTS) + ")")
P("}")
print("\n".join(o))
