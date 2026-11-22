#!/usr/bin/env python3
"""Prints the generated part of src/idct16.rs: one pass of the inverse DCT
over 16-bit rows, as libjpeg-turbo's NEON code has it. Each product is a
widening multiply of a 16-bit lane by a constant held in a lane of a table
vector, added to another product or to a finished sum in the same
instruction; the eight results are 32-bit lanes, the low four columns and
the high four separately. Beside each lane value `sN` the proof keeps the
exact value `gN` and the number `eN` of times 2^32 separates them (as
gen_idct_neon.py does). The text between the `// BEGIN generated` and
`// END generated` lines of src/idct16.rs is this script's output.

Two passes come out, each for the low and the high half: `vp16_lo` and
`vp16_hi` for eight inputs, `vp16s_lo` and `vp16s_hi` for inputs 4 to 7
zero. With them, the bound `lemma_pass_wbound` on a pass's results from
the sum of its inputs' magnitudes, and `lemma_pass_shift16`: 16 more in
input 0 is 2^17 more in every result."""
import random
import sys

M = "0x1_0000_0000"
V = "uint8x16_t"
# The table of constants: lane L of vector B holds K[8 * B + L].
K = [4433, -10704, 10703, 8192, -6436, 9633, 6437, -4927, -7373, -4176, -20995, 4177, 4926, 2260, -11362, -2259, 11363]
T = ", ".join("t%d" % i for i in range(8))


# --- The pass as jidctint.c writes it: what `lemma_pass_link` names. -------
def cbuild():
    st = []

    def emit(kind, a, b=None, c=None):
        st.append((kind, a, b, c))
        return len(st)

    add = lambda a, b: emit("add", a, b)
    sub = lambda a, b: emit("sub", a, b)
    mul = lambda a, c: emit("mul", a, c=c)
    x = [-i for i in range(8)]
    z1 = mul(add(x[2], x[6]), 4433)
    t2 = add(z1, mul(x[6], -15137))
    t3 = add(z1, mul(x[2], 6270))
    t0 = mul(add(x[0], x[4]), 8192)
    t1 = mul(sub(x[0], x[4]), 8192)
    t10, t13, t11, t12 = add(t0, t3), sub(t0, t3), add(t1, t2), sub(t1, t2)
    z1, z2, z3, z4 = add(x[7], x[1]), add(x[5], x[3]), add(x[7], x[3]), add(x[5], x[1])
    z5 = mul(add(z3, z4), 9633)
    z1, z2 = mul(z1, -7373), mul(z2, -20995)
    z3, z4 = add(mul(z3, -16069), z5), add(mul(z4, -3196), z5)
    u0 = add(add(mul(x[7], 2446), z1), z3)
    u1 = add(add(mul(x[5], 16819), z2), z4)
    u2 = add(add(mul(x[3], 25172), z2), z3)
    u3 = add(add(mul(x[1], 12299), z1), z4)
    outs = [add(t10, u3), add(t11, u2), add(t12, u1), add(t13, u0), sub(t13, u0), sub(t12, u1), sub(t11, u2), sub(t10, u3)]
    return st, outs


csteps, couts = cbuild()
CN = len(csteps)


def ceval(x):
    v = {}
    g = lambda k: x[-k] if k <= 0 else v[k]
    for n, (kind, a, b, c) in enumerate(csteps, 1):
        v[n] = g(a) + g(b) if kind == "add" else g(a) - g(b) if kind == "sub" else g(a) * c
    return [v[o] for o in couts]


def canon(o, inp, p="c"):
    """Lets `c1`.. for the exact values of the pass as jidctint.c writes it,
    over the inputs named by `inp`, and the call that links them to
    `idct_1d`."""
    cn = lambda k: inp(-k) if k <= 0 else "%s%d" % (p, k)
    for n, (kind, a, b, c) in enumerate(csteps, 1):
        if kind == "add":
            o.append("    let %s%d = %s + %s;" % (p, n, cn(a), cn(b)))
        elif kind == "sub":
            o.append("    let %s%d = %s - %s;" % (p, n, cn(a), cn(b)))
        else:
            o.append("    let %s%d = %s * (%d);" % (p, n, cn(a), c))
    o.append("    lemma_pass_link(" + ", ".join(inp(i) for i in range(8)) + ", " + ", ".join("%s%d" % (p, i) for i in range(1, CN + 1)) + ");")


# --- The pass on 16-bit rows. ----------------------------------------------
# A 16-bit operand is (vector name, exact value over t0..t7, value function).
def X(i):
    return ("x%d" % i, "t%d" % i, lambda x: x[i])


PE = ("pe", "(t0 + t4)", lambda x: x[0] + x[4])
PD = ("pd", "(t0 - t4)", lambda x: x[0] - x[4])
PZ3 = ("pz3", "(t7 + t3)", lambda x: x[7] + x[3])
PZ4 = ("pz4", "(t5 + t1)", lambda x: x[5] + x[1])


class Pass:
    def __init__(self):
        self.st = []

    def emit(self, *s):
        self.st.append(s)
        return len(self.st)

    def mul(self, a, c):
        return self.emit("mul", a, c)

    def mla(self, acc, a, c):
        return self.emit("mla", acc, a, c)

    def add(self, a, b):
        return self.emit("add", a, b)

    def sub(self, a, b):
        return self.emit("sub", a, b)

    def finish(self, t10, t11, t12, t13, u0, u1, u2, u3):
        self.outs = [self.add(t10, u3), self.add(t11, u2), self.add(t12, u1), self.add(t13, u0), self.sub(t13, u0), self.sub(t12, u1), self.sub(t11, u2), self.sub(t10, u3)]

    def eval(self, x):
        v = {}
        for n, s in enumerate(self.st, 1):
            if s[0] == "mul":
                v[n] = s[1][2](x) * s[2]
            elif s[0] == "mla":
                v[n] = v[s[1]] + s[2][2](x) * s[3]
            elif s[0] == "add":
                v[n] = v[s[1]] + v[s[2]]
            else:
                v[n] = v[s[1]] - v[s[2]]
        return [v[o] for o in self.outs]


def full():
    p = Pass()
    t2 = p.mla(p.mul(X(2), 4433), X(6), -10704)
    t3 = p.mla(p.mul(X(2), 10703), X(6), 4433)
    t0, t1 = p.mul(PE, 8192), p.mul(PD, 8192)
    t10, t13, t11, t12 = p.add(t0, t3), p.sub(t0, t3), p.add(t1, t2), p.sub(t1, t2)
    y3 = p.mla(p.mul(PZ3, -6436), PZ4, 9633)
    y4 = p.mla(p.mul(PZ3, 9633), PZ4, 6437)
    u0 = p.mla(p.mla(y3, X(7), -4927), X(1), -7373)
    u1 = p.mla(p.mla(y4, X(5), -4176), X(3), -20995)
    u2 = p.mla(p.mla(y3, X(3), 4177), X(5), -20995)
    u3 = p.mla(p.mla(y4, X(1), 4926), X(7), -7373)
    p.finish(t10, t11, t12, t13, u0, u1, u2, u3)
    return p


def sparse():
    p = Pass()
    t2, t3, t0 = p.mul(X(2), 4433), p.mul(X(2), 10703), p.mul(X(0), 8192)
    t10, t13, t11, t12 = p.add(t0, t3), p.sub(t0, t3), p.add(t0, t2), p.sub(t0, t2)
    u0 = p.mla(p.mul(X(1), 2260), X(3), -6436)
    u1 = p.mla(p.mul(X(3), -11362), X(1), 6437)
    u2 = p.mla(p.mul(X(3), -2259), X(1), 9633)
    u3 = p.mla(p.mul(X(1), 11363), X(3), 9633)
    p.finish(t10, t11, t12, t13, u0, u1, u2, u3)
    return p


rnd = random.Random(1)
for _ in range(200):
    x = [rnd.randint(-40000, 40000) for _ in range(8)]
    assert full().eval(x) == ceval(x)
    x[4:] = [0, 0, 0, 0]
    assert sparse().eval(x) == ceval(x)

# The weight of each input in each result, and the largest.
W = [[ceval([1 if j == m else 0 for j in range(8)])[k] for m in range(8)] for k in range(8)]
WMAX = max(abs(w) for r in W for w in r)
assert WMAX == 11363


def lane(o, name, p, zero):
    N = len(p.st)
    ins = range(4) if zero else range(8)
    tv = lambda i: "t%d" % i if i in ins else "0int"
    o.append("/// One lane of `%s_lo` and `%s_hi`: the lane values `s1`..`s%d`, each made" % (name, name, N))
    o.append("/// from earlier ones modulo 2^32, end congruent to `idct_1d` of the exact")
    o.append("/// inputs%s." % (", inputs 4 to 7 being zero" if zero else ""))
    o.append("#[verifier::rlimit(60)]")
    o.append("#[verifier::spinoff_prover]")
    o.append("proof fn lemma_%s_lane(" % name + ", ".join("t%d: int" % i for i in ins) + ", " + ", ".join("s%d: int" % i for i in range(1, N + 1)) + ")")
    o.append("    requires")
    for n, s in enumerate(p.st, 1):
        if s[0] == "mul":
            o.append("        rmul(s%d, %s, %d)," % (n, s[1][1], s[2]))
        elif s[0] == "mla":
            o.append("        rmla(s%d, s%d, %s, %d)," % (n, s[1], s[2][1], s[3]))
        elif s[0] == "add":
            o.append("        radd(s%d, s%d, s%d)," % (n, s[1], s[2]))
        else:
            o.append("        rsub(s%d, s%d, s%d)," % (n, s[1], s[2]))
    o.append("    ensures")
    for k in range(8):
        o.append("        cong(s%d, idct_1d(seq![%s])[%d])," % (p.outs[k], ", ".join(tv(i) for i in range(8)), k))
    o.append("{")
    o.append("    hide(idct_1d);")
    for r in ("radd", "rsub", "rmul", "rmla"):
        o.append("    reveal(%s);" % r)
    for n, s in enumerate(p.st, 1):
        if s[0] == "mul":
            o.append("    let g%d = %s * (%d);" % (n, s[1][1], s[2]))
            o.append("    let e%d = -((%s * (%d)) / %s);" % (n, s[1][1], s[2], M))
        elif s[0] == "mla":
            o.append("    let g%d = g%d + %s * (%d);" % (n, s[1], s[2][1], s[3]))
            o.append("    let e%d = e%d - (s%d + %s * (%d)) / %s;" % (n, s[1], s[1], s[2][1], s[3], M))
        elif s[0] == "add":
            o.append("    let g%d = g%d + g%d;" % (n, s[1], s[2]))
            o.append("    let e%d = e%d + e%d - (s%d + s%d) / %s;" % (n, s[1], s[2], s[1], s[2], M))
        else:
            o.append("    let g%d = g%d - g%d;" % (n, s[1], s[2]))
            o.append("    let e%d = e%d - e%d + 1 - (s%d - s%d + %s) / %s;" % (n, s[1], s[2], s[1], s[2], M, M))
        o.append("    assert(s%d == g%d + %s * e%d);" % (n, n, M, n))
    canon(o, tv)
    for k in range(8):
        o.append("    assert(g%d == c%d);" % (p.outs[k], couts[k]))
        o.append("    lemma_cong_k(s%d, g%d, e%d);" % (p.outs[k], p.outs[k], p.outs[k]))
    o.append("}")
    o.append("")


def vec(o, name, p, zero, half):
    N = len(p.st)
    off = 0 if half == "lo" else 4
    ins = range(4) if zero else range(8)
    pre = [] if zero else [PE, PD, PZ3, PZ4]
    o.append("/// One pass over the %s four columns of 16-bit rows%s: each" % ("low" if off == 0 else "high", ", rows 4 to 7 being zero" if zero else ""))
    o.append("/// result is right modulo 2^32, lane by lane.")
    o.append("#[inline(always)]")
    args = ["x%d: %s" % (i, V) for i in ins] + ["%s: %s" % (q[0], V) for q in pre] + ["k0: %s" % V, "k1: %s" % V, "k2: %s" % V]
    args += ["Ghost(t%d): Ghost<Seq<int>>" % i for i in range(8)]
    o.append("fn %s_%s(" % (name, half) + ", ".join(args) + ") -> (r: (" + ", ".join([V] * 8) + "))")
    o.append("    requires")
    o.append("        neon(),")
    for i in ins:
        o.append("        x16(x%d, t%d)," % (i, i))
    if zero:
        for i in range(4, 8):
            o.append("        zero8(t%d)," % i)
    else:
        o.append("        x16(pe, vsum(t0, t4)),")
        o.append("        x16(pd, vdif(t0, t4)),")
        o.append("        x16(pz3, vsum(t7, t3)),")
        o.append("        x16(pz4, vsum(t5, t1)),")
    o.append("        kok(k0, k1, k2),")
    o.append("    ensures")
    for k in range(8):
        o.append("        pc16(r.%d, %s, %d, %d)," % (k, T, off, k))
    o.append("{")
    o.append("    hide(idct_1d);")
    o.append("    hide(cong);")
    o.append("    hide(l32);")
    ml, al = ("mlo", "alo") if off == 0 else ("mhi", "ahi")
    for n, s in enumerate(p.st, 1):
        if s[0] == "mul":
            b, l = divmod(K.index(s[2]), 8)
            o.append("    let v%d = %s::<%d>(%s, k%d);" % (n, ml, l, s[1][0], b))
        elif s[0] == "mla":
            b, l = divmod(K.index(s[3]), 8)
            o.append("    let v%d = %s::<%d>(v%d, %s, k%d);" % (n, al, l, s[1], s[2][0], b))
        elif s[0] == "add":
            o.append("    let v%d = vadd(v%d, v%d);" % (n, s[1], s[2]))
        else:
            o.append("    let v%d = vsub(v%d, v%d);" % (n, s[1], s[2]))
    o.append("    proof {")
    for k in range(8):
        o.append("        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v%d, i), idct_1d(col(%s, %d + i))[%d]) by {" % (p.outs[k], T, off, k))
        if not zero:
            o.append("            assert(vsum(t0, t4)[%d + i] == t0[%d + i] + t4[%d + i] && vdif(t0, t4)[%d + i] == t0[%d + i] - t4[%d + i]);" % ((off,) * 6))
            o.append("            assert(vsum(t7, t3)[%d + i] == t7[%d + i] + t3[%d + i] && vsum(t5, t1)[%d + i] == t5[%d + i] + t1[%d + i]);" % ((off,) * 6))
        o.append("            lemma_%s_lane(" % name + ", ".join("t%d[%d + i]" % (j, off) for j in ins) + ", " + ", ".join("l32(v%d, i)" % n for n in range(1, N + 1)) + ");")
        if zero:
            o.append("            assert(col(%s, %d + i) =~= seq![t0[%d + i], t1[%d + i], t2[%d + i], t3[%d + i], 0int, 0int, 0int, 0int]);" % ((T,) + (off,) * 5))
        o.append("        }")
    o.append("    }")
    o.append("    (" + ", ".join("v%d" % p.outs[k] for k in range(8)) + ")")
    o.append("}")
    o.append("")


o = []
for name, p, zero in (("vp16", full(), False), ("vp16s", sparse(), True)):
    lane(o, name, p, zero)
    vec(o, name, p, zero, "lo")
    vec(o, name, p, zero, "hi")
    print("%s: %d steps a half" % (name, len(p.st)), file=sys.stderr)

o.append("/// A result of a pass is at most %d times the sum of its inputs'" % WMAX)
o.append("/// magnitudes.")
o.append("#[verifier::rlimit(60)]")
o.append("#[verifier::spinoff_prover]")
o.append("pub proof fn lemma_pass_wbound(" + ", ".join("t%d: int" % i for i in range(8)) + ", " + ", ".join("a%d: int" % i for i in range(8)) + ")")
o.append("    requires")
for i in range(8):
    o.append("        -a%d <= t%d <= a%d," % (i, i, i))
o.append("    ensures")
S = " + ".join("a%d" % i for i in range(8))
for k in range(8):
    o.append("        -%d * (%s) <= idct_1d(seq![%s])[%d] <= %d * (%s)," % (WMAX, S, T, k, WMAX, S))
o.append("{")
o.append("    hide(idct_1d);")
canon(o, lambda i: "t%d" % i)
for k in range(8):
    o.append("    assert(c%d == %s);" % (couts[k], " + ".join("(%d) * t%d" % (W[k][m], m) for m in range(8))))
o.append("}")
o.append("")
o.append("/// 16 more in input 0 is 2^17 more in every result of a pass.")
o.append("pub proof fn lemma_pass_shift16(" + ", ".join("t%d: int" % i for i in range(8)) + ")")
o.append("    ensures")
for k in range(8):
    o.append("        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[%d] == idct_1d(seq![%s])[%d] + 131072," % (k, T, k))
o.append("{")
o.append("    hide(idct_1d);")
canon(o, lambda i: "t%d" % i)
canon(o, lambda i: "(t0 + 16)" if i == 0 else "t%d" % i, "b")
for k in range(8):
    o.append("    assert(b%d == c%d + 131072);" % (couts[k], couts[k]))
o.append("}")
print("\n".join(o))
