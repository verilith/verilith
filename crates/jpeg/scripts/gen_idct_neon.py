#!/usr/bin/env python3
"""Prints the generated part of src/idct_neon.rs: one pass of the inverse
DCT on four 32-bit lanes, and the per-lane bookkeeping its proof needs (as
in gen_pass_w.py: beside each lane value `sN` the exact value `gN` and the
number `eN` of times 2^32 separates them). The text between the
`// BEGIN generated` and `// END generated` lines of src/idct_neon.rs is
this script's output.

Two families come out. `vpass` and `vpass4` compute the pass itself, for
the first pass. `vpassf` and `vpass4f` are for the second pass: 16 is
added to input 0 first, which every output holds 8192 times, so each
output is `pass + 2^17`, the rounding add that the final range limit would
otherwise do on all 64 results."""
import sys

M = "0x1_0000_0000"
steps = []  # (kind, a, b, c)


def emit(kind, a, b=None, c=None):
    steps.append((kind, a, b, c))
    return len(steps)


add = lambda a, b: emit("add", a, b)
sub = lambda a, b: emit("sub", a, b)
mul = lambda a, c: emit("mul", a, c=c)
addk = lambda a, c: emit("addk", a, c=c)


def cbuild(x):
    """The pass as jidctint.c writes it: what `lemma_pass_link` names."""
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
    return [add(t10, u3), add(t11, u2), add(t12, u1), add(t13, u0), sub(t13, u0), sub(t12, u1), sub(t11, u2), sub(t10, u3)]


def build(x, sc, off):
    """The same pass with the constants distributed, as libjpeg-turbo's
    NEON code has it: every product is added to another product or to a
    finished sum, so each is one multiply-accumulate and no value has to be
    copied before it is overwritten. With `sc` 16, the scaled pass."""
    x = list(x)
    if off:
        x[0] = addk(x[0], 16)
    t2 = add(mul(x[2], sc * 4433), mul(x[6], sc * (4433 - 15137)))
    t3 = add(mul(x[2], sc * (4433 + 6270)), mul(x[6], sc * 4433))
    t0 = mul(add(x[0], x[4]), sc * 8192)
    t1 = mul(sub(x[0], x[4]), sc * 8192)
    t10, t13, t11, t12 = add(t0, t3), sub(t0, t3), add(t1, t2), sub(t1, t2)
    z3, z4 = add(x[7], x[3]), add(x[5], x[1])
    y3 = add(mul(z3, sc * (9633 - 16069)), mul(z4, sc * 9633))
    y4 = add(mul(z3, sc * 9633), mul(z4, sc * (9633 - 3196)))
    u0 = add(add(mul(x[7], sc * (2446 - 7373)), mul(x[1], sc * -7373)), y3)
    u1 = add(add(mul(x[5], sc * (16819 - 20995)), mul(x[3], sc * -20995)), y4)
    u2 = add(add(mul(x[3], sc * (25172 - 20995)), mul(x[5], sc * -20995)), y3)
    u3 = add(add(mul(x[1], sc * (12299 - 7373)), mul(x[7], sc * -7373)), y4)
    return [add(t10, u3), add(t11, u2), add(t12, u1), add(t13, u0), sub(t13, u0), sub(t12, u1), sub(t11, u2), sub(t10, u3)]


couts = cbuild([-i for i in range(8)])
csteps = steps
CN = len(csteps)
V = "uint8x16_t"
T = ", ".join("t%d" % i for i in range(8))


def nm(p, k):  # name of value k with prefix p: inputs a/t/x, steps s/g/e/v
    if k <= 0:
        return {"s": "a", "g": "t", "e": "f", "v": "x"}[p] + str(-k)
    return p + str(k)


def canon(o, inp):
    """Lets `c1`.. for the exact values of the pass as jidctint.c writes it,
    over the inputs named by `inp`, and the call that links them to
    `idct_1d`."""
    cn = lambda k: inp(-k) if k <= 0 else "c%d" % k
    for n, (kind, a, b, c) in enumerate(csteps, 1):
        if kind == "add":
            o.append("    let c%d = %s + %s;" % (n, cn(a), cn(b)))
        elif kind == "sub":
            o.append("    let c%d = %s - %s;" % (n, cn(a), cn(b)))
        else:
            o.append("    let c%d = %s * (%d);" % (n, cn(a), c))
    o.append("    lemma_pass_link(" + ", ".join(inp(i) for i in range(8)) + ", " + ", ".join("c%d" % i for i in range(1, CN + 1)) + ");")


def req(o, n, kind, sa, sb, c):
    if kind == "add":
        o.append("        radd(s%d, %s, %s)," % (n, sa, sb))
    elif kind == "sub":
        o.append("        rsub(s%d, %s, %s)," % (n, sa, sb))
    elif kind == "addk":
        o.append("        radd(s%d, %s, %d)," % (n, sa, c))
    else:
        o.append("        rmul(s%d, %s, %d)," % (n, sa, c % (1 << 32)))


def book(o, n, kind, g, e, sa, sb, ga, gb, ea, eb, c):
    """The exact value and the multiple of 2^32 of step `n`."""
    if kind == "add":
        o.append("    let %s%d = %s + %s;" % (g, n, ga, gb))
        o.append("    let %s%d = %s + %s - (%s + %s) / %s;" % (e, n, ea, eb, sa, sb, M))
    elif kind == "sub":
        o.append("    let %s%d = %s - %s;" % (g, n, ga, gb))
        o.append("    let %s%d = %s - %s + 1 - (%s - %s + %s) / %s;" % (e, n, ea, eb, sa, sb, M, M))
    elif kind == "addk":
        o.append("    let %s%d = %s + %d;" % (g, n, ga, c))
        o.append("    let %s%d = %s - (%s + %d) / %s;" % (e, n, ea, sa, c, M))
    else:
        cu = c % (1 << 32)
        o.append("    let %s%d = %s * (%d);" % (g, n, ga, c))
        o.append("    let %s%d = %s * %d%s - (%s * %d) / %s;" % (e, n, ea, cu, " + " + ga if c < 0 else "", sa, cu, M))
    o.append("    assert(s%d == %s%d + %s * %s%d);" % (n, g, n, M, e, n))


def code(o, n, kind, va, vb, c, sc):
    if kind == "add":
        o.append("    let v%d = vadd(%s, %s);" % (n, va, vb))
    elif kind == "sub":
        o.append("    let v%d = vsub(%s, %s);" % (n, va, vb))
    elif kind == "addk":
        o.append("    let v%d = vaddk(%s, %du32);" % (n, va, c))
    elif c == 8192:
        o.append("    let v%d = vshl13(%s);" % (n, va))
    elif c == 131072:
        o.append("    let v%d = vshl17(%s);" % (n, va))
    else:
        o.append("    let v%d = vmulc(%s, %du32);" % (n, va, c % (1 << 32)))


def family(o, sfx, sc, off):
    global steps
    steps = []
    outs = build([-i for i in range(8)], sc, off)
    N = len(steps)
    assert sc == 1
    what = "idct_1d + 2^17" if off else "idct_1d"
    fin = (lambda e: "%s + 131072" % e) if off else (lambda e: e)
    pc = "pcongf" if off else "pcong"

    o.append("/// One lane of `vpass%s`: the lane values `s1`..`s%d`, each made from earlier" % (sfx, N))
    o.append("/// ones modulo 2^32, end congruent to `%s` of the exact inputs." % what)
    o.append("#[verifier::rlimit(60)]")
    o.append("#[verifier::spinoff_prover]")
    o.append("proof fn lemma_pass_lane%s(" % sfx + ", ".join("a%d: int" % i for i in range(8)) + ", " + ", ".join("t%d: int" % i for i in range(8)) + ", " + ", ".join("s%d: int" % i for i in range(1, N + 1)) + ")")
    o.append("    requires")
    for i in range(8):
        o.append("        cong(a%d, t%d)," % (i, i))
    for n, (kind, a, b, c) in enumerate(steps, 1):
        req(o, n, kind, nm("s", a), nm("s", b) if b is not None else None, c)
    o.append("    ensures")
    for k in range(8):
        o.append("        cong(s%d, %s)," % (outs[k], fin("idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[%d]" % k)))
    o.append("{")
    o.append("    hide(idct_1d);")
    o.append("    reveal(radd);")
    o.append("    reveal(rsub);")
    o.append("    reveal(rmul);")
    for i in range(8):
        o.append("    let f%d = (a%d - t%d) / %s;" % (i, i, i, M))
        o.append("    assert(a%d == t%d + %s * f%d);" % (i, i, M, i))
    for n, (kind, a, b, c) in enumerate(steps, 1):
        nb = lambda p: nm(p, b) if b is not None else None
        book(o, n, kind, "g", "e", nm("s", a), nb("s"), nm("g", a), nb("g"), nm("e", a), nb("e"), c)
    canon(o, lambda i: "t%d" % i)
    for k in range(8):
        o.append("    assert(g%d == %s);" % (outs[k], fin("c%d" % couts[k])))
        o.append("    lemma_cong_k(s%d, g%d, e%d);" % (outs[k], outs[k], outs[k]))
    o.append("}")
    o.append("")

    if not off:
        # The exact outputs fit 32 bits when the inputs are small.
        o.append("/// A pass over values of at most 15 bits stays well inside 32 bits.")
        o.append("pub proof fn lemma_pass_bound(" + ", ".join("t%d: int" % i for i in range(8)) + ")")
        o.append("    requires")
        for i in range(8):
            o.append("        -16384 <= t%d <= 16384," % i)
        o.append("    ensures")
        for k in range(8):
            o.append("        -0x7000_0000 <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[%d] <= 0x7000_0000," % k)
        o.append("{")
        o.append("    hide(idct_1d);")
        canon(o, lambda i: "t%d" % i)
        o.append("}")
        o.append("")
        o.append("/// One pass over four lanes at once, in wrapping 32-bit arithmetic: right")
        o.append("/// modulo 2^32, lane by lane.")
    else:
        o.append("/// The second pass over four lanes at once, in wrapping 32-bit arithmetic,")
        o.append("/// with the range limit's rounding added: `pass + 2^17` modulo 2^32, lane")
        o.append("/// by lane.")
    o.append("#[inline(always)]")
    o.append("fn vpass%s(" % sfx + ", ".join("x%d: %s" % (i, V) for i in range(8)) + ", " + ", ".join("Ghost(t%d): Ghost<Seq<int>>" % i for i in range(8)) + ") -> (r: (" + ", ".join([V] * 8) + "))")
    o.append("    requires")
    o.append("        neon(),")
    for i in range(8):
        o.append("        lc(x%d, t%d)," % (i, i))
    o.append("    ensures")
    for k in range(8):
        o.append("        %s(r.%d, %s, %d)," % (pc, k, T, k))
    o.append("{")
    o.append("    hide(idct_1d);")
    o.append("    hide(cong);")
    o.append("    hide(l32);")
    for n, (kind, a, b, c) in enumerate(steps, 1):
        code(o, n, kind, nm("v", a), nm("v", b) if b is not None else None, c, sc)
    o.append("    proof {")
    for k in range(8):
        o.append("        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v%d, i), %s) by {" % (outs[k], fin("idct_1d(col(%s, i))[%d]" % (T, k))))
        o.append("            lemma_pass_lane%s(" % sfx + ", ".join("l32(x%d, i)" % j for j in range(8)) + ", " + ", ".join("t%d[i]" % j for j in range(8)) + ", " + ", ".join("l32(v%d, i)" % n for n in range(1, N + 1)) + ");")
        o.append("        }")
    o.append("    }")
    o.append("    (" + ", ".join("v%d" % outs[k] for k in range(8)) + ")")
    o.append("}")

    # -----------------------------------------------------------------------
    # The same pass when inputs 4 to 7 are zero: steps whose result is then
    # zero or a copy of an earlier value are left out. `rep[n]` is what
    # stands for step n of the full pass: None (zero), ("in", i) or
    # ("st", m).
    ssteps = []
    memo = {}
    rep = {}

    def srep(k):
        if k <= 0:
            return ("in", -k) if -k < 4 else None
        return rep[k]

    def semit(kind, ra, rb, c):
        key = (kind, ra, rb, c)
        if key not in memo:
            ssteps.append(key)
            memo[key] = ("st", len(ssteps))
        return memo[key]

    for n, (kind, a, b, c) in enumerate(steps, 1):
        ra = srep(a)
        rb = srep(b) if b is not None else None
        if kind == "add":
            r = rb if ra is None else ra if rb is None else semit("add", ra, rb, None)
        elif kind == "sub":
            assert ra is not None or rb is None
            r = ra if rb is None else semit("sub", ra, rb, None)
        elif kind == "addk":
            assert ra is not None
            r = semit("addk", ra, None, c)
        else:
            r = None if ra is None else semit("mul", ra, None, c)
        rep[n] = r
    S = len(ssteps)

    def rn(p, r):  # name of a sparse value
        if r is None:
            return None
        if r[0] == "in":
            return {"s": "a", "g": "t", "e": "f", "v": "x"}[p] + str(r[1])
        return {"s": "s", "g": "h", "e": "d", "v": "v"}[p] + str(r[1])

    def fg(k):  # exact value of full value k, inputs 4 to 7 being zero
        if k <= 0:
            return "t%d" % -k if -k < 4 else "0int"
        return "g%d" % k

    o.append("")
    o.append("/// One lane of `vpass4%s`: `lemma_pass_lane%s` for inputs 4 to 7 zero, where" % (sfx, sfx))
    o.append("/// the steps that then give zero, or an earlier value again, are gone.")
    o.append("#[verifier::rlimit(60)]")
    o.append("#[verifier::spinoff_prover]")
    o.append("proof fn lemma_pass_lane4%s(" % sfx + ", ".join("a%d: int" % i for i in range(4)) + ", " + ", ".join("t%d: int" % i for i in range(4)) + ", " + ", ".join("s%d: int" % i for i in range(1, S + 1)) + ")")
    o.append("    requires")
    for i in range(4):
        o.append("        cong(a%d, t%d)," % (i, i))
    for m, (kind, ra, rb, c) in enumerate(ssteps, 1):
        req(o, m, kind, rn("s", ra), rn("s", rb), c)
    o.append("    ensures")
    for k in range(8):
        o.append("        cong(%s, %s)," % (rn("s", rep[outs[k]]), fin("idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[%d]" % k)))
    o.append("{")
    o.append("    hide(idct_1d);")
    o.append("    reveal(radd);")
    o.append("    reveal(rsub);")
    o.append("    reveal(rmul);")
    for i in range(4):
        o.append("    let f%d = (a%d - t%d) / %s;" % (i, i, i, M))
        o.append("    assert(a%d == t%d + %s * f%d);" % (i, i, M, i))
    for m, (kind, ra, rb, c) in enumerate(ssteps, 1):
        book(o, m, kind, "h", "d", rn("s", ra), rn("s", rb), rn("g", ra), rn("g", rb), rn("e", ra), rn("e", rb), c)
    # The full pass's exact values, and what stands for each.
    for n, (kind, a, b, c) in enumerate(steps, 1):
        if kind == "add":
            o.append("    let g%d = %s + %s;" % (n, fg(a), fg(b)))
        elif kind == "sub":
            o.append("    let g%d = %s - %s;" % (n, fg(a), fg(b)))
        elif kind == "addk":
            o.append("    let g%d = %s + %d;" % (n, fg(a), c))
        else:
            o.append("    let g%d = %s * (%d);" % (n, fg(a), c))
        o.append("    assert(g%d == %s);" % (n, "0int" if rep[n] is None else rn("g", rep[n])))
    canon(o, lambda i: "t%d" % i if i < 4 else "0int")
    for k in range(8):
        r = rep[outs[k]]
        o.append("    assert(g%d == %s);" % (outs[k], fin("c%d" % couts[k])))
        o.append("    lemma_cong_k(%s, %s, %s);" % (rn("s", r), rn("g", r), rn("e", r)))
    o.append("}")
    o.append("")
    o.append("/// `vpass%s` for inputs 4 to 7 zero." % sfx)
    o.append("#[inline(always)]")
    o.append("fn vpass4%s(" % sfx + ", ".join("x%d: %s" % (i, V) for i in range(4)) + ", " + ", ".join("Ghost(t%d): Ghost<Seq<int>>" % i for i in range(8)) + ") -> (r: (" + ", ".join([V] * 8) + "))")
    o.append("    requires")
    o.append("        neon(),")
    for i in range(4):
        o.append("        lc(x%d, t%d)," % (i, i))
    for i in range(4, 8):
        o.append("        zero4(t%d)," % i)
    o.append("    ensures")
    for k in range(8):
        o.append("        %s(r.%d, %s, %d)," % (pc, k, T, k))
    o.append("{")
    o.append("    hide(idct_1d);")
    o.append("    hide(cong);")
    o.append("    hide(l32);")
    for m, (kind, ra, rb, c) in enumerate(ssteps, 1):
        code(o, m, kind, rn("v", ra), rn("v", rb), c, sc)
    o.append("    proof {")
    for k in range(8):
        r = rep[outs[k]]
        o.append("        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(%s, i), %s) by {" % (rn("v", r), fin("idct_1d(col(%s, i))[%d]" % (T, k))))
        o.append("            lemma_pass_lane4%s(" % sfx + ", ".join("l32(x%d, i)" % j for j in range(4)) + ", " + ", ".join("t%d[i]" % j for j in range(4)) + ", " + ", ".join("l32(v%d, i)" % m for m in range(1, S + 1)) + ");")
        o.append("            assert(col(%s, i) =~= seq![t0[i], t1[i], t2[i], t3[i], 0int, 0int, 0int, 0int]);" % T)
        o.append("        }")
    o.append("    }")
    o.append("    (" + ", ".join(rn("v", rep[outs[k]]) for k in range(8)) + ")")
    o.append("}")
    print("vpass%s: %d steps, sparse %d" % (sfx, N, S), file=sys.stderr)


o = []
family(o, "", 1, False)
o.append("")
family(o, "f", 1, True)
print("\n".join(o))
