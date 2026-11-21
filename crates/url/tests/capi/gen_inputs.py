#!/usr/bin/env python3
"""Writes the differential test's cases (records of length-prefixed fields).

P input base?   parse (base may be absent)
S href setter value   apply a setter
Q query   search params
"""
import json, os, sys, itertools, random

here = os.path.dirname(os.path.abspath(__file__))
data = os.path.join(here, "..", "data")
out = open(sys.argv[1], "wb")


def rec(tag, *fields):
    b = tag.encode()
    for f in fields:
        if isinstance(f, str):
            f = f.encode("utf-8", "surrogatepass")
        b += str(len(f)).encode() + b":" + f
    out.write(b + b"\n")


hrefs = set()
for case in json.load(open(os.path.join(data, "urltestdata.json"))):
    if isinstance(case, str):
        continue
    try:
        case["input"].encode("utf-8")
    except UnicodeEncodeError:
        continue
    if case.get("base"):
        rec("P", case["input"], case["base"])
    else:
        rec("P", case["input"])
    if "href" in case:
        hrefs.add(case["href"])

values = set()
for setter, cases in json.load(open(os.path.join(data, "setters_tests.json"))).items():
    if setter == "comment":
        continue
    for c in cases:
        try:
            c["new_value"].encode("utf-8")
        except UnicodeEncodeError:
            continue
        rec("S", c["href"], setter, c["new_value"])
        hrefs.add(c["href"])
        values.add(c["new_value"])

corpus = sys.argv[2] if len(sys.argv) > 2 else None
if corpus and os.path.exists(corpus):
    lines = open(corpus, "rb").read().split(b"\n")[:20000]
    for l in lines:
        if l:
            rec("P", l)
    hrefs.update(l.decode("utf-8", "replace") for l in lines[:300] if l)

values.update(["", "x", "1", "8080", "65536", "a:b", "/a/../b", "?q", "#h", "%2e", "..", "C|", "[::1]",
               "é", "a b", "\t", "@", "host:99", "xn--a", "1.2.3.4", "0x7f.1", "file", "http", "blob"])
setters = ["href", "protocol", "username", "password", "host", "hostname", "port", "pathname", "search", "hash"]
rng = random.Random(1)
hl = sorted(hrefs)
vl = sorted(values)
for h in hl:
    for s in setters:
        for v in rng.sample(vl, 6):
            rec("S", h, s, v)

queries = ["", "?", "a=1&b=2&a=3", "?c=%20+d&&=&x", "z=1&é=2&a=3&\U0001F600=4&ﬃ=5", "a=%zz%4&b=%e2%82",
           "k=v=w", "+=+", "%FF=%C3"]
for q in queries:
    rec("Q", q)
