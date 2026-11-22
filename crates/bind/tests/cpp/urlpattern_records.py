"""Turns WPT's urlpatterntestdata.json into the records urlpattern_dump.cc
reads. Tests whose arguments are not (string or init, optional base string,
optional options) are left out: those are errors of the JavaScript API.
So are tests with a lone surrogate, which UTF-8 cannot carry."""
import json
import sys


def esc(s):
    return s.replace('\\', '\\\\').replace('\n', '\\n').replace('\t', '\\t').replace('\r', '\\r')


def args(prefix, values, out):
    if not values:
        out.append(f"{prefix}.none\t")
        return True
    first, rest = values[0], values[1:]
    if isinstance(first, str):
        out.append(f"{prefix}.str\t{esc(first)}")
        if rest and isinstance(rest[0], str):
            out.append(f"{prefix}.base\t{esc(rest[0])}")
            rest = rest[1:]
    else:
        for k, v in first.items():
            if not isinstance(v, str):
                return False
            out.append(f"{prefix}.init.{k}\t{esc(v)}")
    if rest and isinstance(rest[0], dict) and prefix == "pat":
        if rest[0].get("ignoreCase"):
            out.append("pat.ignoreCase\t1")
        rest = rest[1:]
    return not rest


for n, t in enumerate(json.load(open(sys.argv[1], encoding='utf-8'))):
    out = [f"#\t{n}"]
    if not args("pat", t["pattern"], out):
        continue
    if "inputs" in t and not args("in", t["inputs"], out):
        continue
    text = "\n".join(out + ["end"])
    try:
        text.encode('utf-8')
    except UnicodeEncodeError:
        continue  # a lone surrogate, which only a JavaScript string can hold
    print(text)
