#!/usr/bin/env python3
"""The trust ledger: every place a crate's proofs take something on trust.

Scans crates/*/src for the Verus constructs that make the verifier assume
rather than check, and writes TRUST-LEDGER.md at the repository root:

  external_body                     a function whose body Verus does not check
  external                          code Verus does not see at all
  axiom fn                          a stated fact with no proof
  assume_specification              a contract for a function outside the crate
  external_type_specification       a type outside the crate
  external_fn_specification         a contract for a function outside the crate
  Ghost/Tracked::assume_new()       a ghost or tracked value made without proof
  exec_allows_no_decreases_clause   a function exempt from the termination check
  plain-Rust files                  src/ files with no verus! block: compiled, never verified
  plain-Rust lines                  the lines of code in those files (comments and blank lines
                                    not counted): the size of what is never verified

`assume(...)` and `admit()` are not allowed anywhere in src/; the script fails
if it finds one.

  scripts/trust-ledger.py           rewrite TRUST-LEDGER.md
  scripts/trust-ledger.py --check   fail if TRUST-LEDGER.md is out of date
                                    (CI runs this)

A change that adds a trusted item therefore shows up in the pull request's
diff of TRUST-LEDGER.md, next to the code.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "TRUST-LEDGER.md")

# Kinds whose items are named after the function that follows them.
NAMED = [
    ("external_body", re.compile(r"#\[\s*verifier::external_body\s*\]")),
    ("external", re.compile(r"#\[\s*verifier::external\s*\]")),
    ("external_fn_specification", re.compile(r"#\[\s*verifier::external_fn_specification\s*\]")),
    ("exec_allows_no_decreases_clause", re.compile(r"#\[\s*verifier::exec_allows_no_decreases_clause\s*\]")),
]
AXIOM = re.compile(r"\baxiom\s+fn\s+([A-Za-z_][A-Za-z0-9_]*)")
ASSUME_SPEC = re.compile(r"\bassume_specification\b")
EXT_TYPE = re.compile(r"#\[\s*verifier::external_type_specification\s*\]")
ASSUME_NEW = re.compile(r"\b(Ghost|Tracked)::assume_new\b")
FORBIDDEN = re.compile(r"(?<![A-Za-z0-9_:.])(assume|admit)\s*\(")
FN_NAME = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")

KINDS = [
    "external_body",
    "external",
    "axiom fn",
    "assume_specification",
    "external_type_specification",
    "external_fn_specification",
    "assume_new",
    "exec_allows_no_decreases_clause",
    "unverified modules",
]


def strip_comments(text):
    """Blanks out // and /* */ comments and string literals, keeping line
    numbers and offsets, so that prose about `assume(` is not counted."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif c == '"' and not (i > 0 and text[i - 1] in "'\\"):
            # Raw strings (r"...", r#"..."#) and ordinary ones.
            k = i - 1
            hashes = 0
            while k >= 0 and text[k] == "#":
                hashes += 1
                k -= 1
            raw = k >= 0 and text[k] == "r" and (k == 0 or not (text[k - 1].isalnum() or text[k - 1] == "_"))
            if raw:
                end = '"' + "#" * hashes
                j = text.find(end, i + 1)
                j = n if j < 0 else j + len(end)
            else:
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
                j = min(n, j + 1)
            out.append('"' + "".join(ch if ch == "\n" else " " for ch in text[i + 1:j - 1]) + '"' if j - i >= 2 else text[i:j])
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def scan_file(path, rel):
    with open(path, encoding="utf-8") as f:
        text = strip_comments(f.read())
    items = {k: [] for k in KINDS}
    items["plain-Rust lines"] = 0
    forbidden = []
    for kind, pat in NAMED:
        for m in pat.finditer(text):
            fm = FN_NAME.search(text, m.end())
            name = fm.group(1) if fm else "?"
            items[kind].append(name)
    for m in AXIOM.finditer(text):
        items["axiom fn"].append(m.group(1))
    items["assume_specification"] += ["*"] * len(ASSUME_SPEC.findall(text))
    for m in EXT_TYPE.finditer(text):
        sm = re.compile(r"\bstruct\s+([A-Za-z_][A-Za-z0-9_]*)").search(text, m.end())
        items["external_type_specification"].append(sm.group(1) if sm else "?")
    for m in ASSUME_NEW.finditer(text):
        items["assume_new"].append(m.group(1))
    if "verus!" not in text:
        items["unverified modules"].append(rel)
        items["plain-Rust lines"] = sum(1 for l in text.splitlines() if l.strip())
    for m in FORBIDDEN.finditer(text):
        forbidden.append(f"{rel}:{line_of(text, m.start())}: {m.group(1)}(")
    return items, forbidden


def scan():
    crates = {}
    forbidden = []
    cdir = os.path.join(ROOT, "crates")
    for crate in sorted(os.listdir(cdir)):
        src = os.path.join(cdir, crate, "src")
        if not os.path.isdir(src):
            continue
        files = {}
        for dp, dns, fns in os.walk(src):
            dns.sort()
            for fn in sorted(fns):
                if not fn.endswith(".rs"):
                    continue
                path = os.path.join(dp, fn)
                rel = os.path.relpath(path, ROOT)
                items, bad = scan_file(path, rel)
                forbidden += bad
                if any(v for k, v in items.items() if k != "plain-Rust lines"):
                    files[os.path.relpath(path, os.path.join(cdir, crate))] = items
        crates[crate] = files
    return crates, forbidden


def render(crates):
    short = {
        "external_body": "external_body",
        "external": "external",
        "axiom fn": "axioms",
        "assume_specification": "assume_spec",
        "external_type_specification": "ext. types",
        "external_fn_specification": "ext. fn specs",
        "assume_new": "assume_new",
        "exec_allows_no_decreases_clause": "no termination check",
        "unverified modules": "plain-Rust files",
    }
    used = [k for k in KINDS if any(f[k] for files in crates.values() for f in files.values())]
    lines = [
        "# Trust ledger",
        "",
        "Generated by `scripts/trust-ledger.py`; do not edit by hand. CI fails",
        "when this file is out of date, so every change to what the proofs take",
        "on trust shows up here, in the same pull request as the code.",
        "",
        "Each count is a place where Verus assumes instead of checks. What each",
        "one assumes, and why it is believed, is in the crate's TRUST.md or the",
        "\"Trusted base\" section of its README. `assume(...)` and `admit()` do",
        "not occur in any crate's `src/` (the script fails if one appears).",
        "",
        "| Kind | Meaning |",
        "|---|---|",
        "| external_body | a function whose contract is assumed and whose body is not checked |",
        "| external | code Verus does not see at all |",
        "| axioms | `axiom fn`: a stated fact with no proof |",
        "| assume_spec | `assume_specification`: an assumed contract for a function outside the crate (verilith-simd's CPU intrinsics) |",
        "| ext. types | `external_type_specification`: a type defined outside the crate |",
        "| ext. fn specs | `external_fn_specification`: an assumed contract for a function outside the crate |",
        "| assume_new | `Ghost::assume_new()` / `Tracked::assume_new()`: a ghost or tracked value made without proof, mostly in unverified glue calling verified code |",
        "| no termination check | `exec_allows_no_decreases_clause`: a function exempt from Verus's termination check (blocking calls, an interpreter loop) |",
        "| plain-Rust files | `src/` files with no `verus!` block: compiled into the library, never seen by Verus (C APIs, bindings, wrappers) |",
        "| plain-Rust lines | the lines of code in those files, not counting comments and blank lines: how much is never verified |",
        "",
        "## Counts",
        "",
        "| Crate | " + " | ".join(short[k] for k in used) + " | plain-Rust lines |",
        "|---|" + "---:|" * (len(used) + 1),
    ]
    totals = {k: 0 for k in used}
    total_lines = 0
    for crate, files in crates.items():
        row = []
        for k in used:
            n = sum(len(f[k]) for f in files.values())
            totals[k] += n
            row.append(str(n) if n else "")
        n = sum(f["plain-Rust lines"] for f in files.values())
        total_lines += n
        row.append(str(n) if n else "")
        lines.append(f"| {crate} | " + " | ".join(row) + " |")
    lines.append("| **total** | " + " | ".join(f"**{totals[k]}**" for k in used) + f" | **{total_lines}** |")
    lines += ["", "## Items", ""]
    for crate, files in crates.items():
        if not files:
            continue
        lines += [f"### {crate}", ""]
        for path, items in files.items():
            parts = []
            for k in used:
                v = items[k]
                if not v:
                    continue
                if k == "assume_specification":
                    parts.append(f"{len(v)} assume_specification")
                elif k == "unverified modules":
                    parts.append(f"plain Rust, {items['plain-Rust lines']} lines")
                elif k == "assume_new":
                    parts.append(f"{len(v)} assume_new")
                else:
                    parts.append(f"{short[k]}: " + ", ".join(f"`{x}`" for x in v))
            lines.append(f"- `crates/{crate}/{path}`: " + "; ".join(parts))
        lines.append("")
    return "\n".join(lines).rstrip("\n") + "\n"


def main():
    check = "--check" in sys.argv[1:]
    crates, forbidden = scan()
    if forbidden:
        print("assume(...) or admit() in src/:", file=sys.stderr)
        for f in forbidden:
            print("  " + f, file=sys.stderr)
        sys.exit(1)
    text = render(crates)
    if check:
        try:
            with open(OUT, encoding="utf-8") as f:
                old = f.read()
        except FileNotFoundError:
            old = ""
        if old != text:
            print("TRUST-LEDGER.md is out of date: run scripts/trust-ledger.py and commit the result.", file=sys.stderr)
            import difflib
            sys.stderr.writelines(difflib.unified_diff(old.splitlines(True), text.splitlines(True), "TRUST-LEDGER.md (committed)", "TRUST-LEDGER.md (generated)"))
            sys.exit(1)
        print("TRUST-LEDGER.md is up to date.")
    else:
        with open(OUT, "w", encoding="utf-8") as f:
            f.write(text)
        print(f"wrote {os.path.relpath(OUT)}")


if __name__ == "__main__":
    main()
