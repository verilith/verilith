#!/usr/bin/env python3
"""Runs Verus for the Buck2 rules in defs.bzl. Standard library only.

    verus.py vstd    ...   compile vstd, Verus's standard library, with the
                           features a crate asks for (as Cargo would)
    verus.py export  ...   compile a crate for the crates that depend on it:
                           its .rmeta and .vir, with no proofs checked
    verus.py verify  ...   check one part of a crate's proofs
    verus.py seal    ...   check that the parts add up to the whole crate
    verus.py rustc   ...   compile a crate that has no proofs (a dependency
                           from crates.io) with the compiler Verus uses

Buck2 only knows that an action exited 0. What makes that mean "the proofs
hold" is checked here, and every check fails closed:

  * Verus is the pinned build. The commit and Rust toolchain Verus reports
    in its own JSON output must be the ones in scripts/verus-version.
  * Verus says it succeeded: no errors, and at least one proof checked
    (a crate or part with none is an error unless it is declared empty).
  * Nothing is left out. A crate verified in one part must be reported by
    Verus as "verifying the entire crate". A crate split into parts is
    split by module, and the list of modules is Verus's own (list_modules).
    Each module goes to exactly one part, each part names its modules to
    Verus one by one (a module Verus does not know is an error), the crate
    root goes with part 1, and `seal` re-checks that the parts cover the
    list.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time


def die(msg):
    print(f"verus.py: {msg}", file=sys.stderr)
    sys.exit(1)


def read_pin(path):
    pin = {}
    for line in open(path):
        m = re.match(r"\s*([A-Z0-9_]+)=(\S+)", line)
        if m:
            pin[m.group(1)] = m.group(2)
    for k in ("VERUS_COMMIT", "VERUS_TOOLCHAIN"):
        if k not in pin:
            die(f"{path} does not set {k}")
    return pin


def find_verus():
    exe = os.environ.get("VERUS") or shutil.which("verus")
    if not exe:
        die("no `verus` on PATH (and VERUS is not set). Build the commit in "
            "scripts/verus-version and put its target-verus/release on PATH.")
    return exe


def check_pin(reported, pin):
    """reported: the "verus" object of Verus's JSON output."""
    commit = reported.get("commit", "")
    toolchain = reported.get("toolchain", "")
    if commit != pin["VERUS_COMMIT"]:
        die(f"wrong Verus: this one was built from {commit or '?'}, "
            f"scripts/verus-version pins {pin['VERUS_COMMIT']}")
    if not toolchain.startswith(pin["VERUS_TOOLCHAIN"] + "-"):
        die(f"wrong Rust toolchain: Verus uses {toolchain or '?'}, "
            f"scripts/verus-version pins {pin['VERUS_TOOLCHAIN']}")


def crate_args(a):
    """The rustc arguments that define the crate, the same for every action
    on it, so that each one sees the same crate."""
    args = ["--crate-name", a.crate, "--crate-type", "lib", f"--edition={a.edition}", a.root]
    for f in a.feature:
        args += ["--cfg", f'feature="{f}"']
    for c in a.cfg:
        args += ["--cfg", c]
    for e in a.extern:
        args += ["--extern", e]
    for i in a.import_:
        args += ["--import", i]
    for d in a.dep_dir:
        args += ["-L", f"dependency={d}"]
    return args


def verus_home():
    """The directory of the Verus build: verus, rust_verify, z3, the builtin
    libraries and the vstd that was built with it."""
    return os.path.dirname(os.path.realpath(find_verus()))


BUILTIN = ("libverus_builtin.rlib", "libverus_builtin_macros", "libverus_state_machines_macros")


def builtin_libs():
    home = verus_home()
    libs = {}
    for f in sorted(os.listdir(home)):
        if f.startswith(BUILTIN) and f.endswith((".rlib", ".so", ".dylib", ".dll")):
            libs[f] = os.path.join(home, f)
    if len(libs) != len(BUILTIN):
        die(f"{home} does not hold Verus's builtin libraries")
    return libs


def crate_env(a):
    env = dict(os.environ)
    env.setdefault("RUST_MIN_STACK", str(10 * 1024 * 1024))
    if getattr(a, "vstd_rlib", None):
        # Verus loads vstd from its own directory. To give it the vstd built
        # for this crate instead, point it at a directory that holds that
        # vstd beside the builtin libraries of the real one.
        scratch = os.environ.get("BUCK_SCRATCH_PATH") or os.path.dirname(os.path.abspath(a.vstd_rlib))
        root = os.path.join(os.path.abspath(scratch), "verus-root")
        os.makedirs(root, exist_ok=True)
        links = dict(builtin_libs())
        links["libvstd.rlib"] = os.path.abspath(a.vstd_rlib)
        links["vstd.vir"] = os.path.abspath(a.vstd_vir)
        for name, target in links.items():
            link = os.path.join(root, name)
            if os.path.lexists(link):
                os.remove(link)
            os.symlink(target, link)
        env["VERUS_ROOT"] = root
        z3 = os.path.join(verus_home(), "z3")
        if "VERUS_Z3_PATH" not in env and os.path.exists(z3):
            env["VERUS_Z3_PATH"] = z3
    v = a.version
    major, minor, patch = (v.split("-")[0].split("+")[0].split(".") + ["0", "0"])[:3]
    env.update({
        "CARGO_PKG_NAME": a.package, "CARGO_PKG_VERSION": v,
        "CARGO_PKG_VERSION_MAJOR": major, "CARGO_PKG_VERSION_MINOR": minor,
        "CARGO_PKG_VERSION_PATCH": patch, "CARGO_CRATE_NAME": a.crate,
        "CARGO_MANIFEST_DIR": os.path.abspath(os.path.dirname(os.path.dirname(a.root))),
    })
    # Verus must not think Cargo is driving it.
    env.pop("__VERUS_DRIVER_VIA_CARGO__", None)
    env.pop("RUSTC_WRAPPER", None)
    return env


def run_verus(a, extra):
    """Runs Verus with --output-json. Returns (exit code, parsed JSON or None,
    seconds). Diagnostics go to stderr as they come."""
    cmd = [find_verus()] + crate_args(a) + ["--output-json"] + extra
    start = time.time()
    p = subprocess.run(cmd, env=crate_env(a), stdout=subprocess.PIPE, text=True)
    secs = time.time() - start
    out = p.stdout
    # The JSON object is the last thing on stdout; anything before it is not ours.
    doc = None
    at = out.find("{")
    while at != -1:
        try:
            doc = json.loads(out[at:])
            sys.stderr.write(out[:at])
            break
        except ValueError:
            at = out.find("{", at + 1)
    if doc is None:
        sys.stderr.write(out)
    return p.returncode, doc, secs


PROBE = "no_such_module_"


def list_modules(a):
    """Every module of the crate that Verus has something to verify in, other
    than the crate root, as {name: weight}. The list is Verus's own: asked
    to verify a module that does not exist, it names the ones that do. If it
    ever stops doing that, this fails rather than guess."""
    cmd = [find_verus()] + crate_args(a) + ["--no-verify", "--verify-only-module", PROBE]
    p = subprocess.run(cmd, env=crate_env(a), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       text=True)
    err = p.stderr
    head = f"could not find module {PROBE} specified by"
    if p.returncode == 0 or head not in err:
        sys.stderr.write(err)
        die(f"{a.crate}: could not get the list of modules from Verus")
    lines = err[err.index(head):].split("\n")
    if len(lines) < 3 or lines[1].strip() != "available modules are:":
        die(f"{a.crate}: Verus's list of modules is not in the form this script knows")
    names, end = [], False
    for line in lines[2:]:
        line = line.strip()
        if line == "or use --verify-root":
            end = True
            break
        m = re.fullmatch(r"- ([A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*)", line)
        if not m:
            die(f"{a.crate}: unexpected line in Verus's list of modules: {line!r}")
        names.append(m.group(1))
    if not end or len(set(names)) != len(names):
        die(f"{a.crate}: Verus's list of modules is cut short or repeats a name")
    # Weights only balance the parts; they cannot leave a module out. The size
    # of the module's own source file, where it is where modules usually are.
    src = os.path.dirname(a.root)
    sizes = {}
    for n in names:
        base = os.path.join(src, *n.split("::"))
        sizes[n] = 1
        for f in (base + ".rs", os.path.join(base, "mod.rs")):
            if os.path.isfile(f):
                sizes[n] = max(1, os.path.getsize(f))
    return sizes


def partition(sizes, parts):
    """Splits the modules into `parts` lists of about equal source size.
    Deterministic: largest first, each to the lightest part so far."""
    bins = [[] for _ in range(parts)]
    load = [0] * parts
    for name in sorted(sizes, key=lambda n: (-sizes[n], n)):
        i = min(range(parts), key=lambda k: (load[k], k))
        bins[i].append(name)
        load[i] += sizes[name]
    return [sorted(b) for b in bins]


def cmd_vstd(a):
    """vstd from its crates.io source, compiled the way Verus's own build
    compiles it, with nothing verified: vstd is verified by the Verus
    project, and `cargo verus focus` does not verify it either."""
    pin = read_pin(a.pin)
    libs = builtin_libs()
    out_dir = os.path.dirname(a.rmeta)
    cmd = [find_verus(), "--internal-test-mode"]
    for f, path in libs.items():
        cmd += ["--extern", f"{f[3:].split('.')[0]}={path}"]
    cmd += ["--crate-name", "vstd", "--crate-type=lib", f"--edition={a.edition}",
            "--is-vstd", "--no-verify", "--no-lifetime", "--no-trait-conflicts",
            "--compile", "--export", a.vir, "--out-dir", out_dir, "--output-json"]
    for f in a.feature:
        cmd += ["--cfg", f'feature="{f}"']
    cmd.append(a.root)
    env = dict(os.environ)
    env.setdefault("RUST_MIN_STACK", str(10 * 1024 * 1024))
    p = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, text=True)
    try:
        doc = json.loads(p.stdout[p.stdout.index("{"):])
    except ValueError:
        sys.stderr.write(p.stdout)
        die(f"vstd: Verus failed (exit {p.returncode})")
    check_pin(doc.get("verus", {}), pin)
    if p.returncode != 0 or not os.path.exists(a.rmeta) or not os.path.exists(a.vir):
        die(f"vstd: Verus failed (exit {p.returncode})")


def cmd_export(a):
    pin = read_pin(a.pin)
    out_dir = os.path.dirname(a.rmeta)
    code, doc, secs = run_verus(a, [
        "--no-verify", "--compile", "--emit=metadata", "--out-dir", out_dir,
        "--export", a.vir,
    ])
    if doc is None or code != 0:
        die(f"{a.crate}: Verus failed to compile the crate (exit {code})")
    check_pin(doc.get("verus", {}), pin)
    for f in (a.rmeta, a.vir):
        if not os.path.exists(f):
            die(f"{a.crate}: Verus did not write {f}")
    modules = None
    if a.parts > 1:
        modules = list_modules(a)
        if len(modules) < a.parts:
            die(f"{a.crate}: {a.parts} parts asked for but only {len(modules)} modules")
    json.dump({"crate": a.crate, "parts": a.parts, "modules": modules}, open(a.modules, "w"),
              indent=1, sort_keys=True)


def cmd_verify(a):
    pin = read_pin(a.pin)
    plan = json.load(open(a.modules))
    if plan["crate"] != a.crate or plan["parts"] != a.parts:
        die(f"{a.modules} is for another crate or split")
    extra = []
    mine = None
    if a.parts > 1:
        mine = partition(plan["modules"], a.parts)[a.part]
        if not mine:
            die(f"{a.crate}: part {a.part + 1} of {a.parts} is empty")
        # The crate root itself (what is not in any module) goes with part 1.
        if a.part == 0:
            extra.append("--verify-root")
        for m in mine:
            extra += ["--verify-only-module", m]
    if a.threads:
        extra += ["--num-threads", str(a.threads)]
    extra += ["--time-expanded"]
    extra += a.verus_arg
    code, doc, secs = run_verus(a, extra)
    label = a.crate if a.parts == 1 else f"{a.crate} part {a.part + 1}/{a.parts}"
    if doc is None:
        die(f"{label}: Verus printed no result (exit {code})")
    check_pin(doc.get("verus", {}), pin)
    res = doc.get("verification-results", {})
    verified, errors = res.get("verified"), res.get("errors")
    ok = (code == 0 and res.get("encountered-error") is False
          and res.get("encountered-vir-error") is False
          and isinstance(verified, int) and errors == 0)
    if not ok:
        die(f"{label}: FAILED: {verified} verified, {errors} errors (exit {code})")
    whole = res.get("is-verifying-entire-crate")
    if a.parts == 1 and (whole is not True or res.get("success") is not True):
        die(f"{label}: Verus did not verify the entire crate")
    if a.parts > 1 and whole is not False:
        die(f"{label}: expected a partial run")
    if verified == 0 and not a.allow_empty:
        die(f"{label}: 0 proofs verified. If that is right, say so with allow_empty.")
    times = doc.get("times-ms", {})
    by_module = {}
    for m in times.get("total-verify-module-times", []):
        by_module[m["module"]] = by_module.get(m["module"], 0) + m["time"]
    json.dump({
        "crate": a.crate, "part": a.part, "parts": a.parts, "modules": mine,
        "root": a.parts == 1 or a.part == 0,
        "verified": verified, "errors": errors, "entire_crate": whole,
        "verus": doc.get("verus"), "seconds": round(secs, 1),
        "module_ms": dict(sorted(by_module.items())),
    }, open(a.out, "w"), indent=1, sort_keys=True)
    print(f"verification results:: {verified} verified, {errors} errors ({label}, {secs:.0f}s)",
          file=sys.stderr)


def cmd_seal(a):
    plan = json.load(open(a.modules))
    results = [json.load(open(r)) for r in a.result]
    crate, parts = plan["crate"], plan["parts"]
    if sorted(r["part"] for r in results) != list(range(parts)):
        die(f"{crate}: expected parts 0..{parts - 1}, got {[r['part'] for r in results]}")
    for r in results:
        if r["crate"] != crate or r["parts"] != parts or r["errors"] != 0:
            die(f"{crate}: a result is for another crate or split, or has errors")
    if parts == 1:
        if results[0]["entire_crate"] is not True:
            die(f"{crate}: the one part did not verify the entire crate")
    else:
        seen = [m for r in results for m in r["modules"]]
        if sorted(seen) != sorted(plan["modules"]):
            die(f"{crate}: the parts cover {sorted(seen)}, the crate has {sorted(plan['modules'])}")
        if sum(1 for r in results if r["root"]) != 1:
            die(f"{crate}: the crate root must be in exactly one part")
    total = sum(r["verified"] for r in results)
    if total == 0 and not a.allow_empty:
        die(f"{crate}: 0 proofs verified")
    commits = {r["verus"]["commit"] for r in results}
    if len(commits) != 1:
        die(f"{crate}: parts were verified by different Verus builds: {commits}")
    json.dump({
        "crate": crate, "verified": total, "errors": 0, "parts": parts,
        "verified_by_part": [r["verified"] for r in sorted(results, key=lambda r: r["part"])],
        "verus": results[0]["verus"],
    }, open(a.out, "w"), indent=1, sort_keys=True)
    print(f"verification results:: {total} verified, 0 errors ({crate})", file=sys.stderr)


def cmd_rustc(a):
    """A crate with no proofs, compiled to .rmeta by the rustc Verus is built on."""
    pin = read_pin(a.pin)
    tc = pin["VERUS_TOOLCHAIN"]
    try:
        rustc = subprocess.check_output(["rustup", "which", "rustc", "--toolchain", tc],
                                        text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        die(f"Rust toolchain {tc} is not installed (rustup toolchain install {tc})")
    cmd = [rustc] + crate_args(a) + ["--emit=metadata", "--cap-lints", "allow",
                                     "--out-dir", os.path.dirname(a.rmeta)]
    code = subprocess.run(cmd, env=crate_env(a)).returncode
    if code != 0 or not os.path.exists(a.rmeta):
        die(f"{a.crate}: rustc failed (exit {code})")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    def crate_flags(p):
        p.add_argument("--pin", required=True, help="scripts/verus-version")
        p.add_argument("--crate", required=True)
        p.add_argument("--package", required=True)
        p.add_argument("--version", required=True)
        p.add_argument("--edition", required=True)
        p.add_argument("--root", required=True, help="the crate root source file")
        p.add_argument("--feature", action="append", default=[])
        p.add_argument("--cfg", action="append", default=[])
        p.add_argument("--extern", action="append", default=[], help="NAME=PATH.rmeta")
        p.add_argument("--import", dest="import_", action="append", default=[], help="NAME=PATH.vir")
        p.add_argument("--dep-dir", action="append", default=[])
        p.add_argument("--vstd-rlib", help="the vstd to verify against (with --vstd-vir)")
        p.add_argument("--vstd-vir")

    p = sub.add_parser("vstd")
    p.add_argument("--pin", required=True)
    p.add_argument("--edition", required=True)
    p.add_argument("--root", required=True)
    p.add_argument("--feature", action="append", default=[])
    p.add_argument("--rmeta", required=True, help="libvstd.rlib")
    p.add_argument("--vir", required=True)
    p.set_defaults(fn=cmd_vstd)

    p = sub.add_parser("export")
    crate_flags(p)
    p.add_argument("--parts", type=int, required=True)
    p.add_argument("--rmeta", required=True)
    p.add_argument("--vir", required=True)
    p.add_argument("--modules", required=True)
    p.set_defaults(fn=cmd_export)

    p = sub.add_parser("verify")
    crate_flags(p)
    p.add_argument("--parts", type=int, required=True)
    p.add_argument("--part", type=int, required=True)
    p.add_argument("--modules", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--threads", type=int, default=0)
    p.add_argument("--allow-empty", action="store_true")
    p.add_argument("--verus-arg", action="append", default=[])
    p.set_defaults(fn=cmd_verify)

    p = sub.add_parser("seal")
    p.add_argument("--modules", required=True)
    p.add_argument("--result", action="append", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--allow-empty", action="store_true")
    p.set_defaults(fn=cmd_seal)

    p = sub.add_parser("rustc")
    crate_flags(p)
    p.add_argument("--rmeta", required=True)
    p.set_defaults(fn=cmd_rustc)

    a = ap.parse_args()
    if a.cmd == "verify" and not 0 <= a.part < a.parts:
        die("--part out of range")
    a.fn(a)


if __name__ == "__main__":
    main()
