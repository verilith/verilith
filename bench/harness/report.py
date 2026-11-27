#!/usr/bin/env python3
"""Summarizes raw.csv from vbench.py into summary.csv and report.md.

For each case, with n alternating sample pairs (ours, original):

  speedup_i = original time_i / our time_i      (> 1: ours is faster)

The headline is the median of the speedup_i, with a distribution-free 95%
confidence interval for that median (order statistics of the binomial
distribution; no normality assumed). Pairing the samples cancels drift
that hits both sides. If the interval contains 1.0 the result is reported
as "no measurable difference".

Instructions per call (median over samples) are reported for both sides
when the machine has counters; they barely move between runs, so they
settle "is it really doing less work" even where time is noisy.

Usage: report.py RESULTS_DIR   (reads raw.csv and machine.json there)
Standard library only.
"""
import csv
import json
import math
import os
import statistics
import sys
from collections import OrderedDict, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import suites  # noqa: E402

META = {c["id"]: c for c in suites.COMPARISONS}


def binom_ci_ranks(n, alpha=0.05):
    """1-based ranks (lo, hi) of a >= 1-alpha CI for the median, or None."""
    k_best = None
    cdf = 0.0
    for k in range(0, n + 1):
        cdf += math.comb(n, k) / 2.0 ** n  # P(X <= k)
        if 2 * cdf <= alpha:
            k_best = k + 1  # interval [r_(k+1), r_(n-k)]
        else:
            break
    if k_best is None:
        return None
    return k_best, n + 1 - k_best


def median_ci(xs, alpha=0.05):
    s = sorted(xs)
    r = binom_ci_ranks(len(s), alpha)
    med = statistics.median(s)
    if r is None:
        return med, s[0], s[-1]
    return med, s[r[0] - 1], s[r[1] - 1]


def fmt_ns(ns):
    if ns >= 1e9:
        return f"{ns / 1e9:.2f} s"
    if ns >= 1e6:
        return f"{ns / 1e6:.2f} ms"
    if ns >= 1e3:
        return f"{ns / 1e3:.2f} µs"
    return f"{ns:.1f} ns"


def summarize(rows):
    groups = OrderedDict()
    for r in rows:
        groups.setdefault((r["suite"], r["comparison"], r["case"]), []).append(r)
    out = []
    for (suite, comp, case), rs in groups.items():
        pairs = defaultdict(dict)
        for r in rs:
            pairs[int(r["pair"])][r["side"]] = r
        pairs = [p for _, p in sorted(pairs.items()) if "ours" in p and "rival" in p]
        if not pairs:
            continue
        o0, r0 = pairs[0]["ours"], pairs[0]["rival"]
        nbytes = int(o0["bytes"])
        sp = [int(p["rival"]["ns"]) / int(p["ours"]["ns"]) for p in pairs]
        med, lo, hi = median_ci(sp)
        if lo > 1:
            verdict = "faster"
        elif hi < 1:
            verdict = "slower"
        else:
            verdict = "no measurable difference"
        per = lambda side, f: statistics.median(int(p[side][f]) / int(p[side]["iters"]) for p in pairs)
        o_ns, r_ns = per("ours", "ns"), per("rival", "ns")
        # Counters that are missing (-1) or did not move (0) give n/a.
        have_ins = all(int(p[s]["instructions"]) > 0 for p in pairs for s in ("ours", "rival"))
        o_ins = per("ours", "instructions") if have_ins else None
        r_ins = per("rival", "instructions") if have_ins else None
        have_cyc = all(int(p[s]["cycles"]) > 0 for p in pairs for s in ("ours", "rival"))
        checks = {p["ours"]["check"] for p in pairs} | {p["rival"]["check"] for p in pairs}
        out.append({
            "suite": suite, "comparison": comp, "api": META.get(comp, {}).get("api", ""), "case": case, "ours": o0["contender"], "original": r0["contender"],
            "pairs": len(pairs), "iters": int(o0["iters"]), "bytes": nbytes,
            "ours_ns_per_call": round(o_ns, 2), "original_ns_per_call": round(r_ns, 2),
            "ours_mb_s": round(nbytes / o_ns * 1e3, 1) if nbytes else "",
            "original_mb_s": round(nbytes / r_ns * 1e3, 1) if nbytes else "",
            "speedup": round(med, 4), "ci95_lo": round(lo, 4), "ci95_hi": round(hi, 4), "verdict": verdict,
            "ours_instructions_per_call": round(o_ins, 1) if have_ins else "",
            "original_instructions_per_call": round(r_ins, 1) if have_ins else "",
            "instructions_ratio": round(o_ins / r_ins, 4) if have_ins and r_ins else "",
            "ours_cycles_per_call": round(per("ours", "cycles"), 1) if have_cyc else "",
            "original_cycles_per_call": round(per("rival", "cycles"), 1) if have_cyc else "",
            "same_check": int(len(checks) == 1),
            "ours_check": p_check(pairs, "ours"), "original_check": p_check(pairs, "rival"),
        })
    return out


def p_check(pairs, side):
    return pairs[-1][side]["check"]


def write_csv(path, rows):
    if not rows:
        return
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def speed_text(s):
    if s["verdict"] == "no measurable difference":
        return f"{s['speedup']:.2f}x (CI {s['ci95_lo']:.2f}–{s['ci95_hi']:.2f}, no measurable difference)"
    return f"**{s['speedup']:.2f}x** ({s['ci95_lo']:.2f}–{s['ci95_hi']:.2f})"


def ins_text(s):
    if s["instructions_ratio"] == "":
        return "n/a"
    r = s["instructions_ratio"]
    pct = (1 - r) * 100
    return f"{abs(pct):.0f}% {'fewer' if pct >= 0 else 'more'}"


def geomean(xs):
    return math.exp(statistics.mean(math.log(x) for x in xs))


def side_by_side(by_comp):
    """The comparisons that share a task and an original, drop-in beside native."""
    L = []
    pairs = OrderedDict()
    for c in suites.COMPARISONS:
        if c.get("pair") and c["id"] in by_comp:
            pairs.setdefault(c["pair"], {})[c["api"]] = c
    pairs = OrderedDict((k, v) for k, v in pairs.items() if "drop-in" in v and "native" in v)
    if not pairs:
        return L
    L.append("## Drop-in and native, side by side\n")
    L.append("Two different numbers, for two different users. **Drop-in** is our library behind the original's "
             "API: the caller's code does not change, and this is the speed a user gets by relinking. **Native** "
             "is the same task done through our own API, against the original doing it through its own best "
             "API: this is the speed after porting the calling code, and a drop-in user does not get it. "
             "Both columns are speedups over the same original running the same driver; each was measured "
             "in its own alternating run, so the original was timed twice.\n")
    L.append("| original | task | cases | drop-in (geomean, range) | native (geomean, range) |")
    L.append("| --- | --- | ---: | --- | --- |")

    def cell(ss):
        sp = [s["speedup"] for s in ss]
        return f"{geomean(sp):.2f}x ({min(sp):.2f}x to {max(sp):.2f}x)"

    for key, v in pairs.items():
        d, n = by_comp[v["drop-in"]["id"]], by_comp[v["native"]["id"]]
        star = " \\*" if v["native"].get("note") else ""
        L.append(f"| {d[0]['original']} | {v['native']['task']} | {len(n)} | {cell(d)} | {cell(n)}{star} |")
    L.append("")
    L.append("\\* The two sides differ in more than the parser; see the note under that table below.\n")
    for key, v in pairs.items():
        # Cases match by name; where the two runners name them differently
        # (a different prefix), by the name after the first "/".
        d = {s["case"]: s for s in by_comp[v["drop-in"]["id"]]}
        n = {s["case"]: s for s in by_comp[v["native"]["id"]]}
        if not set(d) & set(n):
            d = {k.split("/", 1)[-1]: s for k, s in d.items()}
            n = {k.split("/", 1)[-1]: s for k, s in n.items()}
        any_n = next(iter(n.values()))
        any_d = next(iter(d.values()))
        L.append(f"### {any_d['original']}: {v['native']['task']}\n")
        L.append(f"Drop-in is {any_d['ours']} (`{v['drop-in']['id']}`); native is {any_n['ours']} "
                 f"(`{v['native']['id']}`).\n")
        L.append("| case | original | drop-in | native | drop-in speedup (95% CI) | native speedup (95% CI) |")
        L.append("| --- | ---: | ---: | ---: | --- | --- |")
        for case in d:
            if case not in n:
                continue
            a, b = d[case], n[case]
            L.append(f"| {case} | {fmt_ns(a['original_ns_per_call'])} | {fmt_ns(a['ours_ns_per_call'])} | "
                     f"{fmt_ns(b['ours_ns_per_call'])} | {speed_text(a)} | {speed_text(b)} |")
        L.append("")
        if v["native"].get("note"):
            L.append(f"Note: {v['native']['note']}\n")
    return L


def write_md(path, summary, machine, notes):
    L = []
    L.append("# vbench results\n")
    if machine:
        L.append("## Machine\n")
        for k in ("date", "host", "os", "cpu", "cores", "memory", "power", "pinned_cpu", "quiet", "virtual_machine", "rustc", "cc", "node", "counters"):
            if machine.get(k):
                L.append(f"- **{k}**: {machine[k]}")
        L.append("")
        if machine.get("revisions"):
            L.append("Revisions: " + ", ".join(f"{k} `{v}`" for k, v in machine["revisions"].items()) + "\n")
    L.append("## How to read this\n")
    L.append("Speedup is the original library's time divided by ours, so above 1.00x means ours is faster. "
             "Each case alternates the two in the same sitting; the number is the median ratio over the pairs, "
             "with its 95% confidence interval in brackets. Bold means the interval excludes 1.00x. "
             "Instructions compare instructions retired per call (fewer means ours does less work).\n")
    L.append("The API column says what was measured. **drop-in**: ours behind the original's API, the same caller "
             "code on both sides, so the library is the only difference. **native**: the same task through our own "
             "API against the original through its own; the two sides are different programs doing the same job.\n")
    by_comp = OrderedDict()
    for s in summary:
        by_comp.setdefault(s["comparison"], []).append(s)
    L.append("## Overview\n")
    L.append("| comparison | API | ours vs original | cases | geomean speedup | faster / same / slower | instructions (geomean) |")
    L.append("| --- | --- | --- | ---: | ---: | --- | ---: |")
    for comp, ss in by_comp.items():
        g = math.exp(statistics.mean(math.log(s["speedup"]) for s in ss))
        cnt = [sum(s["verdict"] == v for s in ss) for v in ("faster", "no measurable difference", "slower")]
        ir = [s["instructions_ratio"] for s in ss if s["instructions_ratio"] != ""]
        it = "n/a"
        if ir:
            gi = math.exp(statistics.mean(math.log(x) for x in ir))
            it = f"{abs(1 - gi) * 100:.0f}% {'fewer' if gi <= 1 else 'more'}"
        L.append(f"| {comp} | {META.get(comp, {}).get('api', '')} | {ss[0]['ours']} vs {ss[0]['original']} | {len(ss)} | {g:.2f}x | {cnt[0]} / {cnt[1]} / {cnt[2]} | {it} |")
    L.append("")
    L += side_by_side(by_comp)
    L.append("## Every comparison\n")
    for comp, ss in by_comp.items():
        meta = META.get(comp, {})
        label = meta.get("check")
        L.append(f"### {comp}: {ss[0]['ours']} vs {ss[0]['original']}\n")
        about = f"{ss[0]['pairs']} pairs per case."
        if meta.get("api"):
            about = f"API: {meta['api']}. " + about
        if meta.get("task"):
            about += f" Task: {meta['task']}."
        L.append(about + "\n")
        if meta.get("note"):
            L.append(f"Note: {meta['note']}\n")
        head = "| case | ours | original | speedup (95% CI) | instructions |"
        rule = "| --- | ---: | ---: | --- | --- |"
        if label:
            head += f" {label}: ours / original |"
            rule += " ---: |"
        L.append(head)
        L.append(rule)
        for s in ss:
            o = fmt_ns(s["ours_ns_per_call"])
            r = fmt_ns(s["original_ns_per_call"])
            if s["ours_mb_s"] != "":
                o += f" ({s['ours_mb_s']:.0f} MB/s)"
                r += f" ({s['original_mb_s']:.0f} MB/s)"
            flag = " †" if not s["same_check"] and not label else ""
            row = f"| {s['case']}{flag} | {o} | {r} | {speed_text(s)} | {ins_text(s)} |"
            if label:
                row += f" {s['ours_check']} / {s['original_check']} |"
            L.append(row)
        bad = [s for s in ss if not s["same_check"] and not label]
        if bad:
            L.append("\n† the two sides returned different check values, so they did not do the same work: "
                     + "; ".join(f"{s['case']}: ours {s['ours_check']}, original {s['original_check']}" for s in bad))
        L.append("")
    for n in notes:
        L.append(n)
    open(path, "w").write("\n".join(L) + "\n")


def main():
    d = sys.argv[1]
    rows = list(csv.DictReader(open(os.path.join(d, "raw.csv"))))
    summary = summarize(rows)
    write_csv(os.path.join(d, "summary.csv"), summary)
    machine = {}
    mp = os.path.join(d, "machine.json")
    if os.path.exists(mp):
        machine = json.load(open(mp))
    # The samples are the ground truth for whether counters worked.
    n_ins = sum(1 for r in summary if r["ours_instructions_per_call"] != "")
    if summary:
        tool = "proc_pid_rusage" if str(machine.get("os", "")).startswith("macOS") else "perf_event_open"
        machine["counters"] = (f"yes ({tool}; {n_ins} of {len(summary)} cases)" if n_ins
                               else f"no ({tool} gave no counts)")
    notes = []
    np_ = os.path.join(d, "node", "summary.md")
    if os.path.exists(np_):
        notes.append(open(np_).read())
    write_md(os.path.join(d, "report.md"), summary, machine, notes)
    print(f"wrote {os.path.join(d, 'summary.csv')} and {os.path.join(d, 'report.md')}")


if __name__ == "__main__":
    main()
