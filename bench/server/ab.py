#!/usr/bin/env python3
"""A/B two verilith-server builds on bench/server cases, alternating runs.

  ./ab.py BIN_A BIN_B --cases h2c-plaintext,h2-tls-plaintext [--rounds 5] [--secs 5]

Prints, per case, the median req/s and req per server CPU-second of each
build, and B's change over A.
"""
import argparse, os, statistics, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run as R


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("a")
    ap.add_argument("b")
    ap.add_argument("--cases", required=True)
    ap.add_argument("--rounds", type=int, default=5)
    ap.add_argument("--secs", type=float, default=5.0)
    ap.add_argument("--extra", default="")
    x = ap.parse_args()
    n = os.cpu_count()
    scpus, ccpus, threads = "0-%d" % (n // 2 - 1), "%d-%d" % (n // 2, n - 1), n // 2
    run = tempfile.mkdtemp(prefix="vab-")
    env = R.make_env(run, threads)
    res = {}
    for case in x.cases.split(","):
        c = R.CASES[case]
        gen = R.run_h2load if c["tool"] == "h2load" else R.run_wrk
        for r in range(x.rounds):
            order = [("A", x.a), ("B", x.b)] if r % 2 == 0 else [("B", x.b), ("A", x.a)]
            for tag, b in order:
                os.environ["VERILITH_SERVER"] = b
                cmd = R.server_cmds(env)["verilith"] + (x.extra.split() if x.extra else [])
                with R.Server("verilith", cmd, scpus, os.path.join(run, "log"), R.protocols("verilith", cmd)) as srv:
                    gen(case, ccpus, threads, 1.0, run)
                    c0 = srv.cpu()
                    o = gen(case, ccpus, threads, x.secs, run)
                    cpu = srv.cpu() - c0
                res.setdefault((case, tag), []).append((o["rps"] or 0, (o["requests"] or 0) / max(cpu, 1e-9), o.get("errors") or 0))
        a = res[(case, "A")]
        b = res[(case, "B")]
        ma, mb = statistics.median(v[0] for v in a), statistics.median(v[0] for v in b)
        ea, eb = statistics.median(v[1] for v in a), statistics.median(v[1] for v in b)
        print("%-20s A %8.0f req/s %8.0f /cpu-s | B %8.0f req/s %8.0f /cpu-s | %+5.1f%% req/s %+5.1f%% /cpu-s | errors %d %d" % (
            case, ma, ea, mb, eb, 100 * (mb / ma - 1), 100 * (eb / ea - 1), sum(v[2] for v in a), sum(v[2] for v in b)), flush=True)


if __name__ == "__main__":
    main()
