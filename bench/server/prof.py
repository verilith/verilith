#!/usr/bin/env python3
"""Profile one server under one bench/server case with perf.

  ./prof.py verilith h1-plaintext [--secs 8] [--out DIR]

Starts the server as run.py does (pinned to the server CPUs, run.py's
threads), warms up, then runs the load generator while `perf record -g`
samples the server's process group, and writes DIR/<server>-<case>.perf.data
and a flat and a caller-grouped report beside it (DIR defaults to
target/bench-prof). Needs perf, and perf_event_paranoid at most 1.
"""
import argparse, os, subprocess, sys, tempfile, threading, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run as R


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("server")
    ap.add_argument("case")
    ap.add_argument("--secs", type=float, default=8.0)
    ap.add_argument("--freq", type=int, default=1999)
    ap.add_argument("--out", default=os.path.join(R.ROOT, "target/bench-prof"))
    ap.add_argument("--extra", default="", help="extra server arguments, space-separated")
    a = ap.parse_args()
    n = os.cpu_count()
    scpus, ccpus = "0-%d" % (n // 2 - 1), "%d-%d" % (n // 2, n - 1)
    threads = n // 2
    os.makedirs(a.out, exist_ok=True)
    run = tempfile.mkdtemp(prefix="vprof-")
    env = R.make_env(run, threads)
    cmds = R.server_cmds(env)
    cmd = cmds[a.server] + (a.extra.split() if a.extra else [])
    ports = R.protocols(a.server, cmd)
    c = R.CASES[a.case]
    tag = "%s-%s" % (a.server, a.case)
    data = os.path.join(a.out, tag + ".perf.data")
    with R.Server(a.server, cmd, scpus, os.path.join(a.out, tag + ".log"), ports) as srv:
        gen = R.run_h2load if c["tool"] == "h2load" else R.run_wrk
        gen(a.case, ccpus, threads, 2.0, run)  # warm-up
        res = {}
        t = threading.Thread(target=lambda: res.update(gen(a.case, ccpus, threads, a.secs + 2, run)))
        c0 = srv.cpu()
        t.start()
        time.sleep(1.0)
        # Every process in the server's group (nginx's workers too).
        pids = subprocess.run(["pgrep", "-g", str(srv.p.pid)], capture_output=True, text=True).stdout.split()
        subprocess.run(["perf", "record", "-F", str(a.freq), "-g", "--call-graph", "dwarf,16384" if a.server.startswith("verilith") else "fp",
                        "-o", data, "-p", ",".join(pids), "--", "sleep", str(a.secs)], capture_output=True)
        t.join()
        cpu = srv.cpu() - c0
    rps = res.get("rps")
    print("%s: %s req/s, %.0f req per server CPU-s" % (tag, rps, (res.get("requests") or 0) / max(cpu, 1e-9)))
    with open(os.path.join(a.out, tag + ".flat.txt"), "w") as f:
        subprocess.run(["perf", "report", "-i", data, "--no-children", "--sort", "dso,symbol", "--stdio", "-g", "none",
                        "--percent-limit", "0.3"], stdout=f, stderr=subprocess.DEVNULL)
    with open(os.path.join(a.out, tag + ".children.txt"), "w") as f:
        subprocess.run(["perf", "report", "-i", data, "--children", "--sort", "symbol", "--stdio", "-g", "none",
                        "--percent-limit", "1"], stdout=f, stderr=subprocess.DEVNULL)


if __name__ == "__main__":
    main()
