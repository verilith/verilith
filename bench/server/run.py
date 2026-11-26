#!/usr/bin/env python3
"""bench/server: Verilith's HTTP server against hyper, nginx and h2o.

Every server serves the same routes (GET /plaintext and GET /static/<file>),
is pinned to the same CPUs with the same number of worker threads, and is
measured in the same sitting by the same load generators (wrk for HTTP/1.1,
h2load for HTTP/2). Servers take turns case by case, and the order is
reversed every round, so drift in the machine hits all of them alike.

Reported per case and server: requests per second (median of the rounds and
the range), latency percentiles where the load generator gives them, and
requests per server CPU-second: the server's own user+system time over the
measured run, from its process group. The last is the number that survives a
noisy machine best, because it does not depend on how much CPU the load
generator happened to get.

  ./run.py                          # every server found, every case, 3 rounds
  ./run.py --servers nginx,verilith --cases h1-plaintext --rounds 5
  ./run.py --quick                  # 1 round of 3 s per case: a smoke test
  ./run.py --list                   # list cases and servers

The report is results/<date>-<host>/report.md, with raw.json beside it.
Linux only for now (taskset and /proc); macOS support is planned for the
Apple Silicon runs.
"""
import argparse, datetime, json, os, platform, re, shutil, signal, socket, statistics, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PORTS = {"HTTP": 18080, "H2C": 18081, "TLS": 18443}

# Files under /static/. Sizes cover a typical small asset, a large one and a
# download, so that sendfile and write batching both show up.
FILES = {"1k.bin": 1024, "64k.bin": 65536, "1m.bin": 1 << 20}

# A case: the load generator, its arguments, and the port it uses.
#   conns: connections; streams: concurrent streams per HTTP/2 connection;
#   pipeline: requests in flight per HTTP/1.1 connection.
CASES = {
    "h1-plaintext":      dict(tool="wrk", port="HTTP", path="/plaintext", conns=256),
    "h1-plaintext-pipe": dict(tool="wrk", port="HTTP", path="/plaintext", conns=256, pipeline=16),
    "h1-static-1k":      dict(tool="wrk", port="HTTP", path="/static/1k.bin", conns=256),
    "h1-static-64k":     dict(tool="wrk", port="HTTP", path="/static/64k.bin", conns=64),
    "h1-static-1m":      dict(tool="wrk", port="HTTP", path="/static/1m.bin", conns=16),
    "h1-close":          dict(tool="wrk", port="HTTP", path="/plaintext", conns=64, close=True),
    "h1-tls-plaintext":  dict(tool="wrk", port="TLS", path="/plaintext", conns=256, tls=True),
    "h2c-plaintext":     dict(tool="h2load", port="H2C", path="/plaintext", conns=64, streams=32),
    "h2-tls-plaintext":  dict(tool="h2load", port="TLS", path="/plaintext", conns=64, streams=32, tls=True),
    "h2-tls-static-64k": dict(tool="h2load", port="TLS", path="/static/64k.bin", conns=16, streams=16, tls=True),
}


def which(*names):
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    return None


def verilith_bin():
    for p in [os.environ.get("VERILITH_SERVER"),
              os.path.join(ROOT, "target/release/verilith-server"),
              os.path.join(ROOT, "target/release-abort/verilith-server")]:
        if p and os.path.exists(p):
            return p
    return None


def hyper_bin():
    p = os.path.join(HERE, "baselines/hyper/target/release/hyper-hello")
    return p if os.path.exists(p) else None


def fill(src, dst, vars):
    s = open(src).read()
    for k, v in vars.items():
        s = s.replace("@%s@" % k, str(v))
    open(dst, "w").write(s)


def server_cmds(env):
    """Each server: (command, setup). Only servers whose binary is found."""
    v = dict(USER=__import__("getpass").getuser(), THREADS=env["threads"], RUN=env["run"], ROOT=env["root"], CERT=env["cert"], KEY=env["key"], **PORTS)
    out = {}
    b = verilith_bin()
    if b:
        out["verilith"] = [b, "--threads", str(env["threads"]), "--http", str(PORTS["HTTP"]), "--h2c", str(PORTS["H2C"]),
                           "--tls", str(PORTS["TLS"]), "--cert", env["cert"], "--key", env["key"], "--root", env["root"]]
    b = hyper_bin()
    if b:
        out["hyper"] = [b, "--threads", str(env["threads"]), "--http", str(PORTS["HTTP"]), "--h2c", str(PORTS["H2C"]),
                        "--tls", str(PORTS["TLS"]), "--cert", env["cert"], "--key", env["key"], "--root", env["root"]]
    bun = os.environ.get("BUN") or which("bun") or (os.path.expanduser("~/.bun/bin/bun") if os.path.exists(os.path.expanduser("~/.bun/bin/bun")) else None)
    if bun:
        out["bun"] = ["env", "BUN=" + bun, os.path.join(HERE, "baselines/bun/run.sh"), str(env["threads"]),
                      str(PORTS["HTTP"]), str(PORTS["TLS"]), env["cert"], env["key"], env["root"]]
    b = os.path.join(HERE, "baselines/may-minihttp/target/release/may-minihttp-hello")
    if os.path.exists(b):
        out["may-minihttp"] = [b, "--threads", str(env["threads"]), "--http", str(PORTS["HTTP"]), "--root", env["root"]]
    b = which("nginx")
    if b:
        conf = os.path.join(env["run"], "nginx.conf")
        fill(os.path.join(HERE, "conf/nginx.conf.in"), conf, v)
        out["nginx"] = [b, "-c", conf, "-p", env["run"]]
    b = which("h2o")
    if b:
        conf = os.path.join(env["run"], "h2o.conf")
        fill(os.path.join(HERE, "conf/h2o.conf.in"), conf, v)
        out["h2o"] = [b, "-c", conf]
    return out


def make_env(run, threads):
    root = os.path.join(run, "www")
    os.makedirs(root, exist_ok=True)
    for name, size in FILES.items():
        with open(os.path.join(root, name), "wb") as f:
            f.write(bytes((i * 131 + 7) & 0xFF for i in range(size)))
    with open(os.path.join(root, "plaintext"), "wb") as f:
        f.write(b"Hello, World!")
    cert, key = os.path.join(run, "cert.pem"), os.path.join(run, "key.pem")
    # An ECDSA P-256 certificate: what most TLS 1.3 deployments serve, and
    # cheap enough that the handshake does not drown the server's own work.
    subprocess.run(["openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1", "-nodes",
                    "-keyout", key, "-out", cert, "-days", "30", "-subj", "/CN=localhost",
                    "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1"], check=True, capture_output=True)
    for d in ["body", "proxy", "fastcgi", "uwsgi", "scgi"]:
        os.makedirs(os.path.join(run, d), exist_ok=True)
    return dict(run=run, root=root, cert=cert, key=key, threads=threads)


def wait_port(port, timeout=10.0):
    end = time.time() + timeout
    while time.time() < end:
        try:
            socket.create_connection(("127.0.0.1", port), 0.2).close()
            return True
        except OSError:
            time.sleep(0.05)
    return False


def group_cpu(pgid):
    """User+system seconds of every live process in a process group."""
    tick = os.sysconf("SC_CLK_TCK")
    total = 0
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            s = open("/proc/%s/stat" % p).read()
        except OSError:
            continue
        f = s[s.rindex(")") + 2:].split()
        if int(f[2]) == pgid:  # field 5, pgrp
            total += int(f[11]) + int(f[12])  # utime, stime
    return total / tick


def protocols(name, cmd):
    """The ports a server serves: all three, except a verilith-server build
    that says otherwise with --protocols (one line: http, h2c, tls)."""
    fixed = {"bun": {"HTTP", "TLS"}, "may-minihttp": {"HTTP"}}
    if name in fixed:
        return fixed[name]
    if name != "verilith":
        return set(PORTS)
    try:
        out = subprocess.run([cmd[0], "--protocols"], capture_output=True, text=True, timeout=10).stdout
    except Exception:
        return set(PORTS)
    names = {"http": "HTTP", "h2c": "H2C", "tls": "TLS"}
    got = {names[w] for w in out.replace(",", " ").split() if w in names}
    return got or set(PORTS)


class Server:
    def __init__(self, name, cmd, cpus, log, ports=None):
        self.name, self.cmd, self.cpus = name, cmd, cpus
        self.ports = ports or set(PORTS)
        self.log = open(log, "w")

    def __enter__(self):
        self.p = subprocess.Popen(["taskset", "-c", self.cpus] + self.cmd, stdout=self.log, stderr=subprocess.STDOUT,
                                  start_new_session=True)
        for port in [PORTS[k] for k in self.ports]:
            if not wait_port(port):
                self.__exit__()
                raise RuntimeError("%s did not open port %d; see %s" % (self.name, port, self.log.name))
        return self

    def cpu(self):
        return group_cpu(self.p.pid)

    def __exit__(self, *a):
        try:
            os.killpg(self.p.pid, signal.SIGTERM)
            self.p.wait(5)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            try:
                os.killpg(self.p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.p.wait()
        # nginx's workers can outlive the master by a moment; wait for the ports.
        for _ in range(100):
            if not any(port_open(p) for p in PORTS.values()):
                break
            time.sleep(0.05)


def port_open(port):
    try:
        socket.create_connection(("127.0.0.1", port), 0.1).close()
        return True
    except OSError:
        return False


PIPE_LUA = """
init = function(args)
  local r = {}
  for i = 1, %d do r[i] = wrk.format(nil, "%s") end
  req = table.concat(r)
end
request = function() return req end
"""


def unit(v, u):
    m = {"": 1, "k": 1e3, "K": 1e3, "M": 1e6, "G": 1e9, "us": 1e-6, "ms": 1e-3, "s": 1.0, "m": 60.0}
    return float(v) * m[u]


def run_wrk(case, cpus, threads, dur, run):
    c = CASES[case]
    scheme = "https" if c.get("tls") else "http"
    url = "%s://127.0.0.1:%d%s" % (scheme, PORTS[c["port"]], c["path"])
    cmd = ["taskset", "-c", cpus, "wrk", "-t", str(threads), "-c", str(c["conns"]), "-d", "%gs" % dur, "--latency"]
    if c.get("close"):
        cmd += ["-H", "Connection: close"]
    if c.get("pipeline"):
        lua = os.path.join(run, "pipe%d.lua" % c["pipeline"])
        open(lua, "w").write(PIPE_LUA % (c["pipeline"], c["path"]))
        cmd += ["-s", lua]
    cmd.append(url)
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=dur + 60).stdout
    r = {}
    m = re.search(r"Requests/sec:\s+([\d.]+)", out)
    r["rps"] = float(m.group(1)) if m else None
    m = re.search(r"(\d+) requests in", out)
    r["requests"] = int(m.group(1)) if m else None
    for pct in ["50", "90", "99"]:
        m = re.search(r"^\s+%s%%\s+([\d.]+)(us|ms|s)" % pct, out, re.M)
        r["p" + pct] = unit(m.group(1), m.group(2)) if m else None
    m = re.search(r"Non-2xx or 3xx responses: (\d+)", out)
    r["errors"] = int(m.group(1)) if m else 0
    m = re.search(r"Socket errors: connect (\d+), read (\d+), write (\d+), timeout (\d+)", out)
    if m:
        r["errors"] += sum(int(x) for x in m.groups())
    r["raw"] = out
    return r


def run_h2load(case, cpus, threads, dur, run):
    c = CASES[case]
    scheme = "https" if c.get("tls") else "http"
    url = "%s://127.0.0.1:%d%s" % (scheme, PORTS[c["port"]], c["path"])
    conns = c["conns"]
    cmd = ["taskset", "-c", cpus, "h2load", "-t", str(threads), "-c", str(conns), "-m", str(c.get("streams", 1)),
           "-D", "%g" % dur, "--warm-up-time=0"]
    cmd.append(url)
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=dur + 60).stdout
    r = {}
    m = re.search(r"finished in [\d.]+\w+, ([\d.]+) req/s", out)
    r["rps"] = float(m.group(1)) if m else None
    m = re.search(r"requests: \d+ total, \d+ started, (\d+) done, (\d+) succeeded, (\d+) failed, (\d+) errored", out)
    r["requests"] = int(m.group(1)) if m else None
    r["errors"] = (int(m.group(3)) + int(m.group(4))) if m else None
    m = re.search(r"time for request:\s+([\d.]+)(us|ms|s)\s+([\d.]+)(us|ms|s)\s+([\d.]+)(us|ms|s)", out)
    r["mean"] = unit(m.group(5), m.group(6)) if m else None
    r["raw"] = out
    return r


def measure(srv, case, ccpus, cthreads, dur, warm, run):
    f = run_wrk if CASES[case]["tool"] == "wrk" else run_h2load
    if warm:
        f(case, ccpus, cthreads, warm, run)
    c0, t0 = srv.cpu(), time.time()
    r = f(case, ccpus, cthreads, dur, run)
    c1, t1 = srv.cpu(), time.time()
    r["server_cpu_s"] = c1 - c0
    r["wall_s"] = t1 - t0
    if r.get("requests") and r["server_cpu_s"] > 0:
        r["req_per_cpu_s"] = r["requests"] / r["server_cpu_s"]
    return r


def fmt_rate(x):
    if x is None:
        return "n/a"
    return "%.0fk" % (x / 1e3) if x >= 1e4 else "%.0f" % x


def fmt_lat(x):
    if x is None:
        return "n/a"
    return "%.0f µs" % (x * 1e6) if x < 1e-3 else "%.2f ms" % (x * 1e3)


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def report(results, servers, cases, meta, out):
    L = ["# bench/server report", ""]
    L.append("%s, %s, %d CPUs (server on %s, load generator on %s), %d rounds of %gs per case." % (
        meta["date"], meta["cpu"], meta["ncpu"], meta["server_cpus"], meta["client_cpus"], meta["rounds"], meta["duration"]))
    L.append("")
    L.append("Versions: " + ", ".join("%s %s" % (k, v) for k, v in meta["versions"].items()))
    L.append("")
    L.append("Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per "
             "server CPU-second (higher is better), the figure least disturbed by a shared machine.")
    L.append("")
    for case in cases:
        L.append("## %s" % case)
        L.append("")
        L.append("| server | req/s | range | req per server CPU-s | p50 | p99 | errors |")
        L.append("|---|---:|---:|---:|---:|---:|---:|")
        for s in servers:
            rs = results.get(case, {}).get(s, [])
            if not rs:
                continue
            rps = [r.get("rps") for r in rs]
            ok = [x for x in rps if x is not None]
            rng = "%s to %s" % (fmt_rate(min(ok)), fmt_rate(max(ok))) if ok else "n/a"
            p50 = med([r.get("p50") for r in rs]) or med([r.get("mean") for r in rs])
            L.append("| %s | %s | %s | %s | %s | %s | %s |" % (
                s, fmt_rate(med(rps)), rng, fmt_rate(med([r.get("req_per_cpu_s") for r in rs])),
                fmt_lat(p50), fmt_lat(med([r.get("p99") for r in rs])), sum((r.get("errors") or 0) for r in rs)))
        L.append("")
    L.append("h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.")
    open(out, "w").write("\n".join(L) + "\n")


def versions(cmds):
    v = {}
    for name in cmds:
        try:
            if name == "nginx":
                v[name] = subprocess.run(["nginx", "-v"], capture_output=True, text=True).stderr.strip().split("/")[-1]
            elif name == "h2o":
                v[name] = subprocess.run(["h2o", "--version"], capture_output=True, text=True).stdout.split("\n")[0].split()[-1]
            elif name == "hyper":
                lock = open(os.path.join(HERE, "baselines/hyper/Cargo.lock")).read()
                m = re.search(r'name = "hyper"\nversion = "([^"]+)"', lock)
                v[name] = m.group(1) if m else "?"
            elif name == "bun":
                bun = cmds[name][1].split("=", 1)[1]
                v[name] = subprocess.run([bun, "--version"], capture_output=True, text=True).stdout.strip()
            elif name == "may-minihttp":
                lock = open(os.path.join(HERE, "baselines/may-minihttp/Cargo.lock")).read()
                m = re.search(r'name = "may_minihttp"\nversion = "([^"]+)"', lock)
                v[name] = m.group(1) if m else "?"
            elif name == "verilith":
                v[name] = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"], capture_output=True,
                                         text=True).stdout.strip()
        except Exception:
            v[name] = "?"
    return v


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    n = os.cpu_count()
    ap.add_argument("--servers", help="comma-separated (default: every one found)")
    ap.add_argument("--cases", help="comma-separated (default: all)")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--duration", type=float, default=10.0)
    ap.add_argument("--warmup", type=float, default=2.0)
    ap.add_argument("--server-cpus", default="0-%d" % (n // 2 - 1))
    ap.add_argument("--client-cpus", default="%d-%d" % (n // 2, n - 1))
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--out")
    a = ap.parse_args()
    if a.quick:
        a.rounds, a.duration, a.warmup = 1, 3.0, 0.5

    def count(spec):
        k = 0
        for part in spec.split(","):
            lo, _, hi = part.partition("-")
            k += int(hi or lo) - int(lo) + 1
        return k

    run = tempfile.mkdtemp(prefix="vserver-bench-")
    os.chmod(run, 0o755)
    env = make_env(run, count(a.server_cpus))
    cmds = server_cmds(env)
    if a.list:
        print("servers found:", ", ".join(cmds) or "none")
        print("cases:", ", ".join(CASES))
        return
    servers = a.servers.split(",") if a.servers else list(cmds)
    missing = [s for s in servers if s not in cmds]
    if missing:
        sys.exit("not found: %s (build it, or install it)" % ", ".join(missing))
    cases = a.cases.split(",") if a.cases else list(CASES)
    host = socket.gethostname().split(".")[0]
    out = a.out or os.path.join(HERE, "results", "%s-%s" % (datetime.date.today().isoformat(), host))
    os.makedirs(out, exist_ok=True)
    cpu = "?"
    try:
        cpu = re.search(r"model name\s+: (.*)", open("/proc/cpuinfo").read()).group(1)
    except Exception:
        cpu = platform.processor()
    meta = dict(date=datetime.datetime.now().isoformat(timespec="minutes"), cpu=cpu, ncpu=n, server_cpus=a.server_cpus,
                client_cpus=a.client_cpus, rounds=a.rounds, duration=a.duration, versions=versions(servers))
    serves = {s: protocols(s, cmds[s]) for s in servers}
    results = {}
    for rnd in range(a.rounds):
        order = servers if rnd % 2 == 0 else servers[::-1]
        for case in cases:
            for s in order:
                if CASES[case]["port"] not in serves[s]:
                    continue
                try:
                    with Server(s, cmds[s], a.server_cpus, os.path.join(out, "%s.log" % s), serves[s]) as srv:
                        r = measure(srv, case, a.client_cpus, count(a.client_cpus), a.duration, a.warmup, run)
                except RuntimeError as e:
                    print("round %d %-18s %-9s failed: %s" % (rnd + 1, case, s, e), flush=True)
                    continue
                results.setdefault(case, {}).setdefault(s, []).append(r)
                print("round %d %-18s %-9s %10s req/s  %10s req/CPU-s  errors %s" % (
                    rnd + 1, case, s, fmt_rate(r.get("rps")), fmt_rate(r.get("req_per_cpu_s")), r.get("errors")),
                    flush=True)
    json.dump(dict(meta=meta, results=results), open(os.path.join(out, "raw.json"), "w"), indent=1)
    report(results, servers, cases, meta, os.path.join(out, "report.md"))
    print("report:", os.path.join(out, "report.md"))
    shutil.rmtree(run, ignore_errors=True)


if __name__ == "__main__":
    main()
