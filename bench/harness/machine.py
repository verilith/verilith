#!/usr/bin/env python3
"""machine.py OUT.json BIN_DIR SRC_DIR: records the machine, the
toolchain and every source revision a run used. Standard library only."""
import datetime
import json
import os
import platform
import subprocess
import sys


def sh(*cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=30).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def first(s):
    return s.splitlines()[0] if s else ""


def main():
    out, bindir, src = sys.argv[1], sys.argv[2], sys.argv[3]
    m = {"date": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
         "host": platform.node().split(".")[0]}
    if platform.system() == "Darwin":
        m["os"] = f"macOS {sh('sw_vers', '-productVersion')} ({sh('sw_vers', '-buildVersion')}), {platform.machine()}"
        m["cpu"] = sh("sysctl", "-n", "machdep.cpu.brand_string")
        p, e = sh("sysctl", "-n", "hw.perflevel0.physicalcpu"), sh("sysctl", "-n", "hw.perflevel1.physicalcpu")
        m["cores"] = f"{p} performance + {e} efficiency" if p and e else sh("sysctl", "-n", "hw.ncpu")
        mem = sh("sysctl", "-n", "hw.memsize")
        m["memory"] = f"{int(mem) / 2**30:.0f} GiB" if mem.isdigit() else ""
        batt = sh("pmset", "-g", "batt")
        lpm = [l for l in sh("pmset", "-g").splitlines() if "lowpowermode" in l]
        m["power"] = (first(batt).replace("Now drawing from ", "") +
                      ("; low power mode " + lpm[0].split()[-1] if lpm else ""))
        therm = sh("pmset", "-g", "therm")
        m["thermal"] = " ".join(l.strip() for l in therm.splitlines() if "CPU_Speed_Limit" in l or "warning" in l.lower())
    else:
        m["os"] = f"{platform.system()} {platform.release()}, {platform.machine()}"
        cpu = [l.split(":", 1)[1].strip() for l in sh("lscpu").splitlines() if l.startswith("Model name")]
        m["cpu"] = cpu[0] if cpu else platform.processor()
        m["cores"] = str(os.cpu_count())
        try:
            kb = [l for l in open("/proc/meminfo") if l.startswith("MemTotal")][0].split()[1]
            m["memory"] = f"{int(kb) / 2**20:.0f} GiB"
        except OSError:
            pass
        def read(path):
            try:
                return open(path).read().strip()
            except OSError:
                return None
        # What scripts/linux-quiet.sh sets, as it was during this run.
        cpu = os.environ.get("VBENCH_CPU")
        gov = read("/sys/devices/system/cpu/cpu%s/cpufreq/scaling_governor" % (cpu or 0))
        nt, boost = read("/sys/devices/system/cpu/intel_pstate/no_turbo"), read("/sys/devices/system/cpu/cpufreq/boost")
        p = ["governor " + gov] if gov else []
        if nt is not None:
            p.append("turbo " + ("off" if nt == "1" else "on"))
        elif boost is not None:
            p.append("boost " + ("off" if boost == "0" else "on"))
        m["power"] = ", ".join(p)
        m["pinned_cpu"] = cpu
        m["online_cpus"] = read("/sys/devices/system/cpu/online")
        m["quiet"] = os.path.exists("/run/vbench-quiet.state")
        m["virtual_machine"] = "hypervisor" in (read("/proc/cpuinfo") or "")
        m["perf_event_paranoid"] = read("/proc/sys/kernel/perf_event_paranoid")
    m["rustc"] = sh("rustc", "-V")
    m["cc"] = first(sh(os.environ.get("CC", "cc"), "--version"))
    m["developer_dir"] = os.environ.get("DEVELOPER_DIR") or first(sh("xcode-select", "-p")) if sys.platform == "darwin" else None
    m["flags"] = f"C: -O3 {os.environ.get('CPUFLAG', '')}; Rust: {os.environ.get('RUSTFLAGS', '')}, fat LTO, 1 codegen unit"
    # Do the counters work here? Ask any runner.
    exe = os.path.join(bindir, "zlib-zlib")
    if os.path.exists(exe):
        r = subprocess.run([exe, "inflate"], input="info\nquit\n", capture_output=True, text=True,
                           env=dict(os.environ, VBENCH_DATA=os.path.join(os.path.dirname(os.path.dirname(bindir)), "data", "zlib")))
        ok = r.stdout.strip().endswith("1")
        m["counters"] = ("yes" if ok else "no") + (" (proc_pid_rusage)" if platform.system() == "Darwin" else " (perf_event_open)")
    revs = {}
    for name in sorted(os.listdir(src)) if os.path.isdir(src) else []:
        d = os.path.join(src, name)
        # Only clones of the originals: a plain directory would report the
        # revision of whatever repository contains work/.
        if not os.path.exists(os.path.join(d, ".git")):
            continue
        rev = sh("git", "-C", d, "rev-parse", "--short=12", "HEAD")
        if rev:
            dirty = sh("git", "-C", d, "status", "--porcelain", "--untracked-files=no")
            revs[name] = rev + ("+dirty" if dirty else "")
    # Our libraries and this harness are one repository: one revision.
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    rev = sh("git", "-C", root, "rev-parse", "--short=12", "HEAD")
    dirty = sh("git", "-C", root, "status", "--porcelain", "--untracked-files=no")
    revs["verilith"] = (rev + ("+dirty" if dirty else "")) if rev else "uncommitted"
    m["revisions"] = revs
    json.dump(m, open(out, "w"), indent=2)
    print(json.dumps(m, indent=2))


if __name__ == "__main__":
    main()
