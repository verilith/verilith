#!/usr/bin/env bash
# vbench: every Verilith library against the library it
# replaces, on this machine, with one method. One command:
#
#   ./run.sh                 everything (about 1.5 to 2.5 hours on a MacBook,
#                            most of it building and benchmarking Node.js)
#   ./run.sh --skip-node     only the library benchmarks (about 10 to 30 minutes)
#   ./run.sh --quick         smoke test: 3 cases per comparison, 5 pairs, no Node
#
# Options: --only zlib,json   only these suites (or comparison ids; see
#                            `python3 harness/vbench.py --list`); skips Node
#          --pairs N          sample pairs per case (default 31)
#          --out DIR          results directory (default results/DATE-HOST)
#
# Results land in results/<date>-<host>/: report.md (read this), summary.csv,
# raw.csv (every sample), machine.json, node/ and the logs.
set -euo pipefail
cd "$(dirname "$0")"
quick=0 node=1 only="" pairs=31 out=""
while [ $# -gt 0 ]; do
  case $1 in
    --quick) quick=1; node=0; pairs=5 ;;
    --skip-node) node=0 ;;
    --only) only=$2; node=0; shift ;;
    --pairs) pairs=$2; shift ;;
    --out) out=$2; shift ;;
    -h|--help) sed -n '2,19p' "$0"; exit 0 ;;
    *) echo "unknown option $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done
. scripts/lib.sh

# --- Preflight -------------------------------------------------------------
missing=""
tools="git cargo rustc python3 cmake unzip curl patch perl $CC $CXX"
[ "$OS" = Linux ] && tools="$tools xz taskset"
[ "$OS" = Linux ] && [ "$(uname -m)" = x86_64 ] && tools="$tools nasm"
for t in $tools; do command -v "$t" >/dev/null || missing="$missing $t"; done
if [ -n "$missing" ]; then
  if [ "$OS" = Darwin ]; then
    die "missing:$missing. Install with: xcode-select --install (compilers, git); brew install cmake ninja; curl https://sh.rustup.rs -sSf | sh"
  fi
  if command -v apt-get >/dev/null; then die "missing:$missing. Install everything with: scripts/setup-ubuntu.sh --no-server"; fi
  die "missing:$missing"
fi
if ! command -v ninja >/dev/null; then
  if [ "$OS" = Darwin ]; then warn "ninja not found: Node will build with make, which is slower (brew install ninja)"
  else warn "ninja not found: Node will build with make, which is slower (sudo apt-get install ninja-build)"; fi
fi
need=15; [ $node = 1 ] && need=45
free=$(df -Pk "$ROOT" | awk 'NR==2 {print int($4 / 1048576)}')
[ "$free" -ge "$need" ] || warn "only ${free} GB free for work/; this run needs about $need GB"
if [ "$OS" = Linux ]; then
  # Instruction counts need perf_event_open: Ubuntu's kernels default to
  # perf_event_paranoid 4, which refuses it without root.
  p=$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo 0)
  [ "$p" -le 2 ] || warn "kernel.perf_event_paranoid is $p: instruction counts will be n/a (sudo scripts/linux-quiet.sh on sets it to 1)"
  [ -n "${VBENCH_CPU:-}" ] || warn "VBENCH_CPU is not set: runners are not pinned to a CPU (see scripts/linux-quiet.sh)"
  if [ -n "${VBENCH_CPU:-}" ] && ! taskset -c "$VBENCH_CPU" true 2>/dev/null; then die "VBENCH_CPU=$VBENCH_CPU is not a CPU this process can run on"; fi
fi
if [ "$OS" = Darwin ]; then
  src=$(pmset -g batt | head -1)
  case $src in *"AC Power"*) ;; *) warn "on battery: plug in the charger, battery power throttles the CPU ($src)" ;; esac
  if pmset -g | grep -q 'lowpowermode *1'; then warn "Low Power Mode is on: turn it off in System Settings > Battery"; fi
  echo "Before the run starts: quit other apps (browsers, Slack, Docker, Spotlight indexing), keep the lid open and the Mac plugged in." >&2
fi

host=$(hostname -s 2>/dev/null || hostname)
RESULTS=${out:-results/$(date +%Y-%m-%d-%H%M)-$host}
mkdir -p "$RESULTS"
RESULTS=$(cd "$RESULTS" && pwd)
exec > >(tee -a "$RESULTS/run.sh.log") 2>&1
say "results go to $RESULTS"

# Keep the Mac awake for the whole run.
awake() { if [ "$OS" = Darwin ]; then caffeinate -i -s "$@"; else "$@"; fi; }

# --- Fetch, build ----------------------------------------------------------
scripts/fetch.sh
if [ -n "$only" ]; then
  suites=$(python3 -c "
import sys; sys.path.insert(0, 'harness'); import suites
want = set('$only'.split(','))
print(' '.join(sorted({c['suite'] for c in suites.COMPARISONS if c['suite'] in want or c['id'] in want})))")
  scripts/build.sh $suites
else
  scripts/build.sh
fi
python3 harness/machine.py "$RESULTS/machine.json" "$BIN" "$SRC" >/dev/null

# --- Library benchmarks ----------------------------------------------------
say "library benchmarks ($pairs pairs per case)"
args=(--out "$RESULTS" --pairs "$pairs")
[ $quick = 1 ] && args=(--out "$RESULTS" --pairs 5 --target-ms 10 --quick)
[ -n "$only" ] && args+=(--only "$only")
[ "$OS" = Linux ] && [ -n "${VBENCH_CPU:-}" ] && args+=(--cpu "$VBENCH_CPU")
bench_lock library
awake python3 harness/vbench.py "${args[@]}"
bench_unlock

# --- Node.js ---------------------------------------------------------------
if [ $node = 1 ]; then
  if ! awake scripts/node.sh "$RESULTS"; then
    warn "the Node.js part failed; the library results are still complete (log: $RESULTS/run.sh.log)"
  fi
fi

python3 harness/report.py "$RESULTS"
say "done: $RESULTS/report.md"
