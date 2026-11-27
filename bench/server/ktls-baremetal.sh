#!/usr/bin/env bash
# kTLS on a Linux machine: checks the kernel has it, runs the kTLS tests
# with the kernel required to take the connections, shows that a static
# file goes out with sendfile under TLS, then benchmarks verilith-server's
# userspace TLS against kTLS (bench/server/run.py).
#
#   bench/server/ktls-baremetal.sh            # 3 rounds, 10 s per case (about 15 minutes)
#   bench/server/ktls-baremetal.sh --quick    # 1 round, 3 s per case
#
# Run from a checkout, as a user with sudo (for apt and `modprobe tls`).
# SERVER_CPUS and CLIENT_CPUS choose the CPUs (default 0-7 and 8-23: on a
# c7i.metal-24xl these are 8 and 16 physical cores, with their
# hyperthread siblings, 48-71, left idle). Results go to
# bench/server/results/ktls-<date>-<host>/ (report.md, raw.json, and the
# logs of every step).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
quick=""
[ "${1:-}" = "--quick" ] && quick="--quick"
server_cpus=${SERVER_CPUS:-0-7}
client_cpus=${CLIENT_CPUS:-8-23}
out="$root/bench/server/results/ktls-$(date +%F)-$(hostname -s)"
mkdir -p "$out"
step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

step "1/6 Kernel"
uname -a | tee "$out/uname.txt"
sudo modprobe tls || fail "modprobe tls: this kernel has no tls module (CONFIG_TLS)"
grep -qw tls /proc/sys/net/ipv4/tcp_available_ulp || fail "tls is not in tcp_available_ulp"
echo "tcp_available_ulp: $(cat /proc/sys/net/ipv4/tcp_available_ulp)"
# AES-GCM is built into Ubuntu's kernels; ChaCha20-Poly1305 may be a module.
sudo modprobe chacha20poly1305 2> /dev/null || true

step "2/6 Packages and Rust"
need=()
for p in wrk:wrk h2load:nghttp2-client strace:strace curl:curl cmake:cmake clang:clang python3:python3 openssl:openssl cc:build-essential; do
  command -v "${p%%:*}" > /dev/null || need+=("${p#*:}")
done
if [ ${#need[@]} -gt 0 ]; then
  sudo apt-get update -qq
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -qq "${need[@]}" pkg-config
fi
if ! command -v cargo > /dev/null; then
  [ -x "$HOME/.cargo/bin/cargo" ] || curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
  . "$HOME/.cargo/env"
fi
cargo --version

step "3/6 Build (release, --features tls)"
cargo build --release -p verilith-server --features tls 2>&1 | tail -3
bin="$root/target/release/verilith-server"
"$bin" --protocols | grep -qw ktls || fail "$bin was built without kTLS"

step "4/6 kTLS tests (the kernel must take the connections)"
VERILITH_REQUIRE_KTLS=1 cargo test --release -p verilith-server --features tls --test ktls -- --test-threads 1 --nocapture 2>&1 | tee "$out/ktls-tests.log" | grep -E "^test |^ok$|test result|kTLS:"
grep -q "test result: ok" "$out/ktls-tests.log" || fail "kTLS tests; see $out/ktls-tests.log"

step "5/6 One static file over TLS, traced"
tmp=$(mktemp -d)
trap 'pkill -x verilith-server 2> /dev/null || true; rm -rf "$tmp"' EXIT
head -c 65536 /dev/urandom > "$tmp/64k.bin"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -keyout "$tmp/key.pem" -out "$tmp/cert.pem" -days 1 -subj /CN=localhost 2> /dev/null
before=$(awk '$1 == "TlsTxSw" {print $2}' /proc/net/tls_stat)
strace -f -e trace=setsockopt,sendfile -o "$out/trace.txt" "$bin" --threads 1 --http 28080 --tls 28443 --cert "$tmp/cert.pem" --key "$tmp/key.pem" --root "$tmp" --ktls &
spid=$!
for _ in $(seq 50); do curl -sk -o /dev/null https://127.0.0.1:28443/plaintext && break; sleep 0.1; done
curl -sk --http1.1 -o "$tmp/got.bin" https://127.0.0.1:28443/static/64k.bin
# Stop the server, not strace: strace ends with it, its trace complete.
pkill -x verilith-server || true
wait "$spid" 2> /dev/null || true
spid=
cmp -s "$tmp/got.bin" "$tmp/64k.bin" || fail "the file came back different"
after=$(awk '$1 == "TlsTxSw" {print $2}' /proc/net/tls_stat)
grep -q 'TLS_TX' "$out/trace.txt" || fail "no setsockopt(TLS_TX); see $out/trace.txt"
grep -q 'sendfile(.*= 65536' "$out/trace.txt" || fail "the body was not sent with sendfile; see $out/trace.txt"
echo "ok: the kernel took the keys (TlsTxSw $before -> $after) and the 64 KiB body went out with one sendfile"
grep -E 'TLS_TX|sendfile' "$out/trace.txt" | cut -c1-110

step "6/6 Benchmark: userspace TLS against kTLS (server CPUs $server_cpus, client CPUs $client_cpus)"
# verilith: TLS in userspace. verilith-ktls: kTLS, sendfile for 16-112 KiB
# (as on plaintext). verilith-ktls-sendfile-all: kTLS, sendfile for every
# file from 16 KiB up (1m.bin too).
cases=h1-tls-static-1k,h1-tls-static-64k,h1-tls-static-1m,h1-tls-plaintext,h2-tls-static-64k
python3 bench/server/run.py $quick --servers verilith,verilith-ktls,verilith-ktls-sendfile-all --cases "$cases" \
  --server-cpus "$server_cpus" --client-cpus "$client_cpus" --out "$out" 2>&1 | tee "$out/bench.log"
cp /proc/net/tls_stat "$out/tls_stat.txt"
grep -q "kTLS in this kernel" "$out"/verilith-ktls*.log 2> /dev/null && fail "a kTLS server ran in userspace; see $out/verilith-ktls.log"

python3 - "$out/raw.json" << 'EOF'
import json, statistics, sys
r = json.load(open(sys.argv[1]))["results"]
def med(rs, k):
    v = [x.get(k) for x in rs if x.get(k)]
    return statistics.median(v) if v else None
print("\n%-20s %28s %28s %28s" % ("median of rounds", "userspace", "kTLS", "kTLS, sendfile all"))
for case, by in r.items():
    row = []
    base = by.get("verilith", [])
    for s in ["verilith", "verilith-ktls", "verilith-ktls-sendfile-all"]:
        rps, cpu = med(by.get(s, []), "rps"), med(by.get(s, []), "req_per_cpu_s")
        b = med(base, "req_per_cpu_s")
        rel = " (%+.0f%%/CPU)" % (100 * (cpu / b - 1)) if s != "verilith" and cpu and b else ""
        row.append("%9.0f/s %8.0f/CPU-s%s" % (rps or 0, cpu or 0, rel))
    print("%-20s %s" % (case, "  ".join(row)))
EOF
printf '\nDone. Report: %s/report.md (send the whole directory back).\n' "$out"
