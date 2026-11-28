#!/usr/bin/env bash
# verilith-resolver against Unbound, both validating DNSSEC, iterating from
# the signed test hierarchy (tests/sec, on 127.0.1.2-11 port 53; needs root
# for port 53). Each answer of the cold run needs a signature checked; the
# hits are answered from the cache.
#   bench/run-dnssec.sh [ROUNDS] > results.md
# Needs unbound, dnsperf (2.14+), dig, taskset. CPUs as bench/run.sh.
set -euo pipefail
cd "$(dirname "$0")/../../.."
rounds=${1:-3}
CPUS_RES=${CPUS_RES:-0,1}
CPUS_LOAD=${CPUS_LOAD:-2,3}
CPU_HIER=${CPU_HIER:-3}
nres=$(( $(echo "$CPUS_RES" | tr ',' '\n' | wc -l) ))
T=$(mktemp -d)
trap 'pkill -f "examples/signed_hierarchy 53" || true; pkill -f "verilith-resolver --listen 127.0.0.21" || true; [ -f $T/unbound.pid ] && kill $(cat $T/unbound.pid) 2>/dev/null || true; rm -rf $T' EXIT
cargo build -q --release -p verilith-resolver --bin verilith-resolver --example signed_hierarchy
taskset -c $CPU_HIER target/release/examples/signed_hierarchy 53 > $T/anchor 2> /dev/null &
for _ in $(seq 100); do [ -s $T/anchor ] && break; sleep 0.1; done
ds=$(cat $T/anchor)
sed "s|@THREADS@|$nres|;s|@DIR@|$T|;s|@DS@|$ds|" crates/resolver/bench/unbound-dnssec.conf > $T/unbound.conf
for i in $(seq 0 999); do echo "h$i.example.com A"; done > $T/hits.txt
for i in $(seq 2000 9999); do echo "h$i.example.com A"; done > $T/cold.txt

start() { # start NAME
  if [ "$1" = verilith ]; then
    taskset -c $CPUS_RES target/release/verilith-resolver --listen 127.0.0.21 --port 5300 --root 127.0.1.2 \
      --trust-anchor "$ds" 2> /dev/null &
    echo $! > $T/v.pid
  else
    taskset -c $CPUS_RES unbound -c $T/unbound.conf
  fi
  sleep 1
}
stop() {
  if [ "$1" = verilith ]; then kill $(cat $T/v.pid); else kill $(cat $T/unbound.pid); fi
  sleep 0.5
}
addr() { [ "$1" = verilith ] && echo 127.0.0.21 || echo 127.0.0.20; }
pid() { [ "$1" = verilith ] && cat $T/v.pid || cat $T/unbound.pid; }
ticks() { awk '{print $14+$15}' /proc/$1/stat; }
field() { grep "$1" | awk "{print \$$2}"; }
# The status and flags each resolver gives a few names (secure, insecure,
# bogus): they must agree.
check() { # check NAME
  a=$(addr $1)
  for q in www.example.com foo.wild.example.com nx.example.com www.n3 nx.n3 www.unsigned.com www.bad.com www.expired.com; do
    printf "%s %s: %s\n" "$1" "$q" "$(dig +dnssec +tries=1 +time=3 @$a -p 5300 $q A | grep -E '^;; ->>HEADER|^;; flags' | tr '\n' ' ' \
      | sed -E 's/.*status: ([A-Z]+).*flags: ([a-z ]+);.*/\1 \2/')"
  done
}

echo "| round | resolver | UDP hits q/s | CPU µs/hit | UDP cold q/s (validating) | cold NXDOMAIN latency µs |"
echo "|---|---|---|---|---|---|"
for r in $(seq 1 $rounds); do
  order="verilith unbound"; [ $((r % 2)) = 0 ] && order="unbound verilith"
  for name in $order; do
    start $name
    a=$(addr $name)
    [ $r = 1 ] && check $name >> $T/check.txt
    nx=$T/nx-$name-$r.txt
    for i in $(seq 0 1999); do echo "nx$r-$i.example.com A"; done > $nx
    cold_lat=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $nx -n 1 -c 1 -q 1 -D 2>&1 | field "Average Latency" 4)
    cold=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/cold.txt -n 1 -c 20 -T 2 -q 200 -D 2>&1 | field "Queries per second" 4)
    taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/hits.txt -n 1 -c 4 -q 50 -D > /dev/null 2>&1
    t0=$(ticks $(pid $name))
    out=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/hits.txt -c 20 -T 2 -l 10 -q 500 -D 2>&1)
    t1=$(ticks $(pid $name))
    hits=$(echo "$out" | field "Queries per second" 4)
    n=$(echo "$out" | field "Queries completed" 3)
    cpu=$(python3 -c "print(round(($t1-$t0)*1e6/$(getconf CLK_TCK)/$n, 2))")
    printf "| %s | %s | %.0f | %s | %.0f | %.0f |\n" $r $name $hits $cpu $cold $(python3 -c "print($cold_lat*1e6)")
    stop $name
  done
done
echo
echo '```'
cat $T/check.txt
echo '```'
