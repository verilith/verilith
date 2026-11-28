#!/usr/bin/env bash
# verilith-resolver against Unbound, both iterating from the test
# hierarchy (tests/hier, on 127.0.0.2-9 port 53; needs root for port 53).
#   bench/run.sh [ROUNDS] > results.md
# Needs unbound, dnsperf (2.14+), h2load (nghttp2-client), openssl, taskset.
# The resolvers get CPUs 0-1, the load generators CPUs 2-3 and the
# hierarchy CPU 3 (set CPUS_RES, CPUS_LOAD, CPU_HIER to change).
set -euo pipefail
cd "$(dirname "$0")/../../.."
rounds=${1:-3}
CPUS_RES=${CPUS_RES:-0,1}
CPUS_LOAD=${CPUS_LOAD:-2,3}
CPU_HIER=${CPU_HIER:-3}
nres=$(( $(echo "$CPUS_RES" | tr ',' '\n' | wc -l) ))
T=$(mktemp -d)
trap 'pkill -f "examples/hierarchy 53" || true; pkill -f "verilith-resolver --listen 127.0.0.21" || true; [ -f $T/unbound.pid ] && kill $(cat $T/unbound.pid) 2>/dev/null || true; rm -rf $T' EXIT
cargo build -q --release -p verilith-resolver --features tls --bin verilith-resolver --example hierarchy
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes -keyout $T/key.pem -out $T/cert.pem \
  -days 30 -subj /CN=localhost -addext subjectAltName=IP:127.0.0.20,IP:127.0.0.21 2>/dev/null
sed "s|@KEY@|$T/key.pem|;s|@CERT@|$T/cert.pem|;s|@THREADS@|$nres|;s|@DIR@|$T|" crates/resolver/bench/unbound.conf > $T/unbound.conf
taskset -c $CPU_HIER target/release/examples/hierarchy 53 2> /dev/null &
sleep 0.5
for i in $(seq 0 999); do echo "h$i.example.com A"; done > $T/hits.txt
for i in $(seq 2000 9999); do echo "h$i.example.com A"; done > $T/cold.txt
# The query of the DoH test: h5.example.com A, base64url.
doh_q=AAABAAABAAAAAAAAAmg1B2V4YW1wbGUDY29tAAABAAE

start() { # start NAME
  if [ "$1" = verilith ]; then
    taskset -c $CPUS_RES target/release/verilith-resolver --listen 127.0.0.21 --port 5300 --root 127.0.0.2 \
      --dot 8530 --doh 4430 --http 8053 --cert $T/cert.pem --key $T/key.pem 2> /dev/null &
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

echo "| round | resolver | UDP hits q/s | CPU µs/hit | UDP cold q/s | cold latency µs | DoT hits q/s | DoH hits req/s |"
echo "|---|---|---|---|---|---|---|---|"
for r in $(seq 1 $rounds); do
  order="verilith unbound"; [ $((r % 2)) = 0 ] && order="unbound verilith"
  for name in $order; do
    start $name
    a=$(addr $name)
    nx=$T/nx-$name-$r.txt
    for i in $(seq 0 1999); do echo "nx$r-$i.example.com A"; done > $nx
    cold_lat=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $nx -n 1 -c 1 -q 1 2>&1 | field "Average Latency" 4)
    cold=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/cold.txt -n 1 -c 20 -T 2 -q 200 2>&1 | field "Queries per second" 4)
    taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/hits.txt -n 1 -c 4 -q 50 > /dev/null 2>&1
    t0=$(ticks $(pid $name))
    out=$(taskset -c $CPUS_LOAD dnsperf -s $a -p 5300 -d $T/hits.txt -c 20 -T 2 -l 10 -q 500 2>&1)
    t1=$(ticks $(pid $name))
    hits=$(echo "$out" | field "Queries per second" 4)
    n=$(echo "$out" | field "Queries completed" 3)
    cpu=$(python3 -c "print(round(($t1-$t0)*1e6/$(getconf CLK_TCK)/$n, 2))")
    dot=$(taskset -c $CPUS_LOAD dnsperf -m dot -s $a -p 8530 -d $T/hits.txt -c 20 -T 2 -l 5 -q 200 2>&1 | field "Queries per second" 4)
    doh=$(taskset -c $CPUS_LOAD h2load -n 300000 -c 20 -m 10 -t 2 "https://$a:4430/dns-query?dns=$doh_q" 2>&1 | grep "finished in" | awk '{print $4}')
    printf "| %s | %s | %.0f | %s | %.0f | %.0f | %.0f | %.0f |\n" $r $name $hits $cpu $cold $(python3 -c "print($cold_lat*1e6)") $dot $doh
    stop $name
  done
done
