#!/usr/bin/env bash
# verilith-proxy against nginx as a reverse proxy, on one machine.
#
#   bench/proxy/run.sh [SECONDS]
#
# One upstream (verilith-server, /plaintext and a 16 KiB HTML file),
# then each proxy in front of it with one worker thread and keep-alive
# upstream connections; wrk (HTTP/1.1) and h2load (h2c) as clients, each
# on its own CPUs. nginx: proxy_pass with an upstream keepalive pool,
# proxy_http_version 1.1, no buffering to disk; gzip level 6 where
# compression is measured (nginx has no Brotli or zstd module here).
set -euo pipefail
cd "$(dirname "$0")/../.."
D=${1:-10}
T=$(mktemp -d)
trap 'kill $(jobs -p) 2>/dev/null || true; rm -rf "$T"' EXIT
cargo build --release -q -p verilith-server -p verilith-proxy
mkdir -p "$T/www"
python3 -c "import sys; sys.stdout.write(''.join(f'<p>paragraph {i} of a page that proxies compress</p>\n' for i in range(320)))" > "$T/www/page.html"

UP=19001 VP=19080 NG=19081 VPH2=19082 NGH2=19083
taskset -c 0 target/release/verilith-server --threads 1 --http $UP --root "$T/www" >/dev/null 2>&1 &
taskset -c 1 target/release/verilith-proxy --threads 1 --http $VP --h2c $VPH2 --cache-mb 0 --upstream up=127.0.0.1:$UP >/dev/null 2>&1 &
cat > "$T/nginx.conf" <<CONF
worker_processes 1;
daemon off;
pid $T/nginx.pid;
error_log $T/error.log;
events { worker_connections 4096; }
http {
  access_log off;
  keepalive_requests 10000000;
  upstream up { server 127.0.0.1:$UP; keepalive 64; }
  gzip on; gzip_comp_level 6; gzip_types text/html; gzip_min_length 256; gzip_proxied any;
  server {
    listen 127.0.0.1:$NG;
    listen 127.0.0.1:$NGH2 http2;
    location / { proxy_pass http://up; proxy_http_version 1.1; proxy_set_header Connection ""; proxy_buffering on; }
  }
}
CONF
taskset -c 1 nginx -c "$T/nginx.conf" -p "$T" >/dev/null 2>&1 &
sleep 1

w() { taskset -c 2,3 wrk -t2 -c64 -d"${D}s" "$@" | awk '/Requests\/sec/ {print $2}'; }
row() { printf '%-34s %12s %12s\n' "$1" "$2" "$3"; }
row "req/s (one proxy CPU)" "verilith" "nginx"
row "h1 /plaintext" "$(w http://127.0.0.1:$VP/plaintext)" "$(w http://127.0.0.1:$NG/plaintext)"
row "h1 16 KiB HTML, identity" "$(w http://127.0.0.1:$VP/static/page.html)" "$(w http://127.0.0.1:$NG/static/page.html)"
row "h1 16 KiB HTML, gzip" "$(w -H 'Accept-Encoding: gzip' http://127.0.0.1:$VP/static/page.html)" "$(w -H 'Accept-Encoding: gzip' http://127.0.0.1:$NG/static/page.html)"
row "h1 16 KiB HTML, br only (q2)" "$(w -H 'Accept-Encoding: br' http://127.0.0.1:$VP/static/page.html)" "-"
row "h1 16 KiB HTML, zstd (level 3)" "$(w -H 'Accept-Encoding: zstd' http://127.0.0.1:$VP/static/page.html)" "-"
h() { taskset -c 2,3 h2load -t2 -c64 -m10 -D"$D" "$@" 2>/dev/null | awk '/^finished in/ {print $4}' | tr -d ','; }
row "h2c /plaintext (10 streams)" "$(h http://127.0.0.1:$VPH2/plaintext)" "$(h http://127.0.0.1:$NGH2/plaintext)"
