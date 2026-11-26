#!/bin/sh
# bun/run.sh THREADS HTTP_PORT TLS_PORT CERT KEY ROOT: one Bun process per thread.
n=$1; shift
BUN=${BUN:-bun}
here=$(cd "$(dirname "$0")" && pwd)
i=0
while [ $i -lt "$n" ]; do
  "$BUN" "$here/server.js" "$@" &
  i=$((i + 1))
done
wait
