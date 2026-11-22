#!/usr/bin/env bash
# Builds a benchmark corpus in DIR: a few kinds of data, each compressed
# with the zstd CLI at levels 1, 3, 9 and 19. Needs `zstd` and python3.
set -euo pipefail
dir=${1:?usage: corpus.sh DIR}
mkdir -p "$dir/raw"
cd "$dir/raw"
python3 - <<'PY'
import random, os
r = random.Random(1)
words = [''.join(r.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(r.randint(1, 10))) for _ in range(5000)]
with open('text', 'w') as f:
    f.write(' '.join(words[int(r.paretovariate(1.2)) % 5000] for _ in range(4_000_000)))
with open('json', 'w') as f:
    f.write('[' + ','.join('{"id":%d,"name":"%s","tags":["%s","%s"],"score":%.3f,"active":%s}' % (i, r.choice(words), r.choice(words), r.choice(words), r.random() * 100, r.choice(['true', 'false'])) for i in range(300_000)) + ']')
with open('random', 'wb') as f:
    f.write(os.urandom(8_000_000))
with open('lowent', 'wb') as f:
    f.write(bytes(r.choice(b'aaaabbc\n') for _ in range(16_000_000)))
PY
# A binary, if one is around.
for b in /usr/bin/python3 /bin/bash; do
    if [ -f "$b" ]; then cp -L "$b" binary; break; fi
done
cd ..
for f in raw/*; do
    for l in 1 3 9 19; do
        zstd -q -f -"$l" "$f" -o "$(basename "$f").$l.zst"
    done
done
ls -la "$dir"
