#!/bin/bash
# Rewrites the generated section of src/idct_neon.rs.
cd "$(dirname "$0")/.." && python3 - <<'PY'
import subprocess
g = subprocess.check_output(['python3', 'scripts/gen_idct_neon.py']).decode()
s = open('src/idct_neon.rs').read()
a = s.index('// BEGIN generated'); a = s.index('\n', a) + 1; b = s.index('// END generated')
open('src/idct_neon.rs', 'w').write(s[:a] + g + s[b:])
PY
