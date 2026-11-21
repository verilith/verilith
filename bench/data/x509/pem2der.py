#!/usr/bin/env python3
"""pem2der.py BUNDLE.pem OUTDIR: writes each certificate of a PEM bundle
to OUTDIR/NNN.der, in bundle order."""
import base64
import os
import re
import sys

pem = open(sys.argv[1]).read()
out = sys.argv[2]
os.makedirs(out, exist_ok=True)
blocks = re.findall(r"-----BEGIN CERTIFICATE-----(.*?)-----END CERTIFICATE-----", pem, re.S)
for i, b in enumerate(blocks):
    with open(os.path.join(out, f"{i:03d}.der"), "wb") as f:
        f.write(base64.b64decode("".join(b.split())))
print(f"{len(blocks)} certificates", file=sys.stderr)
