#!/usr/bin/env python3
"""Builds the differential test corpus: every certificate in x509-limbo,
pyca/cryptography's test vectors and the system trust store, as one DER file
each, named by a prefix of its SHA-256. See README.md."""
import base64, hashlib, json, os, re, sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
seen = {}


def add(der, origin):
    h = hashlib.sha256(der).hexdigest()[:20]
    if h in seen:
        return
    seen[h] = origin
    with open(os.path.join(out, h + '.der'), 'wb') as f:
        f.write(der)


pem_re = re.compile(rb'-----BEGIN CERTIFICATE-----(.*?)-----END CERTIFICATE-----', re.S)


def from_pem(data, origin):
    for m in pem_re.finditer(data):
        try:
            add(base64.b64decode(b''.join(m.group(1).split())), origin)
        except Exception:
            pass


with open(os.path.join(src, 'limbo.json')) as f:
    limbo = json.load(f)
for t in limbo['testcases']:
    for k in ('trusted_certs', 'untrusted_intermediates'):
        for p in t.get(k) or []:
            from_pem(p.encode(), 'limbo:' + t['id'])
    if t.get('peer_certificate'):
        from_pem(t['peer_certificate'].encode(), 'limbo:' + t['id'])

root = os.path.join(src, 'vec', 'cryptography_vectors', 'x509')
for d, _, fs in os.walk(root):
    if any(x in d for x in ('crls', 'requests', 'ocsp', 'pkcs12', 'smime')):
        continue
    for name in fs:
        with open(os.path.join(d, name), 'rb') as f:
            data = f.read()
        if b'-----BEGIN CERTIFICATE' in data:
            from_pem(data, 'pyca:' + name)
        elif data[:1] == b'\x30' and not name.endswith(('.pem', '.txt')):
            add(data, 'pyca:' + name)

store = '/etc/ssl/certs/ca-certificates.crt'
if os.path.exists(store):
    with open(store, 'rb') as f:
        from_pem(f.read(), 'system')

with open(os.path.join(src, 'sources.json'), 'w') as f:
    json.dump(seen, f, indent=0)
print(len(seen), 'certificates')
