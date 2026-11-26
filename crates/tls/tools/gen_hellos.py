#!/usr/bin/env python3
"""Captures real ClientHellos for tests/data: Python's ssl module (OpenSSL)
with several configurations, and `openssl s_client` with other groups
and ALPN lists (Python's OpenSSL offers X25519MLKEM768 by default). Each file is the ClientHello handshake message body (no
record or handshake header)."""
import os, socket, ssl, subprocess, sys, threading

out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "..", "tests", "data")

def body_from_records(raw):
    # Concatenate handshake fragments, then strip the 4-byte header.
    hs = b""
    i = 0
    while i + 5 <= len(raw):
        ln = int.from_bytes(raw[i + 3:i + 5], "big")
        if raw[i] == 22:
            hs += raw[i + 5:i + 5 + ln]
        i += 5 + ln
    assert hs[0] == 1
    ln = int.from_bytes(hs[1:4], "big")
    return hs[4:4 + ln]

def py_hello(name, sni=None, alpn=None, minv=None, maxv=None, ciphers=None):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    if alpn:
        ctx.set_alpn_protocols(alpn)
    if minv:
        ctx.minimum_version = minv
    if maxv:
        ctx.maximum_version = maxv
    if ciphers:
        ctx.set_ciphers(ciphers)
    i, o = ssl.MemoryBIO(), ssl.MemoryBIO()
    s = ctx.wrap_bio(i, o, server_hostname=sni)
    try:
        s.do_handshake()
    except ssl.SSLWantReadError:
        pass
    write(name, body_from_records(o.read()))

def write(name, b):
    with open(os.path.join(out, name + ".bin"), "wb") as f:
        f.write(b)
    print(name, len(b))

def s_client(name, args):
    srv = socket.socket()
    srv.settimeout(5)
    srv.bind(("127.0.0.1", 0))
    srv.listen(1)
    port = srv.getsockname()[1]
    p = subprocess.Popen(["openssl", "s_client", "-connect", f"127.0.0.1:{port}"] + args,
                         stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    c, _ = srv.accept()
    c.settimeout(1)
    raw = b""
    try:
        while True:
            d = c.recv(65536)
            if not d:
                break
            raw += d
    except socket.timeout:
        pass
    c.close()
    p.kill()
    srv.close()
    write(name, body_from_records(raw))

os.makedirs(out, exist_ok=True)
py_hello("py-default-sni-alpn", sni="example.com", alpn=["h2", "http/1.1"])
py_hello("py-no-sni", alpn=["http/1.1"])
py_hello("py-tls12-only", sni="example.org", maxv=ssl.TLSVersion.TLSv1_2)
py_hello("py-tls13-only", sni="a.example", minv=ssl.TLSVersion.TLSv1_3)
s_client("ossl-alpn3", ["-servername", "pq.example", "-alpn", "h2,http/1.1,acme-tls/1"])
s_client("ossl-p256-p384", ["-servername", "x.example", "-groups", "P-256:P-384", "-tls1_3"])
