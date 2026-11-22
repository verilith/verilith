#!/usr/bin/env python3
"""Differential test of vhttp's llhttp drop-in against llhttp.

Generates request and response streams (pipelined messages, chunked and
fixed-length bodies, upgrades, and random corruptions of them), runs both
trace binaries on each with several ways of splitting the input, and checks:

- whenever vhttp accepts a stream, llhttp reports exactly the same
  callbacks (so Node.js sees the same thing);
- vhttp gives the same trace however the input is split, and when a
  callback pauses the parser and it resumes.

Streams that llhttp accepts and vhttp rejects are counted by vhttp's error,
since vhttp is stricter on purpose.

    diff.py DIR N [SEED]   (DIR holds trace-llhttp and trace-vhttp)
"""
import collections
import os
import random
import subprocess
import sys
import tempfile

METHODS = ["GET", "POST", "PUT", "DELETE", "HEAD", "OPTIONS", "PATCH", "CONNECT", "M-SEARCH",
           "PROPFIND", "QUERY", "FOO", "get"]
TARGETS = ["/", "/a/b?c=d&e", "*", "example.com:443", "http://h/p", "/%7E/x#f", "/\x80\xff"]
NAMES = ["Host", "User-Agent", "Accept", "X-Custom", "Cookie", "Connection", "Upgrade",
         "content-length", "Transfer-Encoding", "Keep-Alive", "X-Empty", "Proxy-Connection"]
VALUES = ["example.com", "curl/8.0", "*/*", "a, b,c", "", "  padded  ", "keep-alive", "close",
          "Upgrade", "websocket", "x\x80y", "Keep-Alive, Upgrade", "upgrade, close"]


def chunked(body, rng):
    out = []
    i = 0
    while i < len(body):
        n = rng.randint(1, max(1, len(body) - i))
        size = "%x" % n
        if rng.random() < 0.2:
            size = size.upper()
        ext = rng.choice(["", "", ";a=b", ";x", ";q=\"v\""])
        out.append("%s%s\r\n%s\r\n" % (size, ext, body[i:i + n]))
        i += n
    trailer = rng.choice(["", "", "T: v\r\n", "X-Sum: 1\r\nY: 2\r\n"])
    out.append("0\r\n%s\r\n" % trailer)
    return "".join(out)


def message(rng, req):
    lines = []
    # llhttp also takes HTTP/0.9 and HTTP/2.0, and a request line with no
    # version (as HTTP/0.9); vhttp checks those as HTTP/1.0.
    ver = rng.choice(["1.1", "1.1", "1.1", "1.1", "1.0", "1.0", "0.9", "2.0", "1.2"])
    minor = 1 if ver == "1.1" else 0
    if req:
        if ver == "0.9" and rng.random() < 0.5:
            lines.append("%s %s" % (rng.choice(METHODS), rng.choice(TARGETS)))
        else:
            lines.append("%s %s HTTP/%s" % (rng.choice(METHODS), rng.choice(TARGETS), ver))
    else:
        code = rng.choice([200, 200, 204, 304, 101, 100, 404, 500, 302])
        reason = rng.choice(["OK", "", "Not Found", "X Y Z"])
        sp = "" if (reason == "" and rng.random() < 0.5) else " "
        lines.append("HTTP/%s %d%s%s" % (ver, code, sp, reason))
    if req and (minor == 1 or rng.random() < 0.3):
        lines.append("Host: example.com")
    body = rng.choice(["", "", "hello", "x" * rng.randint(0, 300)])
    framing = rng.choice(["none", "cl", "cl", "te", "te"])
    for _ in range(rng.randint(0, 6)):
        n = rng.choice(NAMES)
        if n.lower() in ("content-length", "transfer-encoding", "host"):
            continue
        lines.append("%s: %s" % (n, rng.choice(VALUES)))
    if framing == "cl":
        lines.append("Content-Length: %d" % len(body))
        payload = body
    elif framing == "te" and minor == 1:
        te = rng.choice(["chunked", "chunked", "gzip, chunked", "Chunked", "gzip", "chunkedchunked", ""])
        lines.append("Transfer-Encoding: %s" % te)
        payload = chunked(body, rng)
    else:
        payload = ""
    rest = lines[1:]
    rng.shuffle(rest)
    return "\r\n".join(lines[:1] + rest) + "\r\n\r\n" + payload


def corrupt(s, rng):
    b = bytearray(s.encode("latin-1"))
    for _ in range(rng.randint(1, 3)):
        if not b:
            break
        i = rng.randrange(len(b))
        op = rng.random()
        if op < 0.3:
            b[i] = rng.choice(b" \t\r\n:;,\"\x00\x7f\xffaZ0-_")
        elif op < 0.6:
            b.insert(i, rng.choice(b" \t\r\n:;,\x00aZ0-_"))
        else:
            del b[i]
    return bytes(b)


def run(binary, kind, split, path, pause=None):
    env = dict(os.environ, PAUSE=str(pause)) if pause else None
    return subprocess.run([binary, kind, split, path], capture_output=True, check=True, env=env).stdout


def main():
    d, n = sys.argv[1], int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    ref, ours = os.path.join(d, "trace-llhttp"), os.path.join(d, "trace-vhttp")
    stricter = collections.Counter()
    looser = collections.Counter()
    same = 0
    bad = 0
    shown = collections.Counter()
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "in")
        for k in range(n):
            req = rng.random() < 0.6
            s = "".join(message(rng, req) for _ in range(rng.randint(1, 3)))
            data = corrupt(s, rng) if rng.random() < 0.5 else s.encode("latin-1")
            with open(path, "wb") as f:
                f.write(data)
            kind = "req" if req else "res"
            a = run(ref, kind, "whole", path)
            b = run(ours, kind, "whole", path)
            for split in ("bytes", str(k)):
                b2 = run(ours, kind, split, path)
                if b"stop " in b or b"finish HPE" in b:
                    # A rejection: callbacks before it depend on the split,
                    # as in llhttp; the error and its position do not.
                    last = lambda t: [l for l in t.split(b"\n") if l.startswith((b"stop", b"finish"))]
                    if last(b2) != last(b):
                        bad += 1
                        print("SPLIT ERROR MISMATCH (%s) on %r: %r vs %r" % (split, data, last(b), last(b2)))
                elif b2 != b:
                    bad += 1
                    print("SPLIT MISMATCH (%s) on %r\n--- whole\n%s--- split\n%s" % (split, data, b.decode("latin-1"), b2.decode("latin-1")))
            ok_a = b"stop " not in a and b"finish HPE" not in a
            ok_b = b"stop " not in b and b"finish HPE" not in b
            if ok_b:
                k_pause = rng.randint(1, 30)
                for split in ("whole", "bytes"):
                    b3 = run(ours, kind, split, path, k_pause)
                    if b3 != b:
                        bad += 1
                        print("PAUSE MISMATCH (%s, callback %d) on %r\n--- plain\n%s--- paused\n%s" % (split, k_pause, data, b.decode("latin-1"), b3.decode("latin-1")))
                if a != b:
                    bad += 1
                    key = ([l for l in a.split(b"\n") if l.startswith(b"stop")] or [b"differs"])[0].split(b" @")[0]
                    shown[key] += 1
                    if shown[key] <= 3:
                        print("MISMATCH on %r\n--- llhttp\n%s--- vhttp\n%s" % (data, a.decode("latin-1"), b.decode("latin-1")))
                else:
                    same += 1
            elif ok_a:
                why = [l for l in b.split(b"\n") if l.startswith((b"stop", b"finish"))][0].split(b" @")[0]
                stricter[why.decode()] += 1
                if os.environ.get("SHOW_STRICT") and stricter[why.decode()] <= 2:
                    print("STRICTER %s on %r" % (why.decode(), data))
            if ok_b and not ok_a:
                looser["llhttp rejects, vhttp accepts"] += 1
    print("accepted by vhttp, identical to llhttp: %d" % same)
    print("mismatches: %d" % bad)
    for k, v in shown.most_common():
        print("  %s: %d" % (k.decode(), v))
    for k, v in stricter.most_common():
        print("llhttp accepts, vhttp rejects (%s): %d" % (k, v))
    for k, v in looser.items():
        print("%s: %d" % (k, v))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
