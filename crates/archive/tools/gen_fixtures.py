#!/usr/bin/env python3
"""Writes tests/data/: archives of one small tree, made by the tools people
make archives with (Info-ZIP zip, GNU tar, bsdtar, Python's zipfile). The
differential test reads each with varchive and with libarchive.

Needs zip, tar (GNU), bsdtar and python3 on PATH. The output is committed, so
the tests themselves need none of them."""
import os, random, shutil, subprocess, sys, zipfile, gzip

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "data")
shutil.rmtree(root, ignore_errors=True)
os.makedirs(root)
work = os.path.join(root, "_work")
tree = os.path.join(work, "tree")
os.makedirs(os.path.join(tree, "dir/sub/deeper"))
os.makedirs(os.path.join(tree, "empty-dir"))
rnd = random.Random(1)

def put(name, data):
    p = os.path.join(tree, name)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "wb") as f:
        f.write(data)
    os.utime(p, (1700000000, 1700000000))

put("hello.txt", b"hello, world\n")
put("empty", b"")
put("dir/text.txt", b"The quick brown fox jumps over the lazy dog.\n" * 2000)
put("dir/random.bin", bytes(rnd.randrange(256) for _ in range(40000)))
put("dir/sub/exactly-512", b"x" * 512)
put("dir/sub/513", b"y" * 513)
put("dir/sub/deeper/" + "n" * 120 + ".txt", b"a name longer than 100 bytes\n")
put("/".join(["long-directory-name-%02d" % i for i in range(14)]) + "/leaf.txt", b"a path longer than 255 bytes\n")
put("unicode-é中文.txt", "café\n".encode())
put("dir/script.sh", b"#!/bin/sh\necho hi\n")
os.chmod(os.path.join(tree, "dir/script.sh"), 0o755)
os.symlink("text.txt", os.path.join(tree, "dir/link-to-text"))
os.symlink("../hello.txt", os.path.join(tree, "dir/sub/link-up"))
os.link(os.path.join(tree, "hello.txt"), os.path.join(tree, "dir/hard-hello"))

def run(*cmd, cwd=tree):
    subprocess.run(cmd, cwd=cwd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

out = lambda n: os.path.join(root, n)
names = sorted(os.listdir(tree))
for fmt in ["gnu", "oldgnu", "pax", "ustar", "v7"]:
    if fmt in ("ustar", "v7"):
        # These formats cannot hold the long names.
        short = [n for n in names if not n.startswith("long-")]
        run("tar", "--format=" + fmt, "--exclude=" + "n" * 120 + ".txt", "-cf", out("gnutar-%s.tar" % fmt), *short)
    else:
        run("tar", "--format=" + fmt, "-cf", out("gnutar-%s.tar" % fmt), *names)
for fmt in ["pax", "gnutar", "ustar"]:
    run("bsdtar", "--format", fmt, "-cf", out("bsdtar-%s.tar" % fmt), *names)
run("tar", "--format=gnu", "-czf", out("gnutar-gnu.tar.gz"), *names)
run("bsdtar", "--format", "pax", "--zstd", "-cf", out("bsdtar-pax.tar.zst"), *names)
run("zip", "-r", "-y", out("infozip-deflate.zip"), *names)
run("zip", "-r", "-y", "-0", out("infozip-stored.zip"), *names)
run("zip", "-r", "-y", "-fz", out("infozip-zip64.zip"), *names)
run("bsdtar", "--format", "zip", "-cf", out("bsdtar.zip"), *names)

def pyzip(name, method, force64=False, comment=b""):
    with zipfile.ZipFile(out(name), "w", method) as z:
        z.comment = comment
        for d, _, fs in sorted(os.walk(tree)):
            for f in sorted(fs):
                p = os.path.join(d, f)
                if os.path.islink(p):
                    continue
                arc = os.path.relpath(p, tree)
                with open(p, "rb") as src, z.open(zipfile.ZipInfo(arc, (2023, 11, 14, 22, 13, 20)), "w", force_zip64=force64) as dst:
                    dst.write(src.read())

pyzip("python-deflate.zip", zipfile.ZIP_DEFLATED)
pyzip("python-stored-comment.zip", zipfile.ZIP_STORED, comment=b"an archive comment")
pyzip("python-zip64.zip", zipfile.ZIP_DEFLATED, force64=True)
if hasattr(zipfile, "ZIP_ZSTANDARD"):
    pyzip("python-zstd.zip", zipfile.ZIP_ZSTANDARD)
open(out("empty.tar"), "wb").write(b"\0" * 10240)
shutil.rmtree(work)
print("\n".join(sorted(os.listdir(root))))
