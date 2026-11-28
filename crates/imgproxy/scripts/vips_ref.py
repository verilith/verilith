#!/usr/bin/env python3
"""Run libvips on test images, for tests/libvips.rs to compare against.

Calls an installed libvips (libvips.so.42) through ctypes, as imgproxy's
vips.c calls it: vips_apply_filters's premultiply, gaussblur, sharpen,
pixelate (mirror embed, shrink, zoom, crop) and unpremultiply. Writes each case's
input and libvips's output as raw RGBA to the directory given:

    scripts/vips_ref.py /tmp/ref
    VERILITH_VIPS_REF=/tmp/ref cargo test --test libvips -- --ignored

Set VIPS_NOVECTOR=1 for libvips's C paths (and VERILITH_VIPS_C=1 for
the test). libvips before 8.17 divides exactly in vips_shrink; the proxy
follows 8.17 and later (fixed point), so the test leaves out pixelate
for an older libvips.
"""
import ctypes as C
import os
import random
import sys

v = C.CDLL("libvips.so.42")
if v.vips_init(b"vips_ref") != 0:
    sys.exit("vips_init failed")
v.vips_image_new_from_memory_copy.restype = C.c_void_p
v.vips_image_new_from_memory_copy.argtypes = [C.c_char_p, C.c_size_t, C.c_int, C.c_int, C.c_int, C.c_int]
v.vips_image_write_to_memory.restype = C.c_void_p
v.vips_image_write_to_memory.argtypes = [C.c_void_p, C.POINTER(C.c_size_t)]
v.vips_image_get_width.argtypes = [C.c_void_p]
v.vips_image_get_height.argtypes = [C.c_void_p]
v.vips_error_buffer.restype = C.c_char_p
UCHAR = 0
MIRROR = 3
SRGB = 22


def img(px, w, h):
    return C.c_void_p(v.vips_image_new_from_memory_copy(bytes(px), len(px), w, h, 4, UCHAR))


def call(name, *args):
    out = C.c_void_p()
    r = getattr(v, name)(*args[:1], C.byref(out), *args[1:], None)
    if r != 0:
        raise RuntimeError(v.vips_error_buffer().decode())
    return out


def data(im):
    n = C.c_size_t()
    p = v.vips_image_write_to_memory(im, C.byref(n))
    return C.string_at(p, n.value)


def filters(px, w, h, blur, sharp, pix):
    """imgproxy's vips_apply_filters."""
    im = call("vips_copy", img(px, w, h), b"interpretation", C.c_int(SRGB))
    pre = blur > 0 or sharp > 0
    if pre:
        im = call("vips_premultiply", im)
        im = call("vips_cast", im, C.c_int(UCHAR))
    if blur > 0:
        im = call("vips_gaussblur", im, C.c_double(blur))
    if sharp > 0:
        im = call("vips_sharpen", im, b"sigma", C.c_double(sharp))
    pix = min(pix, max(w, h))
    if pix > 1:
        tw = -(-w // pix) * pix
        th = -(-h // pix) * pix
        if tw > w or th > h:
            im = call("vips_embed", im, C.c_int(0), C.c_int(0), C.c_int(tw), C.c_int(th), b"extend", C.c_int(MIRROR))
        im = call("vips_shrink", im, C.c_double(pix), C.c_double(pix))
        im = call("vips_zoom", im, C.c_int(pix), C.c_int(pix))
        im = call("vips_extract_area", im, C.c_int(0), C.c_int(0), C.c_int(w), C.c_int(h))
    if pre:
        im = call("vips_unpremultiply", im)
        im = call("vips_cast", im, C.c_int(UCHAR))
    return data(im)


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    rnd = random.Random(7)
    cases = []
    for blur in [0, 0.3, 0.5, 1, 1.5, 2.7, 5, 12.5, 40]:
        cases.append((blur, 0, 0))
    for sharp in [0.3, 0.5, 1, 2.2, 6, 10]:
        cases.append((0, sharp, 0))
    for pix in [2, 3, 5, 7, 16, 40, 1000]:
        cases.append((0, 0, pix))
    cases.append((1.5, 1, 6))
    n = 0
    for blur, sharp, pix in cases:
        for (w, h) in [(1, 1), (5, 3), (33, 17), (64, 48), (13, 90)]:
            for kind in ["noise", "alpha", "smooth"]:
                px = bytearray()
                for y in range(h):
                    for x in range(w):
                        if kind == "smooth":
                            px += bytes([(x * 7) % 256, (y * 5) % 256, (x * y) % 256, 255])
                        else:
                            px += bytes(rnd.randrange(256) for _ in range(3))
                            px.append(255 if kind == "noise" else rnd.randrange(256))
                res = filters(px, w, h, blur, sharp, pix)
                name = f"{n:04}_{w}x{h}_bl{blur}_sh{sharp}_pix{pix}"
                open(os.path.join(out, name + ".in"), "wb").write(px)
                open(os.path.join(out, name + ".out"), "wb").write(res)
                n += 1
    # The colour conversions sharpen uses, on their own: sRGB to LabS for
    # every 8-bit colour, and LabS back to sRGB for a spread of values.
    rgb = bytes(c for r in range(0, 256) for g in range(256) for b in range(256) for c in (r, g, b))
    im = C.c_void_p(v.vips_image_new_from_memory_copy(rgb, len(rgb), 4096, 4096, 3, UCHAR))
    im = call("vips_copy", im, b"interpretation", C.c_int(SRGB))
    open(os.path.join(out, "labs.out"), "wb").write(data(call("vips_colourspace", im, C.c_int(21))))
    labs = bytearray()
    for _ in range(1 << 20):
        labs += rnd.randrange(32768).to_bytes(2, "little")
        labs += rnd.randrange(-32768, 32768).to_bytes(2, "little", signed=True)
        labs += rnd.randrange(-32768, 32768).to_bytes(2, "little", signed=True)
    im = C.c_void_p(v.vips_image_new_from_memory_copy(bytes(labs), len(labs), 1024, 1024, 3, 3))
    im = call("vips_copy", im, b"interpretation", C.c_int(21))
    open(os.path.join(out, "srgb.in"), "wb").write(labs)
    open(os.path.join(out, "srgb.out"), "wb").write(data(call("vips_colourspace", im, C.c_int(SRGB))))
    ver = f"{v.vips_version(0)}.{v.vips_version(1)}.{v.vips_version(2)}"
    open(os.path.join(out, "version"), "w").write(ver)
    print(n, "cases, libvips", ver)


main()
