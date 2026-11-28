#!/usr/bin/env python3
"""Run libvips on test images, for tests/libvips.rs to compare against.

Calls an installed libvips (libvips.so.42) through ctypes, as imgproxy's
vips.c calls it: vips_apply_filters's premultiply, gaussblur, sharpen,
pixelate (mirror embed, shrink, zoom, crop) and unpremultiply; vips_resize_go;
smart crop. Writes each case's
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
    # Smart gravity: vips_smartcrop's attention point, for images of
    # coloured blobs (some skin-toned) on gradients, with and without alpha.
    smart = []
    for i in range(120):
        w, h = rnd.randrange(32, 400), rnd.randrange(32, 400)
        alpha = i % 3 == 2
        blobs = [(rnd.randrange(w), rnd.randrange(h), rnd.randrange(4, max(5, min(w, h) // 3)),
                  rnd.choice([(224, 172, 140), (198, 134, 66), (rnd.randrange(256), rnd.randrange(256), rnd.randrange(256))]))
                 for _ in range(rnd.randrange(1, 6))]
        g0 = [rnd.randrange(256) for _ in range(6)]
        px = bytearray()
        for y in range(h):
            for x in range(w):
                c = [(g0[k] * (w - x) + g0[k + 3] * x) // w for k in range(3)]
                for (bx, by, r, col) in blobs:
                    if (x - bx) ** 2 + (y - by) ** 2 <= r * r:
                        c = list(col)
                c = [min(255, max(0, v + rnd.randrange(-6, 7))) for v in c]
                a = (255 - ((x * 7 + y * 3) % 200)) if alpha else 255
                px += bytes(c + [a])
        cw, ch = rnd.randrange(1, w + 1), rnd.randrange(1, h + 1)
        nb = 4 if alpha else 3
        src = px if alpha else bytes(b for k in range(w * h) for b in px[k * 4:k * 4 + 3])
        im = C.c_void_p(v.vips_image_new_from_memory_copy(bytes(src), len(src), w, h, nb, UCHAR))
        im = call("vips_copy", im, b"interpretation", C.c_int(SRGB))
        ax, ay = C.c_int(), C.c_int()
        call("vips_smartcrop", im, C.c_int(cw), C.c_int(ch), b"attention_x", C.byref(ax), b"attention_y", C.byref(ay))
        open(os.path.join(out, f"smart{i:03}.rgba"), "wb").write(px)
        smart.append(f"{i} {w} {h} {int(alpha)} {cw} {ch} {ax.value} {ay.value}")
    open(os.path.join(out, "smart.txt"), "w").write("\n".join(smart) + "\n")
    # Resizing: vips_resize as imgproxy's vips_resize_go calls it (scales
    # 1 / (src / dst), premultiplied when there is alpha), every kernel,
    # sizes from a pixel to several strips and box shrinks.
    kernels = ["nearest", "linear", "cubic", "mitchell", "lanczos2", "lanczos3"]
    rs = []
    for i in range(240):
        w, h = rnd.randrange(1, 700 if i % 4 == 0 else 120), rnd.randrange(1, 700 if i % 4 == 1 else 120)
        dw, dh = rnd.randrange(1, w + 1), rnd.randrange(1, h + 1)
        if (dw, dh) == (w, h):
            continue
        k = 5 if i % 2 == 0 else rnd.randrange(6)
        alpha = i % 3 == 0
        px = bytearray()
        for y in range(h):
            for x in range(w):
                if i % 5 == 4:
                    px += bytes([(x * 9) % 256, (y * 4) % 256, (x + y) % 256])
                else:
                    px += bytes(rnd.randrange(256) for _ in range(3))
                px.append(rnd.randrange(256) if alpha else 255)
        nb = 4 if alpha else 3
        src = px if alpha else bytes(b for j in range(w * h) for b in px[j * 4:j * 4 + 3])
        im = C.c_void_p(v.vips_image_new_from_memory_copy(bytes(src), len(src), w, h, nb, UCHAR))
        im = call("vips_copy", im, b"interpretation", C.c_int(SRGB))
        if alpha:
            im = call("vips_premultiply", im)
            im = call("vips_cast", im, C.c_int(UCHAR))
        im = call("vips_resize", im, C.c_double(1.0 / (w / dw)), b"vscale", C.c_double(1.0 / (h / dh)), b"kernel", C.c_int(k))
        if alpha:
            im = call("vips_unpremultiply", im)
            im = call("vips_cast", im, C.c_int(UCHAR))
        ow, oh = v.vips_image_get_width(im), v.vips_image_get_height(im)
        open(os.path.join(out, f"rz{i:03}.in"), "wb").write(px)
        open(os.path.join(out, f"rz{i:03}.out"), "wb").write(data(im))
        rs.append(f"{i} {w} {h} {dw} {dh} {kernels[k]} {int(alpha)} {ow} {oh}")
    open(os.path.join(out, "resize.txt"), "w").write("\n".join(rs) + "\n")
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


if __name__ == "__main__":
    main()
