#!/usr/bin/env python3
"""rules.py FILE: names the first TIFF 6.0 rule the TIFF file's first image
breaks, or a part of TIFF that verilith-tiff does not read, and exits 0; or
prints "conforming" and exits 1.

An independent check of src/spec.rs, written from the standard rather than
from the spec: difftest/compare.sh runs it on every file that libtiff
decodes and verilith-tiff rejects, and a file this calls conforming fails
the run. It decodes PackBits and LZW itself and Deflate with Python's zlib,
to check the strips the way the standard describes them. Standard library
only. (Section numbers are TIFF 6.0's.)"""
import struct
import sys
import zlib

SIZES = {1: 1, 3: 2, 4: 4}


def check(d):
    if len(d) < 8 or d[:2] not in (b"II", b"MM"):
        return "not TIFF: header"
    e = "<" if d[:2] == b"II" else ">"
    if struct.unpack(e + "H", d[2:4])[0] == 43:
        return "unsupported: BigTIFF"
    if struct.unpack(e + "H", d[2:4])[0] != 42:
        return "not TIFF: header"
    o = struct.unpack(e + "I", d[4:8])[0]
    if o % 2:
        return "§2: the IFD must begin on a word boundary"
    if o < 8:
        return "§2: the IFD is after the header"
    if o + 2 > len(d):
        return "§2: IFD outside the file"
    n = struct.unpack(e + "H", d[o:o + 2])[0]
    if n == 0 or o + 2 + 12 * n > len(d):
        return "§2: IFD outside the file"
    ents = [struct.unpack(e + "HHII", d[o + 2 + 12 * i:o + 14 + 12 * i]) for i in range(n)]
    tags = [x[0] for x in ents]
    if any(tags[i] >= tags[i + 1] for i in range(n - 1)):
        return "§2: entries must be sorted in ascending order by tag"
    E = {x[0]: (i, x) for i, x in enumerate(ents)}

    def present(tag):
        return tag in E and E[tag][1][1] in SIZES

    def vals(tag):
        """The values of an unsigned integer field; None if absent or of a
        type readers skip (§2); "range" if outside the file."""
        if not present(tag):
            return None
        i, (t, ty, c, v) = E[tag]
        s = SIZES[ty] * c
        pos = o + 2 + 12 * i + 8 if s <= 4 else v
        if pos + s > len(d):
            return "range"
        return list(struct.unpack(e + {1: "B", 3: "H", 4: "I"}[ty] * c, d[pos:pos + s]))

    def one(tag, default):
        v = vals(tag)
        if v is None:
            return default
        if v == "range" or len(v) != 1:
            return "bad"
        return v[0]

    def first(tag):
        v = vals(tag)
        return v[0] if isinstance(v, list) and v else None

    # Parts of TIFF not read here.
    comp0, pred0 = first(259), first(317)
    bv0 = vals(258)
    bits0 = [1] if bv0 is None else (bv0 if isinstance(bv0, list) and bv0 else None)
    sf0 = vals(339)
    if comp0 in (2, 3, 4, 6, 7):
        return "unsupported: CCITT or JPEG compression"
    if first(262) == 6:
        return "unsupported: YCbCr"
    if first(266) == 2:
        return "unsupported: FillOrder 2"
    if bits0 and (len(set(bits0)) > 1 or bits0[0] > 32):
        return "unsupported: BitsPerSample above 32 or differing between samples"
    if isinstance(sf0, list) and len(set(sf0)) > 1:
        return "unsupported: SampleFormat differing between samples"
    if comp0 in (5, 8) and (pred0 == 3 or (pred0 == 2 and bits0 and bits0[0] not in (8, 16, 32))):
        return "unsupported: this predictor"

    for t in (256, 257, 258, 259, 262, 266, 277, 278, 284, 317, 322, 323, 338, 339):
        if vals(t) == "range":
            return "§2: values outside the file"
    w, h = vals(256), vals(257)
    if not w or not h or len(w) != 1 or len(h) != 1 or w[0] == 0 or h[0] == 0:
        return "§8: ImageWidth and ImageLength"
    w, h = w[0], h[0]
    spp, comp, planar = one(277, 1), one(259, 1), one(284, 1)
    pred, fill, rps = one(317, 1), one(266, 1), one(278, 2 ** 32 - 1)
    if "bad" in (spp, comp, planar, pred, fill, rps):
        return "§8: a field with the wrong number of values"
    if comp not in (1, 5, 8, 32773):
        return "§8: a Compression TIFF does not define"
    if planar not in (1, 2) or spp == 0 or rps == 0:
        return "§8: PlanarConfiguration, SamplesPerPixel or RowsPerStrip"
    if fill != 1:
        return "§8: a FillOrder TIFF does not define"
    ph = vals(262)
    if ph is None:
        return "§8: PhotometricInterpretation is required"
    if len(ph) != 1:
        return "§8: a field with the wrong number of values"
    ph = ph[0]
    bv = vals(258)
    if bv is None:
        bps = 1
    elif len(bv) != spp or len(set(bv)) != 1:
        return "§8: BitsPerSample needs one value per sample"
    else:
        bps = bv[0]
    if not 1 <= bps:
        return "§8: BitsPerSample"
    if comp in (5, 8) and pred not in (1, 2):
        return "§14: a Predictor TIFF does not define"
    sf = vals(339)
    if sf is not None and (len(sf) != spp or not 1 <= sf[0] <= 4):
        return "§19: SampleFormat"
    es = vals(338)
    if es is not None and any(x > 2 for x in es):
        return "§8: an ExtraSamples value TIFF does not define"
    m = None if es is None else len(es)
    inks = one(334, 4) if ph == 5 else 4
    if inks == "bad":
        return "§16: NumberOfInks"
    if ph == 8:
        if m is not None and not (m <= spp and spp - m in (1, 3)):
            return "§23: CIELab needs 1 or 3 colour samples"
    elif ph <= 5:
        c = 3 if ph == 2 else inks if ph == 5 else 1
        if c < 1 or spp < c or (m is not None and m != spp - c):
            return "§8: the samples do not match PhotometricInterpretation and ExtraSamples"
        if ph == 3 and spp != 1:
            return "§8: a palette image has one sample"
        if ph == 4 and (spp != 1 or bps != 1):
            return "§8: a transparency mask has one 1-bit sample"
    else:
        return "§8: a PhotometricInterpretation TIFF 6.0 does not define"
    if ph == 3:
        cm = vals(320)
        if not isinstance(cm, list) or len(cm) != 3 * 2 ** bps:
            return "§5: a palette image needs a ColorMap of 3 * 2**BitsPerSample values"
    for t in (340, 341):
        if t in E and E[t][1][2] != spp:
            return "§19: SMinSampleValue and SMaxSampleValue need one value per sample"
    planes = spp if planar == 2 else 1
    sc = 1 if planar == 2 else spp
    if present(322) or present(323):
        if not (present(322) and present(323)):
            return "§15: TileWidth and TileLength go together"
        if present(273) or present(279) or present(278):
            return "§15: do not use both strip-oriented and tile-oriented fields"
        tw, th = one(322, 0), one(323, 0)
        if tw in (0, "bad") or th in (0, "bad"):
            return "§15: TileWidth and TileLength"
        if tw % 16 or th % 16:
            return "§15: TileWidth and TileLength must be multiples of 16"
        count = planes * (-(-w // tw)) * (-(-h // th))
        offt, cntt = 324, 325
        rb = tw * sc * bps // 8

        def rows(k):
            return th
    else:
        if present(324) or present(325):
            return "§15: do not use both strip-oriented and tile-oriented fields"
        rs = min(rps, h)
        spl = -(-h // rs)
        count = planes * spl
        offt, cntt = 273, 279
        rb = -(-(w * sc * bps) // 8)

        def rows(k):
            j = k % spl
            return rs if (j + 1) * rs <= h else h - j * rs
    offs, cnts = vals(offt), vals(cntt)
    if not isinstance(offs, list) or not isinstance(cnts, list):
        return "§8, §15: the offsets and byte counts are required"
    if len(offs) != count or len(cnts) != count:
        return "§8, §15: one offset and byte count per strip or tile"
    for k in range(count):
        a, c = offs[k], cnts[k]
        if a + c > len(d):
            return "§7: strip or tile outside the file"
        data, need = d[a:a + c], rows(k) * rb
        why = chunk(comp, data, need, rb)
        if why:
            return why
    return None


def chunk(comp, data, need, rb):
    if comp == 1:
        return "§8: an uncompressed strip shorter than the strip" if len(data) < need else None
    if comp == 8:
        z = zlib.decompressobj()
        try:
            out = z.decompress(data)
        except zlib.error:
            return "Deflate: not a zlib stream"
        if not z.eof:
            return "Deflate: the stream does not end"
        return "§3, §15: Deflate data that is not the strip's size" if len(out) != need else None
    if comp == 32773:
        i = out = 0
        while out < need:
            if i >= len(data):
                return "§9: PackBits data that runs out"
            x = data[i]
            if x == 128:
                i += 1
                continue
            room = rb - out % rb
            ln = 257 - x if x > 128 else x + 1
            if ln > room:
                return "§9: do not compress across row boundaries"
            step = 2 if x > 128 else 1 + ln
            if i + step > len(data):
                return "§9: PackBits data that runs out"
            i += step
            out += ln
        return None
    return lzw(data, need)


def lzw(data, need):
    total = 8 * len(data)
    padded = data + b"\0\0\0"
    q = out = 0
    w, prev, started, dic = 9, None, False, None
    while True:
        if q + w > total:
            return "§13: each strip ends with an EndOfInformation code"
        i = q >> 3
        v = (padded[i] << 16) | (padded[i + 1] << 8) | padded[i + 2]
        c = (v >> (24 - (q & 7) - w)) & ((1 << w) - 1)
        q += w
        if c == 256:
            dic = [bytes([i]) for i in range(256)] + [b"", b""]
            w, prev, started = 9, None, True
            continue
        if c == 257:
            if started and out == need:
                return None
            return "§13: LZW data that is not the strip's size"
        if not started:
            return "§13: each strip begins with a ClearCode"
        if prev is None:
            if c >= 256:
                return "§13: a code not in the table"
            s = dic[c]
        else:
            if len(dic) >= 4096:
                return "§13: the table can have at most 4096 entries"
            if c < len(dic):
                s = dic[c]
            elif c == len(dic):
                s = dic[prev] + dic[prev][:1]
            else:
                return "§13: a code not in the table"
            dic.append(dic[prev] + s[:1])
            if len(dic) + 1 >= (1 << w) and w < 12:
                w += 1
        if out + len(s) > need:
            return "§13: LZW data that is not the strip's size"
        out += len(s)
        prev = c


try:
    r = check(open(sys.argv[1], "rb").read())
except Exception as ex:  # a bug here, not a verdict
    print("rules.py failed:", ex)
    sys.exit(2)
print(r or "conforming")
sys.exit(0 if r else 1)
