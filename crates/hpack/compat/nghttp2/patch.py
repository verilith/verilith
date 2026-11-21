#!/usr/bin/env python3
"""Points an nghttp2 source tree's HPACK inflater at vhpack.

    compat/nghttp2/patch.py NGHTTP2_LIB_DIR

NGHTTP2_LIB_DIR is nghttp2's lib/ (or Node.js's deps/nghttp2/lib). In
nghttp2_hd.c, the inflater's functions are compiled out (#ifndef
NGHTTP2_VHPACK) and nghttp2_hd_vhpack.inc, copied next to it, takes their
place; nghttp2_hd.h's inflater struct gets the decoder pointer. Build with
-DNGHTTP2_VHPACK and link libverilith_hpack.a. Originals are kept as *.orig, and
running it twice is harmless. Tested with nghttp2 1.70.0 (Node.js 24).
"""
import os
import re
import shutil
import sys

FUNCS = [
    "nghttp2_hd_inflate_init", "nghttp2_hd_inflate_free",
    "nghttp2_hd_inflate_change_table_size", "nghttp2_hd_inflate_hd_nv",
    "nghttp2_hd_inflate_end_headers", "nghttp2_hd_inflate_get_num_table_entries",
    "nghttp2_hd_inflate_get_table_entry", "nghttp2_hd_inflate_get_dynamic_table_size",
    "nghttp2_hd_inflate_get_max_dynamic_table_size",
]


def main():
    d = sys.argv[1]
    here = os.path.dirname(os.path.abspath(__file__))
    c, h = os.path.join(d, "nghttp2_hd.c"), os.path.join(d, "nghttp2_hd.h")
    for p in (c, h):
        if not os.path.exists(p + ".orig"):
            shutil.copy(p, p + ".orig")
    src = open(c + ".orig").read()
    for f in FUNCS:
        # The definition: return type line(s), the name at a line start or
        # after the type, up to the first "\n}\n".
        m = re.search(r"\n((?:[a-z_0-9 ]+\*?\s*\n)?[a-z_0-9 ]*\*?\s*" + f + r"\()", src)
        assert m, f
        start = m.start(1)
        end = src.index("\n}\n", start) + 3
        src = src[:start] + "#ifndef NGHTTP2_VHPACK\n" + src[start:end] + "#endif\n" + src[end:]
    src += '\n#ifdef NGHTTP2_VHPACK\n#include "nghttp2_hd_vhpack.inc"\n#endif\n'
    open(c, "w").write(src)
    hdr = open(h + ".orig").read()
    anchor = "struct nghttp2_hd_inflater {\n"
    assert anchor in hdr
    hdr = hdr.replace(anchor, anchor + "#ifdef NGHTTP2_VHPACK\n  /* vhpack's decoder, and the entry\n     nghttp2_hd_inflate_get_table_entry returns, and the capacities of\n     nv_name_keep and nv_value_keep, which are reused when no one else\n     holds them. */\n  void *vh;\n  nghttp2_nv vh_nv;\n  size_t vh_name_cap, vh_value_cap;\n  void *vh_slots;\n#endif\n")
    open(h, "w").write(hdr)
    shutil.copy(os.path.join(here, "nghttp2_hd_vhpack.inc"), os.path.join(d, "nghttp2_hd_vhpack.inc"))
    print("patched %s and %s" % (c, h))


main()
