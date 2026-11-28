#!/usr/bin/env python3
"""Adds counters to a copy of crates/webp (never the checkout itself):
    instrument.py WORKTREE ROOT_BITS
- every prefix code built: its longest code length (`stats::built`);
- every symbol the slow path decodes: its code length (`stats::slow`);
and builds the codes with ROOT_BITS table bits instead of `MAX_ROOT`.
With a small ROOT_BITS every symbol longer than it takes the slow path, so
one run gives the slow-path count for every larger root too."""
import pathlib, re, sys
wt, root = pathlib.Path(sys.argv[1]), int(sys.argv[2])
src = wt / "crates/webp/src"
(src / "stats.rs").write_text('''//! Counters added by bench/webp-root/instrument.py.
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
pub static BUILT: [AtomicU64; 16] = [const { AtomicU64::new(0) }; 16];
pub static SLOW: [AtomicU64; 16] = [const { AtomicU64::new(0) }; 16];
pub fn built(lens: &[u8]) {
    let m = lens.iter().copied().max().unwrap_or(0) as usize;
    BUILT[m.min(15)].fetch_add(1, Relaxed);
}
pub fn slow(e: Option<u32>) {
    if let Some(e) = e {
        SLOW[((e >> 16) as usize).min(15)].fetch_add(1, Relaxed);
    }
}
''')
lib = src / "lib.rs"
t = lib.read_text()
lib.write_text(t.replace("pub mod spec;", "pub mod spec;\npub mod stats;", 1))
c = src / "codes.rs"
t = c.read_text()
old = "let (hr, Ghost(hw)) = build(&lens, MAX_ROOT);"
assert old in t
t = t.replace(old, f"crate::stats::built(&lens);\n    let (hr, Ghost(hw)) = build(&lens, {root});")
old = "let (r, Ghost(sw)) = decode_long(&g.codes[j], buf, cnt, Ghost(lens));"
assert old in t
t = t.replace(old, old + "\n    crate::stats::slow(r);")
c.write_text(t)
b = src / "bitreader.rs"
t = b.read_text()
old = "let (r, Ghost(sw)) = decode_long(h, self.buf, self.cnt, Ghost(lens));"
assert old in t
b.write_text(t.replace(old, old + "\n            crate::stats::slow(r);"))
