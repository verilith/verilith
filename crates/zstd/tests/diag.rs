//! Says where vzstd rejects the frames named in VZSTD_DIAG (a directory).
//! Only for single-frame inputs; a diagnostic, not a test of anything.
use vstd::prelude::{Ghost, Tracked};
use verilith_zstd::bits::{bstart_exec, rd};
use verilith_zstd::frame::{frame_header_exec, le_at};
use verilith_zstd::huf::*;
use verilith_zstd::seq::*;

/// A limit no test output reaches: 1 TiB, or 1 GiB on 32-bit targets
/// (where the decoder takes limits up to 2 GiB).
const BIG: usize = if usize::BITS == 64 { (1u64 << 40) as usize } else { 1 << 30 };

fn diag(c: &[u8]) -> String {
    let h = match frame_header_exec(&c[4..]) {
        None => return "header".into(),
        Some(h) => h,
    };
    let mut p = 4 + h.size;
    let bmax = h.window.min(131072) as usize;
    let mut d = FrameDec { out: vec![], fstart: 0, r1: 1, r2: 4, r3: 8, huf: None, seqt: None, lits: vec![] };
    let mut k = 0;
    loop {
        if p + 3 > c.len() {
            return format!("block {k}: truncated header");
        }
        let bh = le_at(c, p, 3);
        let (last, ty, size) = (bh & 1, (bh >> 1) & 3, (bh >> 3) as usize);
        p += 3;
        if size > bmax {
            return format!("block {k}: size {size} > bmax {bmax}");
        }
        if ty == 2 {
            if p + size > c.len() {
                return format!("block {k}: truncated");
            }
            let blk = &c[p..p + size];
            let used = match lit_section_exec(blk, bmax, &mut d.huf, &mut d.lits, Tracked::assume_new()) {
                None => return format!("block {k}: literals section (type {}): {}", blk[0] & 3, lit_diag(blk, bmax)),
                Some(u) => u,
            };
            let sec = &blk[used..];
            let (n, hh) = match nb_seq_exec(sec) {
                None => return format!("block {k}: nb_seq"),
                Some(x) => x,
            };
            if n == 0 && hh != sec.len() {
                return format!("block {k}: no sequences but {} bytes left", sec.len() - hh);
            }
            if n > 0 && sec.len() > hh && sec[hh] % 4 != 0 {
                return format!("block {k}: reserved bits in modes byte {:02x}", sec[hh]);
            }
            if n > 0 {
                let (tabs, a3) = match seq_hdr_exec(sec, hh, &d.seqt, Ghost::assume_new(), Tracked::assume_new()) {
                    None => return format!("block {k}: sequence tables (modes {:02x})", sec[hh]),
                    Some(x) => x,
                };
                let s = &sec[a3..];
                let mut q = match bstart_exec(s) {
                    None => return format!("block {k}: seq bitstream start"),
                    Some(q) => q,
                };
                let (l1, l2, l3) = (tabs.ll.log as usize, tabs.of.log as usize, tabs.ml.log as usize);
                if l1 + l2 + l3 > q {
                    return format!("block {k}: seq init states overrun");
                }
                let mut sll = rd(s, q, l1 as u32) as u32;
                let mut sof = rd(s, q - l1, l2 as u32) as u32;
                let mut sml = rd(s, q - l1 - l2, l3 as u32) as u32;
                q -= l1 + l2 + l3;
                let (mut r1, mut r2, mut r3, mut li) = (d.r1, d.r2, d.r3, 0usize);
                let lits = d.lits.clone();
                for i in 0..n {
                    // One sequence adds under 2^19 bytes; the step wants that much
                    // room reserved, and 64 bytes more.
                    let lim = d.out.len() + (1 << 19);
                    let mut w = verilith_core::tail::Tail::take(&mut d.out, (1 << 19) + 64);
                    let step = seq_step_exec(&tabs, s, &lits, h.window, q, sll, sof, sml, r1, r2, r3, li, &mut w, 0, lim, Ghost::assume_new(), Tracked::assume_new());
                    w.put_back(&mut d.out);
                    let o = match step {
                        Err(_) => return format!("block {k}: sequence {i}/{n} step (p={q}, li={li}, lits={}, out={})", lits.len(), d.out.len()),
                        Ok(o) => o,
                    };
                    (r1, r2, r3, li) = (o.r1, o.r2, o.r3, o.li);
                    q = o.p;
                    if i + 1 < n {
                        match seq_next_exec(&tabs, s, q, sll, sof, sml, Ghost::assume_new()) {
                            None => return format!("block {k}: sequence {i}/{n} state update overrun (p={q})"),
                            Some((a, b, cc, dd)) => {
                                q = a;
                                sll = b;
                                sof = cc;
                                sml = dd;
                            },
                        }
                    }
                }
                if q != 0 {
                    return format!("block {k}: {q} bits left in sequences bitstream");
                }
                d.out.extend_from_slice(&lits[li..]);
                d.r1 = r1;
                d.r2 = r2;
                d.r3 = r3;
                d.seqt = Some(tabs);
            } else {
                d.out.extend_from_slice(&d.lits.clone());
            }
            p += size;
        } else if ty == 0 {
            d.out.extend_from_slice(&c[p..p + size]);
            p += size;
        } else if ty == 1 {
            d.out.extend(std::iter::repeat(c[p]).take(size));
            p += 1;
        } else {
            return format!("block {k}: reserved type");
        }
        if last == 1 {
            break;
        }
        k += 1;
    }
    format!("blocks fine; out {} fcs {:?} checksum {} rest {}", d.out.len(), h.fcs, h.checksum, c.len() - p)
}

#[test]
fn diag_dir() {
    let Ok(dir) = std::env::var("VZSTD_DIAG") else { return };
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    for f in names {
        let c = std::fs::read(&f).unwrap();
        eprintln!("{}: {} | whole: {:?}", f.display(), diag(&c), verilith_zstd::frame::decompress_exec(&c, BIG).map(|v| v.len()));
    }
}

fn lit_diag(b: &[u8], bmax: usize) -> String {
    if b.len() < 5 {
        return "short".into();
    }
    let sf = (b[0] / 4) % 4;
    let (lh, n, c) = lit_huf_sizes(b);
    if n > bmax || (sf != 0 && n < 6) || lh + c > b.len() {
        return format!("sizes n={n} c={c} lh={lh} len={}", b.len());
    }
    let region = &b[lh..lh + c];
    let (t, u) = match huf_desc_exec(region, Tracked::assume_new()) {
        None => return format!("tree description (header byte {})", region[0]),
        Some(x) => x,
    };
    let streams = &region[u..];
    let mut out = vec![];
    if sf == 0 {
        format!("1 stream n={n} ok={}", huf_stream_exec(&t, streams, n, &mut out, Tracked::assume_new()))
    } else {
        // Per-stream detail.
        let l1 = streams[0] as usize | (streams[1] as usize) << 8;
        let l2 = streams[2] as usize | (streams[3] as usize) << 8;
        let l3 = streams[4] as usize | (streams[5] as usize) << 8;
        let seg = (n + 3) / 4;
        let mut v = vec![];
        let mut at = 6;
        for (i, l) in [l1, l2, l3, streams.len().saturating_sub(6 + l1 + l2 + l3)].iter().enumerate() {
            if at + l > streams.len() {
                v.push(format!("s{i} overruns"));
                break;
            }
            let want = if i < 3 { seg } else { n - 3 * seg };
            let mut o = vec![];
            v.push(format!("s{i}:{}", huf_stream_exec(&t, &streams[at..at + l], want, &mut o, Tracked::assume_new())));
            at += l;
        }
        format!("4 streams n={n} log={} {}", t.log, v.join(" "))
    }
}
