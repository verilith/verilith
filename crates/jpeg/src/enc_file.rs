//! The file the encoder writes, as libjpeg writes it: SOI, a JFIF APP0
//! segment, the two quantization tables, the frame header, the four
//! Huffman tables, the scan header, the scan's data and EOI. Proven: under
//! the specification, the file decodes to the frame, the coefficients and
//! the quantization tables coded, in YCbCr.
use crate::enc_bits::*;
use crate::enc_huff::*;
use crate::enc_scan::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Segments
// ---------------------------------------------------------------------------
pub open spec fn soi() -> Seq<u8> {
    seq![0xFFu8, 0xD8]
}

pub open spec fn eoi() -> Seq<u8> {
    seq![0xFFu8, 0xD9]
}

/// JFIF 1.01, no units, 1:1, no thumbnail (libjpeg's `emit_jfif_app0`).
pub open spec fn app0() -> Seq<u8> {
    seq![0xFFu8, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0]
}

/// Quantization table `n`, 8-bit entries, in zigzag order.
pub open spec fn dqt_seg(n: u8, q: Seq<u8>) -> Seq<u8> {
    seq![0xFFu8, 0xDB, 0, 67, n] + Seq::new(64, |i: int| q[zz(i)])
}

/// The frame header: baseline, 8 bits, `h` rows of `w`, three components.
pub open spec fn sof_seg(w: int, h: int, hv: u8) -> Seq<u8> {
    seq![
        0xFFu8,
        0xC0,
        0,
        17,
        8,
        (h / 256) as u8,
        (h % 256) as u8,
        (w / 256) as u8,
        (w % 256) as u8,
        3,
        1,
        hv,
        0,
        2,
        0x11,
        1,
        3,
        0x11,
        1
    ]
}

/// The number of symbols of a table.
pub open spec fn total(t: HuffTable) -> int {
    hbase(t, 17)
}

/// A Huffman table, class and number `tc`.
pub open spec fn dht_seg(tc: u8, t: HuffTable) -> Seq<u8> {
    let len = 19 + total(t);
    seq![0xFFu8, 0xC4, (len / 256) as u8, (len % 256) as u8, tc] + t.counts + t.vals.subrange(0, total(t))
}

/// The scan header: components 1, 2, 3 with tables 0, 1, 1; all of the
/// spectrum; no successive approximation.
pub open spec fn sos_seg() -> Seq<u8> {
    seq![0xFFu8, 0xDA, 0, 12, 3, 1, 0, 2, 0x11, 3, 0x11, 0, 63, 0]
}

/// The headers: everything before the scan's data.
pub open spec fn headers(w: int, h: int, hv: u8, q0: Seq<u8>, q1: Seq<u8>, ht: Seq<HuffTable>) -> Seq<u8> {
    soi() + app0() + dqt_seg(0, q0) + dqt_seg(1, q1) + sof_seg(w, h, hv) + dht_seg(0x00, ht[0]) + dht_seg(0x10, ht[1])
        + dht_seg(0x01, ht[2]) + dht_seg(0x11, ht[3]) + sos_seg()
}

/// The whole file around the scan data `done` (unstuffed).
#[verifier::opaque]
pub open spec fn jfile(w: int, h: int, hv: u8, q0: Seq<u8>, q1: Seq<u8>, ht: Seq<HuffTable>, done: Seq<u8>) -> Seq<u8> {
    headers(w, h, hv, q0, q1, ht) + stuff(done) + eoi()
}

/// The frame the file declares.
pub open spec fn frame_of(w: int, h: int, hv: u8) -> Frame {
    Frame {
        prog: false,
        w,
        h,
        nc: 3,
        comps: seq![
            Comp { id: 1, h: hv / 16, v: hv % 16, tq: 0 },
            Comp { id: 2, h: 1, v: 1, tq: 1 },
            Comp { id: 3, h: 1, v: 1, tq: 1 }
        ],
    }
}

/// A table the file can carry: sixteen counts, 256 symbols of which those
/// past the last are zero (as a DHT segment reads them).
pub open spec fn tab_ok(t: HuffTable) -> bool {
    &&& t.counts.len() == 16
    &&& t.vals.len() == 256
    &&& huff_ok(t)
    &&& forall|i: int| total(t) <= i < 256 ==> #[trigger] t.vals[i] == 0
}

/// A quantization table for the file: 64 entries from 1 to 255.
pub open spec fn q_ok(q: Seq<u8>) -> bool {
    q.len() == 64 && forall|i: int| 0 <= i < 64 ==> #[trigger] q[i] >= 1
}

pub open spec fn q16(q: Seq<u8>) -> Seq<u16> {
    Seq::new(64, |i: int| q[i] as u16)
}

// ---------------------------------------------------------------------------
// Placement
// ---------------------------------------------------------------------------
/// `s` is in `d` at `p`.
pub open spec fn at(d: Seq<u8>, p: int, s: Seq<u8>) -> bool {
    0 <= p && p + s.len() <= d.len() && d.subrange(p, p + s.len()) == s
}

pub proof fn lemma_at_cat(d: Seq<u8>, p: int, x: Seq<u8>, y: Seq<u8>)
    requires
        at(d, p, x + y),
    ensures
        at(d, p, x),
        at(d, p + x.len(), y),
{
    assert(d.subrange(p, p + x.len()) =~= (x + y).subrange(0, x.len() as int));
    assert((x + y).subrange(0, x.len() as int) =~= x);
    assert(d.subrange(p + x.len(), p + x.len() + y.len()) =~= (x + y).subrange(x.len() as int, (x.len() + y.len()) as int));
    assert((x + y).subrange(x.len() as int, (x.len() + y.len()) as int) =~= y);
}

pub proof fn lemma_at_byte(d: Seq<u8>, p: int, s: Seq<u8>)
    requires
        at(d, p, s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> #[trigger] byte(d, p + i) == s[i],
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] byte(d, p + i) == s[i] by {
        assert(d.subrange(p, p + s.len())[i] == d[p + i]);
    }
    if s.len() > 0 {
        assert(byte(d, p + 0) == s[0]);
    }
}

/// A marker right at `p`.
pub proof fn lemma_marker_at(d: Seq<u8>, p: int, code: u8)
    requires
        0 <= p,
        p + 2 <= d.len(),
        byte(d, p + 0) == 0xFF,
        byte(d, p + 1) == code,
        code != 0xFF,
        code != 0,
    ensures
        marker_after(d, p) == (code, p + 2),
{
    assert(skip_ff(d, p + 1) == p + 1);
}

// ---------------------------------------------------------------------------
// Each segment, as `run` reads it
// ---------------------------------------------------------------------------
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_run_app0(d: Seq<u8>, st: Dec, p: int)
    requires
        at(d, p, app0()),
    ensures
        run(d, st, p) == run(d, Dec { jfif: true, ..st }, p + 18),
{
    lemma_at_byte(d, p, app0());
    lemma_marker_at(d, p, 0xE0);
    let q = p + 2;
    assert(be16(d, q) == 16);
    assert(has_tag(d, q + 2, seq![0x4Au8, 0x46u8, 0x49u8, 0x46u8, 0u8])) by {
        assert forall|i: int| 0 <= i < 5 implies byte(d, q + 2 + i) == seq![0x4Au8, 0x46u8, 0x49u8, 0x46u8, 0u8][i] by {
            assert(byte(d, p + (4 + i)) == app0()[4 + i]);
        }
    }
    assert(skip_seg(d, q) == p + 18);
    assert(p < d.len());
}

proof fn lemma_dqt_fill(d: Seq<u8>, p: int, q: Seq<u8>, i: int, acc: Seq<u16>)
    requires
        0 <= i <= 64,
        acc.len() == 64,
        q.len() == 64,
        forall|j: int| 0 <= j < 64 ==> #[trigger] byte(d, p + j) == q[zz(j)],
    ensures
        dqt_fill(d, p, false, i, acc) == Seq::new(
            64,
            |x: int| if zzi(x) >= i { q[x] as u16 } else { acc[x] },
        ),
    decreases 64 - i,
{
    lemma_zz_perm();
    if i >= 64 {
        assert(dqt_fill(d, p, false, i, acc) =~= Seq::new(64, |x: int| if zzi(x) >= i { q[x] as u16 } else { acc[x] }));
    } else {
        let v = byte(d, p + i) as u16;
        let acc2 = acc.update(zz(i), v);
        lemma_dqt_fill(d, p, q, i + 1, acc2);
        assert(Seq::new(64, |x: int| if zzi(x) >= i + 1 { q[x] as u16 } else { acc2[x] }) =~= Seq::new(
            64,
            |x: int| if zzi(x) >= i { q[x] as u16 } else { acc[x] },
        )) by {
            assert forall|x: int| 0 <= x < 64 implies (if zzi(x) >= i + 1 { q[x] as u16 } else { acc2[x] }) == (if zzi(
                x,
            ) >= i {
                q[x] as u16
            } else {
                acc[x]
            }) by {
                if zzi(x) == i {
                    assert(zz(i) == x);
                } else if x == zz(i) {
                    assert(zzi(zz(i)) == i);
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_run_dqt(d: Seq<u8>, st: Dec, p: int, n: u8, q: Seq<u8>)
    requires
        at(d, p, dqt_seg(n, q)),
        n < 2,
        q.len() == 64,
        st.t.q.len() == 4,
        st.t.q[n as int].len() == 64,
        st.t.qdef.len() == 4,
    ensures
        run(d, st, p) == run(
            d,
            Dec { t: Tables { q: st.t.q.update(n as int, q16(q)), qdef: st.t.qdef.update(n as int, true), ..st.t }, ..st },
            p + 69,
        ),
{
    let hd = seq![0xFFu8, 0xDB, 0, 67, n];
    let tb = Seq::new(64, |i: int| q[zz(i)]);
    lemma_at_cat(d, p, hd, tb);
    lemma_at_byte(d, p, hd);
    lemma_at_byte(d, p + 5, tb);
    assert(byte(d, p + 1) == 0xDB && byte(d, p + 2) == 0 && byte(d, p + 3) == 67 && byte(d, p + 4) == n);
    lemma_marker_at(d, p, 0xDB);
    let qq = p + 2;
    assert(be16(d, qq) == 67);
    assert(byte(d, qq + 2) == n);
    assert forall|j: int| 0 <= j < 64 implies #[trigger] byte(d, qq + 3 + j) == q[zz(j)] by {
        assert(byte(d, p + 5 + j) == tb[j]);
    }
    lemma_dqt_fill(d, qq + 3, q, 0, st.t.q[n as int]);
    lemma_zz_perm();
    assert(Seq::new(64, |x: int| if zzi(x) >= 0 { q[x] as u16 } else { st.t.q[n as int][x] }) =~= q16(q));
    let t2 = Tables { q: st.t.q.update(n as int, q16(q)), qdef: st.t.qdef.update(n as int, true), ..st.t };
    assert(dqt(d, qq + 2, 65, st.t) == dqt(d, qq + 2 + 65, 0, t2));
    assert(dqt(d, qq + 2 + 65, 0, t2) == Some(t2));
    assert(p < d.len());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_run_sof(d: Seq<u8>, st: Dec, p: int, w: int, h: int, hv: u8)
    requires
        at(d, p, sof_seg(w, h, hv)),
        1 <= w <= 65500,
        1 <= h <= 65500,
        hv == 0x11 || hv == 0x12 || hv == 0x21 || hv == 0x22,
        st.f is None,
    ensures
        run(d, st, p) == run(d, Dec { f: Some(frame_of(w, h, hv)), ..st }, p + 19),
        enc_frame(frame_of(w, h, hv)),
{
    let s = sof_seg(w, h, hv);
    lemma_at_byte(d, p, s);
    lemma_marker_at(d, p, 0xC0);
    let q = p + 2;
    assert(be16(d, q) == 17);
    assert(byte(d, q + 2) == 8);
    assert(byte(d, q + 7) == 3);
    assert(be16(d, q + 3) == h) by {
        assert(byte(d, p + 5) == s[5] && byte(d, p + 6) == s[6]);
    }
    assert(be16(d, q + 5) == w) by {
        assert(byte(d, p + 7) == s[7] && byte(d, p + 8) == s[8]);
    }
    let f = sof_frame(d, q, false);
    let g = frame_of(w, h, hv);
    assert(byte(d, q + 8) == 1 && byte(d, q + 9) == hv && byte(d, q + 10) == 0);
    assert(byte(d, q + 11) == 2 && byte(d, q + 12) == 0x11 && byte(d, q + 13) == 1);
    assert(byte(d, q + 14) == 3 && byte(d, q + 15) == 0x11 && byte(d, q + 16) == 1);
    assert(f.comps =~= g.comps);
    assert(f == g);
    lemma_geom_frame(w, h, hv);
    assert(sof(d, q, false) == Some(g));
    assert(p < d.len());
}

proof fn lemma_geom_frame(w: int, h: int, hv: u8)
    requires
        1 <= w <= 65500,
        1 <= h <= 65500,
        hv == 0x11 || hv == 0x12 || hv == 0x21 || hv == 0x22,
    ensures
        enc_frame(frame_of(w, h, hv)),
        frame_ok(frame_of(w, h, hv)),
{
    let f = frame_of(w, h, hv);
    assert(maxh(f) == hv / 16);
    assert(maxv(f) == hv % 16);
}

proof fn lemma_dht_total(d: Seq<u8>, p: int, t: HuffTable, i: int)
    requires
        0 <= i <= 16,
        t.counts.len() == 16,
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(d, p + j) == t.counts[j],
    ensures
        dht_total(d, p, i) == hbase(t, i + 1),
    decreases i,
{
    if i > 0 {
        lemma_dht_total(d, p, t, i - 1);
        assert(hcount(t, i) == t.counts[i - 1]);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_run_dht(d: Seq<u8>, st: Dec, p: int, tc: u8, t: HuffTable)
    requires
        at(d, p, dht_seg(tc, t)),
        tab_ok(t),
        tc == 0x00 || tc == 0x10 || tc == 0x01 || tc == 0x11,
        st.t.dc.len() == 4 && st.t.dcdef.len() == 4 && st.t.ac.len() == 4 && st.t.acdef.len() == 4,
    ensures
        run(d, st, p) == run(
            d,
            Dec {
                t: if tc >= 16 {
                    Tables {
                        ac: st.t.ac.update(tc as int - 16, t),
                        acdef: st.t.acdef.update(tc as int - 16, true),
                        ..st.t
                    }
                } else {
                    Tables { dc: st.t.dc.update(tc as int, t), dcdef: st.t.dcdef.update(tc as int, true), ..st.t }
                },
                ..st
            },
            p + 21 + total(t),
        ),
{
    let n = total(t);
    crate::huff::lemma_hbase_mono(t, 1, 17);
    assert(0 <= n <= 256);
    let len = 19 + n;
    let hd = seq![0xFFu8, 0xC4, (len / 256) as u8, (len % 256) as u8, tc];
    let vs = t.vals.subrange(0, n);
    assert(dht_seg(tc, t) == hd + t.counts + vs);
    lemma_at_cat(d, p, hd + t.counts, vs);
    lemma_at_cat(d, p, hd, t.counts);
    lemma_at_byte(d, p, hd);
    lemma_at_byte(d, p + 5, t.counts);
    lemma_at_byte(d, p + 21, vs);
    assert(byte(d, p + 1) == 0xC4 && byte(d, p + 4) == tc);
    lemma_marker_at(d, p, 0xC4);
    let q = p + 2;
    assert(be16(d, q) == 19 + n) by {
        assert(byte(d, p + 2) == hd[2] && byte(d, p + 3) == hd[3]);
        lemma_fundamental_div_mod(19 + n, 256);
    }
    assert(byte(d, q + 2) == tc);
    assert forall|j: int| 0 <= j < 16 implies #[trigger] byte(d, q + 3 + j) == t.counts[j] by {
        assert(byte(d, p + 5 + j) == t.counts[j]);
    }
    lemma_dht_total(d, q + 3, t, 16);
    let h = dht_table(d, q + 3, n);
    reveal_with_fuel(dht, 2);
    assert(h.counts =~= t.counts);
    assert(h.vals =~= t.vals) by {
        assert forall|i: int| 0 <= i < 256 implies h.vals[i] == t.vals[i] by {
            if i < n {
                assert(byte(d, p + 21 + i) == vs[i]);
                assert(q + 3 + 16 + i == p + 21 + i);
            }
        }
    }
    assert(h == t);
    let rem = 19 + n - 2;
    assert(rem > 16);
    let t2 = if tc >= 16 {
        Tables { ac: st.t.ac.update(tc as int - 16, t), acdef: st.t.acdef.update(tc as int - 16, true), ..st.t }
    } else {
        Tables { dc: st.t.dc.update(tc as int, t), dcdef: st.t.dcdef.update(tc as int, true), ..st.t }
    };
    assert(dht(d, q + 2, rem, st.t) == dht(d, q + 2 + 17 + n, 0, t2));
    assert(dht(d, q + 2 + 17 + n, 0, t2) == Some(t2));
    assert(q + be16(d, q) == p + 21 + n);
    assert(p < d.len());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_run_sos(d: Seq<u8>, st: Dec, p: int, k: Codes, a: Seq<Seq<i16>>)
    requires
        at(d, p, sos_seg()),
        st.f is Some,
        enc_frame(st.f->0),
        st.f->0.comps[0].id == 1 && st.f->0.comps[1].id == 2 && st.f->0.comps[2].id == 3,
        st.f->0.comps[0].tq == 0 && st.f->0.comps[1].tq == 1 && st.f->0.comps[2].tq == 1,
        !st.started,
        st.jfif,
        st.adobe is None,
        st.ql == seq![zeros64(), zeros64(), zeros64()],
        st.qset == seq![false, false, false],
        st.t.qdef.len() == 4 && st.t.qdef[0] && st.t.qdef[1],
        st.t.q.len() == 4,
        st.t.dcdef.len() == 4 && st.t.dcdef[0] && st.t.dcdef[1],
        st.t.acdef.len() == 4 && st.t.acdef[0] && st.t.acdef[1],
        st.t.dc.len() == 4 && st.t.ac.len() == 4,
        huff_dc_ok(st.t.dc[0]) && huff_dc_ok(st.t.dc[1]),
        scan_pre(d, st.f->0, with_std(st.t), k, a, p + 14),
    ensures
        run(d, st, p) == run(
            d,
            Dec {
                t: with_std(st.t),
                started: true,
                multi: false,
                color: Color::YCbCr,
                ql: seq![st.t.q[0], st.t.q[1], st.t.q[1]],
                qset: seq![true, true, true],
                a,
                ..st
            },
            p + 14,
        ),
{
    let f = st.f->0;
    let s = sos_seg();
    lemma_at_byte(d, p, s);
    lemma_marker_at(d, p, 0xDA);
    let q = p + 2;
    assert(be16(d, q) == 12);
    assert(byte(d, q + 2) == 3);
    let sc = sos(d, q, f)->0;
    assert(byte(d, q + 3) == 1 && byte(d, q + 5) == 2 && byte(d, q + 7) == 3);
    assert(byte(d, q + 4) == 0 && byte(d, q + 6) == 0x11 && byte(d, q + 8) == 0x11);
    assert(byte(d, q + 9) == 0 && byte(d, q + 10) == 63 && byte(d, q + 11) == 0);
    reveal_with_fuel(find_comp, 4);
    assert(find_comp(f, 1, 0, 0) == 0);
    assert(find_comp(f, 2, 1, 0) == 1);
    assert(find_comp(f, 3, 2, 0) == 2);
    assert(sc.ci =~= enc_scan_hdr().ci);
    assert(sc.td =~= enc_scan_hdr().td);
    assert(sc.ta =~= enc_scan_hdr().ta);
    assert(sc == enc_scan_hdr());
    let t = with_std(st.t);
    lemma_geom(f);
    assert(scan_ok(f, t, sc)) by {
        assert(t.dc[0] == st.t.dc[0] && t.dc[1] == st.t.dc[1]);
        assert(t.dcdef[0] && t.dcdef[1] && t.acdef[0] && t.acdef[1]);
        assert(codes_ready(t, k));
        assert(dc_ready(t.dc[0], k.dco[0], k.dsi[0]));
        assert(dc_ready(t.dc[1], k.dco[1], k.dsi[1]));
        assert(ac_ready(t.ac[0], k.aco[0], k.asi[0]));
        assert(ac_ready(t.ac[1], k.aco[1], k.asi[1]));
        assert(mcu_blocks(f, sc) <= 6) by (nonlinear_arith)
            requires
                mcu_blocks(f, sc) == f.comps[0].h * f.comps[0].v + 2,
                1 <= f.comps[0].h <= 2,
                1 <= f.comps[0].v <= 2,
        ;
    }
    reveal_with_fuel(latch, 4);
    let lt = latch(f, t, sc, st.ql, st.qset, 0);
    assert(t.qdef == st.t.qdef && t.q == st.t.q);
    assert(lt == Some((seq![st.t.q[0], st.t.q[1], st.t.q[1]], seq![true, true, true]))) by {
        assert(st.ql.update(0, t.q[0]).update(1, t.q[1]).update(2, t.q[1]) =~= seq![st.t.q[0], st.t.q[1], st.t.q[1]]);
        assert(st.qset.update(0, true).update(1, true).update(2, true) =~= seq![true, true, true]);
    }
    let z = Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16));
    lemma_scan(d, f, t, k, a, p + 14);
    assert(color_of(f, true, None) == Color::YCbCr);
    assert(p < d.len());
}

// ---------------------------------------------------------------------------
// The file
// ---------------------------------------------------------------------------
/// What the encoder knows of its file.
pub open spec fn file_pre(
    w: int,
    h: int,
    hv: u8,
    q0: Seq<u8>,
    q1: Seq<u8>,
    ht: Seq<HuffTable>,
    k: Codes,
    a: Seq<Seq<i16>>,
    done: Seq<u8>,
) -> bool {
    let f = frame_of(w, h, hv);
    let all = enc_upto(f, k, a, n_mcus(f)).0;
    &&& 1 <= w <= 65500
    &&& 1 <= h <= 65500
    &&& hv == 0x11 || hv == 0x22
    &&& q_ok(q0) && q_ok(q1)
    &&& ht.len() == 4
    &&& forall|i: int| 0 <= i < 4 ==> tab_ok(#[trigger] ht[i])
    &&& huff_dc_ok(ht[0]) && huff_dc_ok(ht[2])
    &&& k.dco.len() == 2 && k.dsi.len() == 2 && k.aco.len() == 2 && k.asi.len() == 2
    &&& dc_ready(ht[0], k.dco[0], k.dsi[0]) && ac_ready(ht[1], k.aco[0], k.asi[0])
    &&& dc_ready(ht[2], k.dco[1], k.dsi[1]) && ac_ready(ht[3], k.aco[1], k.asi[1])
    &&& coefs_ok(f, a)
    &&& bits_at(done, 0, all)
    &&& all.len() <= 8 * done.len()
}

/// The theorem: the file decodes to its frame, the coefficients coded and
/// the quantization tables, in YCbCr.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_file(
    w: int,
    h: int,
    hv: u8,
    q0: Seq<u8>,
    q1: Seq<u8>,
    ht: Seq<HuffTable>,
    k: Codes,
    a: Seq<Seq<i16>>,
    done: Seq<u8>,
)
    requires
        file_pre(w, h, hv, q0, q1, ht, k, a, done),
    ensures
        jpeg_coded(jfile(w, h, hv, q0, q1, ht, done)) == Some(
            Coded { f: frame_of(w, h, hv), a, ql: seq![q16(q0), q16(q1), q16(q1)], color: Color::YCbCr },
        ),
{
    hide(run);
    let d = jfile(w, h, hv, q0, q1, ht, done);
    let f = frame_of(w, h, hv);
    let s1 = soi();
    let s2 = app0();
    let s3 = dqt_seg(0, q0);
    let s4 = dqt_seg(1, q1);
    let s5 = sof_seg(w, h, hv);
    let s6 = dht_seg(0x00, ht[0]);
    let s7 = dht_seg(0x10, ht[1]);
    let s8 = dht_seg(0x01, ht[2]);
    let s9 = dht_seg(0x11, ht[3]);
    let s10 = sos_seg();
    let s11 = stuff(done);
    let s12 = eoi();
    let p2 = 2int;
    let p3 = p2 + 18;
    let p4 = p3 + 69;
    let p5 = p4 + 69;
    let p6 = p5 + 19;
    let p7 = p6 + s6.len();
    let p8 = p7 + s7.len();
    let p9 = p8 + s8.len();
    let p10 = p9 + s9.len();
    let p11 = p10 + 14;
    let p12 = p11 + s11.len();
    lemma_layout(w, h, hv, q0, q1, ht, done);
    lemma_at_byte(d, 0, s1);
    // The scan's data, then EOI.
    lemma_at_byte(d, p12, s12);
    assert(d.subrange(p11, p11 + s11.len()) == s11);
    lemma_ecs_stuffed(d, p11, done);
    // The tables as the file defines them.
    let st0 = dec_init();
    let st1 = Dec { jfif: true, ..st0 };
    lemma_run_app0(d, st0, p2);
    let t2 = Tables { q: st1.t.q.update(0, q16(q0)), qdef: st1.t.qdef.update(0, true), ..st1.t };
    let st2 = Dec { t: t2, ..st1 };
    lemma_run_dqt(d, st1, p3, 0, q0);
    let t3 = Tables { q: t2.q.update(1, q16(q1)), qdef: t2.qdef.update(1, true), ..t2 };
    let st3 = Dec { t: t3, ..st2 };
    lemma_run_dqt(d, st2, p4, 1, q1);
    let st4 = Dec { f: Some(f), ..st3 };
    lemma_run_sof(d, st3, p5, w, h, hv);
    let t5 = Tables { dc: t3.dc.update(0, ht[0]), dcdef: t3.dcdef.update(0, true), ..t3 };
    let st5 = Dec { t: t5, ..st4 };
    assert(tab_ok(ht[0]) && tab_ok(ht[1]) && tab_ok(ht[2]) && tab_ok(ht[3]));
    lemma_run_dht(d, st4, p6, 0x00, ht[0]);
    let t6 = Tables { ac: t5.ac.update(0, ht[1]), acdef: t5.acdef.update(0, true), ..t5 };
    let st6 = Dec { t: t6, ..st5 };
    lemma_run_dht(d, st5, p7, 0x10, ht[1]);
    let t7 = Tables { dc: t6.dc.update(1, ht[2]), dcdef: t6.dcdef.update(1, true), ..t6 };
    let st7 = Dec { t: t7, ..st6 };
    lemma_run_dht(d, st6, p8, 0x01, ht[2]);
    let t8 = Tables { ac: t7.ac.update(1, ht[3]), acdef: t7.acdef.update(1, true), ..t7 };
    let st8 = Dec { t: t8, ..st7 };
    lemma_run_dht(d, st7, p9, 0x11, ht[3]);
    let t = with_std(t8);
    assert(t.dc[0] == ht[0] && t.dc[1] == ht[2] && t.ac[0] == ht[1] && t.ac[1] == ht[3]);
    assert(t.dc.len() == 4 && t.ac.len() == 4);
    assert(codes_ready(t, k)) by {
        assert forall|i: int| 0 <= i < 2 implies dc_ready(t.dc[i], #[trigger] k.dco[i], k.dsi[i]) by {
            if i == 0 {
            } else {
            }
        }
        assert forall|i: int| 0 <= i < 2 implies ac_ready(t.ac[i], #[trigger] k.aco[i], k.asi[i]) by {
            if i == 0 {
            } else {
            }
        }
    }
    assert(t.ri == 0);
    assert(ecs(d, p11) == done);
    assert(scan_pre(d, f, t, k, a, p11));
    assert(st8.ql == seq![zeros64(), zeros64(), zeros64()]);
    lemma_run_sos(d, st8, p10, k, a);
    let st9 = Dec {
        t,
        started: true,
        multi: false,
        color: Color::YCbCr,
        ql: seq![t8.q[0], t8.q[1], t8.q[1]],
        qset: seq![true, true, true],
        a,
        ..st8
    };
    assert(t8.q[0] == q16(q0) && t8.q[1] == q16(q1));
    assert(marker_after(d, p11) == (0xD9u8, p12 + 2));
    lemma_run_eoi(d, st9, p11);
    assert(byte(d, 0) == 0xFF && byte(d, 1) == 0xD8);
    assert(st9.ql == seq![q16(q0), q16(q1), q16(q1)]);
    assert forall|i: int| 0 <= i < 4 implies 0 <= total(#[trigger] ht[i]) <= 256 by {
        crate::huff::lemma_hbase_mono(ht[i], 1, 17);
    }
    assert(s6.len() == 21 + total(ht[0]));
    assert(s7.len() == 21 + total(ht[1]));
    assert(run(d, st0, 2) == run(d, st1, 20));
    assert(run(d, st1, 20) == run(d, st2, 89));
    assert(run(d, st2, 89) == run(d, st3, 158));
    assert(run(d, st3, 158) == run(d, st4, 177));
    assert(run(d, st4, 177) == run(d, st5, p7));
    assert(run(d, st5, p7) == run(d, st6, p8));
    assert(run(d, st6, p8) == run(d, st7, p9));
    assert(run(d, st7, p9) == run(d, st8, p10));
    assert(run(d, st8, p10) == run(d, st9, p11));
    assert(run(d, dec_init(), 2) == Some(st9));
}

proof fn lemma_run_eoi(d: Seq<u8>, st: Dec, p: int)
    requires
        marker_after(d, p).0 == 0xD9,
        st.started,
    ensures
        run(d, st, p) == Some(st),
{
}

proof fn lemma_layout(w: int, h: int, hv: u8, q0: Seq<u8>, q1: Seq<u8>, ht: Seq<HuffTable>, done: Seq<u8>)
    requires
        q0.len() == 64,
        q1.len() == 64,
        ht.len() == 4,
    ensures
        ({
            let d = jfile(w, h, hv, q0, q1, ht, done);
            let p7: int = 177 + dht_seg(0x00, ht[0]).len() as int;
            let p8: int = p7 + dht_seg(0x10, ht[1]).len() as int;
            let p9: int = p8 + dht_seg(0x01, ht[2]).len() as int;
            let p10: int = p9 + dht_seg(0x11, ht[3]).len() as int;
            let p11: int = p10 + 14;
            let p12: int = p11 + stuff(done).len() as int;
            &&& at(d, 0, soi())
            &&& at(d, 2, app0())
            &&& at(d, 20, dqt_seg(0, q0))
            &&& at(d, 89, dqt_seg(1, q1))
            &&& at(d, 158, sof_seg(w, h, hv))
            &&& at(d, 177, dht_seg(0x00, ht[0]))
            &&& at(d, p7, dht_seg(0x10, ht[1]))
            &&& at(d, p8, dht_seg(0x01, ht[2]))
            &&& at(d, p9, dht_seg(0x11, ht[3]))
            &&& at(d, p10, sos_seg())
            &&& at(d, p11, stuff(done))
            &&& at(d, p12, eoi())
            &&& d.len() == p12 + 2
        }),
{
    reveal(jfile);
    let d = jfile(w, h, hv, q0, q1, ht, done);
    let s1 = soi();
    let s2 = app0();
    let s3 = dqt_seg(0, q0);
    let s4 = dqt_seg(1, q1);
    let s5 = sof_seg(w, h, hv);
    let s6 = dht_seg(0x00, ht[0]);
    let s7 = dht_seg(0x10, ht[1]);
    let s8 = dht_seg(0x01, ht[2]);
    let s9 = dht_seg(0x11, ht[3]);
    let s10 = sos_seg();
    let s11 = stuff(done);
    let s12 = eoi();
    assert(at(d, 0, d)) by {
        assert(d.subrange(0, d.len() as int) =~= d);
    }
    let p1 = 0int;
    let p2 = p1 + s1.len();
    let p3 = p2 + s2.len();
    let p4 = p3 + s3.len();
    let p5 = p4 + s4.len();
    let p6 = p5 + s5.len();
    let p7 = p6 + s6.len();
    let p8 = p7 + s7.len();
    let p9 = p8 + s8.len();
    let p10 = p9 + s9.len();
    let p11 = p10 + s10.len();
    let p12 = p11 + s11.len();
    assert(d == s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + s11 + s12);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + s11, s12);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10, s11);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9, s10);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8, s9);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6 + s7, s8);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5 + s6, s7);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4 + s5, s6);
    lemma_at_cat(d, 0, s1 + s2 + s3 + s4, s5);
    lemma_at_cat(d, 0, s1 + s2 + s3, s4);
    lemma_at_cat(d, 0, s1 + s2, s3);
    lemma_at_cat(d, 0, s1, s2);
}


} // verus!
