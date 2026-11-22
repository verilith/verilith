//! Streaming decompression, proven against `spec::frame`: input in pieces
//! of any size, output handed out in pieces of any size, and only the last
//! window of output kept.
#[allow(unused_imports)]
use crate::spec::*;
use crate::frame::*;
use crate::seq::*;
use crate::xxh::*;
use crate::prims::copy_into;
use vstd::slice::slice_subrange;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Matches reach back at most one window
// ---------------------------------------------------------------------------

/// `st` with `p` in front of its output.
pub open spec fn shift(st: FrameState, p: Seq<u8>) -> FrameState {
    FrameState { out: p + st.out, ..st }
}

pub open spec fn shift_seq(st: SeqState, p: Seq<u8>) -> SeqState {
    SeqState { out: p + st.out, ..st }
}

pub open spec fn shift_opt(r: Option<FrameState>, p: Seq<u8>) -> Option<FrameState> {
    match r {
        None => None,
        Some(st) => Some(shift(st, p)),
    }
}

/// A match copies the same bytes whatever lies more than `d` back.
pub proof fn lemma_copy_match_shift(p: Seq<u8>, o: Seq<u8>, d: nat, len: nat)
    requires
        1 <= d <= o.len(),
    ensures
        copy_match(p + o, d, len) == p + copy_match(o, d, len),
    decreases len,
{
    if len > 0 {
        let o2 = o.push(o[o.len() - d]);
        assert((p + o).push((p + o)[(p + o).len() - d]) =~= p + o2);
        lemma_copy_match_shift(p, o2, d, (len - 1) as nat);
    }
}

/// Sequences decode the same with more output in front of a window's
/// worth of it.
pub proof fn lemma_seq_run_shift(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, w: nat, n: nat, st: SeqState, p: Seq<u8>)
    requires
        w <= st.out.len(),
    ensures
        seq_run(t, s, lits, w, n, shift_seq(st, p)) == match seq_run(t, s, lits, w, n, st) {
            None => None,
            Some(f) => Some(shift_seq(f, p)),
        },
    decreases n,
{
    reveal(seq_run);
    let sp = shift_seq(st, p);
    if n == 0 {
    } else if st.sll >= t.ll.rows.len() || st.sof >= t.of.rows.len() || st.sml >= t.ml.rows.len() {
    } else {
        let ell = t.ll.rows[st.sll as int];
        let eof = t.of.rows[st.sof as int];
        let eml = t.ml.rows[st.sml as int];
        let oc = eof.sym;
        let mlb = ml_bits(eml.sym);
        let llb = ll_bits(ell.sym);
        let p0 = st.p;
        if oc + mlb + llb > p0 {
        } else {
            let ov = pow2(oc) + bits(s, p0 - oc, oc);
            let p1 = p0 - oc;
            let ml = ml_base(eml.sym) + bits(s, p1 - mlb, mlb);
            let p2 = p1 - mlb;
            let ll = ll_base(ell.sym) + bits(s, p2 - llb, llb);
            let p3 = p2 - llb;
            match resolve_offset(ov, ll == 0, st.reps) {
                None => {},
                Some((off, reps)) => {
                    if st.li + ll > lits.len() {
                    } else {
                        let out1 = st.out + lits.subrange(st.li, st.li + ll);
                        let out1p = sp.out + lits.subrange(st.li, st.li + ll);
                        assert(out1p =~= p + out1);
                        if off > out1.len() || off > w || off == 0 {
                        } else {
                            let out2 = copy_match(out1, off, ml);
                            lemma_copy_match_shift(p, out1, off, ml);
                            lemma_copy_match_len(out1, off, ml);
                            let li = st.li + ll;
                            if n == 1 {
                            } else if ell.nb + eml.nb + eof.nb > p3 {
                            } else {
                                let sll = ell.base + bits(s, p3 - ell.nb, ell.nb);
                                let p4 = p3 - ell.nb;
                                let sml = eml.base + bits(s, p4 - eml.nb, eml.nb);
                                let p5 = p4 - eml.nb;
                                let sof = eof.base + bits(s, p5 - eof.nb, eof.nb);
                                let p6 = p5 - eof.nb;
                                let nx = SeqState { p: p6, sll: sll, sof: sof, sml: sml, reps: reps, li: li, out: out2 };
                                lemma_seq_run_shift(t, s, lits, w, (n - 1) as nat, nx, p);
                                assert(shift_seq(nx, p) == SeqState {
                                    p: p6,
                                    sll: sll,
                                    sof: sof,
                                    sml: sml,
                                    reps: reps,
                                    li: li,
                                    out: copy_match(out1p, off, ml),
                                });
                            }
                        }
                    }
                },
            }
        }
    }
}

#[verifier::rlimit(60)]
pub proof fn lemma_seq_section_shift(b: Seq<u8>, lits: Seq<u8>, w: nat, st: FrameState, p: Seq<u8>)
    requires
        w <= st.out.len(),
    ensures
        seq_section(b, lits, w, shift(st, p)) == shift_opt(seq_section(b, lits, w, st), p),
{
    reveal(seq_section);
    let sp = shift(st, p);
    match nb_seq(b) {
        None => {},
        Some((n, h)) => if n == 0 {
            assert(sp.out + lits =~= p + (st.out + lits));
        } else if h + 1 > b.len() || b[h] % 4 != 0 {
        } else {
            let modes = b[h];
            let prev_ll = match st.seqt {
                None => None,
                Some(t) => Some(t.ll),
            };
            let prev_of = match st.seqt {
                None => None,
                Some(t) => Some(t.of),
            };
            let prev_ml = match st.seqt {
                None => None,
                Some(t) => Some(t.ml),
            };
            let a0 = h + 1;
            match seq_table(b.subrange(a0, b.len() as int), 0, (modes / 64) as nat, prev_ll) {
                None => {},
                Some((ll, u0)) => {
                    let a1 = a0 + u0;
                    match seq_table(b.subrange(a1, b.len() as int), 1, ((modes / 16) % 4) as nat, prev_of) {
                        None => {},
                        Some((of, u1)) => {
                            let a2 = a1 + u1;
                            match seq_table(b.subrange(a2, b.len() as int), 2, ((modes / 4) % 4) as nat, prev_ml) {
                                None => {},
                                Some((ml, u2)) => {
                                    let a3 = a2 + u2;
                                    let s = b.subrange(a3, b.len() as int);
                                    let t = SeqTables { ll: ll, of: of, ml: ml };
                                    match bstart(s) {
                                        None => {},
                                        Some(q) => if ll.log + of.log + ml.log > q {
                                        } else {
                                            let sll = bits(s, q - ll.log, ll.log);
                                            let sof = bits(s, q - ll.log - of.log, of.log);
                                            let sml = bits(s, q - ll.log - of.log - ml.log, ml.log);
                                            let st0 = SeqState {
                                                p: q - ll.log - of.log - ml.log,
                                                sll: sll,
                                                sof: sof,
                                                sml: sml,
                                                reps: st.reps,
                                                li: 0,
                                                out: st.out,
                                            };
                                            lemma_seq_run_shift(t, s, lits, w, n, st0, p);
                                            match seq_run(t, s, lits, w, n, st0) {
                                                None => {},
                                                Some(fin) => {
                                                    assert((p + fin.out) + lits.subrange(fin.li, lits.len() as int) =~= p
                                                        + (fin.out + lits.subrange(fin.li, lits.len() as int)));
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

pub proof fn lemma_compressed_block_shift(b: Seq<u8>, w: nat, bmax: nat, st: FrameState, p: Seq<u8>)
    requires
        w <= st.out.len(),
    ensures
        compressed_block(b, w, bmax, shift(st, p)) == shift_opt(compressed_block(b, w, bmax, st), p),
{
    match lit_section(b, bmax, st.huf) {
        None => {},
        Some(l) => {
            let s2 = FrameState { huf: l.huf, ..st };
            assert(FrameState { huf: l.huf, ..shift(st, p) } == shift(s2, p));
            lemma_seq_section_shift(b.subrange(l.used, b.len() as int), l.lits, w, s2, p);
        },
    }
}

// ---------------------------------------------------------------------------
// One block at a time, and what a block depends on
// ---------------------------------------------------------------------------

/// One block of `blocks`: the position after it, the state, and whether it
/// is the last.
pub open spec fn block_step(b: Seq<u8>, i: int, window: nat, st: FrameState) -> Option<(int, FrameState, bool)> {
    if i < 0 || i + 3 > b.len() {
        None
    } else {
        let bh = le(b, i, 3);
        let last = bh % 2 == 1;
        let ty = (bh / 2) % 4;
        let size = bh / 8;
        let bmax = min(window as int, BLOCK_MAX as int) as nat;
        let c = i + 3;
        if size > bmax {
            None
        } else {
            let r: Option<(int, FrameState)> = if ty == 0 {
                if c + size > b.len() {
                    None
                } else {
                    Some((c + size, FrameState { out: st.out + b.subrange(c, c + size), ..st }))
                }
            } else if ty == 1 {
                if c + 1 > b.len() {
                    None
                } else {
                    Some((c + 1, FrameState { out: st.out + Seq::new(size, |k: int| b[c]), ..st }))
                }
            } else if ty == 2 {
                if c + size > b.len() {
                    None
                } else {
                    match compressed_block(b.subrange(c, c + size), window, bmax, st) {
                        None => None,
                        Some(st2) => Some((c + size, st2)),
                    }
                }
            } else {
                None
            };
            match r {
                None => None,
                Some((j, st2)) => Some((j, st2, last)),
            }
        }
    }
}

pub proof fn lemma_blocks_unfold(b: Seq<u8>, i: int, w: nat, st: FrameState)
    ensures
        blocks(b, i, w, st) == match block_step(b, i, w, st) {
            None => None,
            Some((j, st2, last)) => if last {
                Some((j, st2))
            } else {
                blocks(b, j, w, st2)
            },
        },
{
}

/// The bytes a block takes after its header, by its header alone.
pub open spec fn body_len(u: Seq<u8>) -> int {
    let bh = le(u, 0, 3);
    if (bh / 2) % 4 == 1 {
        1
    } else {
        (bh / 8) as int
    }
}

/// `le` reads only its `n` bytes.
pub proof fn lemma_le_local(x: Seq<u8>, i: int, y: Seq<u8>, k: int, n: nat)
    requires
        0 <= i,
        i + n <= x.len(),
        0 <= k,
        k + n <= y.len(),
        x.subrange(i, i + n) == y.subrange(k, k + n),
    ensures
        le(x, i, n) == le(y, k, n),
    decreases n,
{
    if n > 0 {
        assert(x[i] == x.subrange(i, i + n)[0]);
        assert(y[k] == y.subrange(k, k + n)[0]);
        assert(x.subrange(i + 1, i + n) =~= x.subrange(i, i + n).subrange(1, n as int));
        assert(y.subrange(k + 1, k + n) =~= y.subrange(k, k + n).subrange(1, n as int));
        lemma_le_local(x, i + 1, y, k + 1, (n - 1) as nat);
    }
}

/// A block decodes the same from a copy of just its bytes `u`.
pub proof fn lemma_block_step_local(b: Seq<u8>, i: int, u: Seq<u8>, w: nat, st: FrameState)
    requires
        0 <= i,
        3 <= u.len(),
        i + u.len() <= b.len(),
        b.subrange(i, i + u.len()) == u,
        3 + body_len(u) <= u.len(),
    ensures
        block_step(b, i, w, st) == match block_step(u, 0, w, st) {
            None => None,
            Some((j, s, l)) => Some((j + i, s, l)),
        },
{
    assert(b.subrange(i, i + 3) =~= u.subrange(0, 3));
    lemma_le_local(b, i, u, 0, 3);
    let bh = le(u, 0, 3);
    let size = bh / 8;
    let c = i + 3;
    if (bh / 2) % 4 == 1 {
        assert(b[c] == u[3]) by {
            assert(u[3] == b.subrange(i, i + u.len())[3]);
        }
        assert(Seq::new(size, |k: int| b[c]) =~= Seq::new(size, |k: int| u[3]));
    } else if 3 + size <= u.len() {
        assert(b.subrange(c, c + size) =~= u.subrange(3, 3 + size as int));
    }
}

/// A block decodes the same with more output in front of a window's worth.
pub proof fn lemma_block_step_shift(b: Seq<u8>, i: int, w: nat, st: FrameState, p: Seq<u8>)
    requires
        w <= st.out.len(),
    ensures
        block_step(b, i, w, shift(st, p)) == match block_step(b, i, w, st) {
            None => None,
            Some((j, s, l)) => Some((j, shift(s, p), l)),
        },
{
    if 0 <= i && i + 3 <= b.len() {
        let bh = le(b, i, 3);
        let size = bh / 8;
        let bmax = min(w as int, BLOCK_MAX as int) as nat;
        let c = i + 3;
        let ty = (bh / 2) % 4;
        if ty == 0 && c + size <= b.len() {
            assert((p + st.out) + b.subrange(c, c + size) =~= p + (st.out + b.subrange(c, c + size)));
        } else if ty == 1 && c + 1 <= b.len() {
            assert((p + st.out) + Seq::new(size, |k: int| b[c]) =~= p + (st.out + Seq::new(size, |k: int| b[c])));
        } else if ty == 2 && c + size <= b.len() {
            lemma_compressed_block_shift(b.subrange(c, c + size), w, bmax, st, p);
        }
    }
}

/// A frame header reads only its own bytes.
pub proof fn lemma_header_ext(x: Seq<u8>, y: Seq<u8>)
    requires
        frame_header(x) is Some,
        x.len() <= y.len(),
        y.subrange(0, x.len() as int) == x,
    ensures
        frame_header(y) == frame_header(x),
{
    assert forall|t: int| 0 <= t < x.len() implies y[t] == x[t] by {
        assert(x[t] == y.subrange(0, x.len() as int)[t]);
    }
    let fhd = x[0];
    let did_flag = fhd % 4;
    let single = (fhd / 32) % 2 == 1;
    let fcs_flag = fhd / 64;
    let wd_size: int = if single { 0 } else { 1 };
    let did_size: int = if did_flag == 0 { 0 } else if did_flag == 1 { 1 } else if did_flag == 2 { 2 } else { 4 };
    let fcs_size: int = if fcs_flag == 0 { if single { 1 } else { 0 } } else if fcs_flag == 1 { 2 } else if fcs_flag == 2 { 4 } else { 8 };
    let size = 1 + wd_size + did_size + fcs_size;
    assert(size <= x.len());
    assert(y.subrange(1 + wd_size, 1 + wd_size + did_size) =~= x.subrange(1 + wd_size, 1 + wd_size + did_size));
    lemma_le_local(y, 1 + wd_size, x, 1 + wd_size, did_size as nat);
    assert(y.subrange(1 + wd_size + did_size, size) =~= x.subrange(1 + wd_size + did_size, size));
    lemma_le_local(y, 1 + wd_size + did_size, x, 1 + wd_size + did_size, fcs_size as nat);
}

// ---------------------------------------------------------------------------
// Output only grows
// ---------------------------------------------------------------------------

pub open spec fn prefix(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() <= b.len() && b.subrange(0, a.len() as int) == a
}

pub proof fn lemma_prefix_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        prefix(a, b),
        prefix(b, c),
    ensures
        prefix(a, c),
{
    assert(c.subrange(0, a.len() as int) =~= c.subrange(0, b.len() as int).subrange(0, a.len() as int));
}

pub proof fn lemma_prefix_append(a: Seq<u8>, x: Seq<u8>)
    ensures
        prefix(a, a + x),
{
    assert((a + x).subrange(0, a.len() as int) =~= a);
}

pub proof fn lemma_seq_run_prefix(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, w: nat, n: nat, st: SeqState)
    ensures
        seq_run(t, s, lits, w, n, st) is Some ==> prefix(st.out, seq_run(t, s, lits, w, n, st).unwrap().out),
    decreases n,
{
    reveal(seq_run);
    if n == 0 {
        assert(st.out.subrange(0, st.out.len() as int) =~= st.out);
    } else if st.sll >= t.ll.rows.len() || st.sof >= t.of.rows.len() || st.sml >= t.ml.rows.len() {
    } else {
        let ell = t.ll.rows[st.sll as int];
        let eof = t.of.rows[st.sof as int];
        let eml = t.ml.rows[st.sml as int];
        let oc = eof.sym;
        let mlb = ml_bits(eml.sym);
        let llb = ll_bits(ell.sym);
        let p0 = st.p;
        if oc + mlb + llb > p0 {
        } else {
            let ov = pow2(oc) + bits(s, p0 - oc, oc);
            let p1 = p0 - oc;
            let ml = ml_base(eml.sym) + bits(s, p1 - mlb, mlb);
            let p2 = p1 - mlb;
            let ll = ll_base(ell.sym) + bits(s, p2 - llb, llb);
            let p3 = p2 - llb;
            match resolve_offset(ov, ll == 0, st.reps) {
                None => {},
                Some((off, reps)) => {
                    if st.li + ll > lits.len() {
                    } else {
                        let out1 = st.out + lits.subrange(st.li, st.li + ll);
                        if off > out1.len() || off > w || off == 0 {
                        } else {
                            let out2 = copy_match(out1, off, ml);
                            lemma_prefix_append(st.out, lits.subrange(st.li, st.li + ll));
                            lemma_copy_match_prefix(out1, off, ml);
                            lemma_copy_match_len(out1, off, ml);
                            lemma_prefix_trans(st.out, out1, out2);
                            let li = st.li + ll;
                            if n == 1 {
                            } else if ell.nb + eml.nb + eof.nb > p3 {
                            } else {
                                let sll = ell.base + bits(s, p3 - ell.nb, ell.nb);
                                let p4 = p3 - ell.nb;
                                let sml = eml.base + bits(s, p4 - eml.nb, eml.nb);
                                let p5 = p4 - eml.nb;
                                let sof = eof.base + bits(s, p5 - eof.nb, eof.nb);
                                let p6 = p5 - eof.nb;
                                let nx = SeqState { p: p6, sll: sll, sof: sof, sml: sml, reps: reps, li: li, out: out2 };
                                lemma_seq_run_prefix(t, s, lits, w, (n - 1) as nat, nx);
                                if seq_run(t, s, lits, w, n, st) is Some {
                                    lemma_prefix_trans(st.out, out2, seq_run(t, s, lits, w, n, st).unwrap().out);
                                }
                            }
                        }
                    }
                },
            }
        }
    }
}

#[verifier::rlimit(60)]
pub proof fn lemma_seq_section_prefix(b: Seq<u8>, lits: Seq<u8>, w: nat, st: FrameState)
    ensures
        seq_section(b, lits, w, st) is Some ==> prefix(st.out, seq_section(b, lits, w, st).unwrap().out),
{
    reveal(seq_section);
    match nb_seq(b) {
        None => {},
        Some((n, h)) => if n == 0 {
            lemma_prefix_append(st.out, lits);
        } else if h + 1 > b.len() || b[h] % 4 != 0 {
        } else {
            let modes = b[h];
            let prev_ll = match st.seqt {
                None => None,
                Some(t) => Some(t.ll),
            };
            let prev_of = match st.seqt {
                None => None,
                Some(t) => Some(t.of),
            };
            let prev_ml = match st.seqt {
                None => None,
                Some(t) => Some(t.ml),
            };
            let a0 = h + 1;
            match seq_table(b.subrange(a0, b.len() as int), 0, (modes / 64) as nat, prev_ll) {
                None => {},
                Some((ll, u0)) => {
                    let a1 = a0 + u0;
                    match seq_table(b.subrange(a1, b.len() as int), 1, ((modes / 16) % 4) as nat, prev_of) {
                        None => {},
                        Some((of, u1)) => {
                            let a2 = a1 + u1;
                            match seq_table(b.subrange(a2, b.len() as int), 2, ((modes / 4) % 4) as nat, prev_ml) {
                                None => {},
                                Some((ml, u2)) => {
                                    let a3 = a2 + u2;
                                    let s = b.subrange(a3, b.len() as int);
                                    let t = SeqTables { ll: ll, of: of, ml: ml };
                                    match bstart(s) {
                                        None => {},
                                        Some(q) => if ll.log + of.log + ml.log > q {
                                        } else {
                                            let sll = bits(s, q - ll.log, ll.log);
                                            let sof = bits(s, q - ll.log - of.log, of.log);
                                            let sml = bits(s, q - ll.log - of.log - ml.log, ml.log);
                                            let st0 = SeqState {
                                                p: q - ll.log - of.log - ml.log,
                                                sll: sll,
                                                sof: sof,
                                                sml: sml,
                                                reps: st.reps,
                                                li: 0,
                                                out: st.out,
                                            };
                                            lemma_seq_run_prefix(t, s, lits, w, n, st0);
                                            match seq_run(t, s, lits, w, n, st0) {
                                                None => {},
                                                Some(fin) => {
                                                    lemma_prefix_append(fin.out, lits.subrange(fin.li, lits.len() as int));
                                                    lemma_prefix_trans(
                                                        st.out,
                                                        fin.out,
                                                        fin.out + lits.subrange(fin.li, lits.len() as int),
                                                    );
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

/// A block only appends to the output.
pub proof fn lemma_block_step_prefix(b: Seq<u8>, i: int, w: nat, st: FrameState)
    ensures
        block_step(b, i, w, st) is Some ==> {
            &&& prefix(st.out, block_step(b, i, w, st).unwrap().1.out)
            &&& block_step(b, i, w, st).unwrap().0 >= i + 3
        },
{
    if 0 <= i && i + 3 <= b.len() {
        let bh = le(b, i, 3);
        let size = bh / 8;
        let bmax = min(w as int, BLOCK_MAX as int) as nat;
        let c = i + 3;
        let ty = (bh / 2) % 4;
        if ty == 0 && c + size <= b.len() {
            lemma_prefix_append(st.out, b.subrange(c, c + size));
        } else if ty == 1 && c + 1 <= b.len() {
            lemma_prefix_append(st.out, Seq::new(size, |k: int| b[c]));
        } else if ty == 2 && c + size <= b.len() {
            let cb = b.subrange(c, c + size);
            match lit_section(cb, bmax, st.huf) {
                None => {},
                Some(l) => {
                    lemma_seq_section_prefix(cb.subrange(l.used, cb.len() as int), l.lits, w, FrameState { huf: l.huf, ..st });
                },
            }
        }
    }
}

/// The blocks only append to the output.
pub proof fn lemma_blocks_prefix(b: Seq<u8>, i: int, w: nat, st: FrameState)
    ensures
        blocks(b, i, w, st) is Some ==> prefix(st.out, blocks(b, i, w, st).unwrap().1.out),
    decreases b.len() - i,
{
    lemma_blocks_unfold(b, i, w, st);
    lemma_block_step_prefix(b, i, w, st);
    match block_step(b, i, w, st) {
        None => {},
        Some((j, st2, last)) => {
            if !last {
                if j <= b.len() {
                    lemma_blocks_prefix(b, j, w, st2);
                    if blocks(b, j, w, st2) is Some {
                        lemma_prefix_trans(st.out, st2.out, blocks(b, j, w, st2).unwrap().1.out);
                    }
                } else {
                    assert(blocks(b, j, w, st2) is None);
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// What a stream must produce
// ---------------------------------------------------------------------------

/// `b` starts with `x`.
pub open spec fn ext(b: Seq<u8>, x: Seq<u8>) -> bool {
    x.len() <= b.len() && b.subrange(0, x.len() as int) == x
}

/// A whole skippable frame.
pub open spec fn skip_frame(x: Seq<u8>) -> bool {
    &&& x.len() >= 8
    &&& skippable(le(x, 0, 4))
    &&& le(x, 4, 4) + 8 < 0x1_0000_0000
    &&& x.len() == 8 + le(x, 4, 4)
}

/// `x` is one whole frame with content `o`, whatever input follows it: a
/// Zstandard frame (`spec::frame`) or a skippable frame.
pub open spec fn frame_ok(x: Seq<u8>, o: Seq<u8>) -> bool {
    ||| (x.len() >= 4 && le(x, 0, 4) == MAGIC && forall|b: Seq<u8>| ext(b, x) ==> #[trigger] frame(b, 0) == Some((x.len() as int, o)))
    ||| (skip_frame(x) && o.len() == 0)
}

pub proof fn lemma_ext_trans(b: Seq<u8>, x: Seq<u8>, y: Seq<u8>)
    requires
        ext(b, x),
        ext(x, y),
    ensures
        ext(b, y),
{
    assert(b.subrange(0, y.len() as int) =~= b.subrange(0, x.len() as int).subrange(0, y.len() as int));
}

pub proof fn lemma_ext_prefix(x: Seq<u8>, k: int)
    requires
        0 <= k <= x.len(),
    ensures
        ext(x, x.subrange(0, k)),
{
}

// ---------------------------------------------------------------------------
// The streaming decoder
// ---------------------------------------------------------------------------

pub const SBLOCK_MAX: usize = 131072;

/// Most output a frame may have when streamed.
pub const SLIMIT: u64 = 0x1_0000_0000_0000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stage {
    /// Collecting a frame's first 5 bytes (or a skippable frame's 8).
    Magic,
    /// Collecting the rest of the frame header.
    Header,
    BlockHeader,
    /// Collecting a block's body.
    Block,
    Checksum,
    /// Skipping a skippable frame's content.
    Skip,
    /// The frame is decoded; its output is still being handed out.
    Done,
    /// A previous call failed; only a reset helps.
    Failed,
}

/// Why a stream failed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fail {
    /// Not a frame's magic number.
    Prefix,
    /// A skippable frame too large.
    Param,
    /// A frame header the spec rejects (reserved bit, window log over 31).
    Header,
    /// A frame that names a dictionary.
    Dict,
    /// A window larger than the caller allows.
    Window,
    /// A block, content size or checksum the spec rejects.
    Corrupt,
    Checksum,
    /// More output than `SLIMIT`.
    Limit,
}

pub struct Stream {
    pub stage: Stage,
    /// The bytes of the unit being collected (magic, header, block, checksum).
    pub unit: Vec<u8>,
    /// Its full size.
    pub need: usize,
    /// Bytes left to skip in a skippable frame.
    pub skip: usize,
    pub window: u64,
    pub fcs: Option<u64>,
    pub checksum: bool,
    pub dec: FrameDec,
    /// Output decoded so far in this frame, before `dec.out` (dropped).
    pub dropped: u64,
    /// The first byte of `dec.out` not yet handed out.
    pub flushed: usize,
    pub hash: Xxh64,
    /// Largest window accepted (libzstd's `maxWindowSize`).
    pub max_window: u64,
    pub fail: Fail,
    /// The input of this frame so far.
    pub gin: Ghost<Seq<u8>>,
    /// The output handed out for this frame so far.
    pub gemit: Ghost<Seq<u8>>,
    /// The spec's state after the blocks decoded so far.
    pub gst: Ghost<FrameState>,
    pub ghdr: Ghost<Header>,
    /// Where in `gin` the next block starts.
    pub gbpos: Ghost<int>,
}

pub open spec fn rank(s: Stage) -> int {
    match s {
        Stage::Magic => 6,
        Stage::Header => 5,
        Stage::Skip => 4,
        Stage::Block => 3,
        Stage::BlockHeader => 2,
        Stage::Checksum => 1,
        Stage::Done => 0,
        Stage::Failed => 0,
    }
}

impl Stream {
    /// The decoder state matches the spec's state `gst`, with the first
    /// `dropped` bytes of its output dropped and the first `dropped +
    /// flushed` handed out.
    pub open spec fn dec_inv(&self) -> bool {
        let gst = self.gst@;
        &&& self.dec.fstart == 0
        &&& self.dropped as int <= gst.out.len()
        &&& self.dec.out@ == gst.out.subrange(self.dropped as int, gst.out.len() as int)
        &&& dec_is(&self.dec, FrameState { out: self.dec.out@, ..gst })
        &&& (self.dropped == 0 || self.window as int <= self.dec.out@.len())
        &&& self.flushed <= self.dec.out@.len()
        &&& self.gemit@ == gst.out.subrange(0, self.dropped + self.flushed)
        &&& self.hash.is(gst.out)
        &&& gst.out.len() <= SLIMIT
    }

    /// Memory: the output kept is at most two windows and three blocks.
    pub open spec fn mem_ok(&self) -> bool {
        self.dec.out@.len() <= 2 * self.window + 3 * SBLOCK_MAX + 2
    }

    pub open spec fn hdr_inv(&self) -> bool {
        let g = self.gin@;
        let h = self.ghdr@;
        &&& 1 <= h.size <= 14
        &&& g.len() >= 4 + h.size
        &&& le(g, 0, 4) == MAGIC
        &&& frame_header(g.subrange(4, 4 + h.size)) == Some(h)
        &&& h.dict_id == 0
        &&& self.window as nat == h.window
        &&& self.window <= 0x100_0000_0000
        &&& match self.fcs {
            None => h.fcs is None,
            Some(f) => h.fcs == Some(f as nat),
        }
        &&& self.checksum == h.checksum
    }

    /// The blocks so far are the start of the frame's blocks.
    pub open spec fn blocks_inv(&self) -> bool {
        let g = self.gin@;
        let h = self.ghdr@;
        &&& 4 + h.size <= self.gbpos@ <= g.len()
        &&& forall|b: Seq<u8>|
            ext(b, g.subrange(0, self.gbpos@)) ==> #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == blocks(
                b,
                self.gbpos@,
                h.window,
                self.gst@,
            )
    }

    /// The frame's blocks ended at `gbpos`.
    pub open spec fn last_inv(&self) -> bool {
        let g = self.gin@;
        let h = self.ghdr@;
        &&& 4 + h.size <= self.gbpos@ <= g.len()
        &&& forall|b: Seq<u8>|
            ext(b, g.subrange(0, self.gbpos@)) ==> #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == Some(
                (self.gbpos@, self.gst@),
            )
        &&& match h.fcs {
            None => true,
            Some(f) => f == self.gst@.out.len(),
        }
    }

    /// `unit` is what `gin` holds after `gbpos`.
    pub open spec fn unit_inv(&self) -> bool {
        &&& self.gbpos@ + self.unit@.len() == self.gin@.len()
        &&& self.gin@.subrange(self.gbpos@, self.gin@.len() as int) == self.unit@
        &&& self.unit@.len() <= self.need
    }

    pub open spec fn fresh(&self) -> bool {
        &&& self.gin@ == self.unit@
        &&& self.gemit@.len() == 0
        &&& self.unit@.len() <= self.need <= 8
    }

    pub open spec fn inv(&self) -> bool {
        match self.stage {
            Stage::Failed => true,
            Stage::Magic => {
                &&& self.fresh()
                &&& self.unit@.len() >= 5 ==> skippable(le(self.unit@, 0, 4))
            },
            Stage::Header => {
                &&& self.gin@ == self.unit@
                &&& self.gemit@.len() == 0
                &&& 5 <= self.unit@.len() <= self.need <= 18
                &&& le(self.gin@, 0, 4) == MAGIC
            },
            Stage::Skip => {
                let g = self.gin@;
                &&& g.len() >= 8
                &&& skippable(le(g, 0, 4))
                &&& le(g, 4, 4) + 8 < 0x1_0000_0000
                &&& g.len() + self.skip == 8 + le(g, 4, 4)
                &&& self.gemit@.len() == 0
            },
            Stage::BlockHeader => {
                &&& self.hdr_inv()
                &&& self.mem_ok()
                &&& self.dec_inv()
                &&& self.blocks_inv()
                &&& self.unit_inv()
                &&& self.need == 3
                &&& self.unit@.len() < 3
            },
            Stage::Block => {
                &&& self.hdr_inv()
                &&& self.mem_ok()
                &&& self.dec_inv()
                &&& self.blocks_inv()
                &&& self.unit_inv()
                &&& self.unit@.len() >= 3
                &&& self.need == 3 + body_len(self.unit@)
                &&& self.need <= 3 + SBLOCK_MAX
            },
            Stage::Checksum => {
                &&& self.hdr_inv()
                &&& self.mem_ok()
                &&& self.dec_inv()
                &&& self.last_inv()
                &&& self.unit_inv()
                &&& self.checksum
                &&& self.need == 4
                &&& self.unit@.len() < 4
            },
            Stage::Done => {
                &&& self.dec_inv()
                &&& self.mem_ok()
                &&& self.gin@.len() >= 4
                &&& le(self.gin@, 0, 4) == MAGIC
                &&& forall|b: Seq<u8>| ext(b, self.gin@) ==> #[trigger] frame(b, 0) == Some((self.gin@.len() as int, self.gst@.out))
            },
        }
    }

    pub fn new(max_window: u64) -> (r: Stream)
        ensures
            r.inv(),
            r.stage == Stage::Magic,
            r.gin@.len() == 0,
    {
        Stream {
            stage: Stage::Magic,
            unit: Vec::new(),
            need: 5,
            skip: 0,
            window: 1,
            fcs: None,
            checksum: false,
            dec: FrameDec { out: Vec::new(), fstart: 0, r1: 1, r2: 4, r3: 8, huf: None, seqt: None, lits: Vec::new() },
            dropped: 0,
            flushed: 0,
            hash: Xxh64::new(),
            max_window,
            fail: Fail::Corrupt,
            gin: Ghost(Seq::empty()),
            gemit: Ghost(Seq::empty()),
            gst: Ghost(initial_state()),
            ghdr: Ghost(Header { window: 1, fcs: None, checksum: false, dict_id: 0, size: 1 }),
            gbpos: Ghost(0),
        }
    }

    /// Starts over at a frame's first byte.
    pub fn reset(&mut self)
        ensures
            final(self).inv(),
            final(self).stage == Stage::Magic,
            final(self).gin@.len() == 0,
            final(self).max_window == old(self).max_window,
    {
        self.stage = Stage::Magic;
        self.unit.clear();
        self.need = 5;
        self.dec.out.clear();
        self.dec.fstart = 0;
        self.flushed = 0;
        self.dropped = 0;
        self.gin = Ghost(Seq::empty());
        self.gemit = Ghost(Seq::empty());
    }

    fn failed(&mut self, f: Fail) -> (r: Result<usize, Fail>)
        ensures
            final(self).inv(),
            final(self).stage == Stage::Failed,
            r == Err::<usize, Fail>(f),
            final(self).max_window == old(self).max_window,
    {
        self.stage = Stage::Failed;
        self.fail = f;
        Err(f)
    }
}

/// Takes input into `unit` until it holds `need` bytes; true when it does.
fn collect(unit: &mut Vec<u8>, need: usize, inp: &[u8], ipos: &mut usize) -> (r: bool)
    requires
        old(unit)@.len() <= need,
        *old(ipos) <= inp@.len(),
    ensures
        *old(ipos) <= *final(ipos) <= inp@.len(),
        final(unit)@ == old(unit)@ + inp@.subrange(*old(ipos) as int, *final(ipos) as int),
        final(unit)@.len() <= need,
        r == (final(unit)@.len() == need),
        !r ==> *final(ipos) == inp@.len(),
{
    let a = need - unit.len();
    let b = inp.len() - *ipos;
    let n = if a < b { a } else { b };
    crate::prims::extend_from(unit, inp, *ipos, n);
    *ipos = *ipos + n;
    unit.len() == need
}

/// The size of a frame header (`frame_header`'s `size`) from its first byte.
fn header_size(fhd: u8) -> (r: usize)
    ensures
        forall|x: Seq<u8>| x.len() >= 1 && x[0] == fhd && #[trigger] frame_header(x) is Some ==> frame_header(x).unwrap().size == r as int,
        1 <= r <= 14,
{
    let did_flag = fhd % 4;
    let single = (fhd / 32) % 2 == 1;
    let fcs_flag = fhd / 64;
    let wd: usize = if single { 0 } else { 1 };
    let did: usize = if did_flag == 0 { 0 } else if did_flag == 1 { 1 } else if did_flag == 2 { 2 } else { 4 };
    let fcs: usize = if fcs_flag == 0 {
        if single { 1 } else { 0 }
    } else if fcs_flag == 1 {
        2
    } else if fcs_flag == 2 {
        4
    } else {
        8
    };
    1 + wd + did + fcs
}

/// Hands out `src[from..]` into `out[opos..]`, as much as fits; true when
/// all of it is out.
fn give(src: &[u8], from: &mut usize, out: &mut [u8], opos: &mut usize) -> (r: bool)
    requires
        *old(from) <= src@.len(),
        *old(opos) <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        *old(opos) <= *final(opos) <= final(out)@.len(),
        *old(from) <= *final(from) <= src@.len(),
        *final(from) - *old(from) == *final(opos) - *old(opos),
        final(out)@.subrange(0, *old(opos) as int) == old(out)@.subrange(0, *old(opos) as int),
        final(out)@.subrange(*old(opos) as int, *final(opos) as int) == src@.subrange(*old(from) as int, *final(from) as int),
        r == (*final(from) == src@.len()),
{
    let a = src.len() - *from;
    let b = out.len() - *opos;
    let n = if a < b { a } else { b };
    let ghost o0 = out@;
    copy_into(out, *opos, src, *from, n);
    proof {
        assert(out@.subrange(0, *opos as int) =~= o0.subrange(0, *opos as int));
        assert(out@.subrange(*opos as int, *opos + n) =~= src@.subrange(*from as int, *from + n));
    }
    *opos = *opos + n;
    *from = *from + n;
    *from == src.len()
}

/// `gave` grows by what one more `give` wrote.
proof fn lemma_gave(o0: Seq<u8>, o1: Seq<u8>, o2: Seq<u8>, a: int, b: int, c: int)
    requires
        0 <= a <= b <= c <= o2.len(),
        o1.len() == o2.len(),
        o2.subrange(0, b) == o1.subrange(0, b),
    ensures
        o2.subrange(a, c) == o1.subrange(a, b) + o2.subrange(b, c),
        o2.subrange(0, a) == o1.subrange(0, a),
{
    assert(o2.subrange(a, c) =~= o2.subrange(0, b).subrange(a, b) + o2.subrange(b, c));
    assert(o1.subrange(a, b) =~= o1.subrange(0, b).subrange(a, b));
    assert(o2.subrange(0, a) =~= o2.subrange(0, b).subrange(0, a));
    assert(o1.subrange(0, a) =~= o1.subrange(0, b).subrange(0, a));
}

impl Stream {
    /// Hands out decoded output; true when all of it is out.
    fn flush(&mut self, out: &mut [u8], opos: &mut usize) -> (r: bool)
        requires
            old(self).dec_inv(),
            *old(opos) <= old(out)@.len(),
        ensures
            final(self).dec_inv(),
            final(self).stage == old(self).stage,
            final(self).unit == old(self).unit,
            final(self).need == old(self).need,
            final(self).skip == old(self).skip,
            final(self).window == old(self).window,
            final(self).fcs == old(self).fcs,
            final(self).checksum == old(self).checksum,
            final(self).dropped == old(self).dropped,
            final(self).dec.out@ == old(self).dec.out@,
            final(self).max_window == old(self).max_window,
            final(self).gin == old(self).gin,
            final(self).gst == old(self).gst,
            final(self).ghdr == old(self).ghdr,
            final(self).gbpos == old(self).gbpos,
            final(out)@.len() == old(out)@.len(),
            *old(opos) <= *final(opos) <= final(out)@.len(),
            final(out)@.subrange(0, *old(opos) as int) == old(out)@.subrange(0, *old(opos) as int),
            final(self).gemit@ == old(self).gemit@ + final(out)@.subrange(*old(opos) as int, *final(opos) as int),
            r == (final(self).flushed == final(self).dec.out@.len()),
    {
        let ghost f0 = self.flushed;
        let mut f = self.flushed;
        let r = give(self.dec.out.as_slice(), &mut f, out, opos);
        self.flushed = f;
        proof {
            let g = self.gst@.out;
            let d = self.dropped as int;
            assert(self.gemit@ + self.dec.out@.subrange(f0 as int, f as int) =~= g.subrange(0, d + f));
        }
        self.gemit = Ghost(self.gemit@ + self.dec.out@.subrange(f0 as int, f as int));
        r
    }

    /// Drops output older than the window once it is all handed out and
    /// the buffer has grown well past the window.
    fn trim(&mut self)
        requires
            old(self).dec_inv(),
            old(self).window <= 0x100_0000_0000,
        ensures
            final(self).dec_inv(),
            final(self).stage == old(self).stage,
            final(self).unit == old(self).unit,
            final(self).need == old(self).need,
            final(self).skip == old(self).skip,
            final(self).window == old(self).window,
            final(self).fcs == old(self).fcs,
            final(self).checksum == old(self).checksum,
            final(self).max_window == old(self).max_window,
            final(self).gin == old(self).gin,
            final(self).gemit == old(self).gemit,
            final(self).gst == old(self).gst,
            final(self).ghdr == old(self).ghdr,
            final(self).gbpos == old(self).gbpos,
            final(self).dropped + final(self).dec.out@.len() == old(self).dropped + old(self).dec.out@.len(),
            final(self).dec.out@.len() <= old(self).dec.out@.len(),
            old(self).flushed == old(self).dec.out@.len() ==> final(self).dec.out@.len() <= 2 * old(self).window + SBLOCK_MAX + 2,
    {
        let keep: usize = if self.window > 1 { self.window as usize } else { 1 };
        let len = self.dec.out.len();
        if len > 2 * keep + SBLOCK_MAX && self.flushed >= len - keep {
            let cut = len - keep;
            let ghost o0 = self.dec.out@;
            // In place: the buffer keeps its capacity, so it is not grown
            // again from the window size.
            crate::prims::drop_front(&mut self.dec.out, cut);
            self.flushed = self.flushed - cut;
            self.dropped = self.dropped + cut as u64;
            proof {
                let g = self.gst@.out;
                assert(self.dec.out@ =~= g.subrange(self.dropped as int, g.len() as int));
                assert(fout(self.dec.out@, 0) =~= self.dec.out@);
            }
        }
    }
}

/// The frame ends at the end of `g`, whatever follows it.
proof fn lemma_frame_done(g: Seq<u8>, h: Header, j: int, st: FrameState)
    requires
        1 <= h.size,
        4 + h.size <= j <= g.len(),
        frame_header(g.subrange(4, 4 + h.size)) == Some(h),
        h.dict_id == 0,
        forall|b: Seq<u8>|
            ext(b, g.subrange(0, j)) ==> #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == Some((j, st)),
        match h.fcs {
            None => true,
            Some(f) => f == st.out.len(),
        },
        if h.checksum {
            g.len() == j + 4 && le(g, j, 4) == xxh64(st.out) as nat % 0x1_0000_0000
        } else {
            g.len() == j
        },
    ensures
        forall|b: Seq<u8>| ext(b, g) ==> #[trigger] frame(b, 0) == Some((g.len() as int, st.out)),
{
    assert forall|b: Seq<u8>| ext(b, g) implies #[trigger] frame(b, 0) == Some((g.len() as int, st.out)) by {
        lemma_ext_trans(b, g, g.subrange(0, j));
        let x = g.subrange(4, 4 + h.size);
        let y = b.subrange(4, b.len() as int);
        assert(y.subrange(0, x.len() as int) =~= x) by {
            assert(b.subrange(0, g.len() as int) == g);
            assert forall|t: int| 0 <= t < x.len() implies #[trigger] y.subrange(0, x.len() as int)[t] == x[t] by {
                assert(b.subrange(0, g.len() as int)[4 + t] == g[4 + t]);
            }
        }
        lemma_header_ext(x, y);
        assert(blocks(b, 4 + h.size, h.window, initial_state()) == Some((j, st)));
        if h.checksum {
            assert(b.subrange(j, j + 4) =~= g.subrange(j, j + 4)) by {
                assert forall|t: int| 0 <= t < 4 implies #[trigger] b.subrange(j, j + 4)[t] == g.subrange(j, j + 4)[t] by {
                    assert(b.subrange(0, g.len() as int)[j + t] == g[j + t]);
                }
            }
            lemma_le_local(b, j, g, j, 4);
        }
    }
}

pub open spec fn step_post(
    s0: Stream,
    s1: Stream,
    inp: Seq<u8>,
    i0: int,
    i1: int,
    o0: Seq<u8>,
    o1: Seq<u8>,
    p0: int,
    p1: int,
    r: Option<Result<usize, Fail>>,
) -> bool {
    let took = inp.subrange(i0, i1);
    let gave = o1.subrange(p0, p1);
    &&& i0 <= i1 <= inp.len()
    &&& p0 <= p1 <= o1.len()
    &&& o1.len() == o0.len()
    &&& o1.subrange(0, p0) == o0.subrange(0, p0)
    &&& s1.max_window == s0.max_window
    &&& match r {
        None => {
            &&& s1.inv()
            &&& s1.stage != Stage::Failed
            &&& s1.gin@ == s0.gin@ + took
            &&& s1.gemit@ == s0.gemit@ + gave
            &&& 16 * (inp.len() - i1) + rank(s1.stage) < 16 * (inp.len() - i0) + rank(s0.stage)
        },
        Some(Ok(n)) => if n == 0 {
            &&& frame_ok(s0.gin@ + took, s0.gemit@ + gave)
            &&& s1.inv()
            &&& s1.stage == Stage::Magic
            &&& s1.gin@.len() == 0
        } else {
            &&& s1.inv()
            &&& s1.stage != Stage::Failed
            &&& s1.gin@ == s0.gin@ + took
            &&& s1.gemit@ == s0.gemit@ + gave
        },
        Some(Err(_)) => s1.stage == Stage::Failed,
    }
}

impl Stream {
    fn step_done(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Done,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        if !self.flush(out, opos) {
            proof {
                assert(inp@.subrange(i0 as int, i0 as int) =~= Seq::<u8>::empty());
                assert(self.gin@ =~= s0.gin@ + Seq::<u8>::empty());
            }
            return Some(Ok(1));
        }
        proof {
            let g = self.gst@.out;
            assert(self.gemit@ =~= g);
            assert(inp@.subrange(i0 as int, i0 as int) =~= Seq::<u8>::empty());
            assert(s0.gin@ + inp@.subrange(i0 as int, i0 as int) =~= s0.gin@);
            assert(frame_ok(s0.gin@, g));
        }
        self.reset();
        Some(Ok(0))
    }

    fn step_skip(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Skip,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        let avail = inp.len() - *ipos;
        let n = if self.skip < avail { self.skip } else { avail };
        *ipos = *ipos + n;
        self.skip = self.skip - n;
        self.gin = Ghost(self.gin@ + inp@.subrange(i0 as int, *ipos as int));
        proof {
            let g0 = s0.gin@;
            let g = self.gin@;
            assert(g.subrange(0, 8) =~= g0.subrange(0, 8));
            assert(g.subrange(0, 4) =~= g0.subrange(0, 4));
            assert(g.subrange(4, 8) =~= g0.subrange(4, 8));
            lemma_le_local(g, 0, g0, 0, 4);
            lemma_le_local(g, 4, g0, 4, 4);
            assert(out@.subrange(*opos as int, *opos as int) =~= Seq::<u8>::empty());
            assert(self.gemit@ =~= s0.gemit@ + Seq::<u8>::empty());
        }
        if self.skip > 0 {
            return Some(Ok(self.skip));
        }
        proof {
            assert(skip_frame(self.gin@));
            assert(self.gemit@.len() == 0);
        }
        self.reset();
        Some(Ok(0))
    }

    fn step_checksum(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Checksum,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        let done = collect(&mut self.unit, self.need, inp, ipos);
        self.gin = Ghost(self.gin@ + inp@.subrange(i0 as int, *ipos as int));
        proof {
            let g = self.gin@;
            let j = self.gbpos@;
            assert(g.subrange(j, g.len() as int) =~= self.unit@);
            assert(g.subrange(0, j) =~= s0.gin@.subrange(0, j));
            assert(g.subrange(4, 4 + self.ghdr@.size) =~= s0.gin@.subrange(4, 4 + self.ghdr@.size));
            assert(g.subrange(0, 4) =~= s0.gin@.subrange(0, 4));
            lemma_le_local(g, 0, s0.gin@, 0, 4);
            assert(out@.subrange(*opos as int, *opos as int) =~= Seq::<u8>::empty());
            assert(self.gemit@ =~= s0.gemit@ + Seq::<u8>::empty());
        }
        if !done {
            return Some(Ok(self.need - self.unit.len()));
        }
        let want = le_at(self.unit.as_slice(), 0, 4);
        let d = self.hash.digest(Ghost(self.gst@.out));
        let lo = d & 0xFFFF_FFFF;
        proof {
            assert(d & 0xFFFF_FFFF == d % 0x1_0000_0000) by (bit_vector);
        }
        if lo != want {
            return Some(self.failed(Fail::Checksum));
        }
        proof {
            let g = self.gin@;
            let j = self.gbpos@;
            assert(g.subrange(j, j + 4) =~= self.unit@.subrange(0, 4));
            lemma_le_local(g, j, self.unit@, 0, 4);
            lemma_frame_done(g, self.ghdr@, j, self.gst@);
        }
        self.stage = Stage::Done;
        None
    }
}

impl Stream {
    fn step_magic(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Magic,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        proof {
            assert(out@.subrange(*opos as int, *opos as int) =~= Seq::<u8>::empty());
            assert(self.gemit@ =~= s0.gemit@ + Seq::<u8>::empty());
        }
        // A skippable frame needs only 8 bytes, but its magic decides.
        if self.unit.len() < 4 {
            self.need = 4;
            let i1 = *ipos;
            let done = collect(&mut self.unit, 4, inp, ipos);
            self.gin = Ghost(self.gin@ + inp@.subrange(i1 as int, *ipos as int));
            if !done {
                proof {
                    assert(inp@.subrange(i0 as int, *ipos as int) =~= inp@.subrange(i1 as int, *ipos as int));
                }
                return Some(Ok(5 - self.unit.len()));
            }
        }
        proof {
            assert(self.gin@ =~= s0.gin@ + inp@.subrange(i0 as int, *ipos as int));
        }
        let m = le_at(self.unit.as_slice(), 0, 4);
        let ghost um = self.unit@;
        if m / 16 == 0x184D2A5 {
            self.need = 8;
            let i1 = *ipos;
            let done = collect(&mut self.unit, 8, inp, ipos);
            self.gin = Ghost(self.gin@ + inp@.subrange(i1 as int, *ipos as int));
            proof {
                assert(self.gin@ =~= s0.gin@ + inp@.subrange(i0 as int, *ipos as int));
                assert(self.unit@.subrange(0, 4) =~= um.subrange(0, 4));
                lemma_le_local(self.unit@, 0, um, 0, 4);
            }
            if !done {
                return Some(Ok(8 - self.unit.len()));
            }
            let n = le_at(self.unit.as_slice(), 4, 4);
            if n > 0xFFFF_FFFF - 8 {
                return Some(self.failed(Fail::Param));
            }
            self.skip = n as usize;
            self.stage = Stage::Skip;
            return None;
        }
        if m != 0xFD2F_B528 {
            return Some(self.failed(Fail::Prefix));
        }
        self.need = 5;
        let i1 = *ipos;
        let done = collect(&mut self.unit, 5, inp, ipos);
        self.gin = Ghost(self.gin@ + inp@.subrange(i1 as int, *ipos as int));
        proof {
            assert(self.gin@ =~= s0.gin@ + inp@.subrange(i0 as int, *ipos as int));
            assert(self.unit@.subrange(0, 4) =~= um.subrange(0, 4));
            lemma_le_local(self.unit@, 0, um, 0, 4);
        }
        if !done {
            return Some(Ok(1));
        }
        let fhd = self.unit[4];
        if fhd & 0x08 != 0 {
            return Some(self.failed(Fail::Param));
        }
        self.need = 4 + header_size(fhd);
        self.stage = Stage::Header;
        None
    }

    fn step_header(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Header,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        proof {
            assert(out@.subrange(*opos as int, *opos as int) =~= Seq::<u8>::empty());
            assert(self.gemit@ =~= s0.gemit@ + Seq::<u8>::empty());
        }
        let done = collect(&mut self.unit, self.need, inp, ipos);
        self.gin = Ghost(self.gin@ + inp@.subrange(i0 as int, *ipos as int));
        proof {
            assert(self.gin@.subrange(0, 4) =~= s0.gin@.subrange(0, 4));
            lemma_le_local(self.gin@, 0, s0.gin@, 0, 4);
        }
        if !done {
            return Some(Ok(self.need - self.unit.len()));
        }
        let x = slice_subrange(self.unit.as_slice(), 4, self.unit.len());
        let h = match frame_header_exec(x) {
            None => {
                return Some(self.failed(Fail::Header));
            },
            Some(h) => h,
        };
        let ghost hs = frame_header(x@).unwrap();
        if h.size != self.need - 4 {
            return Some(self.failed(Fail::Header));
        }
        if h.dict_id != 0 {
            return Some(self.failed(Fail::Dict));
        }
        if h.window > self.max_window || h.window > 0x100_0000_0000 {
            return Some(self.failed(Fail::Window));
        }
        self.window = h.window;
        self.fcs = h.fcs;
        self.checksum = h.checksum;
        self.dec.out.clear();
        reset(&mut self.dec);
        self.flushed = 0;
        self.dropped = 0;
        self.hash = Xxh64::new();
        self.gst = Ghost(initial_state());
        self.ghdr = Ghost(hs);
        self.gbpos = Ghost(self.gin@.len() as int);
        self.unit.clear();
        self.need = 3;
        self.stage = Stage::BlockHeader;
        proof {
            let g = self.gin@;
            assert(g.subrange(4, 4 + hs.size) =~= x@);
            assert(g.subrange(self.gbpos@, g.len() as int) =~= self.unit@);
            assert(self.gemit@ =~= self.gst@.out.subrange(0, 0));
            assert(self.dec.out@ =~= self.gst@.out.subrange(0, 0));
            assert(self.blocks_inv());
        }
        None
    }

    fn step_block_header(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::BlockHeader,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        proof {
            assert(out@.subrange(*opos as int, *opos as int) =~= Seq::<u8>::empty());
            assert(self.gemit@ =~= s0.gemit@ + Seq::<u8>::empty());
        }
        let done = collect(&mut self.unit, self.need, inp, ipos);
        self.gin = Ghost(self.gin@ + inp@.subrange(i0 as int, *ipos as int));
        proof {
            let g = self.gin@;
            let j = self.gbpos@;
            let k = 4 + self.ghdr@.size;
            assert(g.subrange(j, g.len() as int) =~= self.unit@);
            assert(g.subrange(0, j) =~= s0.gin@.subrange(0, j));
            assert(g.subrange(4, k) =~= s0.gin@.subrange(4, k));
            assert(g.subrange(0, 4) =~= s0.gin@.subrange(0, 4));
            lemma_le_local(g, 0, s0.gin@, 0, 4);
        }
        if !done {
            return Some(Ok(self.need - self.unit.len()));
        }
        let bh = le_at(self.unit.as_slice(), 0, 3);
        let ty = (bh / 2) % 4;
        let size = (bh / 8) as usize;
        let bmax: usize = if self.window < SBLOCK_MAX as u64 { self.window as usize } else { SBLOCK_MAX };
        if ty == 3 || size > bmax {
            return Some(self.failed(Fail::Corrupt));
        }
        self.need = 3 + if ty == 1 { 1 } else { size };
        self.stage = Stage::Block;
        None
    }
}

/// The block `src` at `gbpos` of `g`: what the frame's blocks are after it.
proof fn lemma_next_block(g0: Seq<u8>, j: int, src: Seq<u8>, h: Header, st: FrameState, j2: int, st2: FrameState, last: bool)
    requires
        1 <= h.size,
        4 + h.size <= j <= g0.len(),
        3 <= src.len(),
        3 + body_len(src) <= src.len(),
        forall|b: Seq<u8>|
            ext(b, g0.subrange(0, j)) ==> #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == blocks(b, j, h.window, st),
        block_step(src, 0, h.window, st) == Some((j2, st2, last)),
    ensures
        ({
            let g1 = g0.subrange(0, j) + src;
            forall|b: Seq<u8>|
                ext(b, g1) ==> #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == if last {
                    Some((j + j2, st2))
                } else {
                    blocks(b, j + j2, h.window, st2)
                }
        }),
{
    let g1 = g0.subrange(0, j) + src;
    assert forall|b: Seq<u8>| ext(b, g1) implies #[trigger] blocks(b, 4 + h.size, h.window, initial_state()) == if last {
        Some((j + j2, st2))
    } else {
        blocks(b, j + j2, h.window, st2)
    } by {
        assert(g1.subrange(0, j) =~= g0.subrange(0, j)) by {
            assert forall|t: int| 0 <= t < j implies #[trigger] g1.subrange(0, j)[t] == g0.subrange(0, j)[t] by {
                assert(g1[t] == g0.subrange(0, j)[t]);
            }
        }
        lemma_ext_trans(b, g1, g0.subrange(0, j));
        assert(b.subrange(j, j + src.len()) =~= src) by {
            assert forall|t: int| 0 <= t < src.len() implies #[trigger] b.subrange(j, j + src.len())[t] == src[t] by {
                assert(b.subrange(0, g1.len() as int)[j + t] == g1[j + t]);
            }
        }
        lemma_block_step_local(b, j, src, h.window, st);
        lemma_blocks_unfold(b, j, h.window, st);
    }
}

impl Stream {
    #[verifier::rlimit(400)]
    fn step_block(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Option<Result<usize, Fail>>)
        requires
            old(self).inv(),
            old(self).stage == Stage::Block,
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            step_post(*old(self), *final(self), inp@, *old(ipos) as int, *final(ipos) as int, old(out)@, final(out)@, *old(opos) as int, *final(opos) as int, r),
    {
        let ghost s0 = *self;
        let ghost i0 = *ipos;
        let ghost o0 = out@;
        // Hand out what is there before decoding more.
        if !self.flush(out, opos) {
            proof {
                assert(inp@.subrange(i0 as int, i0 as int) =~= Seq::<u8>::empty());
                assert(self.gin@ =~= s0.gin@ + Seq::<u8>::empty());
            }
            return Some(Ok(1));
        }
        proof {
            assert(inp@.subrange(i0 as int, i0 as int) =~= Seq::<u8>::empty());
            assert(self.gin@ =~= s0.gin@ + Seq::<u8>::empty());
        }
        let ghost s1 = *self;
        // When the header came from this input and the whole block follows
        // it, decode it in place, without copying.
        let direct = self.unit.len() == 3 && *ipos >= 3 && inp.len() - *ipos >= self.need - 3 && inp[*ipos - 3]
            == self.unit[0] && inp[*ipos - 2] == self.unit[1] && inp[*ipos - 1] == self.unit[2];
        if !direct {
            let done = collect(&mut self.unit, self.need, inp, ipos);
            self.gin = Ghost(self.gin@ + inp@.subrange(i0 as int, *ipos as int));
            proof {
                let g = self.gin@;
                let j = self.gbpos@;
                let k = 4 + self.ghdr@.size;
                assert(g.subrange(j, g.len() as int) =~= self.unit@);
                assert(g.subrange(0, j) =~= s0.gin@.subrange(0, j));
                assert(g.subrange(4, k) =~= s0.gin@.subrange(4, k));
                assert(g.subrange(0, 4) =~= s0.gin@.subrange(0, 4));
                lemma_le_local(g, 0, s0.gin@, 0, 4);
                assert(self.unit@.subrange(0, 3) =~= s0.unit@.subrange(0, 3));
                lemma_le_local(self.unit@, 0, s0.unit@, 0, 3);
            }
            if !done {
                return Some(Ok(self.need - self.unit.len()));
            }
        }
        self.trim();
        let before = self.dec.out.len();
        if self.dropped > SLIMIT - (2 * SBLOCK_MAX) as u64 || before as u64 > SLIMIT - (2 * SBLOCK_MAX) as u64 - self.dropped {
            return Some(self.failed(Fail::Limit));
        }
        let olimit = before + 2 * SBLOCK_MAX;
        let need = self.need;
        let src: &[u8] = if direct {
            let s = slice_subrange(inp, *ipos - 3, *ipos - 3 + need);
            let i1 = *ipos;
            *ipos = *ipos + (need - 3);
            proof {
                assert(s@ =~= self.unit@ + inp@.subrange(i1 as int, *ipos as int)) by {
                    assert forall|t: int| 0 <= t < 3 implies #[trigger] s@[t] == self.unit@[t] by {}
                }
            }
            self.gin = Ghost(self.gin@ + inp@.subrange(i1 as int, *ipos as int));
            s
        } else {
            self.unit.as_slice()
        };
        let ghost g = self.gin@;
        let ghost j = self.gbpos@;
        let ghost h = self.ghdr@;
        proof {
            assert(g =~= g.subrange(0, j) + src@);
            assert(g.subrange(0, j) =~= s0.gin@.subrange(0, j));
            assert(g =~= s0.gin@ + inp@.subrange(i0 as int, *ipos as int));
            assert(src@.subrange(0, 3) =~= s0.unit@.subrange(0, 3));
            lemma_le_local(src@, 0, s0.unit@, 0, 3);
            assert(g.subrange(4, 4 + h.size) =~= s0.gin@.subrange(4, 4 + h.size));
            assert(g.subrange(0, 4) =~= s0.gin@.subrange(0, 4));
            lemma_le_local(g, 0, s0.gin@, 0, 4);
        }
        let ghost gst = self.gst@;
        let ghost strim = FrameState { out: self.dec.out@, ..gst };
        let ghost pre = gst.out.subrange(0, self.dropped as int);
        let (res, _, last) = block_exec(src, 0, self.window, &mut self.dec, olimit, Ghost(strim));
        match res {
            Step::Done => {},
            Step::Limit => {
                return Some(self.failed(Fail::Limit));
            },
            Step::Bad => {
                return Some(self.failed(Fail::Corrupt));
            },
        }
        let ghost bs = block_step(src@, 0, h.window, strim);
        proof {
            assert(bs is Some);
        }
        let ghost j2 = bs.unwrap().0;
        let ghost st2 = bs.unwrap().1;
        let ghost nst = shift(st2, pre);
        proof {
            assert(gst.out =~= pre + strim.out);
            assert(gst == shift(strim, pre));
            if self.dropped == 0 {
                assert(pre =~= Seq::<u8>::empty());
                assert(st2.out =~= pre + st2.out);
                assert(nst == st2);
                assert(strim == gst);
            } else {
                lemma_block_step_shift(src@, 0, h.window, strim, pre);
            }
            lemma_block_step_prefix(src@, 0, h.window, strim);
            assert(block_step(src@, 0, h.window, gst) == Some((j2, nst, last)));
            assert(j2 == src@.len());
            lemma_next_block(s0.gin@, j, src@, h, gst, j2, nst, last);
            assert(g =~= s0.gin@.subrange(0, j) + src@);
            assert(fout(self.dec.out@, 0) =~= self.dec.out@);
            assert(self.dec.out@ == st2.out);
            assert(st2.out.subrange(0, before as int) == strim.out);
        }
        let new = slice_subrange(self.dec.out.as_slice(), before, self.dec.out.len());
        proof {
            assert(nst.out =~= gst.out + new@);
        }
        self.hash.update(new, Ghost(gst.out));
        self.gst = Ghost(nst);
        self.gbpos = Ghost(g.len() as int);
        proof {
            assert(nst.out.subrange(self.dropped as int, nst.out.len() as int) =~= st2.out);
            assert(nst.out.subrange(0, self.dropped + self.flushed) =~= gst.out.subrange(0, self.dropped + self.flushed));
            assert(FrameState { out: self.dec.out@, ..nst } == st2);
            assert(g.subrange(0, g.len() as int) =~= g);
        }
        let total = self.dropped + self.dec.out.len() as u64;
        if last {
            match self.fcs {
                Some(f) => {
                    if f != total {
                        return Some(self.failed(Fail::Corrupt));
                    }
                },
                None => {},
            }
            if self.checksum {
                self.unit.clear();
                self.need = 4;
                self.stage = Stage::Checksum;
                proof {
                    assert(self.gin@.subrange(self.gbpos@, self.gin@.len() as int) =~= self.unit@);
                }
            } else {
                proof {
                    lemma_frame_done(g, h, g.len() as int, nst);
                }
                self.stage = Stage::Done;
            }
        } else {
            match self.fcs {
                Some(f) => {
                    if total > f {
                        return Some(self.failed(Fail::Corrupt));
                    }
                },
                None => {},
            }
            self.unit.clear();
            self.need = 3;
            self.stage = Stage::BlockHeader;
            proof {
                assert(self.gin@.subrange(self.gbpos@, self.gin@.len() as int) =~= self.unit@);
            }
        }
        None
    }
}

impl Stream {
    /// The streaming step (`ZSTD_decompressStream`): takes input from
    /// `inp[ipos..]` and hands output out to `out[opos..]`. Returns 0 at the
    /// end of a frame, once all of its output is out, with the frame's
    /// input and output proven to be a whole frame and its content
    /// (`frame_ok`); otherwise a hint of the input still wanted, with
    /// everything handed out so far the start of the frame's content.
    pub fn stream(&mut self, out: &mut [u8], opos: &mut usize, inp: &[u8], ipos: &mut usize) -> (r: Result<usize, Fail>)
        requires
            old(self).inv(),
            *old(ipos) <= inp@.len(),
            *old(opos) <= old(out)@.len(),
        ensures
            final(out)@.len() == old(out)@.len(),
            *old(ipos) <= *final(ipos) <= inp@.len(),
            *old(opos) <= *final(opos) <= final(out)@.len(),
            final(out)@.subrange(0, *old(opos) as int) == old(out)@.subrange(0, *old(opos) as int),
            final(self).inv(),
            final(self).max_window == old(self).max_window,
            ({
                let took = inp@.subrange(*old(ipos) as int, *final(ipos) as int);
                let gave = final(out)@.subrange(*old(opos) as int, *final(opos) as int);
                match r {
                    Ok(n) => if n == 0 {
                        &&& frame_ok(old(self).gin@ + took, old(self).gemit@ + gave)
                        &&& final(self).stage == Stage::Magic
                        &&& final(self).gin@.len() == 0
                    } else {
                        &&& final(self).stage != Stage::Failed
                        &&& final(self).gin@ == old(self).gin@ + took
                        &&& final(self).gemit@ == old(self).gemit@ + gave
                    },
                    Err(_) => final(self).stage == Stage::Failed,
                }
            }),
    {
        match self.stage {
            Stage::Failed => {
                return Err(self.fail);
            },
            _ => {},
        }
        let ghost s00 = *self;
        let ghost i00 = *ipos;
        let ghost p00 = *opos;
        let ghost o00 = out@;
        proof {
            assert(inp@.subrange(i00 as int, i00 as int) =~= Seq::<u8>::empty());
            assert(out@.subrange(p00 as int, p00 as int) =~= Seq::<u8>::empty());
            assert(self.gin@ =~= s00.gin@ + Seq::<u8>::empty());
            assert(self.gemit@ =~= s00.gemit@ + Seq::<u8>::empty());
        }
        loop
            invariant
                self.inv(),
                self.stage != Stage::Failed,
                s00 == *old(self),
                o00 == old(out)@,
                i00 == *old(ipos),
                p00 == *old(opos),
                self.max_window == s00.max_window,
                i00 <= *ipos <= inp@.len(),
                p00 <= *opos <= out@.len(),
                out@.len() == o00.len(),
                out@.subrange(0, p00 as int) == o00.subrange(0, p00 as int),
                self.gin@ == s00.gin@ + inp@.subrange(i00 as int, *ipos as int),
                self.gemit@ == s00.gemit@ + out@.subrange(p00 as int, *opos as int),
            decreases 16 * (inp@.len() - *ipos) + rank(self.stage),
        {
            let ghost s1 = *self;
            let ghost i1 = *ipos;
            let ghost p1 = *opos;
            let ghost o1 = out@;
            let r = match self.stage {
                Stage::Magic => self.step_magic(out, opos, inp, ipos),
                Stage::Header => self.step_header(out, opos, inp, ipos),
                Stage::BlockHeader => self.step_block_header(out, opos, inp, ipos),
                Stage::Block => self.step_block(out, opos, inp, ipos),
                Stage::Checksum => self.step_checksum(out, opos, inp, ipos),
                Stage::Skip => self.step_skip(out, opos, inp, ipos),
                Stage::Done => self.step_done(out, opos, inp, ipos),
                Stage::Failed => {
                    return Err(self.fail);
                },
            };
            proof {
                assert(step_post(s1, *self, inp@, i1 as int, *ipos as int, o1, out@, p1 as int, *opos as int, r));
                assert(out@.len() == o00.len());
                assert(i00 <= *ipos);
                lemma_gave(o1, out@, out@, p00 as int, p1 as int, *opos as int);
                lemma_gave(o1, out@, out@, 0, p00 as int, p1 as int);
                assert(out@.subrange(p00 as int, *opos as int) =~= o1.subrange(p00 as int, p1 as int) + out@.subrange(
                    p1 as int,
                    *opos as int,
                )) by {
                    lemma_gave(o1, o1, out@, p00 as int, p1 as int, *opos as int);
                }
                assert(out@.subrange(0, p00 as int) =~= o00.subrange(0, p00 as int)) by {
                    assert(out@.subrange(0, p00 as int) =~= out@.subrange(0, p1 as int).subrange(0, p00 as int));
                    assert(o1.subrange(0, p00 as int) =~= o1.subrange(0, p1 as int).subrange(0, p00 as int));
                }
                assert(inp@.subrange(i00 as int, *ipos as int) =~= inp@.subrange(i00 as int, i1 as int) + inp@.subrange(
                    i1 as int,
                    *ipos as int,
                ));
                assert(s1.gin@ + inp@.subrange(i1 as int, *ipos as int) =~= s00.gin@ + inp@.subrange(i00 as int, *ipos as int));
                assert(s1.gemit@ + out@.subrange(p1 as int, *opos as int) =~= s00.gemit@ + out@.subrange(p00 as int, *opos as int));
            }
            match r {
                None => {},
                Some(x) => {
                    return x;
                },
            }
        }
    }
}

impl Stream {
    /// Everything handed out is the start of the frame's content, for any
    /// input that completes the frame.
    pub proof fn lemma_emitted_prefix(&self, b: Seq<u8>)
        requires
            self.inv(),
            self.stage != Stage::Failed,
            ext(b, self.gin@),
            frame(b, 0) is Some,
        ensures
            prefix(self.gemit@, frame(b, 0).unwrap().1),
    {
        let o = frame(b, 0).unwrap().1;
        match self.stage {
            Stage::Magic | Stage::Header | Stage::Skip => {
                assert(o.subrange(0, 0) =~= self.gemit@);
            },
            Stage::Done => {
                assert(prefix(self.gemit@, self.gst@.out));
            },
            _ => {
                let g = self.gin@;
                let h = self.ghdr@;
                let x = g.subrange(4, 4 + h.size);
                let y = b.subrange(4, b.len() as int);
                assert(y.subrange(0, x.len() as int) =~= x) by {
                    assert forall|t: int| 0 <= t < x.len() implies #[trigger] y.subrange(0, x.len() as int)[t] == x[t] by {
                        assert(b.subrange(0, g.len() as int)[4 + t] == g[4 + t]);
                    }
                }
                lemma_header_ext(x, y);
                lemma_ext_trans(b, g, g.subrange(0, self.gbpos@));
                let st2 = blocks(b, 4 + h.size, h.window, initial_state()).unwrap().1;
                assert(o == st2.out);
                if self.stage == Stage::Checksum {
                    assert(st2 == self.gst@);
                    assert(st2.out.subrange(0, st2.out.len() as int) =~= st2.out);
                } else {
                    lemma_blocks_prefix(b, self.gbpos@, h.window, self.gst@);
                }
                assert(prefix(self.gst@.out, st2.out));
                assert(prefix(self.gemit@, self.gst@.out));
                lemma_prefix_trans(self.gemit@, self.gst@.out, st2.out);
            },
        }
    }
}

} // verus!
