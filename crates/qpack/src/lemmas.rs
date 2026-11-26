//! Prefix stability of framing: once an instruction's end is known (or it
//! is known to be an error), more input after it changes nothing
//! (`*_ext`), and the end depends only on the bytes before it (`*_trunc`).
//! From these: the encoder and decoder streams give the same result however
//! they are split into pieces (`lemma_erun_split`, `lemma_drun_split`).
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Integers
// ---------------------------------------------------------------------------

proof fn lemma_tail_ext(b: Seq<u8>, c: Seq<u8>, pos: int, i: nat, acc: nat)
    requires
        0 <= pos,
        !(int_tail(b, pos, i, acc) is Short),
    ensures
        int_tail(b + c, pos, i, acc) == int_tail(b, pos, i, acc),
    decreases 9 - i,
{
    assert((b + c)[pos] == b[pos]);
    if i < 9 && pos < b.len() {
        let acc2 = acc + ((b[pos] as nat) % 128) * p128(i);
        if !(acc2 > MAX_INT) && !(b[pos] < 128) {
            lemma_tail_ext(b, c, pos + 1, i + 1, acc2);
        }
    }
}

pub proof fn lemma_int_ext(b: Seq<u8>, c: Seq<u8>, pos: int, n: nat)
    requires
        0 <= pos,
        !(int_dec(b, pos, n) is Short),
    ensures
        int_dec(b + c, pos, n) == int_dec(b, pos, n),
{
    assert((b + c)[pos] == b[pos]);
    let k = (p2(n) - 1) as nat;
    if !((b[pos] as nat) % p2(n) < k) {
        lemma_tail_ext(b, c, pos + 1, 0, k);
    }
}

proof fn lemma_tail_pos(b: Seq<u8>, pos: int, i: nat, acc: nat)
    ensures
        int_tail(b, pos, i, acc) matches IntR::Ok(_, e) ==> pos < e <= b.len(),
    decreases 9 - i,
{
    if 0 <= pos < b.len() && i < 9 {
        let acc2 = acc + ((b[pos] as nat) % 128) * p128(i);
        if !(acc2 > MAX_INT) && !(b[pos] < 128) {
            lemma_tail_pos(b, pos + 1, i + 1, acc2);
        }
    }
}

pub proof fn lemma_int_pos(b: Seq<u8>, pos: int, n: nat)
    ensures
        int_dec(b, pos, n) matches IntR::Ok(_, e) ==> pos < e <= b.len(),
{
    if 0 <= pos < b.len() {
        lemma_tail_pos(b, pos + 1, 0, (p2(n) - 1) as nat);
    }
}

proof fn lemma_tail_trunc(x: Seq<u8>, m: int, pos: int, i: nat, acc: nat)
    requires
        0 <= pos,
        m <= x.len(),
        int_tail(x, pos, i, acc) is Ok,
        int_tail(x, pos, i, acc)->Ok_1 <= m,
    ensures
        int_tail(x.subrange(0, m), pos, i, acc) == int_tail(x, pos, i, acc),
    decreases 9 - i,
{
    lemma_tail_pos(x, pos, i, acc);
    let y = x.subrange(0, m);
    assert(y[pos] == x[pos]);
    if i < 9 && pos < x.len() {
        let acc2 = acc + ((x[pos] as nat) % 128) * p128(i);
        if !(acc2 > MAX_INT) && !(x[pos] < 128) {
            lemma_tail_trunc(x, m, pos + 1, i + 1, acc2);
        }
    }
}

pub proof fn lemma_int_trunc(x: Seq<u8>, m: int, pos: int, n: nat)
    requires
        0 <= pos,
        m <= x.len(),
        int_dec(x, pos, n) is Ok,
        int_dec(x, pos, n)->Ok_1 <= m,
    ensures
        int_dec(x.subrange(0, m), pos, n) == int_dec(x, pos, n),
{
    lemma_int_pos(x, pos, n);
    let y = x.subrange(0, m);
    assert(y[pos] == x[pos]);
    let k = (p2(n) - 1) as nat;
    if !((x[pos] as nat) % p2(n) < k) {
        lemma_tail_trunc(x, m, pos + 1, 0, k);
    }
}

// ---------------------------------------------------------------------------
// String ends
// ---------------------------------------------------------------------------

pub proof fn lemma_end_ext(b: Seq<u8>, c: Seq<u8>, pos: int, n: nat, lim: nat)
    requires
        0 <= pos,
        !(str_end(b, pos, n, lim) is Short),
    ensures
        str_end(b + c, pos, n, lim) == str_end(b, pos, n, lim),
        str_end(b, pos, n, lim) matches EndR::Ok(e) ==> pos < e <= b.len(),
{
    lemma_int_ext(b, c, pos, (n - 1) as nat);
    lemma_int_pos(b, pos, (n - 1) as nat);
}

pub proof fn lemma_end_trunc(x: Seq<u8>, m: int, pos: int, n: nat, lim: nat)
    requires
        0 <= pos,
        m <= x.len(),
        str_end(x, pos, n, lim) is Ok,
        str_end(x, pos, n, lim)->Ok_0 <= m,
    ensures
        str_end(x.subrange(0, m), pos, n, lim) == str_end(x, pos, n, lim),
{
    lemma_int_pos(x, pos, (n - 1) as nat);
    lemma_int_trunc(x, m, pos, (n - 1) as nat);
}

pub proof fn lemma_end_pos(b: Seq<u8>, pos: int, n: nat, lim: nat)
    ensures
        str_end(b, pos, n, lim) matches EndR::Ok(e) ==> pos < e <= b.len(),
{
    lemma_int_pos(b, pos, (n - 1) as nat);
}

// ---------------------------------------------------------------------------
// Encoder instructions
// ---------------------------------------------------------------------------

pub proof fn lemma_eframe_ext(b: Seq<u8>, c: Seq<u8>, mc: nat)
    requires
        !(eframe(b, mc) is Short),
    ensures
        eframe(b + c, mc) == eframe(b, mc),
        eframe(b, mc) matches EndR::Ok(e) ==> 0 < e <= b.len(),
{
    reveal(eframe);
    let lim = str_limit(mc);
    assert((b + c)[0] == b[0]);
    if b[0] >= 0x80 {
        lemma_int_ext(b, c, 0, 6);
        lemma_int_pos(b, 0, 6);
        if int_dec(b, 0, 6) is Ok {
            lemma_end_ext(b, c, int_dec(b, 0, 6)->Ok_1, 8, lim);
        }
    } else if b[0] >= 0x40 {
        lemma_end_pos(b, 0, 6, lim);
        if str_end(b, 0, 6, lim) is Short {
        } else {
            lemma_end_ext(b, c, 0, 6, lim);
            if str_end(b, 0, 6, lim) is Ok {
                lemma_end_ext(b, c, str_end(b, 0, 6, lim)->Ok_0, 8, lim);
            }
        }
    } else {
        lemma_int_ext(b, c, 0, 5);
        lemma_int_pos(b, 0, 5);
    }
}

pub proof fn lemma_eframe_trunc(x: Seq<u8>, m: int, mc: nat)
    requires
        eframe(x, mc) is Ok,
        eframe(x, mc)->Ok_0 <= m <= x.len(),
    ensures
        eframe(x.subrange(0, m), mc) == eframe(x, mc),
{
    reveal(eframe);
    let lim = str_limit(mc);
    let y = x.subrange(0, m);
    lemma_eframe_ext(x, Seq::empty(), mc);
    assert(y[0] == x[0]);
    if x[0] >= 0x80 {
        lemma_int_pos(x, 0, 6);
        let e = int_dec(x, 0, 6)->Ok_1;
        lemma_end_pos(x, e, 8, lim);
        lemma_int_trunc(x, m, 0, 6);
        lemma_end_trunc(x, m, e, 8, lim);
    } else if x[0] >= 0x40 {
        lemma_end_pos(x, 0, 6, lim);
        let e = str_end(x, 0, 6, lim)->Ok_0;
        lemma_end_pos(x, e, 8, lim);
        lemma_end_trunc(x, m, 0, 6, lim);
        lemma_end_trunc(x, m, e, 8, lim);
    } else {
        lemma_int_pos(x, 0, 5);
        lemma_int_trunc(x, m, 0, 5);
    }
}

/// Input that frames as too short stays too short when cut.
pub proof fn lemma_eframe_short_prefix(x: Seq<u8>, m: int, mc: nat)
    requires
        0 <= m <= x.len(),
        eframe(x.subrange(0, m), mc) is Short,
    ensures
        eframe(x, mc) matches EndR::Ok(e) ==> e > m,
        !(eframe(x, mc) is Bad) || true,
{
    if eframe(x, mc) is Ok && eframe(x, mc)->Ok_0 <= m {
        lemma_eframe_trunc(x, m, mc);
    }
}

/// `erun`'s result shifted by `k` bytes.
pub open spec fn shift<S>(r: Run<S>, k: int) -> Run<S> {
    match r {
        Run::Bad => Run::Bad,
        Run::Ok(s, j) => Run::Ok(s, j + k),
    }
}

/// What `erun` leaves is an incomplete instruction, and it consumed at most
/// its input.
pub proof fn lemma_erun_rest(t: Table, mc: nat, b: Seq<u8>)
    ensures
        erun(t, mc, b) matches Run::Ok(_, k) ==> 0 <= k <= b.len() && eframe(b.subrange(k, b.len() as int), mc) is Short,
    decreases b.len(),
{
    match eframe(b, mc) {
        EndR::Short => {
            assert(b.subrange(0, b.len() as int) =~= b);
        },
        EndR::Bad => {},
        EndR::Ok(e) => {
            if 0 < e <= b.len() {
                if let Some(t2) = einst(t, mc, b.subrange(0, e)) {
                    let r = b.subrange(e, b.len() as int);
                    lemma_erun_rest(t2, mc, r);
                    if let Run::Ok(_, k) = erun(t2, mc, r) {
                        assert(r.subrange(k, r.len() as int) =~= b.subrange(e + k, b.len() as int));
                    }
                }
            }
        },
    }
}

/// Consuming anything means the first instruction was whole.
pub proof fn lemma_erun_first(t: Table, mc: nat, b: Seq<u8>)
    ensures
        erun(t, mc, b) matches Run::Ok(_, k) ==> (k > 0 ==> (eframe(b, mc) matches EndR::Ok(e) && e <= k)),
{
    match eframe(b, mc) {
        EndR::Ok(e) => {
            if 0 < e <= b.len() {
                if let Some(t2) = einst(t, mc, b.subrange(0, e)) {
                    lemma_erun_rest(t2, mc, b.subrange(e, b.len() as int));
                }
            }
        },
        _ => {},
    }
}

/// Split invariance of the encoder stream: running `a` and then what it
/// left followed by `c` is running `a + c`. So a decoder that keeps the
/// unconsumed end of each piece and prepends it to the next
/// (`Decoder::feed_encoder`) reaches the same table, and the same error,
/// however the stream is cut into pieces.
pub proof fn lemma_erun_split(t: Table, mc: nat, a: Seq<u8>, c: Seq<u8>)
    ensures
        match erun(t, mc, a) {
            Run::Bad => erun(t, mc, a + c) is Bad,
            Run::Ok(t1, k) => 0 <= k <= a.len() && erun(t, mc, a + c) == shift(erun(t1, mc, a.subrange(k, a.len() as int) + c), k),
        },
    decreases a.len(),
{
    match eframe(a, mc) {
        EndR::Short => {
            assert(a.subrange(0, a.len() as int) + c =~= a + c);
            match erun(t, mc, a + c) {
                Run::Bad => {},
                Run::Ok(_, _) => {},
            }
        },
        EndR::Bad => {
            lemma_eframe_ext(a, c, mc);
        },
        EndR::Ok(e) => {
            lemma_eframe_ext(a, c, mc);
            let ac = a + c;
            assert(ac.subrange(0, e) =~= a.subrange(0, e));
            match einst(t, mc, a.subrange(0, e)) {
                None => {},
                Some(t2) => {
                    let ra = a.subrange(e, a.len() as int);
                    assert(ac.subrange(e, ac.len() as int) =~= ra + c);
                    lemma_erun_split(t2, mc, ra, c);
                    match erun(t2, mc, ra) {
                        Run::Bad => {},
                        Run::Ok(t3, k2) => {
                            assert(ra.subrange(k2, ra.len() as int) =~= a.subrange(e + k2, a.len() as int));
                            match erun(t3, mc, a.subrange(e + k2, a.len() as int) + c) {
                                Run::Bad => {},
                                Run::Ok(_, _) => {},
                            }
                        },
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Decoder instructions
// ---------------------------------------------------------------------------

pub proof fn lemma_dframe_ext(b: Seq<u8>, c: Seq<u8>)
    requires
        !(dframe(b) is Short),
    ensures
        dframe(b + c) == dframe(b),
        dframe(b) matches EndR::Ok(e) ==> 0 < e <= b.len(),
{
    reveal(dframe);
    assert((b + c)[0] == b[0]);
    let n: nat = if b[0] >= 0x80 { 7 } else { 6 };
    lemma_int_ext(b, c, 0, n);
    lemma_int_pos(b, 0, n);
}

pub proof fn lemma_drun_rest(st: EncState, b: Seq<u8>)
    ensures
        drun(st, b) matches Run::Ok(_, k) ==> 0 <= k <= b.len() && dframe(b.subrange(k, b.len() as int)) is Short,
    decreases b.len(),
{
    match dframe(b) {
        EndR::Short => {
            assert(b.subrange(0, b.len() as int) =~= b);
        },
        EndR::Bad => {},
        EndR::Ok(e) => {
            if 0 < e <= b.len() {
                if let Some(s2) = dinst(st, b.subrange(0, e)) {
                    let r = b.subrange(e, b.len() as int);
                    lemma_drun_rest(s2, r);
                    if let Run::Ok(_, k) = drun(s2, r) {
                        assert(r.subrange(k, r.len() as int) =~= b.subrange(e + k, b.len() as int));
                    }
                }
            }
        },
    }
}

/// Split invariance of the decoder stream, as for the encoder stream.
pub proof fn lemma_drun_split(st: EncState, a: Seq<u8>, c: Seq<u8>)
    ensures
        match drun(st, a) {
            Run::Bad => drun(st, a + c) is Bad,
            Run::Ok(s1, k) => 0 <= k <= a.len() && drun(st, a + c) == shift(drun(s1, a.subrange(k, a.len() as int) + c), k),
        },
    decreases a.len(),
{
    match dframe(a) {
        EndR::Short => {
            assert(a.subrange(0, a.len() as int) + c =~= a + c);
            match drun(st, a + c) {
                Run::Bad => {},
                Run::Ok(_, _) => {},
            }
        },
        EndR::Bad => {
            lemma_dframe_ext(a, c);
        },
        EndR::Ok(e) => {
            lemma_dframe_ext(a, c);
            let ac = a + c;
            assert(ac.subrange(0, e) =~= a.subrange(0, e));
            match dinst(st, a.subrange(0, e)) {
                None => {},
                Some(s2) => {
                    let ra = a.subrange(e, a.len() as int);
                    assert(ac.subrange(e, ac.len() as int) =~= ra + c);
                    lemma_drun_split(s2, ra, c);
                    match drun(s2, ra) {
                        Run::Bad => {},
                        Run::Ok(s3, k2) => {
                            assert(ra.subrange(k2, ra.len() as int) =~= a.subrange(e + k2, a.len() as int));
                            match drun(s3, a.subrange(e + k2, a.len() as int) + c) {
                                Run::Bad => {},
                                Run::Ok(_, _) => {},
                            }
                        },
                    }
                },
            }
        },
    }
}

pub proof fn lemma_dframe_trunc(x: Seq<u8>, m: int)
    requires
        dframe(x) is Ok,
        dframe(x)->Ok_0 <= m <= x.len(),
    ensures
        dframe(x.subrange(0, m)) == dframe(x),
{
    reveal(dframe);
    let y = x.subrange(0, m);
    lemma_dframe_ext(x, Seq::empty());
    assert(y[0] == x[0]);
    let n: nat = if x[0] >= 0x80 { 7 } else { 6 };
    lemma_int_pos(x, 0, n);
    lemma_int_trunc(x, m, 0, n);
}

pub proof fn lemma_dframe_short_prefix(x: Seq<u8>, m: int)
    requires
        0 <= m <= x.len(),
        dframe(x.subrange(0, m)) is Short,
    ensures
        dframe(x) matches EndR::Ok(e) ==> e > m,
{
    if dframe(x) is Ok && dframe(x)->Ok_0 <= m {
        lemma_dframe_trunc(x, m);
    }
}

pub proof fn lemma_drun_first(st: EncState, b: Seq<u8>)
    ensures
        drun(st, b) matches Run::Ok(_, k) ==> (k > 0 ==> (dframe(b) matches EndR::Ok(e) && e <= k)),
{
    match dframe(b) {
        EndR::Ok(e) => {
            if 0 < e <= b.len() {
                if let Some(s2) = dinst(st, b.subrange(0, e)) {
                    lemma_drun_rest(s2, b.subrange(e, b.len() as int));
                }
            }
        },
        _ => {},
    }
}

} // verus!
