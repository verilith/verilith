//! Extension stability: once a representation decodes (or fails) on some
//! input, more input after it changes nothing. This is what makes the
//! result independent of how the input is split (`Decoder::feed`).
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn not_short_int(r: IntR) -> bool {
    !(r is Short)
}

pub proof fn lemma_int_tail_ext(b: Seq<u8>, c: Seq<u8>, pos: int, i: nat, acc: nat)
    requires
        0 <= pos,
        !(int_tail(b, pos, i, acc) is Short),
    ensures
        int_tail(b + c, pos, i, acc) == int_tail(b, pos, i, acc),
        int_tail(b, pos, i, acc) matches IntR::Ok(_, e) ==> e <= b.len(),
    decreases 5 - i,
{
    assert((b + c)[pos] == b[pos]);
    if i < 5 && pos < b.len() {
        let add = ((b[pos] as nat) % 128) * pow128(i);
        if !(acc + add > 0xFFFF_FFFF) && !(b[pos] < 128) {
            lemma_int_tail_ext(b, c, pos + 1, i + 1, acc + add);
        }
    }
}

pub proof fn lemma_int_ext(b: Seq<u8>, c: Seq<u8>, pos: int, n: nat)
    requires
        0 <= pos,
        !(int_dec(b, pos, n) is Short),
    ensures
        int_dec(b + c, pos, n) == int_dec(b, pos, n),
        int_dec(b, pos, n) matches IntR::Ok(_, e) ==> pos < e <= b.len(),
{
    assert((b + c)[pos] == b[pos]);
    let k = (pow2_8(n) - 1) as nat;
    let first = (b[pos] as nat) % pow2_8(n);
    if !(first < k) {
        lemma_int_tail_ext(b, c, pos + 1, 0, k);
        lemma_int_tail_pos(b, pos + 1, 0, k);
    }
}

proof fn lemma_int_tail_pos(b: Seq<u8>, pos: int, i: nat, acc: nat)
    ensures
        int_tail(b, pos, i, acc) matches IntR::Ok(_, e) ==> e > pos,
    decreases 5 - i,
{
    if 0 <= pos < b.len() && i < 5 {
        let add = ((b[pos] as nat) % 128) * pow128(i);
        if !(acc + add > 0xFFFF_FFFF) && !(b[pos] < 128) {
            lemma_int_tail_pos(b, pos + 1, i + 1, acc + add);
        }
    }
}

pub proof fn lemma_str_ext(b: Seq<u8>, c: Seq<u8>, pos: int)
    requires
        0 <= pos,
        !(str_dec(b, pos) is Short),
    ensures
        str_dec(b + c, pos) == str_dec(b, pos),
        str_dec(b, pos) matches StrR::Ok(_, e) ==> pos < e <= b.len(),
{
    lemma_int_ext(b, c, pos, 7);
    match int_dec(b, pos, 7) {
        IntR::Ok(n, e) => {
            if n <= MAX_STR && e + n <= b.len() {
                assert((b + c).subrange(e, e + n) =~= b.subrange(e, e + n));
                assert((b + c)[pos] == b[pos]);
            }
        },
        _ => {},
    }
}

/// The extension lemma for representations.
pub proof fn lemma_rep_ext(st: DState, b: Seq<u8>, c: Seq<u8>)
    requires
        !(rep(st, b) is Short),
    ensures
        rep(st, b + c) == rep(st, b),
        rep(st, b) matches Rep::Field(_, _, e) ==> 0 < e <= b.len(),
        rep(st, b) matches Rep::Update(_, e) ==> 0 < e <= b.len(),
{
    assert(b.len() > 0);
    assert((b + c)[0] == b[0]);
    let ch = b[0];
    if ch & 0xE0 == 0x20 {
        if st.at_start {
            lemma_int_ext(b, c, 0, 5);
        }
    } else if !st.expect {
        if ch >= 0x80 {
            lemma_int_ext(b, c, 0, 7);
        } else {
            let incr = ch & 0x40 != 0;
            let newname = ch == 0x40 || ch == 0x00 || ch == 0x10;
            if newname {
                lemma_str_ext(b, c, 1);
                match str_dec(b, 1) {
                    StrR::Ok(_, e1) => lemma_str_ext(b, c, e1),
                    _ => {},
                }
            } else {
                let pn: nat = if incr { 6 } else { 4 };
                lemma_int_ext(b, c, 0, pn);
                match int_dec(b, 0, pn) {
                    IntR::Ok(i, e) => {
                        if !(i == 0 || i > st.table.len() + 61) {
                            lemma_str_ext(b, c, e);
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

/// Appending one more update to `upd`.
pub proof fn lemma_upd_step(st: DState, b: Seq<u8>, n: int, s1: DState, s2: DState, e: int)
    requires
        0 <= n <= b.len(),
        upd(st, b, n) == Some(s1),
        rep(s1, b.subrange(n, b.len() as int)) == Rep::Update(s2, e),
        0 < e <= b.len() - n,
    ensures
        upd(st, b, n + e) == Some(s2),
    decreases n,
{
    if n == 0 {
        assert(b.subrange(0, b.len() as int) =~= b);
        assert(b.subrange(e, b.len() as int).len() == b.len() - e);
        let t = b.subrange(e, b.len() as int);
        assert(upd(s2, t, 0) == Some(s2));
    } else {
        match rep(st, b) {
            Rep::Update(sa, ea) => {
                let t = b.subrange(ea, b.len() as int);
                assert(t.subrange(n - ea, t.len() as int) =~= b.subrange(n, b.len() as int));
                lemma_upd_step(sa, t, n - ea, s1, s2, e);
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// Truncation: a representation that decodes reads nothing past its end, so
// cutting the input anywhere after that end changes nothing. With the
// extension lemmas above, this pins down where a buffered representation
// can end (`lemma_end_at_need`), which the work bound of `Decoder::feed`
// rests on.
// ---------------------------------------------------------------------------

/// `b2` starts with `b`.
pub open spec fn ext_of(b2: Seq<u8>, b: Seq<u8>) -> bool {
    b.len() <= b2.len() && b2.subrange(0, b.len() as int) == b
}

/// Every input that starts with `b` and is shorter than `need` is too
/// short to decode in state `st` (what `Step::Short(need, _)` promises).
pub open spec fn short_upto(st: DState, b: Seq<u8>, need: int) -> bool {
    forall|b2: Seq<u8>| ext_of(b2, b) && b2.len() < need ==> #[trigger] rep(st, b2) is Short
}

/// The same for a string literal at `pos`.
pub open spec fn str_short_upto(b: Seq<u8>, pos: int, need: int) -> bool {
    forall|b2: Seq<u8>| ext_of(b2, b) && b2.len() < need ==> #[trigger] str_dec(b2, pos) is Short
}

/// Where a representation that decodes ends.
pub open spec fn rep_end(r: Rep) -> int {
    match r {
        Rep::Field(_, _, e) => e,
        Rep::Update(_, e) => e,
        _ => -1,
    }
}

/// `b2` is `b` and what follows it.
pub proof fn lemma_ext_split(b2: Seq<u8>, b: Seq<u8>)
    requires
        ext_of(b2, b),
    ensures
        b2 == b + b2.subrange(b.len() as int, b2.len() as int),
        b.len() > 0 ==> b2[0] == b[0],
{
    assert(b2 =~= b2.subrange(0, b.len() as int) + b2.subrange(b.len() as int, b2.len() as int));
    if b.len() > 0 {
        assert(b2.subrange(0, b.len() as int)[0] == b2[0]);
    }
}

/// An input that starts with `b` and is no longer is `b`.
pub proof fn lemma_ext_same(b2: Seq<u8>, b: Seq<u8>)
    requires
        ext_of(b2, b),
        b2.len() <= b.len(),
    ensures
        b2 == b,
{
    assert(b2.subrange(0, b2.len() as int) =~= b2);
}

/// Starting with `b + c` means starting with `b`.
pub proof fn lemma_ext_trans(b2: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        ext_of(b2, b + c),
    ensures
        ext_of(b2, b),
{
    assert(b2.subrange(0, b.len() as int) =~= b2.subrange(0, (b + c).len() as int).subrange(0, b.len() as int));
    assert((b + c).subrange(0, b.len() as int) =~= b);
}

/// A representation that is short on `b` is short on every input that
/// starts with it and is no longer.
pub proof fn lemma_short_same(st: DState, b: Seq<u8>)
    requires
        rep(st, b) is Short,
    ensures
        short_upto(st, b, b.len() + 1 as int),
{
    assert forall|b2: Seq<u8>| ext_of(b2, b) && b2.len() < b.len() + 1 implies #[trigger] rep(st, b2) is Short by {
        lemma_ext_same(b2, b);
    }
}

pub proof fn lemma_str_short_same(b: Seq<u8>, pos: int)
    requires
        str_dec(b, pos) is Short,
    ensures
        str_short_upto(b, pos, b.len() + 1 as int),
{
    assert forall|b2: Seq<u8>| ext_of(b2, b) && b2.len() < b.len() + 1 implies #[trigger] str_dec(b2, pos) is Short by {
        lemma_ext_same(b2, b);
    }
}

/// Short stays short with more input that does not reach `need`.
pub proof fn lemma_short_more(st: DState, b: Seq<u8>, c: Seq<u8>, need: int)
    requires
        short_upto(st, b, need),
    ensures
        short_upto(st, b + c, need),
{
    assert forall|b2: Seq<u8>| ext_of(b2, b + c) && b2.len() < need implies #[trigger] rep(st, b2) is Short by {
        lemma_ext_trans(b2, b, c);
    }
}

pub proof fn lemma_int_tail_trunc(x: Seq<u8>, m: int, pos: int, i: nat, acc: nat)
    requires
        0 <= pos,
        m <= x.len(),
        int_tail(x, pos, i, acc) is Ok,
        int_tail(x, pos, i, acc)->Ok_1 <= m,
    ensures
        int_tail(x.subrange(0, m), pos, i, acc) == int_tail(x, pos, i, acc),
    decreases 5 - i,
{
    lemma_int_tail_pos(x, pos, i, acc);
    let y = x.subrange(0, m);
    assert(y[pos] == x[pos]);
    if i < 5 && pos < x.len() {
        let add = ((x[pos] as nat) % 128) * pow128(i);
        if !(acc + add > 0xFFFF_FFFF) && !(x[pos] < 128) {
            lemma_int_tail_trunc(x, m, pos + 1, i + 1, acc + add);
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
    lemma_int_ext(x, Seq::empty(), pos, n);
    let y = x.subrange(0, m);
    assert(y[pos] == x[pos]);
    let k = (pow2_8(n) - 1) as nat;
    let first = (x[pos] as nat) % pow2_8(n);
    if !(first < k) {
        lemma_int_tail_trunc(x, m, pos + 1, 0, k);
    }
}

pub proof fn lemma_str_trunc(x: Seq<u8>, m: int, pos: int)
    requires
        0 <= pos,
        m <= x.len(),
        str_dec(x, pos) is Ok,
        str_dec(x, pos)->Ok_1 <= m,
    ensures
        str_dec(x.subrange(0, m), pos) == str_dec(x, pos),
{
    let y = x.subrange(0, m);
    lemma_int_ext(x, Seq::empty(), pos, 7);
    let n = int_dec(x, pos, 7)->Ok_0;
    let e = int_dec(x, pos, 7)->Ok_1;
    lemma_int_trunc(x, m, pos, 7);
    assert(y.subrange(e, e + n) =~= x.subrange(e, e + n));
    assert(y[pos] == x[pos]);
}

/// The truncation lemma for representations.
pub proof fn lemma_rep_trunc(st: DState, x: Seq<u8>, m: int)
    requires
        rep(st, x) is Field || rep(st, x) is Update,
        rep_end(rep(st, x)) <= m <= x.len(),
    ensures
        rep(st, x.subrange(0, m)) == rep(st, x),
{
    lemma_rep_ext(st, x, Seq::empty());
    let y = x.subrange(0, m);
    assert(y[0] == x[0]);
    let ch = x[0];
    if ch & 0xE0 == 0x20 {
        if st.at_start {
            lemma_int_trunc(x, m, 0, 5);
        }
    } else if !st.expect {
        if ch >= 0x80 {
            lemma_int_trunc(x, m, 0, 7);
        } else {
            let incr = ch & 0x40 != 0;
            let newname = ch == 0x40 || ch == 0x00 || ch == 0x10;
            if newname {
                lemma_str_ext(x, Seq::empty(), 1);
                let e1 = str_dec(x, 1)->Ok_1;
                lemma_str_ext(x, Seq::empty(), e1);
                lemma_str_trunc(x, m, 1);
                lemma_str_trunc(x, m, e1);
            } else {
                let pn: nat = if incr { 6 } else { 4 };
                lemma_int_ext(x, Seq::empty(), 0, pn);
                let e1 = int_dec(x, 0, pn)->Ok_1;
                lemma_str_ext(x, Seq::empty(), e1);
                lemma_int_trunc(x, m, 0, pn);
                lemma_str_trunc(x, m, e1);
            }
        }
    }
}

/// A buffered representation that was short below `need`, decoded from at
/// most `need` bytes, ends exactly at the end of them: `feed` never takes
/// input past the representation it completes.
pub proof fn lemma_end_at_need(st: DState, buf: Seq<u8>, need: int, bb: Seq<u8>)
    requires
        short_upto(st, buf, need),
        buf.len() < need,
        ext_of(bb, buf),
        bb.len() <= need,
        rep(st, bb) is Field || rep(st, bb) is Update,
    ensures
        rep_end(rep(st, bb)) == bb.len(),
{
    lemma_rep_ext(st, bb, Seq::empty());
    let e = rep_end(rep(st, bb));
    if e < bb.len() {
        let m = if e < buf.len() { buf.len() as int } else { e };
        lemma_rep_trunc(st, bb, m);
        let y = bb.subrange(0, m);
        assert(y.subrange(0, buf.len() as int) =~= bb.subrange(0, buf.len() as int));
        assert(ext_of(y, buf));
        assert(rep(st, y) is Short);
    }
}

/// A buffered representation that decodes once more input is added had
/// more input added.
pub proof fn lemma_taken(st: DState, buf: Seq<u8>, need: int, bb: Seq<u8>)
    requires
        short_upto(st, buf, need),
        buf.len() < need,
        ext_of(bb, buf),
        !(rep(st, bb) is Short),
    ensures
        bb.len() > buf.len(),
{
    if bb.len() <= buf.len() {
        lemma_ext_same(bb, buf);
        assert(ext_of(buf, buf)) by {
            assert(buf.subrange(0, buf.len() as int) =~= buf);
        }
        assert(rep(st, buf) is Short);
    }
}

} // verus!
