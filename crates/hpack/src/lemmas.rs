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

} // verus!
