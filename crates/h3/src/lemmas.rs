//! Lemmas about `spec::run`: a unit's outcome depends only on its own
//! bytes, and a stream read further continues from the unit it ended in.
//! Together they make the reader's result independent of how its input is
//! split.
use crate::spec::*;
use crate::varint::*;
use vstd::prelude::*;

verus! {

/// The varint at the start of `s` depends only on its own bytes.
pub proof fn lemma_var_same(s: Seq<u8>, t: Seq<u8>, k: nat)
    requires
        var_dec(s) is Ok,
        var_dec(s)->Ok_1 <= k,
        k <= s.len(),
        k <= t.len(),
        t.take(k as int) =~= s.take(k as int),
    ensures
        var_dec(t) == var_dec(s),
{
    let n = var_dec(s)->Ok_1;
    assert(t.take(n as int) =~= t.take(k as int).take(n as int));
    assert(s.take(n as int) =~= s.take(k as int).take(n as int));
    lemma_var_ext(s, t);
}

pub proof fn lemma_var_ok(s: Seq<u8>)
    requires
        var_dec(s) is Ok,
    ensures
        1 <= var_dec(s)->Ok_1 <= 8,
        var_dec(s)->Ok_1 <= s.len(),
{
}

/// Likewise the frame header.
pub proof fn lemma_hdr_same(s: Seq<u8>, t: Seq<u8>, k: nat)
    requires
        hdr_dec(s) is Ok,
        hdr_dec(s)->Ok_2 <= k,
        k <= s.len(),
        k <= t.len(),
        t.take(k as int) =~= s.take(k as int),
    ensures
        hdr_dec(t) == hdr_dec(s),
{
    let n = var_dec(s)->Ok_1;
    lemma_var_same(s, t, k);
    let s2 = s.skip(n as int);
    let t2 = t.skip(n as int);
    let m = var_dec(s2)->Ok_1;
    assert(t2.take(k - n) =~= s2.take(k - n)) by {
        assert forall|i: int| 0 <= i < k - n implies #[trigger] t2.take(k - n)[i] == s2.take(k - n)[i] by {
            assert(t.take(k as int)[i + n] == s.take(k as int)[i + n]);
        }
    }
    lemma_var_same(s2, t2, (k - n) as nat);
}

pub proof fn lemma_hdr_ok(s: Seq<u8>)
    requires
        hdr_dec(s) is Ok,
    ensures
        2 <= hdr_dec(s)->Ok_2 <= 16,
        hdr_dec(s)->Ok_2 <= s.len(),
        hdr_dec(s)->Ok_0 <= MAX_VARINT,
        hdr_dec(s)->Ok_1 <= MAX_VARINT,
{
    let n = var_dec(s)->Ok_1;
    lemma_var_bound(s);
    lemma_var_bound(s.skip(n as int));
}

/// A varint's value fits in 62 bits.
pub proof fn lemma_var_bound(s: Seq<u8>)
    requires
        var_dec(s) is Ok,
    ensures
        var_dec(s)->Ok_0 <= MAX_VARINT,
        1 <= var_dec(s)->Ok_1 <= 8,
        var_dec(s)->Ok_1 <= s.len(),
{
    let n = var_len(s[0]);
    let su = s.update(0, s[0] % 64);
    lemma_be_first(su, n, 64);
    lemma_p256((n - 1) as nat);
    lemma_p256_mono((n - 1) as nat, 7);
    lemma_p256(7);
}

/// How many bytes the unit at the start of `s` depends on, once it is not
/// incomplete.
pub open spec fn need(server: bool, limit: nat, s: Seq<u8>, st: RSt) -> nat {
    match st {
        RSt::Type | RSt::PushId => var_dec(s)->Ok_1,
        RSt::Frames(o) => match hdr_dec(s) {
            Hdr::Ok(t, len, h) => match accept(o, server, limit, t, len) {
                Err(_) => h,
                Ok(_) => h + len,
            },
            Hdr::Short => 0,
        },
    }
}

/// A unit's outcome depends only on its own bytes.
pub proof fn lemma_unit_same(server: bool, limit: nat, s: Seq<u8>, t: Seq<u8>, st: RSt, k: nat)
    requires
        !(unit(server, limit, s, st) is Incomplete),
        need(server, limit, s, st) <= k,
        k <= s.len(),
        k <= t.len(),
        t.take(k as int) =~= s.take(k as int),
    ensures
        unit(server, limit, t, st) == unit(server, limit, s, st),
        need(server, limit, t, st) == need(server, limit, s, st),
{
    match st {
        RSt::Type | RSt::PushId => {
            lemma_var_same(s, t, k);
        },
        RSt::Frames(o) => {
            lemma_hdr_same(s, t, k);
            let (ty, len, h) = (hdr_dec(s)->Ok_0, hdr_dec(s)->Ok_1, hdr_dec(s)->Ok_2);
            if accept(o, server, limit, ty, len) is Ok {
                assert(t.subrange(h as int, (h + len) as int) =~= s.subrange(h as int, (h + len) as int)) by {
                    assert forall|i: int| h <= i < h + len implies #[trigger] t[i] == s[i] by {
                        assert(t.take(k as int)[i] == s.take(k as int)[i]);
                    }
                }
            }
        },
    }
}

/// A unit that is not incomplete fits in `s`, and is at least a byte.
pub proof fn lemma_unit_len(server: bool, limit: nat, s: Seq<u8>, st: RSt)
    ensures
        unit(server, limit, s, st) matches Unit::Done(_, n, _, _) ==> 1 <= n <= s.len() && n == need(server, limit, s, st),
        unit(server, limit, s, st) matches Unit::Handoff(_, n) ==> 1 <= n <= s.len() && n == need(server, limit, s, st),
        !(unit(server, limit, s, st) is Incomplete) ==> need(server, limit, s, st) <= s.len(),
{
    match st {
        RSt::Type | RSt::PushId => {
            if var_dec(s) is Ok {
                lemma_var_bound(s);
            }
        },
        RSt::Frames(o) => {
            if hdr_dec(s) is Ok {
                lemma_hdr_ok(s);
            }
        },
    }
}

/// Nothing is a complete unit.
pub proof fn lemma_unit_empty(server: bool, limit: nat, st: RSt)
    ensures
        unit(server, limit, Seq::<u8>::empty(), st) is Incomplete,
        run(server, limit, Seq::<u8>::empty(), st) == (Out { ev: seq![], body: seq![], tail: Tail::At(st, 0) }),
{
}

pub proof fn lemma_shift(t: Tail, a: nat, b: nat)
    ensures
        shift(t, 0) == t,
        shift(shift(t, a), b) == shift(t, a + b),
{
}

/// Where a stream read so far ends: a unit that is incomplete.
pub proof fn lemma_run_at(server: bool, limit: nat, s: Seq<u8>, st: RSt)
    ensures
        run(server, limit, s, st).tail matches Tail::At(st1, q) ==> q <= s.len() && unit(server, limit, s.skip(q as int), st1) is Incomplete,
        run(server, limit, s, st).tail matches Tail::Handoff(_, q) ==> q <= s.len(),
    decreases s.len(),
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    lemma_unit_len(server, limit, s, st);
    match unit(server, limit, s, st) {
        Unit::Done(st2, n, ev, d) => {
            lemma_run_at(server, limit, s.skip(n as int), st2);
            let r = run(server, limit, s.skip(n as int), st2);
            if let Tail::At(st1, q) = r.tail {
                lemma_skip_skip2(s, n as int, q as int);
            }
        },
        Unit::Incomplete => {
            assert(s.skip(0) =~= s);
        },
        _ => {},
    }
}

pub proof fn lemma_skip_skip2(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= s.len(),
        0 <= b <= s.len() - a,
    ensures
        s.skip(a).skip(b) == s.skip(a + b),
{
    assert(s.skip(a).skip(b) =~= s.skip(a + b));
}

/// Reading on: a stream whose first part ends inside the unit at `q`
/// continues from that unit.
pub proof fn lemma_run_ext(server: bool, limit: nat, s: Seq<u8>, m: Seq<u8>, st: RSt)
    requires
        run(server, limit, s, st).tail is At,
    ensures
        ({
            let r = run(server, limit, s, st);
            let q = r.tail->At_1;
            let x = run(server, limit, (s + m).skip(q as int), r.tail->At_0);
            q <= s.len() && run(server, limit, s + m, st) == (Out { ev: r.ev + x.ev, body: r.body + x.body, tail: shift(x.tail, q) })
        }),
    decreases s.len(),
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    lemma_unit_len(server, limit, s, st);
    lemma_run_at(server, limit, s, st);
    let r = run(server, limit, s, st);
    match unit(server, limit, s, st) {
        Unit::Incomplete => {
            assert((s + m).skip(0) =~= s + m);
            let x = run(server, limit, s + m, st);
            assert(r.ev + x.ev =~= x.ev);
            assert(r.body + x.body =~= x.body);
            lemma_shift(x.tail, 0, 0);
        },
        Unit::Done(st2, n, ev, d) => {
            lemma_unit_same(server, limit, s, s + m, st, n);
            lemma_unit_len(server, limit, s + m, st);
            let s1 = s.skip(n as int);
            assert((s + m).skip(n as int) =~= s1 + m);
            lemma_run_ext(server, limit, s1, m, st2);
            let r1 = run(server, limit, s1, st2);
            let q1 = r1.tail->At_1;
            let q = q1 + n;
            assert((s + m).skip(q as int) =~= (s1 + m).skip(q1 as int));
            let x = run(server, limit, (s1 + m).skip(q1 as int), r1.tail->At_0);
            lemma_shift(x.tail, q1, n);
            assert(ev + (r1.ev + x.ev) =~= (ev + r1.ev) + x.ev);
            assert(d + (r1.body + x.body) =~= (d + r1.body) + x.body);
        },
        _ => {},
    }
}

/// Appending one complete unit to a stream that ends exactly at a unit
/// boundary.
pub proof fn lemma_advance(server: bool, limit: nat, b: Seq<u8>, w: Seq<u8>, st: RSt, st0: RSt, k: nat)
    requires
        run(server, limit, b, st).tail == Tail::At(st0, b.len()),
        unit(server, limit, w, st0) is Done,
        k == unit(server, limit, w, st0)->Done_1,
        k <= w.len(),
    ensures
        ({
            let r = run(server, limit, b, st);
            let u = unit(server, limit, w, st0);
            run(server, limit, b + w.take(k as int), st) == (Out {
                ev: r.ev + u->Done_2,
                body: r.body + u->Done_3,
                tail: Tail::At(u->Done_0, b.len() + k),
            })
        }),
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    let m = w.take(k as int);
    lemma_unit_len(server, limit, w, st0);
    lemma_unit_same(server, limit, w, m, st0, k);
    lemma_run_ext(server, limit, b, m, st);
    assert((b + m).skip(b.len() as int) =~= m);
    let u = unit(server, limit, w, st0);
    assert(m.skip(k as int) =~= Seq::<u8>::empty());
    lemma_unit_empty(server, limit, u->Done_0);
    let x = run(server, limit, m, st0);
    assert(x.ev =~= u->Done_2 + seq![]);
    assert(x.body =~= u->Done_3 + seq![]);
    assert(u->Done_2 + seq![] =~= u->Done_2);
    assert(u->Done_3 + seq![] =~= u->Done_3);
}

/// Appending bytes that end inside the next unit.
pub proof fn lemma_stay(server: bool, limit: nat, b: Seq<u8>, w: Seq<u8>, st: RSt, st0: RSt)
    requires
        run(server, limit, b, st).tail == Tail::At(st0, b.len()),
        unit(server, limit, w, st0) is Incomplete,
    ensures
        run(server, limit, b + w, st) == run(server, limit, b, st),
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    lemma_run_ext(server, limit, b, w, st);
    assert((b + w).skip(b.len() as int) =~= w);
    let r = run(server, limit, b, st);
    assert(r.ev + seq![] =~= r.ev);
    assert(r.body + seq![] =~= r.body);
}

/// Appending a unit that fails.
pub proof fn lemma_fail(server: bool, limit: nat, b: Seq<u8>, w: Seq<u8>, st: RSt, st0: RSt)
    requires
        run(server, limit, b, st).tail == Tail::At(st0, b.len()),
        unit(server, limit, w, st0) is Fail,
    ensures
        run(server, limit, b + w, st).tail == Tail::Fail(unit(server, limit, w, st0)->Fail_0),
        run(server, limit, b + w, st).ev == run(server, limit, b, st).ev,
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    lemma_run_ext(server, limit, b, w, st);
    assert((b + w).skip(b.len() as int) =~= w);
    let r = run(server, limit, b, st);
    assert(r.ev + seq![] =~= r.ev);
}

/// Appending a stream type that hands the stream off.
pub proof fn lemma_handoff(server: bool, limit: nat, b: Seq<u8>, w: Seq<u8>, st: RSt, st0: RSt, k: nat)
    requires
        run(server, limit, b, st).tail == Tail::At(st0, b.len()),
        unit(server, limit, w, st0) is Handoff,
        k == unit(server, limit, w, st0)->Handoff_1,
        k <= w.len(),
    ensures
        run(server, limit, b + w.take(k as int), st).tail == Tail::Handoff(unit(server, limit, w, st0)->Handoff_0, b.len() + k),
        run(server, limit, b + w.take(k as int), st).ev == run(server, limit, b, st).ev.push(Ev::StreamType(unit(server, limit, w, st0)->Handoff_0)),
{
    hide(unit);
    hide(need);
    hide(hdr_dec);
    hide(var_dec);
    hide(accept);
    let m = w.take(k as int);
    lemma_unit_len(server, limit, w, st0);
    lemma_unit_same(server, limit, w, m, st0, k);
    lemma_run_ext(server, limit, b, m, st);
    assert((b + m).skip(b.len() as int) =~= m);
    let r = run(server, limit, b, st);
    assert(r.ev + seq![Ev::StreamType(unit(server, limit, w, st0)->Handoff_0)] =~= r.ev.push(Ev::StreamType(unit(server, limit, w, st0)->Handoff_0)));
}

} // verus!
