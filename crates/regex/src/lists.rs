//! Lemmas about the list functions of the specs: each distributes over
//! concatenation, and matches end where they should.
use crate::sem::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_drop_app(a: Seq<M>, b: Seq<M>)
    requires
        a.len() > 0,
    ensures
        (a + b).drop_first() =~= a.drop_first() + b,
        (a + b)[0] == a[0],
{
}

pub proof fn lemma_pm_all_app(p: Seq<SInst>, s: Seq<u8>, e: int, a: Seq<M>, b: Seq<M>)
    ensures
        pm_all(p, s, e, a + b) == pm_all(p, s, e, a) + pm_all(p, s, e, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_drop_app(a, b);
        lemma_pm_all_app(p, s, e, a.drop_first(), b);
    }
}

pub proof fn lemma_pm_all_one(p: Seq<SInst>, s: Seq<u8>, e: int, m: M)
    ensures
        pm_all(p, s, e, seq![m]) == pm(p, s, e, m.end, m.caps),
{
    assert(seq![m].drop_first() =~= Seq::<M>::empty());
    assert(pm_all(p, s, e, Seq::<M>::empty()) =~= Seq::<M>::empty());
}

pub proof fn lemma_pm_all2_app(p: Seq<SInst>, s: Seq<u8>, e0: int, ne: int, i: int, a: Seq<M>, b: Seq<M>)
    ensures
        pm_all2(p, s, e0, ne, i, a + b) == pm_all2(p, s, e0, ne, i, a) + pm_all2(p, s, e0, ne, i, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_drop_app(a, b);
        lemma_pm_all2_app(p, s, e0, ne, i, a.drop_first(), b);
    }
}

pub proof fn lemma_pm_all2_one(p: Seq<SInst>, s: Seq<u8>, e0: int, ne: int, i: int, m: M)
    ensures
        pm_all2(p, s, e0, ne, i, seq![m]) == pm(p, s, if m.end > i { ne } else { e0 }, m.end, m.caps),
{
    assert(seq![m].drop_first() =~= Seq::<M>::empty());
    assert(pm_all2(p, s, e0, ne, i, Seq::<M>::empty()) =~= Seq::<M>::empty());
}

/// Every match in `rs` ends in `lo..=hi`.
pub open spec fn ends_in(rs: Seq<M>, lo: int, hi: int) -> bool {
    forall|k: int| 0 <= k < rs.len() ==> lo <= (#[trigger] rs[k]).end <= hi
}

/// If everything in `rs` consumed something, `pm_all2` is `pm_all`.
pub proof fn lemma_pm_all2_gt(p: Seq<SInst>, s: Seq<u8>, e0: int, ne: int, i: int, rs: Seq<M>)
    requires
        ends_in(rs, i + 1, s.len() as int),
    ensures
        pm_all2(p, s, e0, ne, i, rs) == pm_all(p, s, ne, rs),
    decreases rs.len(),
{
    if rs.len() > 0 {
        assert(rs[0].end > i);
        assert forall|k: int| 0 <= k < rs.drop_first().len() implies i + 1 <= (#[trigger] rs.drop_first()[k]).end
            <= s.len() by {
            assert(rs.drop_first()[k] == rs[k + 1]);
        }
        lemma_pm_all2_gt(p, s, e0, ne, i, rs.drop_first());
    }
}

pub proof fn lemma_ends_app(a: Seq<M>, b: Seq<M>, lo: int, hi: int)
    requires
        ends_in(a, lo, hi),
        ends_in(b, lo, hi),
    ensures
        ends_in(a + b, lo, hi),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies lo <= (#[trigger] (a + b)[k]).end <= hi by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

pub proof fn lemma_ends_tail(rs: Seq<M>, lo: int, hi: int)
    requires
        ends_in(rs, lo, hi),
        rs.len() > 0,
    ensures
        ends_in(rs.drop_first(), lo, hi),
        lo <= rs[0].end <= hi,
{
    assert forall|k: int| 0 <= k < rs.drop_first().len() implies lo <= (#[trigger] rs.drop_first()[k]).end <= hi by {
        assert(rs.drop_first()[k] == rs[k + 1]);
    }
}

pub proof fn lemma_close_ends(rs: Seq<M>, k: nat, lo: int, hi: int)
    requires
        ends_in(rs, lo, hi),
    ensures
        ends_in(close(rs, k), lo, hi),
        close(rs, k).len() == rs.len(),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, lo, hi);
        lemma_close_ends(rs.drop_first(), k, lo, hi);
        let h = seq![M { end: rs[0].end, caps: rs[0].caps.update(2 * k as int + 1, rs[0].end) }];
        assert(ends_in(h, lo, hi));
        lemma_ends_app(h, close(rs.drop_first(), k), lo, hi);
    }
}

/// Matches of `r` from `i` end between `i` and the end of the text.
pub proof fn lemma_ms_ends(r: Re, s: Seq<u8>, i: int, c: Seq<int>)
    requires
        0 <= i <= s.len(),
    ensures
        ends_in(ms(r, s, i, c), i, s.len() as int),
    decreases r, 0int, 0int, 0nat,
{
    let n = s.len() as int;
    match r {
        Re::Empty => {},
        Re::Char(set) => {},
        Re::Look(k) => {},
        Re::Group(k, x) => {
            lemma_ms_ends(*x, s, i, c.update(2 * k as int, i));
            lemma_close_ends(ms(*x, s, i, c.update(2 * k as int, i)), k, i, n);
        },
        Re::Cat(x, y) => {
            lemma_ms_ends(*x, s, i, c);
            lemma_then_ends(ms(*x, s, i, c), *y, s, i);
        },
        Re::Alt(x, y) => {
            lemma_ms_ends(*x, s, i, c);
            lemma_ms_ends(*y, s, i, c);
            lemma_ends_app(ms(*x, s, i, c), ms(*y, s, i, c), i, n);
        },
        Re::Opt(x, greedy) => {
            lemma_ms_ends(*x, s, i, c);
            let one = seq![M { end: i, caps: c }];
            assert(ends_in(one, i, n));
            if greedy {
                lemma_ends_app(ms(*x, s, i, c), one, i, n);
            } else {
                lemma_ends_app(one, ms(*x, s, i, c), i, n);
            }
        },
        Re::Plus(x, greedy) => {
            lemma_ms_ends(*x, s, i, c);
            lemma_first_ends(ms(*x, s, i, c), *x, greedy, s, i);
        },
    }
}

pub proof fn lemma_then_ends(rs: Seq<M>, y: Re, s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        ends_in(rs, i, s.len() as int),
    ensures
        ends_in(ms_then(rs, y, s), i, s.len() as int),
    decreases y, s.len() + 2, 0int, rs.len(),
{
    let n = s.len() as int;
    if rs.len() > 0 {
        lemma_ends_tail(rs, i, n);
        lemma_ms_ends(y, s, rs[0].end, rs[0].caps);
        lemma_then_ends(rs.drop_first(), y, s, i);
        let a = ms(y, s, rs[0].end, rs[0].caps);
        assert(ends_in(a, i, n)) by {
            assert forall|k: int| 0 <= k < a.len() implies i <= (#[trigger] a[k]).end <= n by {}
        }
        lemma_ends_app(a, ms_then(rs.drop_first(), y, s), i, n);
    }
}

pub proof fn lemma_first_ends(rs: Seq<M>, x: Re, greedy: bool, s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        ends_in(rs, i, s.len() as int),
    ensures
        ends_in(first_it(rs, x, greedy, s, i), i, s.len() as int),
    decreases x, s.len() - i + 1, 2int, rs.len(),
{
    let n = s.len() as int;
    if rs.len() > 0 {
        lemma_ends_tail(rs, i, n);
        lemma_first_ends(rs.drop_first(), x, greedy, s, i);
        let a = if i < rs[0].end <= s.len() {
            more(x, greedy, s, rs[0].end, rs[0].caps)
        } else {
            seq![rs[0]]
        };
        if i < rs[0].end <= s.len() {
            lemma_more_ends(x, greedy, s, rs[0].end, rs[0].caps);
            assert forall|k: int| 0 <= k < a.len() implies i <= (#[trigger] a[k]).end <= n by {}
        }
        assert(ends_in(a, i, n));
        lemma_ends_app(a, first_it(rs.drop_first(), x, greedy, s, i), i, n);
    }
}

pub proof fn lemma_more_ends(x: Re, greedy: bool, s: Seq<u8>, j: int, c: Seq<int>)
    requires
        0 <= j <= s.len(),
    ensures
        ends_in(more(x, greedy, s, j, c), j, s.len() as int),
    decreases x, s.len() - j + 1, 1int, 0nat,
{
    let n = s.len() as int;
    lemma_ms_ends(x, s, j, c);
    lemma_more_it_ends(ms(x, s, j, c), x, greedy, s, j);
    let one = seq![M { end: j, caps: c }];
    assert(ends_in(one, j, n));
    let it = more_it(ms(x, s, j, c), x, greedy, s, j);
    if greedy {
        lemma_ends_app(it, one, j, n);
    } else {
        lemma_ends_app(one, it, j, n);
    }
}

pub proof fn lemma_more_it_ends(rs: Seq<M>, x: Re, greedy: bool, s: Seq<u8>, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        ends_in(more_it(rs, x, greedy, s, j), j, s.len() as int),
    decreases x, s.len() - j + 1, 0int, rs.len(),
{
    let n = s.len() as int;
    if rs.len() > 0 {
        lemma_more_it_ends(rs.drop_first(), x, greedy, s, j);
        let a = if j < rs[0].end <= s.len() {
            more(x, greedy, s, rs[0].end, rs[0].caps)
        } else {
            seq![]
        };
        if j < rs[0].end <= s.len() {
            lemma_more_ends(x, greedy, s, rs[0].end, rs[0].caps);
            assert forall|k: int| 0 <= k < a.len() implies j <= (#[trigger] a[k]).end <= n by {}
        }
        assert(ends_in(a, j, n));
        lemma_ends_app(a, more_it(rs.drop_first(), x, greedy, s, j), j, n);
    }
}

} // verus!
