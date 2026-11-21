//! The compiler's code is right: run from its entry, the code for `r`
//! finds exactly the matches `ms(r, ..)` lists, in the same order, each
//! continuing at the code's exit.
use crate::lists::*;
use crate::sem::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn ctx(p: Seq<SInst>, f: int) -> bool {
    fwd(p) && 0 <= f < p.len() && p[f] == SInst::Fail
}

pub proof fn lemma_len(r: Re, b: int, e: int, nb: int, ne: int, f: int)
    ensures
        code_n(r, b, e, f).len() == ln(r),
        code_z(r, b, e, nb, ne, f).len() == lz(r),
    decreases r,
{
    match r {
        Re::Empty => {},
        Re::Char(_) => {},
        Re::Look(_) => {},
        Re::Group(k, x) => {
            lemma_len(*x, b + 1, b + 1 + ln(*x), 0, 0, f);
            lemma_len(*x, b + 1, b + 1 + lz(*x), nb + 1, nb + 1 + ln(*x), f);
        },
        Re::Cat(x, y) => {
            lemma_len(*x, b, ent_n(*y, b + ln(*x), e), 0, 0, f);
            lemma_len(*y, b + ln(*x), e, 0, 0, f);
            lemma_len(*x, b, ent_z(*y, b + lz(*x), e), nb, ent_n(*y, nb + ln(*x), ne), f);
            lemma_len(*y, b + lz(*x), e, nb + ln(*x), ne, f);
        },
        Re::Alt(x, y) => {
            lemma_len(*x, b + 1, e, nb + 1, ne, f);
            lemma_len(*y, b + 1 + ln(*x), e, 0, 0, f);
            lemma_len(*y, b + 1 + lz(*x), e, nb + 1 + ln(*x), ne, f);
        },
        Re::Opt(x, g) => {
            lemma_len(*x, b + 1, e, nb + 1, ne, f);
        },
        Re::Plus(x, g) => {
            let l = b + ln(*x);
            lemma_len(*x, b, l, 0, 0, f);
            lemma_len(*x, l + 1, f, b, l, f);
            lemma_len(*x, l + 1 + lz(*x), e, b, l, f);
            lemma_len(*x, b, e, nb, nb + ln(*x), f);
        },
    }
}

pub proof fn lemma_has_app(p: Seq<SInst>, b: int, x: Seq<SInst>, y: Seq<SInst>)
    requires
        has(p, b, x + y),
    ensures
        has(p, b, x),
        has(p, b + x.len(), y),
{
    assert forall|k: int| 0 <= k < x.len() implies #[trigger] p[b + k] == x[k] by {
        assert((x + y)[k] == x[k]);
    }
    assert forall|k: int| 0 <= k < y.len() implies #[trigger] p[b + x.len() + k] == y[k] by {
        assert((x + y)[x.len() + k] == y[k]);
        assert(p[b + (x.len() + k)] == (x + y)[x.len() + k]);
    }
}

pub proof fn lemma_has_first(p: Seq<SInst>, b: int, code: Seq<SInst>)
    requires
        has(p, b, code),
        code.len() > 0,
    ensures
        0 <= b < p.len(),
        p[b] == code[0],
{
    assert(p[b + 0] == code[0]);
}

/// Closing a group, in the program and in the spec.
proof fn lemma_close(p: Seq<SInst>, s: Seq<u8>, cl: int, e: int, k: nat, rs: Seq<M>)
    requires
        fwd(p),
        0 <= cl < p.len(),
        p[cl] == (SInst::Save { slot: 2 * k as int + 1, next: e }),
        ends_in(rs, 0, s.len() as int),
    ensures
        pm_all(p, s, cl, rs) == pm_all(p, s, e, close(rs, k)),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, 0, s.len() as int);
        lemma_close(p, s, cl, e, k, rs.drop_first());
        let m = M { end: rs[0].end, caps: rs[0].caps.update(2 * k as int + 1, rs[0].end) };
        assert(fwd_at(p, cl));
        assert(pm(p, s, cl, rs[0].end, rs[0].caps) == pm(p, s, e, m.end, m.caps));
        lemma_pm_all_app(p, s, e, seq![m], close(rs.drop_first(), k));
        lemma_pm_all_one(p, s, e, m);
    }
}

/// The same for the two copies of a group's closing instruction.
proof fn lemma_close2(p: Seq<SInst>, s: Seq<u8>, cl: int, e0: int, ncl: int, ne: int, i: int, k: nat, rs: Seq<M>)
    requires
        fwd(p),
        0 <= cl < p.len(),
        p[cl] == (SInst::Save { slot: 2 * k as int + 1, next: e0 }),
        0 <= ncl < p.len(),
        p[ncl] == (SInst::Save { slot: 2 * k as int + 1, next: ne }),
        ends_in(rs, 0, s.len() as int),
    ensures
        pm_all2(p, s, cl, ncl, i, rs) == pm_all2(p, s, e0, ne, i, close(rs, k)),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, 0, s.len() as int);
        lemma_close2(p, s, cl, e0, ncl, ne, i, k, rs.drop_first());
        let m = M { end: rs[0].end, caps: rs[0].caps.update(2 * k as int + 1, rs[0].end) };
        assert(fwd_at(p, cl));
        assert(fwd_at(p, ncl));
        assert(pm(p, s, if rs[0].end > i { ncl } else { cl }, rs[0].end, rs[0].caps) == pm(
            p,
            s,
            if m.end > i { ne } else { e0 },
            m.end,
            m.caps,
        ));
        lemma_pm_all2_app(p, s, e0, ne, i, seq![m], close(rs.drop_first(), k));
        lemma_pm_all2_one(p, s, e0, ne, i, m);
    }
}

/// The parts of the code of `x+`.
pub open spec fn plus_has(p: Seq<SInst>, x: Re, g: bool, b: int, e: int, f: int) -> bool {
    let l = b + ln(x);
    &&& has(p, b, code_n(x, b, l, f))
    &&& 0 <= l < p.len()
    &&& p[l] == split(ent_z(x, l + 1, f), e, g)
    &&& has(p, l + 1, code_z(x, l + 1, f, b, l, f))
    &&& has(p, l + 1 + lz(x), code_z(x, l + 1 + lz(x), e, b, l, f))
}

proof fn lemma_plus_parts(p: Seq<SInst>, x: Re, g: bool, b: int, e: int, f: int)
    requires
        has(p, b, code_n(Re::Plus(Box::new(x), g), b, e, f)),
    ensures
        plus_has(p, x, g, b, e, f),
{
    let l = b + ln(x);
    let a = code_n(x, b, l, f);
    let sp = seq![split(ent_z(x, l + 1, f), e, g)];
    let z2 = code_z(x, l + 1, f, b, l, f);
    let z1 = code_z(x, l + 1 + lz(x), e, b, l, f);
    lemma_len(x, b, l, 0, 0, f);
    lemma_len(x, l + 1, f, b, l, f);
    lemma_len(x, l + 1 + lz(x), e, b, l, f);
    assert(code_n(Re::Plus(Box::new(x), g), b, e, f) == a + sp + z2 + z1);
    lemma_has_app(p, b, a + sp + z2, z1);
    lemma_has_app(p, b, a + sp, z2);
    lemma_has_app(p, b, a, sp);
    lemma_has_first(p, l, sp);
}

/// The normal copy.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub proof fn lemma_n(p: Seq<SInst>, s: Seq<u8>, r: Re, b: int, e: int, f: int, i: int, c: Seq<int>)
    requires
        ctx(p, f),
        has(p, b, code_n(r, b, e, f)),
        0 <= i <= s.len(),
    ensures
        pm(p, s, ent_n(r, b, e), i, c) == pm_all(p, s, e, ms(r, s, i, c)),
    decreases r, 0int, 0int, 0nat,
{
    let code = code_n(r, b, e, f);
    lemma_len(r, b, e, 0, 0, f);
    match r {
        Re::Empty => {
            lemma_pm_all_one(p, s, e, M { end: i, caps: c });
        },
        Re::Char(cls) => {
            lemma_has_first(p, b, code);
            match dec(s, i) {
                Some((cp, l)) => {
                    if cls.contains(cp) {
                        lemma_pm_all_one(p, s, e, M { end: i + l, caps: c });
                    }
                },
                None => {},
            }
        },
        Re::Look(k) => {
            lemma_has_first(p, b, code);
            assert(fwd_at(p, b));
            if look_holds(k, s, i) {
                lemma_pm_all_one(p, s, e, M { end: i, caps: c });
            }
        },
        Re::Group(k, x) => {
            let cl = b + 1 + ln(*x);
            let open = seq![SInst::Save { slot: 2 * k as int, next: ent_n(*x, b + 1, cl) }];
            let body = code_n(*x, b + 1, cl, f);
            let shut = seq![SInst::Save { slot: 2 * k as int + 1, next: e }];
            lemma_len(*x, b + 1, cl, 0, 0, f);
            assert(code == open + body + shut);
            lemma_has_app(p, b, open + body, shut);
            lemma_has_app(p, b, open, body);
            lemma_has_first(p, b, open);
            lemma_has_first(p, cl, shut);
            assert(fwd_at(p, b));
            let c1 = c.update(2 * k as int, i);
            lemma_n(p, s, *x, b + 1, cl, f, i, c1);
            lemma_ms_ends(*x, s, i, c1);
            lemma_close(p, s, cl, e, k, ms(*x, s, i, c1));
        },
        Re::Cat(x, y) => {
            let m = b + ln(*x);
            let ey = ent_n(*y, m, e);
            lemma_len(*x, b, ey, 0, 0, f);
            lemma_has_app(p, b, code_n(*x, b, ey, f), code_n(*y, m, e, f));
            lemma_n(p, s, *x, b, ey, f, i, c);
            lemma_ms_ends(*x, s, i, c);
            lemma_n_then(p, s, *y, m, e, f, ms(*x, s, i, c));
        },
        Re::Alt(x, y) => {
            let m = b + 1 + ln(*x);
            let sp = seq![SInst::Split { a: ent_n(*x, b + 1, e), b: ent_n(*y, m, e) }];
            lemma_len(*x, b + 1, e, 0, 0, f);
            assert(code == sp + code_n(*x, b + 1, e, f) + code_n(*y, m, e, f));
            lemma_has_app(p, b, sp + code_n(*x, b + 1, e, f), code_n(*y, m, e, f));
            lemma_has_app(p, b, sp, code_n(*x, b + 1, e, f));
            lemma_has_first(p, b, sp);
            assert(fwd_at(p, b));
            lemma_n(p, s, *x, b + 1, e, f, i, c);
            lemma_n(p, s, *y, m, e, f, i, c);
            lemma_pm_all_app(p, s, e, ms(*x, s, i, c), ms(*y, s, i, c));
        },
        Re::Opt(x, g) => {
            let sp = seq![split(ent_n(*x, b + 1, e), e, g)];
            lemma_has_app(p, b, sp, code_n(*x, b + 1, e, f));
            lemma_has_first(p, b, sp);
            assert(fwd_at(p, b));
            lemma_n(p, s, *x, b + 1, e, f, i, c);
            let one = seq![M { end: i, caps: c }];
            lemma_pm_all_one(p, s, e, M { end: i, caps: c });
            if g {
                lemma_pm_all_app(p, s, e, ms(*x, s, i, c), one);
            } else {
                lemma_pm_all_app(p, s, e, one, ms(*x, s, i, c));
            }
        },
        Re::Plus(x, g) => {
            lemma_plus_parts(p, *x, g, b, e, f);
            let l = b + ln(*x);
            lemma_z(p, s, *x, l + 1 + lz(*x), e, b, l, f, i, c);
            lemma_ms_ends(*x, s, i, c);
            lemma_first(p, s, *x, g, b, e, f, i, ms(*x, s, i, c));
        },
    }
}

/// After each of `rs`, the code of `y`.
proof fn lemma_n_then(p: Seq<SInst>, s: Seq<u8>, y: Re, b: int, e: int, f: int, rs: Seq<M>)
    requires
        ctx(p, f),
        has(p, b, code_n(y, b, e, f)),
        ends_in(rs, 0, s.len() as int),
    ensures
        pm_all(p, s, ent_n(y, b, e), rs) == pm_all(p, s, e, ms_then(rs, y, s)),
    decreases y, s.len() + 2, 0int, rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, 0, s.len() as int);
        lemma_n(p, s, y, b, e, f, rs[0].end, rs[0].caps);
        lemma_n_then(p, s, y, b, e, f, rs.drop_first());
        lemma_pm_all_app(p, s, e, ms(y, s, rs[0].end, rs[0].caps), ms_then(rs.drop_first(), y, s));
    }
}

/// The first iteration of `x+`, which ran in the copy that leaves the
/// loop if it consumed nothing.
proof fn lemma_first(p: Seq<SInst>, s: Seq<u8>, x: Re, g: bool, b: int, e: int, f: int, i: int, rs: Seq<M>)
    requires
        ctx(p, f),
        plus_has(p, x, g, b, e, f),
        0 <= i <= s.len(),
        ends_in(rs, i, s.len() as int),
    ensures
        pm_all2(p, s, e, b + ln(x), i, rs) == pm_all(p, s, e, first_it(rs, x, g, s, i)),
    decreases x, s.len() - i + 1, 2int, rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, i, s.len() as int);
        lemma_first(p, s, x, g, b, e, f, i, rs.drop_first());
        let a = if i < rs[0].end <= s.len() {
            more(x, g, s, rs[0].end, rs[0].caps)
        } else {
            seq![rs[0]]
        };
        if i < rs[0].end <= s.len() {
            lemma_loop(p, s, x, g, b, e, f, rs[0].end, rs[0].caps);
        } else {
            lemma_pm_all_one(p, s, e, rs[0]);
        }
        lemma_pm_all_app(p, s, e, a, first_it(rs.drop_first(), x, g, s, i));
    }
}

/// The loop head of `x+`.
proof fn lemma_loop(p: Seq<SInst>, s: Seq<u8>, x: Re, g: bool, b: int, e: int, f: int, j: int, c: Seq<int>)
    requires
        ctx(p, f),
        plus_has(p, x, g, b, e, f),
        0 <= j <= s.len(),
    ensures
        pm(p, s, b + ln(x), j, c) == pm_all(p, s, e, more(x, g, s, j, c)),
    decreases x, s.len() - j + 1, 1int, 0nat,
{
    let l = b + ln(x);
    assert(fwd_at(p, l));
    lemma_z(p, s, x, l + 1, f, b, l, f, j, c);
    lemma_ms_ends(x, s, j, c);
    lemma_more_it(p, s, x, g, b, e, f, j, ms(x, s, j, c));
    let one = seq![M { end: j, caps: c }];
    let it = more_it(ms(x, s, j, c), x, g, s, j);
    lemma_pm_all_one(p, s, e, M { end: j, caps: c });
    if g {
        lemma_pm_all_app(p, s, e, it, one);
    } else {
        lemma_pm_all_app(p, s, e, one, it);
    }
}

/// Later iterations of `x+`, which ran in the copy that fails if it
/// consumed nothing.
proof fn lemma_more_it(p: Seq<SInst>, s: Seq<u8>, x: Re, g: bool, b: int, e: int, f: int, j: int, rs: Seq<M>)
    requires
        ctx(p, f),
        plus_has(p, x, g, b, e, f),
        0 <= j <= s.len(),
        ends_in(rs, j, s.len() as int),
    ensures
        pm_all2(p, s, f, b + ln(x), j, rs) == pm_all(p, s, e, more_it(rs, x, g, s, j)),
    decreases x, s.len() - j + 1, 0int, rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, j, s.len() as int);
        lemma_more_it(p, s, x, g, b, e, f, j, rs.drop_first());
        let a = if j < rs[0].end <= s.len() {
            more(x, g, s, rs[0].end, rs[0].caps)
        } else {
            seq![]
        };
        if j < rs[0].end <= s.len() {
            lemma_loop(p, s, x, g, b, e, f, rs[0].end, rs[0].caps);
        } else {
            assert(pm(p, s, f, rs[0].end, rs[0].caps) =~= seq![]);
            assert(pm_all(p, s, e, a) =~= seq![]);
        }
        lemma_pm_all_app(p, s, e, a, more_it(rs.drop_first(), x, g, s, j));
    }
}

/// The no-progress copy.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub proof fn lemma_z(p: Seq<SInst>, s: Seq<u8>, r: Re, b: int, e0: int, nb: int, ne: int, f: int, i: int, c: Seq<int>)
    requires
        ctx(p, f),
        has(p, b, code_z(r, b, e0, nb, ne, f)),
        has(p, nb, code_n(r, nb, ne, f)),
        0 <= i <= s.len(),
    ensures
        pm(p, s, ent_z(r, b, e0), i, c) == pm_all2(p, s, e0, ne, i, ms(r, s, i, c)),
    decreases r, 0int, 0int, 0nat,
{
    let code = code_z(r, b, e0, nb, ne, f);
    let ncode = code_n(r, nb, ne, f);
    lemma_len(r, b, e0, nb, ne, f);
    lemma_len(r, nb, ne, 0, 0, f);
    match r {
        Re::Empty => {
            lemma_pm_all2_one(p, s, e0, ne, i, M { end: i, caps: c });
        },
        Re::Char(cls) => {
            lemma_has_first(p, b, code);
            match dec(s, i) {
                Some((cp, l)) => {
                    if cls.contains(cp) {
                        lemma_pm_all2_one(p, s, e0, ne, i, M { end: i + l, caps: c });
                    }
                },
                None => {},
            }
        },
        Re::Look(k) => {
            lemma_has_first(p, b, code);
            assert(fwd_at(p, b));
            if look_holds(k, s, i) {
                lemma_pm_all2_one(p, s, e0, ne, i, M { end: i, caps: c });
            }
        },
        Re::Group(k, x) => {
            let cl = b + 1 + lz(*x);
            let ncl = nb + 1 + ln(*x);
            let open = seq![SInst::Save { slot: 2 * k as int, next: ent_z(*x, b + 1, cl) }];
            let body = code_z(*x, b + 1, cl, nb + 1, ncl, f);
            let shut = seq![SInst::Save { slot: 2 * k as int + 1, next: e0 }];
            let nopen = seq![SInst::Save { slot: 2 * k as int, next: ent_n(*x, nb + 1, ncl) }];
            let nbody = code_n(*x, nb + 1, ncl, f);
            let nshut = seq![SInst::Save { slot: 2 * k as int + 1, next: ne }];
            lemma_len(*x, b + 1, cl, nb + 1, ncl, f);
            lemma_len(*x, nb + 1, ncl, 0, 0, f);
            assert(code == open + body + shut);
            assert(ncode == nopen + nbody + nshut);
            lemma_has_app(p, b, open + body, shut);
            lemma_has_app(p, b, open, body);
            lemma_has_first(p, b, open);
            lemma_has_first(p, cl, shut);
            lemma_has_app(p, nb, nopen + nbody, nshut);
            lemma_has_app(p, nb, nopen, nbody);
            lemma_has_first(p, ncl, nshut);
            assert(fwd_at(p, b));
            let c1 = c.update(2 * k as int, i);
            lemma_z(p, s, *x, b + 1, cl, nb + 1, ncl, f, i, c1);
            lemma_ms_ends(*x, s, i, c1);
            lemma_close2(p, s, cl, e0, ncl, ne, i, k, ms(*x, s, i, c1));
        },
        Re::Cat(x, y) => {
            let m = b + lz(*x);
            let nm = nb + ln(*x);
            let e0x = ent_z(*y, m, e0);
            let nex = ent_n(*y, nm, ne);
            lemma_len(*x, b, e0x, nb, nex, f);
            lemma_len(*x, nb, nex, 0, 0, f);
            lemma_has_app(p, b, code_z(*x, b, e0x, nb, nex, f), code_z(*y, m, e0, nm, ne, f));
            lemma_has_app(p, nb, code_n(*x, nb, nex, f), code_n(*y, nm, ne, f));
            lemma_z(p, s, *x, b, e0x, nb, nex, f, i, c);
            lemma_ms_ends(*x, s, i, c);
            lemma_z_then(p, s, *y, m, e0, nm, ne, f, i, ms(*x, s, i, c));
        },
        Re::Alt(x, y) => {
            let m = b + 1 + lz(*x);
            let nm = nb + 1 + ln(*x);
            let sp = seq![SInst::Split { a: ent_z(*x, b + 1, e0), b: ent_z(*y, m, e0) }];
            let nsp = seq![SInst::Split { a: ent_n(*x, nb + 1, ne), b: ent_n(*y, nm, ne) }];
            let zx = code_z(*x, b + 1, e0, nb + 1, ne, f);
            let zy = code_z(*y, m, e0, nm, ne, f);
            let nx = code_n(*x, nb + 1, ne, f);
            let ny = code_n(*y, nm, ne, f);
            lemma_len(*x, b + 1, e0, nb + 1, ne, f);
            lemma_len(*x, nb + 1, ne, 0, 0, f);
            assert(code == sp + zx + zy);
            assert(ncode == nsp + nx + ny);
            lemma_has_app(p, b, sp + zx, zy);
            lemma_has_app(p, b, sp, zx);
            lemma_has_first(p, b, sp);
            lemma_has_app(p, nb, nsp + nx, ny);
            lemma_has_app(p, nb, nsp, nx);
            assert(fwd_at(p, b));
            lemma_z(p, s, *x, b + 1, e0, nb + 1, ne, f, i, c);
            lemma_z(p, s, *y, m, e0, nm, ne, f, i, c);
            lemma_pm_all2_app(p, s, e0, ne, i, ms(*x, s, i, c), ms(*y, s, i, c));
        },
        Re::Opt(x, g) => {
            let sp = seq![split(ent_z(*x, b + 1, e0), e0, g)];
            let nsp = seq![split(ent_n(*x, nb + 1, ne), ne, g)];
            lemma_has_app(p, b, sp, code_z(*x, b + 1, e0, nb + 1, ne, f));
            lemma_has_first(p, b, sp);
            lemma_has_app(p, nb, nsp, code_n(*x, nb + 1, ne, f));
            assert(fwd_at(p, b));
            lemma_z(p, s, *x, b + 1, e0, nb + 1, ne, f, i, c);
            let one = seq![M { end: i, caps: c }];
            lemma_pm_all2_one(p, s, e0, ne, i, M { end: i, caps: c });
            if g {
                lemma_pm_all2_app(p, s, e0, ne, i, ms(*x, s, i, c), one);
            } else {
                lemma_pm_all2_app(p, s, e0, ne, i, one, ms(*x, s, i, c));
            }
        },
        Re::Plus(x, g) => {
            lemma_plus_parts(p, *x, g, nb, ne, f);
            let l = nb + ln(*x);
            lemma_z(p, s, *x, b, e0, nb, l, f, i, c);
            lemma_ms_ends(*x, s, i, c);
            lemma_zfirst(p, s, *x, g, e0, nb, ne, f, i, ms(*x, s, i, c));
        },
    }
}

/// After each of `rs`, which started at `i`: the normal code of `y` for
/// those that consumed something, its no-progress code for the others.
proof fn lemma_z_then(
    p: Seq<SInst>,
    s: Seq<u8>,
    y: Re,
    b: int,
    e0: int,
    nb: int,
    ne: int,
    f: int,
    i: int,
    rs: Seq<M>,
)
    requires
        ctx(p, f),
        has(p, b, code_z(y, b, e0, nb, ne, f)),
        has(p, nb, code_n(y, nb, ne, f)),
        0 <= i <= s.len(),
        ends_in(rs, i, s.len() as int),
    ensures
        pm_all2(p, s, ent_z(y, b, e0), ent_n(y, nb, ne), i, rs) == pm_all2(p, s, e0, ne, i, ms_then(rs, y, s)),
    decreases y, s.len() + 2, 0int, rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, i, s.len() as int);
        lemma_z_then(p, s, y, b, e0, nb, ne, f, i, rs.drop_first());
        let j = rs[0].end;
        let a = ms(y, s, j, rs[0].caps);
        if j > i {
            lemma_n(p, s, y, nb, ne, f, j, rs[0].caps);
            lemma_ms_ends(y, s, j, rs[0].caps);
            assert(ends_in(a, i + 1, s.len() as int)) by {
                assert forall|k: int| 0 <= k < a.len() implies i + 1 <= (#[trigger] a[k]).end <= s.len() by {}
            }
            lemma_pm_all2_gt(p, s, e0, ne, i, a);
        } else {
            lemma_z(p, s, y, b, e0, nb, ne, f, i, rs[0].caps);
        }
        lemma_pm_all2_app(p, s, e0, ne, i, a, ms_then(rs.drop_first(), y, s));
    }
}

/// The first iteration of `x+` when the loop itself is in a no-progress
/// copy; `nb` is where the loop's normal copy is.
proof fn lemma_zfirst(p: Seq<SInst>, s: Seq<u8>, x: Re, g: bool, e0: int, nb: int, ne: int, f: int, i: int, rs: Seq<M>)
    requires
        ctx(p, f),
        plus_has(p, x, g, nb, ne, f),
        0 <= i <= s.len(),
        ends_in(rs, i, s.len() as int),
    ensures
        pm_all2(p, s, e0, nb + ln(x), i, rs) == pm_all2(p, s, e0, ne, i, first_it(rs, x, g, s, i)),
    decreases x, s.len() - i + 1, 2int, rs.len(),
{
    if rs.len() > 0 {
        lemma_ends_tail(rs, i, s.len() as int);
        lemma_zfirst(p, s, x, g, e0, nb, ne, f, i, rs.drop_first());
        let a = if i < rs[0].end <= s.len() {
            more(x, g, s, rs[0].end, rs[0].caps)
        } else {
            seq![rs[0]]
        };
        if i < rs[0].end <= s.len() {
            lemma_loop(p, s, x, g, nb, ne, f, rs[0].end, rs[0].caps);
            lemma_more_ends(x, g, s, rs[0].end, rs[0].caps);
            assert(ends_in(a, i + 1, s.len() as int)) by {
                assert forall|k: int| 0 <= k < a.len() implies i + 1 <= (#[trigger] a[k]).end <= s.len() by {}
            }
            lemma_pm_all2_gt(p, s, e0, ne, i, a);
        } else {
            lemma_pm_all2_one(p, s, e0, ne, i, rs[0]);
        }
        lemma_pm_all2_app(p, s, e0, ne, i, a, first_it(rs.drop_first(), x, g, s, i));
    }
}

} // verus!
