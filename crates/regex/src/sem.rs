//! What a program does, and what the compiler emits, as spec functions.
//! Nothing here is trusted: the theorems are stated against `spec.rs`.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// An instruction, with its class as a set.
pub ghost enum SInst {
    Char { cls: ISet<u32>, next: int },
    Split { a: int, b: int },
    Save { slot: int, next: int },
    Look { k: Look, next: int },
    Match,
    Fail,
}

/// Every jump that consumes nothing goes forward, and every jump stays
/// inside the program.
pub open spec fn fwd(p: Seq<SInst>) -> bool {
    forall|pc: int| 0 <= pc < p.len() ==> fwd_at(p, pc)
}

pub open spec fn fwd_at(p: Seq<SInst>, pc: int) -> bool {
    match #[trigger] p[pc] {
        SInst::Char { cls, next } => 0 <= next < p.len(),
        SInst::Split { a, b } => pc < a < p.len() && pc < b < p.len(),
        SInst::Save { slot, next } => pc < next < p.len() && 0 <= slot,
        SInst::Look { k, next } => pc < next < p.len(),
        SInst::Match => true,
        SInst::Fail => true,
    }
}

/// Every match the program `p` finds from instruction `pc` at byte `i`
/// with capture slots `c`, best first: what a backtracking run of the
/// program would find, in order.
pub open spec fn pm(p: Seq<SInst>, s: Seq<u8>, pc: int, i: int, c: Seq<int>) -> Seq<M>
    decreases s.len() - i + 1, p.len() - pc,
{
    if pc < 0 || pc >= p.len() || i < 0 || i > s.len() {
        seq![]
    } else {
        match p[pc] {
            SInst::Match => seq![M { end: i, caps: c }],
            SInst::Fail => seq![],
            SInst::Char { cls, next } => match dec(s, i) {
                Some((cp, l)) => if cls.contains(cp) && l >= 1 {
                    pm(p, s, next, i + l, c)
                } else {
                    seq![]
                },
                None => seq![],
            },
            SInst::Split { a, b } => (if pc < a < p.len() {
                pm(p, s, a, i, c)
            } else {
                seq![]
            }) + (if pc < b < p.len() {
                pm(p, s, b, i, c)
            } else {
                seq![]
            }),
            SInst::Save { slot, next } => if pc < next < p.len() {
                pm(p, s, next, i, c.update(slot, i))
            } else {
                seq![]
            },
            SInst::Look { k, next } => if pc < next < p.len() && look_holds(k, s, i) {
                pm(p, s, next, i, c)
            } else {
                seq![]
            },
        }
    }
}

/// `pm` from `e`, after each of `rs`.
pub open spec fn pm_all(p: Seq<SInst>, s: Seq<u8>, e: int, rs: Seq<M>) -> Seq<M>
    decreases rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        pm(p, s, e, rs[0].end, rs[0].caps) + pm_all(p, s, e, rs.drop_first())
    }
}

/// `pm` after each of `rs`, which started at `i`: from `ne` for those that
/// consumed something, from `e0` for those that did not.
pub open spec fn pm_all2(p: Seq<SInst>, s: Seq<u8>, e0: int, ne: int, i: int, rs: Seq<M>) -> Seq<M>
    decreases rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        pm(p, s, if rs[0].end > i { ne } else { e0 }, rs[0].end, rs[0].caps) + pm_all2(p, s, e0, ne, i, rs.drop_first())
    }
}

// ---------------------------------------------------------------------------
// The code the compiler emits
// ---------------------------------------------------------------------------

/// Instructions in the normal copy of `r`.
pub open spec fn ln(r: Re) -> nat
    decreases r,
{
    match r {
        Re::Empty => 0,
        Re::Char(_) => 1,
        Re::Look(_) => 1,
        Re::Group(_, x) => 2 + ln(*x),
        Re::Cat(x, y) => ln(*x) + ln(*y),
        Re::Alt(x, y) => 1 + ln(*x) + ln(*y),
        Re::Opt(x, _) => 1 + ln(*x),
        Re::Plus(x, _) => ln(*x) + 1 + 2 * lz(*x),
    }
}

/// Instructions in the no-progress copy of `r`.
pub open spec fn lz(r: Re) -> nat
    decreases r,
{
    match r {
        Re::Empty => 0,
        Re::Char(_) => 1,
        Re::Look(_) => 1,
        Re::Group(_, x) => 2 + lz(*x),
        Re::Cat(x, y) => lz(*x) + lz(*y),
        Re::Alt(x, y) => 1 + lz(*x) + lz(*y),
        Re::Opt(x, _) => 1 + lz(*x),
        Re::Plus(x, _) => lz(*x),
    }
}

/// Where the no-progress copy of `r` based at `b` is entered; `e0` is
/// where it leaves to if it consumed nothing.
pub open spec fn ent_z(r: Re, b: int, e0: int) -> int
    decreases r,
{
    match r {
        Re::Empty => e0,
        Re::Cat(x, y) => ent_z(*x, b, ent_z(*y, b + lz(*x), e0)),
        Re::Plus(x, _) => ent_z(*x, b, e0),
        _ => b,
    }
}

/// Where the normal copy of `r` based at `b` is entered; `e` is where it
/// leaves to.
pub open spec fn ent_n(r: Re, b: int, e: int) -> int
    decreases r,
{
    match r {
        Re::Empty => e,
        Re::Cat(x, y) => ent_n(*x, b, ent_n(*y, b + ln(*x), e)),
        Re::Plus(x, _) => ent_z(*x, b + ln(*x) + 1 + lz(*x), e),
        _ => b,
    }
}

pub open spec fn split(a: int, b: int, greedy: bool) -> SInst {
    if greedy {
        SInst::Split { a: a, b: b }
    } else {
        SInst::Split { a: b, b: a }
    }
}

/// The normal copy of `r`: based at `b`, leaving to `e`; `f` is the
/// program's `Fail`.
pub open spec fn code_n(r: Re, b: int, e: int, f: int) -> Seq<SInst>
    decreases r, 1nat,
{
    match r {
        Re::Empty => seq![],
        Re::Char(cls) => seq![SInst::Char { cls: cls, next: e }],
        Re::Look(k) => seq![SInst::Look { k: k, next: e }],
        Re::Group(k, x) => {
            let close = b + 1 + ln(*x);
            seq![SInst::Save { slot: 2 * k as int, next: ent_n(*x, b + 1, close) }] + code_n(*x, b + 1, close, f)
                + seq![SInst::Save { slot: 2 * k as int + 1, next: e }]
        },
        Re::Cat(x, y) => {
            let m = b + ln(*x);
            code_n(*x, b, ent_n(*y, m, e), f) + code_n(*y, m, e, f)
        },
        Re::Alt(x, y) => {
            let m = b + 1 + ln(*x);
            seq![SInst::Split { a: ent_n(*x, b + 1, e), b: ent_n(*y, m, e) }] + code_n(*x, b + 1, e, f) + code_n(
                *y,
                m,
                e,
                f,
            )
        },
        Re::Opt(x, g) => seq![split(ent_n(*x, b + 1, e), e, g)] + code_n(*x, b + 1, e, f),
        Re::Plus(x, g) => {
            // The normal copy; the loop head; the copy later iterations
            // start in (an empty one fails); the copy the first iteration
            // starts in (an empty one leaves the loop).
            let l = b + ln(*x);
            code_n(*x, b, l, f) + seq![split(ent_z(*x, l + 1, f), e, g)] + code_z(*x, l + 1, f, b, l, f) + code_z(
                *x,
                l + 1 + lz(*x),
                e,
                b,
                l,
                f,
            )
        },
    }
}

/// The no-progress copy of `r`: based at `b`, leaving to `e0` if it
/// consumed nothing. Its characters jump into the normal copy of `r`,
/// which is based at `nb` and leaves to `ne`.
pub open spec fn code_z(r: Re, b: int, e0: int, nb: int, ne: int, f: int) -> Seq<SInst>
    decreases r, 0nat,
{
    match r {
        Re::Empty => seq![],
        Re::Char(cls) => seq![SInst::Char { cls: cls, next: ne }],
        Re::Look(k) => seq![SInst::Look { k: k, next: e0 }],
        Re::Group(k, x) => {
            let close = b + 1 + lz(*x);
            seq![SInst::Save { slot: 2 * k as int, next: ent_z(*x, b + 1, close) }] + code_z(
                *x,
                b + 1,
                close,
                nb + 1,
                nb + 1 + ln(*x),
                f,
            ) + seq![SInst::Save { slot: 2 * k as int + 1, next: e0 }]
        },
        Re::Cat(x, y) => {
            let m = b + lz(*x);
            let nm = nb + ln(*x);
            code_z(*x, b, ent_z(*y, m, e0), nb, ent_n(*y, nm, ne), f) + code_z(*y, m, e0, nm, ne, f)
        },
        Re::Alt(x, y) => {
            let m = b + 1 + lz(*x);
            seq![SInst::Split { a: ent_z(*x, b + 1, e0), b: ent_z(*y, m, e0) }] + code_z(*x, b + 1, e0, nb + 1, ne, f)
                + code_z(*y, m, e0, nb + 1 + ln(*x), ne, f)
        },
        Re::Opt(x, g) => seq![split(ent_z(*x, b + 1, e0), e0, g)] + code_z(*x, b + 1, e0, nb + 1, ne, f),
        Re::Plus(x, g) => code_z(*x, b, e0, nb, nb + ln(*x), f),
    }
}

/// `code` sits in `p` at `b`.
pub open spec fn has(p: Seq<SInst>, b: int, code: Seq<SInst>) -> bool {
    0 <= b && b + code.len() <= p.len() && forall|k: int| 0 <= k < code.len() ==> #[trigger] p[b + k] == code[k]
}

} // verus!
