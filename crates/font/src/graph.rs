//! Verified check of the composite-glyph graph and of `maxp`'s limits:
//! decides `wf_glyf_limits` exactly.
//!
//! `glyph_info` is defined with a budget of nesting levels. The checker
//! does not recompute a glyph for every budget: it remembers each glyph's
//! totals, and the lemmas here show that is sound, because a glyph's
//! totals do not depend on the budget once the budget covers its depth.
use crate::glyf::*;
use crate::prims::*;
use crate::spec::*;
use vstd::arithmetic::power::*;
use vstd::prelude::*;

verus! {

/// The executable counterpart of [`Info`].
#[derive(Clone, Copy)]
pub struct InfoX {
    pub points: u32,
    pub contours: u32,
    pub comps: u32,
    pub depth: u32,
    pub elems: u32,
}

impl View for InfoX {
    type V = Info;

    open spec fn view(&self) -> Info {
        Info {
            points: self.points as int,
            contours: self.contours as int,
            comps: self.comps as int,
            depth: self.depth as int,
            elems: self.elems as int,
        }
    }
}

/// What is remembered about a glyph.
#[derive(Clone, Copy)]
pub enum Memo {
    Unknown,
    /// Its totals.
    Done(InfoX),
    /// It has no totals within this many levels.
    Failed(u32),
}

/// The deepest component, among those from `p` on, given all of them have
/// totals within `fuel` levels.
pub open spec fn need(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, g: Seq<u8>, p: int, fuel: nat) -> int
    decreases g.len() - p,
{
    if p < 0 || p + 4 > g.len() {
        0
    } else {
        let d = match glyph_info(glyf, loca, fmt, ng, u16_at(g, p + 2), fuel) {
            Some(c) => c.depth,
            None => 0,
        };
        let q = p + 4 + comp_extra(g[p + 1]);
        let rest = if g[p + 1] & 0x20 != 0 && q <= g.len() {
            need(glyf, loca, fmt, ng, g, q, fuel)
        } else {
            0
        };
        if d > rest {
            d
        } else {
            rest
        }
    }
}

pub open spec fn imax(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

/// A glyph with totals within `f` levels has the same totals within any
/// number of levels that covers its depth, and none within fewer.
pub proof fn lemma_info_fuel(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, gid: int, f: nat, f2: nat)
    requires
        glyph_info(glyf, loca, fmt, ng, gid, f) is Some,
    ensures
        0 <= glyph_info(glyf, loca, fmt, ng, gid, f).unwrap().depth <= f,
        glyph_info(glyf, loca, fmt, ng, gid, f2) == if f2 >= glyph_info(
            glyf,
            loca,
            fmt,
            ng,
            gid,
            f,
        ).unwrap().depth {
            glyph_info(glyf, loca, fmt, ng, gid, f)
        } else {
            None
        },
    decreases f, 0nat,
{
    let g = glyph_of(glyf, loca, fmt, gid);
    if g.len() < 10 || i16_at(g, 0) >= 0 {
    } else {
        lemma_comps_fuel(glyf, loca, fmt, ng, g, 10, (f - 1) as nat, info_zero(), 0);
        if f2 > 0 {
            lemma_comps_fuel(glyf, loca, fmt, ng, g, 10, (f - 1) as nat, info_zero(), (f2 - 1) as nat);
        }
    }
}

pub proof fn lemma_comps_fuel(
    glyf: Seq<u8>,
    loca: Seq<u8>,
    fmt: int,
    ng: int,
    g: Seq<u8>,
    p: int,
    f: nat,
    acc: Info,
    f2: nat,
)
    requires
        comps_info(glyf, loca, fmt, ng, g, p, f, acc) is Some,
        acc.depth >= 0,
    ensures
        0 <= need(glyf, loca, fmt, ng, g, p, f) <= f,
        comps_info(glyf, loca, fmt, ng, g, p, f, acc).unwrap().depth == imax(
            acc.depth,
            need(glyf, loca, fmt, ng, g, p, f) + 1,
        ),
        comps_info(glyf, loca, fmt, ng, g, p, f2, acc) == if f2 >= need(glyf, loca, fmt, ng, g, p, f) {
            comps_info(glyf, loca, fmt, ng, g, p, f, acc)
        } else {
            None
        },
    decreases f, (if p <= g.len() {
        1 + g.len() - p
    } else {
        0
    }) as nat,
{
    let child = u16_at(g, p + 2);
    lemma_info_fuel(glyf, loca, fmt, ng, child, f, f2);
    let c = glyph_info(glyf, loca, fmt, ng, child, f).unwrap();
    let acc2 = Info {
        points: acc.points + c.points,
        contours: acc.contours + c.contours,
        comps: acc.comps + c.comps + 1,
        depth: if acc.depth > c.depth + 1 {
            acc.depth
        } else {
            c.depth + 1
        },
        elems: acc.elems + 1,
    };
    let q = p + 4 + comp_extra(g[p + 1]);
    if g[p + 1] & 0x20 != 0 {
        lemma_comps_fuel(glyf, loca, fmt, ng, g, q, f, acc2, f2);
    }
}

/// What a remembered entry for glyph `gid` claims.
pub open spec fn memo_ok(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, gid: int, m: Memo) -> bool {
    match m {
        Memo::Unknown => true,
        Memo::Done(x) => {
            &&& info_small(x)
            &&& x.depth <= MAX_COMPONENT_DEPTH
            &&& glyph_info(glyf, loca, fmt, ng, gid, x.depth as nat) == Some(x@)
        },
        Memo::Failed(k) => glyph_info(glyf, loca, fmt, ng, gid, k as nat) is None,
    }
}

pub open spec fn info_small(x: InfoX) -> bool {
    &&& x.points <= 0x10000
    &&& x.contours <= 0xFFFF
    &&& x.comps <= 0xFFFF
    &&& x.elems <= 0xFFFF
}

pub open spec fn memos_ok(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, memo: Seq<Memo>) -> bool {
    &&& memo.len() == ng
    &&& forall|i: int| 0 <= i < ng ==> memo_ok(glyf, loca, fmt, ng, i, #[trigger] memo[i])
}

/// Glyph `gid`'s slot.
fn glyph_slot<'a>(glyf: &'a [u8], loca: &[u8], fmt: u16, ng: u16, gid: u16) -> (g: &'a [u8])
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        gid < ng,
    ensures
        g@ == glyph_of(glyf@, loca@, fmt as int, gid as int),
        g@.len() <= glyf@.len(),
{
    proof {
        lemma_loca_le(loca@, fmt as int, ng as int, glyf.len() as int, gid as int + 1);
        assert(loca_step(loca@, fmt as int, gid as int));
    }
    let a = loca_get(loca, fmt, gid as usize);
    let b = loca_get(loca, fmt, gid as usize + 1);
    if b > glyf.len() {
        // Only when no glyph has an outline and glyf is one byte.
        proof {
            assert(glyf@.subrange(a as int, b as int) =~= glyf@.subrange(0, 0));
        }
        return slice(glyf, 0, 0);
    }
    slice(glyf, a, b)
}

/// A composite glyph whose totals [`info_x`] is working out: the
/// components before `p` are summed in `acc`, and `len` is the length of
/// its slot.
#[derive(Clone, Copy)]
pub struct Frame {
    pub gid: u16,
    pub len: usize,
    pub p: usize,
    pub acc: InfoX,
    pub fuel: u32,
}

/// What a frame knows. A `waiting` frame has asked for the totals of the
/// component at `p`.
pub open spec fn frame_ok(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, f: Frame, waiting: bool) -> bool {
    let g = glyph_of(gl, lo, fm, f.gid as int);
    &&& f.gid < n
    &&& g.len() == f.len
    &&& f.len <= gl.len()
    &&& g.len() >= 10
    &&& i16_at(g, 0) < 0
    &&& 10 <= f.p <= g.len()
    &&& 1 <= f.fuel <= MAX_COMPONENT_DEPTH
    &&& info_small(f.acc)
    &&& f.acc.points <= 0xFFFF
    &&& f.acc.elems <= f.acc.comps
    &&& f.acc.depth <= f.fuel
    &&& glyph_info(gl, lo, fm, n, f.gid as int, f.fuel as nat) == comps_info(
        gl,
        lo,
        fm,
        n,
        g,
        f.p as int,
        (f.fuel - 1) as nat,
        f.acc@,
    )
    &&& waiting ==> f.p + 4 <= g.len() && u16_at(g, f.p + 2) < n
}

/// The glyph the frame at `f` waits for.
pub open spec fn child_of(gl: Seq<u8>, lo: Seq<u8>, fm: int, f: Frame) -> int {
    u16_at(glyph_of(gl, lo, fm, f.gid as int), f.p + 2)
}

/// The frames below the top are waiting, each for the one above it; the
/// bottom one is glyph `gid` with `fuel` levels.
pub open spec fn stack_ok(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, gid: int, fuel: int) -> bool {
    &&& st.len() > 0 ==> st[0].gid == gid && st[0].fuel == fuel
    &&& forall|k: int| 0 <= k < st.len() - 1 ==> #[trigger] frame_ok(gl, lo, fm, n, st[k], true)
    &&& forall|k: int|
        0 <= k < st.len() - 1 ==> st[k + 1].gid == child_of(gl, lo, fm, #[trigger] st[k]) && st[k + 1].fuel
            == st[k].fuel - 1
}

/// The glyph and levels the top frame waits for (or the request itself
/// when there are no frames).
pub open spec fn want(gl: Seq<u8>, lo: Seq<u8>, fm: int, st: Seq<Frame>, gid: int, fuel: int) -> (int, int) {
    if st.len() == 0 {
        (gid, fuel)
    } else {
        (child_of(gl, lo, fm, st.last()), st.last().fuel - 1)
    }
}

/// The weight of a frame in the termination measure: what is left of its
/// slot in units of `b` to the power of its levels. A waiting frame has
/// used one more byte: the request it made weighs less than that unit.
pub open spec fn fwt(f: Frame, waiting: bool, b: int) -> int {
    (f.len - f.p - if waiting {
        1int
    } else {
        0int
    }) * pow(b, f.fuel as nat)
}

pub open spec fn fsum(st: Seq<Frame>, b: int) -> int
    decreases st.len(),
{
    if st.len() == 0 {
        0
    } else {
        fsum(st.drop_last(), b) + fwt(st.last(), true, b)
    }
}

proof fn lemma_fsum_nonneg(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, b: int)
    requires
        b > 0,
        forall|k: int| 0 <= k < st.len() ==> #[trigger] frame_ok(gl, lo, fm, n, st[k], true),
    ensures
        fsum(st, b) >= 0,
    decreases st.len(),
{
    if st.len() > 0 {
        let s2 = st.drop_last();
        assert forall|k: int| 0 <= k < s2.len() implies #[trigger] frame_ok(gl, lo, fm, n, s2[k], true) by {
            assert(s2[k] == st[k]);
        }
        lemma_fsum_nonneg(gl, lo, fm, n, s2, b);
        let f = st.last();
        assert(frame_ok(gl, lo, fm, n, st[st.len() - 1], true));
        lemma_pow_positive(b, f.fuel as nat);
        vstd::arithmetic::mul::lemma_mul_nonnegative((f.len - f.p - 1) as int, pow(b, f.fuel as nat));
    }
}

/// Popping the top frame: the one below it was waiting for it.
proof fn lemma_pop(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, gid: int, fuel: int, b: int)
    requires
        stack_ok(gl, lo, fm, n, st, gid, fuel),
        st.len() > 0,
    ensures
        stack_ok(gl, lo, fm, n, st.drop_last(), gid, fuel),
        st.len() > 1 ==> frame_ok(gl, lo, fm, n, st.drop_last().last(), true),
        want(gl, lo, fm, st.drop_last(), gid, fuel) == (st.last().gid as int, st.last().fuel as int),
        fsum(st, b) == fsum(st.drop_last(), b) + fwt(st.last(), true, b),
{
    let s2 = st.drop_last();
    assert forall|k: int| 0 <= k < s2.len() - 1 implies #[trigger] frame_ok(gl, lo, fm, n, s2[k], true) by {
        assert(s2[k] == st[k]);
    }
    assert forall|k: int|
        0 <= k < s2.len() - 1 implies s2[k + 1].gid == child_of(gl, lo, fm, #[trigger] s2[k]) && s2[k + 1].fuel
        == s2[k].fuel - 1 by {
        assert(s2[k] == st[k]);
        assert(s2[k + 1] == st[k + 1]);
    }
    if st.len() > 1 {
        let j = st.len() - 2;
        assert(s2.last() == st[j]);
        assert(frame_ok(gl, lo, fm, n, st[j], true));
        assert(st[j + 1].gid == child_of(gl, lo, fm, st[j]));
        assert(st[j + 1] == st.last());
    } else {
        assert(st[0] == st.last());
    }
}

/// Pushing a frame for what the top one waits for.
proof fn lemma_push(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, gid: int, fuel: int, f: Frame)
    requires
        stack_ok(gl, lo, fm, n, st, gid, fuel),
        st.len() > 0 ==> frame_ok(gl, lo, fm, n, st.last(), true),
        (f.gid as int, f.fuel as int) == want(gl, lo, fm, st, gid, fuel),
    ensures
        stack_ok(gl, lo, fm, n, st.push(f), gid, fuel),
        st.push(f).drop_last() == st,
        st.push(f).last() == f,
{
    let s2 = st.push(f);
    assert(s2.drop_last() =~= st);
    assert forall|k: int| 0 <= k < s2.len() - 1 implies #[trigger] frame_ok(gl, lo, fm, n, s2[k], true) by {
        assert(s2[k] == st[k]);
        if k == st.len() - 1 {
            assert(st[k] == st.last());
        }
    }
    assert forall|k: int|
        0 <= k < s2.len() - 1 implies s2[k + 1].gid == child_of(gl, lo, fm, #[trigger] s2[k]) && s2[k + 1].fuel
        == s2[k].fuel - 1 by {
        assert(s2[k] == st[k]);
        if k + 1 < st.len() {
            assert(s2[k + 1] == st[k + 1]);
        } else {
            assert(st[k] == st.last());
        }
    }
}

/// Replacing the top frame by one for the same glyph and levels.
proof fn lemma_set_top(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, gid: int, fuel: int, f: Frame)
    requires
        stack_ok(gl, lo, fm, n, st, gid, fuel),
        st.len() > 0,
        f.gid == st.last().gid,
        f.fuel == st.last().fuel,
    ensures
        stack_ok(gl, lo, fm, n, st.update(st.len() - 1, f), gid, fuel),
        st.update(st.len() - 1, f).drop_last() == st.drop_last(),
        st.update(st.len() - 1, f).last() == f,
{
    let s2 = st.update(st.len() - 1, f);
    assert(s2.drop_last() =~= st.drop_last());
    assert forall|k: int| 0 <= k < s2.len() - 1 implies #[trigger] frame_ok(gl, lo, fm, n, s2[k], true) by {
        assert(s2[k] == st[k]);
    }
    assert forall|k: int|
        0 <= k < s2.len() - 1 implies s2[k + 1].gid == child_of(gl, lo, fm, #[trigger] s2[k]) && s2[k + 1].fuel
        == s2[k].fuel - 1 by {
        assert(s2[k] == st[k]);
        if k + 1 < s2.len() - 1 {
            assert(s2[k + 1] == st[k + 1]);
        } else {
            assert(st[k + 1] == st.last());
        }
    }
    if st.len() == 1 {
        assert(st[0] == st.last());
    }
}

/// The frames below the top weigh nothing less than zero.
proof fn lemma_below(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, st: Seq<Frame>, gid: int, fuel: int, b: int)
    requires
        stack_ok(gl, lo, fm, n, st, gid, fuel),
        st.len() > 0,
        b > 0,
    ensures
        fsum(st.drop_last(), b) >= 0,
{
    let s2 = st.drop_last();
    assert forall|k: int| 0 <= k < s2.len() implies #[trigger] frame_ok(gl, lo, fm, n, s2[k], true) by {
        assert(s2[k] == st[k]);
    }
    lemma_fsum_nonneg(gl, lo, fm, n, s2, b);
}

/// The measure: the frames, the top one as `waiting` says, and, in
/// `Call` mode, the request being made.
pub open spec fn meas(st: Seq<Frame>, mode: u8, cf: u32, b: int, l: int) -> int {
    if mode == 0 {
        fsum(st, b) + (l + 1) * pow(b, cf as nat)
    } else if mode == 1 {
        fsum(st.drop_last(), b) + fwt(st.last(), false, b)
    } else {
        fsum(st, b)
    }
}

/// What a result says about glyph `gid` within `fuel` levels.
pub open spec fn res_ok(gl: Seq<u8>, lo: Seq<u8>, fm: int, n: int, gid: int, fuel: int, r: Option<InfoX>) -> bool {
    match r {
        Some(x) => glyph_info(gl, lo, fm, n, gid, fuel as nat) == Some(x@) && info_small(x) && x.depth <= fuel,
        None => glyph_info(gl, lo, fm, n, gid, fuel as nat) is None,
    }
}

/// Glyph `gid` within `fuel` levels, if that needs no component: from
/// the memo, or a simple or empty glyph, or no levels left. Otherwise the
/// frame to work it out with.
fn info_leaf(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, gid: u16, fuel: u32, memo: &mut Vec<Memo>) -> (r: Result<
    Option<InfoX>,
    Frame,
>)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        gid < ng,
        fuel <= MAX_COMPONENT_DEPTH,
        memos_ok(glyf@, loca@, fmt as int, ng as int, old(memo)@),
    ensures
        memos_ok(glyf@, loca@, fmt as int, ng as int, final(memo)@),
        match r {
            Ok(x) => res_ok(glyf@, loca@, fmt as int, ng as int, gid as int, fuel as int, x),
            Err(f) => frame_ok(glyf@, loca@, fmt as int, ng as int, f, false) && f.gid == gid && f.fuel == fuel
                && f.p == 10 && f.len <= glyf.len(),
        },
{
    let ghost gl = glyf@;
    let ghost lo = loca@;
    let ghost fm = fmt as int;
    let ghost n = ng as int;
    match memo[gid as usize] {
        Memo::Done(x) => {
            proof {
                lemma_info_fuel(gl, lo, fm, n, gid as int, x.depth as nat, fuel as nat);
            }
            return Ok(
                if x.depth <= fuel {
                    Some(x)
                } else {
                    None
                },
            );
        },
        Memo::Failed(k) => {
            if fuel <= k {
                proof {
                    if glyph_info(gl, lo, fm, n, gid as int, fuel as nat) is Some {
                        lemma_info_fuel(gl, lo, fm, n, gid as int, fuel as nat, k as nat);
                    }
                }
                return Ok(None);
            }
        },
        Memo::Unknown => {},
    }
    let g = glyph_slot(glyf, loca, fmt, ng, gid);
    if g.len() < 10 {
        let x = InfoX { points: 0, contours: 0, comps: 0, depth: 0, elems: 0 };
        memo.set(gid as usize, Memo::Done(x));
        return Ok(Some(x));
    }
    let nc = rdi16(g, 0);
    if nc >= 0 {
        let pts = if nc >= 1 && 10 + 2 * (nc as usize) <= g.len() {
            rd16(g, 10 + 2 * (nc as usize - 1)) as u32 + 1
        } else {
            0
        };
        let x = InfoX { points: pts, contours: nc as u32, comps: 0, depth: 0, elems: 0 };
        memo.set(gid as usize, Memo::Done(x));
        return Ok(Some(x));
    }
    if fuel == 0 {
        memo.set(gid as usize, Memo::Failed(0));
        return Ok(None);
    }
    Err(
        Frame {
            gid: gid,
            len: g.len(),
            p: 10,
            acc: InfoX { points: 0, contours: 0, comps: 0, depth: 0, elems: 0 },
            fuel: fuel,
        },
    )
}

/// The component the frame `f` asks for next, or `None` if there is none
/// where it should be (and so the glyph has no totals).
fn info_ask(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, f: Frame) -> (r: Option<u16>)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        frame_ok(glyf@, loca@, fmt as int, ng as int, f, false),
    ensures
        match r {
            Some(c) => frame_ok(glyf@, loca@, fmt as int, ng as int, f, true) && c == child_of(
                glyf@,
                loca@,
                fmt as int,
                f,
            ),
            None => glyph_info(glyf@, loca@, fmt as int, ng as int, f.gid as int, f.fuel as nat) is None,
        },
{
    let g = glyph_slot(glyf, loca, fmt, ng, f.gid);
    if 4 > g.len() - f.p {
        return None;
    }
    let child = rd16(g, f.p + 2);
    if child >= ng {
        return None;
    }
    Some(child)
}

/// Adds `res`, the totals of the component frame `f` asked for, to it:
/// the glyph's totals if that was its last component (or it has none),
/// otherwise the frame for the rest.
fn info_add(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, f: Frame, res: Option<InfoX>) -> (r: Result<
    Option<InfoX>,
    Frame,
>)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        frame_ok(glyf@, loca@, fmt as int, ng as int, f, true),
        res_ok(
            glyf@,
            loca@,
            fmt as int,
            ng as int,
            child_of(glyf@, loca@, fmt as int, f),
            f.fuel - 1,
            res,
        ),
    ensures
        match r {
            Ok(x) => res_ok(glyf@, loca@, fmt as int, ng as int, f.gid as int, f.fuel as int, x),
            Err(f2) => frame_ok(glyf@, loca@, fmt as int, ng as int, f2, false) && f2.gid == f.gid && f2.fuel
                == f.fuel && f2.len == f.len && f2.p >= f.p + 4,
        },
{
    let ghost gl = glyf@;
    let ghost lo = loca@;
    let ghost fm = fmt as int;
    let ghost n = ng as int;
    let g = glyph_slot(glyf, loca, fmt, ng, f.gid);
    match res {
        None => Ok(None),
        Some(c) => {
            let acc2 = InfoX {
                points: f.acc.points + c.points,
                contours: f.acc.contours + c.contours,
                comps: f.acc.comps + c.comps + 1,
                depth: if f.acc.depth > c.depth + 1 {
                    f.acc.depth
                } else {
                    c.depth + 1
                },
                elems: f.acc.elems + 1,
            };
            if acc2.points > 0xFFFF || acc2.contours > 0xFFFF || acc2.comps > 0xFFFF {
                return Ok(None);
            }
            let lob = rd8(g, f.p + 1);
            let x = comp_extra_sz(lob);
            if lob & 0x20 != 0 {
                if x > g.len() - f.p - 4 {
                    Ok(None)
                } else {
                    Err(Frame { gid: f.gid, len: f.len, p: f.p + 4 + x, acc: acc2, fuel: f.fuel })
                }
            } else {
                proof {
                    assert(comps_info(gl, lo, fm, n, g@, f.p as int, (f.fuel - 1) as nat, f.acc@) == Some(acc2@));
                    lemma_info_fuel(gl, lo, fm, n, f.gid as int, f.fuel as nat, acc2.depth as nat);
                }
                Ok(Some(acc2))
            }
        },
    }
}

/// Remembers what `r` says about glyph `gid` within `fuel` levels.
fn remember(
    memo: &mut Vec<Memo>,
    gid: u16,
    fuel: u32,
    r: Option<InfoX>,
    Ghost(gl): Ghost<Seq<u8>>,
    Ghost(lo): Ghost<Seq<u8>>,
    Ghost(fm): Ghost<int>,
    Ghost(n): Ghost<int>,
)
    requires
        gid < n,
        fuel <= MAX_COMPONENT_DEPTH,
        memos_ok(gl, lo, fm, n, old(memo)@),
        res_ok(gl, lo, fm, n, gid as int, fuel as int, r),
    ensures
        memos_ok(gl, lo, fm, n, final(memo)@),
{
    match r {
        Some(x) => {
            proof {
                lemma_info_fuel(gl, lo, fm, n, gid as int, fuel as nat, x.depth as nat);
            }
            memo.set(gid as usize, Memo::Done(x));
        },
        None => memo.set(gid as usize, Memo::Failed(fuel)),
    }
    proof {
        assert forall|i: int| 0 <= i < n implies memo_ok(gl, lo, fm, n, i, #[trigger] memo@[i]) by {
            if i != gid {
                assert(memo@[i] == old(memo)@[i]);
            }
        }
    }
}

/// Computes `glyph_info` for `gid` within `fuel` levels, remembering
/// what it learns. Components are followed with a stack of frames on the
/// heap, not by recursion, so nesting as deep as `fuel` costs no call
/// stack.
#[verifier::rlimit(100)]
pub fn info_x(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, gid: u16, fuel: u32, memo: &mut Vec<Memo>) -> (r:
    Option<InfoX>)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        gid < ng,
        fuel <= MAX_COMPONENT_DEPTH,
        memos_ok(glyf@, loca@, fmt as int, ng as int, old(memo)@),
    ensures
        memos_ok(glyf@, loca@, fmt as int, ng as int, final(memo)@),
        res_ok(glyf@, loca@, fmt as int, ng as int, gid as int, fuel as int, r),
{
    let ghost gl = glyf@;
    let ghost lo = loca@;
    let ghost fm = fmt as int;
    let ghost n = ng as int;
    let ghost l = glyf.len() as int;
    let ghost b = l + 2;
    let mut st: Vec<Frame> = Vec::new();
    // 0: evaluate the request (cg, cf); 1: the top frame asks for its
    // next component; 2: hand `res`, the totals of what the top frame
    // asked for, to it.
    let mut mode: u8 = 0;
    let mut cg: u16 = gid;
    let mut cf: u32 = fuel;
    let mut res: Option<InfoX> = None;
    loop
        invariant
            fmt <= 1,
            wf_loca(lo, fm, n, glyf.len() as int),
            gl == glyf@,
            lo == loca@,
            fm == fmt,
            n == ng,
            l == glyf.len(),
            b == l + 2,
            gid < ng,
            fuel <= MAX_COMPONENT_DEPTH,
            mode <= 2,
            memos_ok(gl, lo, fm, n, memo@),
            stack_ok(gl, lo, fm, n, st@, gid as int, fuel as int),
            mode != 1 ==> st@.len() > 0 ==> frame_ok(gl, lo, fm, n, st@.last(), true),
            mode == 0 ==> (cg as int, cf as int) == want(gl, lo, fm, st@, gid as int, fuel as int) && cg < ng
                && cf <= MAX_COMPONENT_DEPTH,
            mode == 1 ==> st@.len() > 0 && frame_ok(gl, lo, fm, n, st@.last(), false),
            mode == 2 ==> {
                let w = want(gl, lo, fm, st@, gid as int, fuel as int);
                res_ok(gl, lo, fm, n, w.0, w.1, res)
            },
        decreases meas(st@, mode, cf, b, l), 2 - mode,
    {
        let ghost st0 = st@;
        let ghost m0 = meas(st@, mode, cf, b, l);
        let ghost md0 = mode;
        let ghost cf0 = cf;
        proof {
            lemma_pow_positive(b, cf as nat);
            if st@.len() > 0 {
                lemma_pow_positive(b, st@.last().fuel as nat);
                lemma_below(gl, lo, fm, n, st@, gid as int, fuel as int, b);
            }
        }
        if mode == 0 {
            match info_leaf(glyf, loca, fmt, ng, cg, cf, memo) {
                Ok(r) => {
                    res = r;
                    mode = 2;
                    proof {
                        vstd::arithmetic::mul::lemma_mul_strictly_positive(l + 1, pow(b, cf as nat));
                        assert(m0 == fsum(st0, b) + (l + 1) * pow(b, cf as nat));
                        assert(meas(st@, mode, cf, b, l) == fsum(st0, b));
                    }
                },
                Err(f) => {
                    proof {
                        lemma_push(gl, lo, fm, n, st0, gid as int, fuel as int, f);
                        // The frame weighs less than the request.
                        vstd::arithmetic::mul::lemma_mul_inequality((f.len - 10) as int, l + 1, pow(b, cf as nat));
                    }
                    st.push(f);
                    mode = 1;
                    proof {
                        assert(fwt(f, false, b) < (l + 1) * pow(b, cf as nat)) by (nonlinear_arith)
                            requires
                                fwt(f, false, b) == (f.len - 10) * pow(b, cf as nat),
                                f.len <= l,
                                pow(b, cf as nat) > 0,
                        ;
                        assert(m0 == fsum(st0, b) + (l + 1) * pow(b, cf as nat));
                        assert(meas(st@, mode, cf, b, l) == fsum(st0, b) + fwt(f, false, b));
                    }
                },
            }
        } else if mode == 1 {
            let k = st.len() - 1;
            let f = st[k];
            proof {
                assert(st@[k as int] == st@.last());
            }
            match info_ask(glyf, loca, fmt, ng, f) {
                None => {
                    memo.set(f.gid as usize, Memo::Failed(f.fuel));
                    proof {
                        lemma_pop(gl, lo, fm, n, st0, gid as int, fuel as int, b);
                        lemma_mul_nonneg_frame(f, b);
                    }
                    st.pop();
                    res = None;
                    mode = 2;
                    proof {
                        assert(st@ =~= st0.drop_last());
                        assert(m0 == fsum(st0.drop_last(), b) + fwt(f, false, b));
                        assert(meas(st@, mode, cf, b, l) == fsum(st0.drop_last(), b));
                    }
                },
                Some(child) => {
                    mode = 0;
                    cg = child;
                    cf = f.fuel - 1;
                    proof {
                        lemma_pop(gl, lo, fm, n, st0, gid as int, fuel as int, b);
                        lemma_pow_positive(b, cf as nat);
                        // Asking costs the frame a unit, more than the request
                        // weighs.
                        lemma_pow_adds(b, 1, cf as nat);
                        lemma_pow1(b);
                        assert(fwt(f, false, b) == fwt(f, true, b) + b * pow(b, cf as nat)) by (nonlinear_arith)
                            requires
                                fwt(f, false, b) == (f.len - f.p) * pow(b, f.fuel as nat),
                                fwt(f, true, b) == (f.len - f.p - 1) * pow(b, f.fuel as nat),
                                pow(b, f.fuel as nat) == b * pow(b, cf as nat),
                        ;
                        assert(b * pow(b, cf as nat) > (l + 1) * pow(b, cf as nat)) by (nonlinear_arith)
                            requires
                                b == l + 2,
                                pow(b, cf as nat) > 0,
                        ;
                        assert(m0 == fsum(st0.drop_last(), b) + fwt(f, false, b));
                        assert(meas(st@, mode, cf, b, l) == fsum(st0, b) + (l + 1) * pow(b, cf as nat));
                    }
                },
            }
        } else {
            if st.len() == 0 {
                return res;
            }
            let k = st.len() - 1;
            let f = st[k];
            proof {
                assert(st@[k as int] == st@.last());
                lemma_pop(gl, lo, fm, n, st0, gid as int, fuel as int, b);
            }
            match info_add(glyf, loca, fmt, ng, f, res) {
                Ok(r) => {
                    remember(memo, f.gid, f.fuel, r, Ghost(gl), Ghost(lo), Ghost(fm), Ghost(n));
                    proof {
                        vstd::arithmetic::mul::lemma_mul_strictly_positive(
                            (f.len - f.p - 1) as int,
                            pow(b, f.fuel as nat),
                        );
                    }
                    st.pop();
                    res = r;
                    proof {
                        assert(st@ =~= st0.drop_last());
                        assert(m0 == fsum(st0, b));
                        assert(meas(st@, mode, cf, b, l) == fsum(st0.drop_last(), b));
                    }
                },
                Err(f2) => {
                    proof {
                        lemma_set_top(gl, lo, fm, n, st0, gid as int, fuel as int, f2);
                    }
                    st.set(k, f2);
                    mode = 1;
                    proof {
                        assert(st@ =~= st0.update(st0.len() - 1, f2));
                        assert(fwt(f2, false, b) < fwt(f, true, b)) by (nonlinear_arith)
                            requires
                                fwt(f2, false, b) == (f.len - f2.p) * pow(b, f.fuel as nat),
                                fwt(f, true, b) == (f.len - f.p - 1) * pow(b, f.fuel as nat),
                                f2.p >= f.p + 4,
                                pow(b, f.fuel as nat) > 0,
                        ;
                        assert(m0 == fsum(st0, b));
                        assert(st@.drop_last() == st0.drop_last());
                        assert(st@.last() == f2);
                        assert(meas(st@, mode, cf, b, l) == fsum(st0.drop_last(), b) + fwt(f2, false, b));
                    }
                },
            }
        }
    }
}

proof fn lemma_mul_nonneg_frame(f: Frame, b: int)
    requires
        b > 0,
        f.p <= f.len,
    ensures
        fwt(f, false, b) >= 0,
{
    lemma_pow_positive(b, f.fuel as nat);
    vstd::arithmetic::mul::lemma_mul_nonnegative((f.len - f.p) as int, pow(b, f.fuel as nat));
}

/// The length of the instructions of a composite glyph: see
/// [`comp_ilen`].
fn comp_ilen_x(g: &[u8]) -> (r: u16)
    requires
        g.len() >= 10,
    ensures
        r as int == comp_ilen(g@, 10),
{
    let mut p: usize = 10;
    loop
        invariant
            10 <= p <= g.len(),
            comp_ilen(g@, 10) == comp_ilen(g@, p as int),
        decreases g.len() - p,
    {
        if 4 > g.len() - p {
            return 0;
        }
        let hi = rd8(g, p);
        let lo = rd8(g, p + 1);
        let x = comp_extra_sz(lo);
        if 4 + x > g.len() - p {
            return 0;
        }
        let q = p + 4 + x;
        if lo & 0x20 != 0 {
            p = q;
        } else if hi & 0x01 != 0 && 2 <= g.len() - q {
            return rd16(g, q);
        } else {
            return 0;
        }
    }
}

fn glyph_ilen_x(g: &[u8]) -> (r: u16)
    requires
        g.len() >= 10,
    ensures
        r as int == glyph_ilen(g@),
{
    let nc = rdi16(g, 0);
    if nc >= 1 {
        if 12 + 2 * (nc as usize) <= g.len() {
            rd16(g, 10 + 2 * (nc as usize))
        } else {
            0
        }
    } else {
        comp_ilen_x(g)
    }
}

/// A fresh memo table for `ng` glyphs.
pub fn new_memo(ng: u16, Ghost(glyf): Ghost<Seq<u8>>, Ghost(loca): Ghost<Seq<u8>>, Ghost(fmt): Ghost<int>) -> (memo:
    Vec<Memo>)
    ensures
        memos_ok(glyf, loca, fmt, ng as int, memo@),
{
    let mut memo: Vec<Memo> = Vec::new();
    let mut k: usize = 0;
    while k < ng as usize
        invariant
            k <= ng,
            memo@.len() == k,
            forall|i: int| 0 <= i < k ==> memo@[i] is Unknown,
        decreases ng - k,
    {
        memo.push(Memo::Unknown);
        k += 1;
    }
    memo
}

/// Decides [`glyph_fits`] for glyph `i`.
fn fits_x(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, maxp: &[u8], i: u16, memo: &mut Vec<Memo>) -> (b: bool)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        i < ng,
        maxp.len() >= 32,
        memos_ok(glyf@, loca@, fmt as int, ng as int, old(memo)@),
    ensures
        memos_ok(glyf@, loca@, fmt as int, ng as int, final(memo)@),
        b == glyph_fits(glyf@, loca@, fmt as int, ng as int, maxp@, i as int),
{
    let g = glyph_slot(glyf, loca, fmt, ng, i);
    if g.len() < 10 {
        return true;
    }
    if glyph_ilen_x(g) > rd16(maxp, 26) {
        return false;
    }
    match info_x(glyf, loca, fmt, ng, i, MAX_COMPONENT_DEPTH as u32, memo) {
        Some(x) => {
            if rdi16(g, 0) >= 0 {
                x.points <= rd16(maxp, 6) as u32 && x.contours <= rd16(maxp, 8) as u32
            } else {
                x.points <= rd16(maxp, 10) as u32 && x.contours <= rd16(maxp, 12) as u32 && x.elems <= rd16(
                    maxp,
                    28,
                ) as u32 && x.depth <= rd16(maxp, 30) as u32
            }
        },
        None => false,
    }
}

/// Decides `wf_glyf_limits`.
pub fn check_glyf_limits(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16, maxp: &[u8]) -> (b: bool)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
        maxp.len() >= 32,
    ensures
        b == wf_glyf_limits(glyf@, loca@, fmt as int, ng as int, maxp@),
{
    let mut memo = new_memo(ng, Ghost(glyf@), Ghost(loca@), Ghost(fmt as int));
    let mut i: u16 = 0;
    while i < ng
        invariant
            i <= ng,
            fmt <= 1,
            wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
            maxp.len() >= 32,
            memos_ok(glyf@, loca@, fmt as int, ng as int, memo@),
            forall|j: int|
                0 <= j < i ==> #[trigger] glyph_fits(glyf@, loca@, fmt as int, ng as int, maxp@, j),
        decreases ng - i,
    {
        if !fits_x(glyf, loca, fmt, ng, maxp, i, &mut memo) {
            return false;
        }
        i += 1;
    }
    true
}

/// The largest values any glyph needs of the `maxp` fields that
/// `glyph_fits` reads.
pub struct Limits {
    pub points: u32,
    pub contours: u32,
    pub cpoints: u32,
    pub ccontours: u32,
    pub ilen: u32,
    pub elems: u32,
    pub depth: u32,
}

fn max32(a: u32, b: u32) -> (r: u32)
    ensures
        r == a || r == b,
{
    if a > b {
        a
    } else {
        b
    }
}

/// Works out what `maxp` has to say for every glyph to fit. `None` if some
/// glyph has no totals (a component cycle, nesting too deep, a missing
/// component, or totals past 0xFFFF). Used to build `maxp`; the result is
/// then checked by [`check_glyf_limits`].
pub fn glyf_limits(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16) -> (r: Option<Limits>)
    requires
        fmt <= 1,
        wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
{
    let mut memo = new_memo(ng, Ghost(glyf@), Ghost(loca@), Ghost(fmt as int));
    let mut l = Limits { points: 0, contours: 0, cpoints: 0, ccontours: 0, ilen: 0, elems: 0, depth: 0 };
    let mut i: u16 = 0;
    while i < ng
        invariant
            i <= ng,
            fmt <= 1,
            wf_loca(loca@, fmt as int, ng as int, glyf.len() as int),
            memos_ok(glyf@, loca@, fmt as int, ng as int, memo@),
        decreases ng - i,
    {
        let g = glyph_slot(glyf, loca, fmt, ng, i);
        if g.len() >= 10 {
            let x = info_x(glyf, loca, fmt, ng, i, MAX_COMPONENT_DEPTH as u32, &mut memo)?;
            l.ilen = max32(l.ilen, glyph_ilen_x(g) as u32);
            if rdi16(g, 0) >= 0 {
                l.points = max32(l.points, x.points);
                l.contours = max32(l.contours, x.contours);
            } else {
                l.cpoints = max32(l.cpoints, x.points);
                l.ccontours = max32(l.ccontours, x.contours);
                l.elems = max32(l.elems, x.elems);
                l.depth = max32(l.depth, x.depth);
            }
        }
        i += 1;
    }
    Some(l)
}

} // verus!
