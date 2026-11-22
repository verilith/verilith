//! Verified check of the composite-glyph graph and of `maxp`'s limits:
//! decides [`wf_glyf_limits`] exactly.
//!
//! [`glyph_info`] is defined with a budget of nesting levels. The checker
//! does not recompute a glyph for every budget: it remembers each glyph's
//! totals, and the lemmas here show that is sound, because a glyph's
//! totals do not depend on the budget once the budget covers its depth.
use crate::glyf::*;
use crate::prims::*;
use crate::spec::*;
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

/// Computes [`glyph_info`] for `gid` within `fuel` levels, remembering
/// what it learns.
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
        match r {
            Some(x) => glyph_info(glyf@, loca@, fmt as int, ng as int, gid as int, fuel as nat) == Some(
                x@,
            ) && info_small(x) && x.depth <= fuel,
            None => glyph_info(glyf@, loca@, fmt as int, ng as int, gid as int, fuel as nat) is None,
        },
    decreases fuel,
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
            return if x.depth <= fuel {
                Some(x)
            } else {
                None
            };
        },
        Memo::Failed(k) => {
            if fuel <= k {
                proof {
                    if glyph_info(gl, lo, fm, n, gid as int, fuel as nat) is Some {
                        lemma_info_fuel(gl, lo, fm, n, gid as int, fuel as nat, k as nat);
                    }
                }
                return None;
            }
        },
        Memo::Unknown => {},
    }
    let g = glyph_slot(glyf, loca, fmt, ng, gid);
    if g.len() < 10 {
        let x = InfoX { points: 0, contours: 0, comps: 0, depth: 0, elems: 0 };
        memo.set(gid as usize, Memo::Done(x));
        return Some(x);
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
        return Some(x);
    }
    if fuel == 0 {
        memo.set(gid as usize, Memo::Failed(0));
        return None;
    }
    let mut acc = InfoX { points: 0, contours: 0, comps: 0, depth: 0, elems: 0 };
    let mut p: usize = 10;
    loop
        invariant
            fmt <= 1,
            wf_loca(lo, fm, n, glyf.len() as int),
            gl == glyf@,
            lo == loca@,
            fm == fmt,
            n == ng,
            gid < ng,
            1 <= fuel <= MAX_COMPONENT_DEPTH,
            memos_ok(gl, lo, fm, n, memo@),
            g@ == glyph_of(gl, lo, fm, gid as int),
            g.len() >= 10,
            i16_at(g@, 0) < 0,
            10 <= p <= g.len(),
            info_small(acc),
            acc.points <= 0xFFFF,
            acc.elems <= acc.comps,
            acc.depth <= fuel,
            glyph_info(gl, lo, fm, n, gid as int, fuel as nat) == comps_info(
                gl,
                lo,
                fm,
                n,
                g@,
                p as int,
                (fuel - 1) as nat,
                acc@,
            ),
        decreases g.len() - p,
    {
        if 4 > g.len() - p {
            memo.set(gid as usize, Memo::Failed(fuel));
            return None;
        }
        let child = rd16(g, p + 2);
        if child >= ng {
            memo.set(gid as usize, Memo::Failed(fuel));
            return None;
        }
        let c = match info_x(glyf, loca, fmt, ng, child, fuel - 1, memo) {
            Some(c) => c,
            None => {
                memo.set(gid as usize, Memo::Failed(fuel));
                return None;
            },
        };
        let acc2 = InfoX {
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
        if acc2.points > 0xFFFF || acc2.contours > 0xFFFF || acc2.comps > 0xFFFF {
            memo.set(gid as usize, Memo::Failed(fuel));
            return None;
        }
        let lob = rd8(g, p + 1);
        let x = comp_extra_sz(lob);
        if lob & 0x20 != 0 {
            if x > g.len() - p - 4 {
                memo.set(gid as usize, Memo::Failed(fuel));
                return None;
            }
            acc = acc2;
            p = p + 4 + x;
        } else {
            proof {
                assert(comps_info(gl, lo, fm, n, g@, p as int, (fuel - 1) as nat, acc@) == Some(acc2@));
                lemma_info_fuel(gl, lo, fm, n, gid as int, fuel as nat, acc2.depth as nat);
            }
            memo.set(gid as usize, Memo::Done(acc2));
            return Some(acc2);
        }
    }
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

/// Decides [`wf_glyf_limits`].
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
/// [`glyph_fits`] reads.
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
