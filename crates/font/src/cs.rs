//! Verified check of the CFF charstrings: decides
//! [`wf_charstrings`] exactly, by running every glyph's program the way
//! the specification does.
use crate::cff::*;
use crate::prims::*;
use crate::spec::*;
use crate::spec_cff::*;
use crate::spec_cs::*;
use vstd::prelude::*;

verus! {

/// The executable counterpart of [`Cs`].
pub struct CsX {
    pub stack: Vec<i32>,
    pub width: bool,
    pub stems: usize,
    pub hint: u8,
    pub ops: u32,
}

impl CsX {
    pub open spec fn v(&self) -> Cs {
        Cs {
            stack: self.stack@,
            width: self.width,
            stems: self.stems as int,
            hint: self.hint as int,
            ops: self.ops as int,
        }
    }

    pub open spec fn ok(&self) -> bool {
        self.stack@.len() <= 48 && self.stems <= 96 && self.ops <= MAX_CS_OPS
    }
}

pub enum CsTokX {
    Num(i32, usize),
    Op(u32, usize),
    Bad,
}

impl CsTokX {
    pub open spec fn v(&self) -> CsTok {
        match *self {
            CsTokX::Num(v, q) => CsTok::Num(v, q as int),
            CsTokX::Op(o, q) => CsTok::Op(o as int, q as int),
            CsTokX::Bad => CsTok::Bad,
        }
    }
}

fn cs_tok_x(t: &[u8], p: usize, end: usize) -> (r: CsTokX)
    requires
        p < end <= t.len(),
    ensures
        r.v() == cs_tok(t@, p as int, end as int),
        r matches CsTokX::Num(_, q) ==> p < q <= end,
        r matches CsTokX::Op(_, q) ==> p < q <= end,
{
    let b = rd8(t, p);
    if b == 12 {
        if end - p >= 2 {
            CsTokX::Op(0xC00 + rd8(t, p + 1) as u32, p + 2)
        } else {
            CsTokX::Bad
        }
    } else if b == 28 {
        if end - p >= 3 {
            CsTokX::Num(rdi16(t, p + 1) as i32, p + 3)
        } else {
            CsTokX::Bad
        }
    } else if b <= 31 {
        CsTokX::Op(b as u32, p + 1)
    } else if b <= 246 {
        CsTokX::Num(b as i32 - 139, p + 1)
    } else if b <= 250 {
        if end - p >= 2 {
            CsTokX::Num((b as i32 - 247) * 256 + rd8(t, p + 1) as i32 + 108, p + 2)
        } else {
            CsTokX::Bad
        }
    } else if b <= 254 {
        if end - p >= 2 {
            CsTokX::Num(-(b as i32 - 251) * 256 - rd8(t, p + 1) as i32 - 108, p + 2)
        } else {
            CsTokX::Bad
        }
    } else {
        if end - p >= 5 {
            CsTokX::Num(UNK, p + 5)
        } else {
            CsTokX::Bad
        }
    }
}

/// Pops `k` numbers and pushes `m` untracked ones.
fn replace(st: &mut CsX, k: usize, m: usize)
    requires
        old(st).ok(),
        k <= old(st).stack@.len(),
        1 <= k <= 4,
        m <= 2,
        old(st).stack@.len() - k + m <= 48,
    ensures
        final(st).ok(),
        final(st).width == old(st).width,
        final(st).stems == old(st).stems,
        final(st).hint == old(st).hint,
        final(st).ops == old(st).ops,
        m == 0 ==> final(st).stack@ == old(st).stack@.subrange(0, old(st).stack@.len() - k),
        m == 1 ==> final(st).stack@ == old(st).stack@.subrange(0, old(st).stack@.len() - k).push(UNK),
        m == 2 ==> final(st).stack@ == old(st).stack@.subrange(0, old(st).stack@.len() - k).push(UNK).push(
            UNK,
        ),
{
    let n = st.stack.len();
    st.stack.truncate(n - k);
    if m >= 1 {
        st.stack.push(UNK);
    }
    if m >= 2 {
        st.stack.push(UNK);
    }
}

/// The exec counterpart of [`cs_op`].
fn cs_op_x(op: u32, st: &mut CsX) -> (r: Option<usize>)
    requires
        old(st).ok(),
    ensures
        match cs_op(op as int, old(st).v()) {
            Some((s, k)) => r == Some(k as usize) && final(st).v() == s && final(st).ok() && 0 <= k <= 12,
            None => r is None && final(st).ok(),
        },
{
    let n = st.stack.len();
    let w = st.width;
    let ghost s0 = st.stack@;
    if op == 1 || op == 18 {
        if n >= 2 && st.hint == 0 && (n % 2 == 0 || !w) && st.stems + n / 2 <= 96 {
            st.stems = st.stems + n / 2;
            st.width = true;
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 3 || op == 23 {
        if n >= 2 && st.hint <= 1 && (n % 2 == 0 || !w) && st.stems + n / 2 <= 96 {
            st.stems = st.stems + n / 2;
            st.width = true;
            st.hint = 1;
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 21 {
        if n == 2 || (!w && n == 3) {
            st.width = true;
            st.hint = 3;
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 4 || op == 22 {
        if n == 1 || (!w && n == 2) {
            st.width = true;
            st.hint = 3;
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 19 || op == 20 {
        let stems = if n == 0 || (!w && n == 1) {
            st.stems
        } else {
            st.stems + n / 2
        };
        if (n == 0 || !w || n % 2 == 0) && 1 <= stems && stems <= 96 && (op == 19 || st.hint <= 2) {
            st.stems = stems;
            st.width = true;
            st.hint = if op == 19 {
                3
            } else {
                2
            };
            st.stack.clear();
            return Some((stems + 7) / 8);
        }
        None
    } else if op == 5 {
        if w && n >= 2 && n % 2 == 0 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 6 || op == 7 {
        if w && n >= 1 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 8 {
        if w && n >= 6 && n % 6 == 0 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 24 {
        if w && n >= 8 && (n - 2) % 6 == 0 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 25 {
        if w && n >= 8 && n % 2 == 0 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 26 || op == 27 {
        if w && n >= 4 && (n % 4 == 0 || n % 4 == 1) {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 30 || op == 31 {
        if w && n >= 4 && (n % 8 == 0 || n % 8 == 1 || n % 8 == 4 || n % 8 == 5) {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 0xC00 {
        if n == 0 {
            return Some(0);
        }
        None
    } else if op == 0xC03 || op == 0xC04 || op == 0xC0A || op == 0xC0B || op == 0xC0C || op == 0xC0F
        || op == 0xC18 {
        if n >= 2 {
            replace(st, 2, 1);
            assert(st.stack@ =~= s0.drop_last().drop_last().push(UNK));
            return Some(0);
        }
        None
    } else if op == 0xC05 || op == 0xC09 || op == 0xC0E || op == 0xC1A {
        if n >= 1 {
            replace(st, 1, 1);
            assert(st.stack@ =~= s0.drop_last().push(UNK));
            return Some(0);
        }
        None
    } else if op == 0xC12 {
        if n >= 1 {
            replace(st, 1, 0);
            assert(st.stack@ =~= s0.drop_last());
            return Some(0);
        }
        None
    } else if op == 0xC16 {
        if n >= 4 {
            replace(st, 4, 1);
            assert(st.stack@ =~= s0.drop_last().drop_last().drop_last().drop_last().push(UNK));
            return Some(0);
        }
        None
    } else if op == 0xC1B {
        if 1 <= n && n < 48 {
            replace(st, 1, 2);
            assert(st.stack@ =~= s0.drop_last().push(UNK).push(UNK));
            return Some(0);
        }
        None
    } else if op == 0xC1C {
        if n >= 2 {
            replace(st, 2, 2);
            assert(st.stack@ =~= s0.drop_last().drop_last().push(UNK).push(UNK));
            return Some(0);
        }
        None
    } else if op == 0xC22 {
        if w && n == 7 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 0xC23 {
        if w && n == 13 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 0xC24 {
        if w && n == 9 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else if op == 0xC25 {
        if w && n == 11 {
            st.stack.clear();
            return Some(0);
        }
        None
    } else {
        None
    }
}

/// The exec counterpart of [`cs_subr`].
fn subr_x(t: &[u8], idx: usize, top: i32) -> (r: Option<(usize, usize)>)
    requires
        idx != 0 ==> wf_index(t@, idx as int),
    ensures
        match cs_subr(t@, idx as int, top) {
            Some((a, b)) => r == Some((a as usize, b as usize)) && 0 <= a <= b <= t.len(),
            None => r is None,
        },
{
    if idx == 0 || top == UNK {
        return None;
    }
    let cnt = rd16(t, idx) as i64;
    let bias: i64 = if cnt < 1240 {
        107
    } else if cnt < 33900 {
        1131
    } else {
        32768
    };
    let k = top as i64 + bias;
    if k < 0 || k >= cnt {
        return None;
    }
    let (a, b) = index_range_x(t, idx, k as usize);
    if b - a > 65535 {
        None
    } else {
        Some((a, b))
    }
}

/// The exec counterpart of [`cs_run`]: 0 for a failure, 1 for a return,
/// 2 for `endchar`.
fn run_x(t: &[u8], g: usize, l: usize, p0: usize, end: usize, depth: usize, st: &mut CsX) -> (r:
    u8)
    requires
        old(st).ok(),
        end <= t.len(),
        g != 0 ==> wf_index(t@, g as int),
        l != 0 ==> wf_index(t@, l as int),
        depth <= 10,
    ensures
        final(st).ok(),
        match cs_run(t@, g as int, l as int, p0 as int, end as int, depth as int, old(st).v()) {
            CsRes::Fail => r == 0,
            CsRes::Ret(s) => r == 1 && final(st).v() == s,
            CsRes::End(s) => r == 2 && final(st).v() == s,
        },
    decreases 10 - depth,
{
    let mut p = p0;
    let ghost whole = cs_run(
        t@,
        g as int,
        l as int,
        p0 as int,
        end as int,
        depth as int,
        old(st).v(),
    );
    loop
        invariant
            st.ok(),
            end <= t.len(),
            g != 0 ==> wf_index(t@, g as int),
            l != 0 ==> wf_index(t@, l as int),
            depth <= 10,
            cs_run(t@, g as int, l as int, p as int, end as int, depth as int, st.v()) == whole,
            whole == cs_run(
                t@,
                g as int,
                l as int,
                p0 as int,
                end as int,
                depth as int,
                old(st).v(),
            ),
        decreases end - p,
    {
        if p >= end {
            return 0;
        }
        let ghost s = st.v();
        match cs_tok_x(t, p, end) {
            CsTokX::Bad => {
                return 0;
            },
            CsTokX::Num(v, q) => {
                if st.stack.len() >= 48 {
                    return 0;
                }
                st.stack.push(v);
                assert(st.v() == Cs { stack: s.stack.push(v), ..s });
                p = q;
            },
            CsTokX::Op(op, q) => {
                if st.ops >= MAX_CS_OPS {
                    return 0;
                }
                st.ops = st.ops + 1;
                let ghost s1 = st.v();
                assert(s1 == Cs { ops: s.ops + 1, ..s });
                if op == 11 {
                    return 1;
                }
                if op == 14 {
                    return 2;
                }
                if op == 10 || op == 29 {
                    let n = st.stack.len();
                    if n == 0 || depth >= 10 {
                        return 0;
                    }
                    let top = st.stack[n - 1];
                    let idx = if op == 10 {
                        l
                    } else {
                        g
                    };
                    match subr_x(t, idx, top) {
                        None => {
                            return 0;
                        },
                        Some((a, b)) => {
                            st.stack.pop();
                            assert(st.v() == Cs { stack: s.stack.drop_last(), ..s1 });
                            let r = run_x(t, g, l, a, b, depth + 1, st);
                            if r != 1 {
                                return r;
                            }
                            p = q;
                        },
                    }
                } else {
                    match cs_op_x(op, st) {
                        Some(k) => {
                            if k > end - q {
                                return 0;
                            }
                            p = q + k;
                        },
                        None => {
                            return 0;
                        },
                    }
                }
            },
        }
    }
}

/// The exec counterpart of [`priv_subrs`].
fn priv_subrs_x(t: &[u8], size: i64, off: i64) -> (r: usize)
    requires
        wf_private(t@, size as int, off as int),
    ensures
        r == priv_subrs(t@, size as int, off as int),
        r != 0 ==> wf_index(t@, r as int),
{
    let o = off as usize;
    match priv_read_x(slice(t, o, o + size as usize)) {
        Some(d) => {
            if d.has_subrs {
                (off as i128 + d.subrs as i128) as usize
            } else {
                0
            }
        },
        None => 0,
    }
}

/// The local subroutine INDEX of every Font DICT.
fn fd_table(t: &[u8], fa: usize, nfd: usize, sm: usize) -> (v: Vec<usize>)
    requires
        wf_index(t@, fa as int),
        nfd == index_count(t@, fa as int),
        forall|k: int| 0 <= k < nfd ==> #[trigger] wf_fontdict(t@, fa as int, k, sm as int),
    ensures
        v@.len() == nfd,
        forall|k: int|
            0 <= k < nfd ==> (#[trigger] v@[k]) == fd_subrs(t@, fa as int, k, sm as int) && (v@[k] != 0
                ==> wf_index(t@, v@[k] as int)),
{
    let mut v: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < nfd
        invariant
            i <= nfd,
            v@.len() == i,
            wf_index(t@, fa as int),
            nfd == index_count(t@, fa as int),
            forall|k: int| 0 <= k < nfd ==> #[trigger] wf_fontdict(t@, fa as int, k, sm as int),
            forall|k: int|
                0 <= k < i ==> (#[trigger] v@[k]) == fd_subrs(t@, fa as int, k, sm as int) && (v@[k] != 0
                    ==> wf_index(t@, v@[k] as int)),
        decreases nfd - i,
    {
        assert(wf_fontdict(t@, fa as int, i as int, sm as int));
        let x = match dict_read_x(index_obj_x(t, fa, i), true, sm, t.len()) {
            Some(d) => priv_subrs_x(t, d.priv_size, d.priv_off),
            None => 0,
        };
        v.push(x);
        i += 1;
    }
    v
}

/// Where range `j` of a format 3 FDSelect at `p` starts.
pub open spec fn fds_first(t: Seq<u8>, p: int, j: int) -> int {
    u16_at(t, p + 3 + 3 * j)
}

proof fn lemma_fds_mono(t: Seq<u8>, p: int, n: int, nfd: int, a: int, b: int)
    requires
        forall|k: int| 0 <= k < n ==> #[trigger] fds_range_ok(t, p, k, nfd),
        0 <= a <= b <= n,
    ensures
        fds_first(t, p, a) <= fds_first(t, p, b),
    decreases b - a,
{
    if a < b {
        assert(fds_range_ok(t, p, b - 1, nfd));
        lemma_fds_mono(t, p, n, nfd, a, b - 1);
    }
}

proof fn lemma_fds3(t: Seq<u8>, p: int, n: int, nfd: int, c: int, k: int, i: int)
    requires
        forall|j: int| 0 <= j < n ==> #[trigger] fds_range_ok(t, p, j, nfd),
        0 <= c <= k < n,
        fds_first(t, p, c) <= i < fds_first(t, p, c + 1),
    ensures
        fds3_fd(t, p, k, i) == t[p + 3 + 3 * c + 2],
    decreases k - c,
{
    if k > c {
        lemma_fds_mono(t, p, n, nfd, c + 1, k);
        lemma_fds3(t, p, n, nfd, c, k - 1, i);
    }
}

/// The Font DICT of glyph `i`, and the FDSelect range it was found in
/// (to start the search for the next glyph from).
fn glyph_fd_x(t: &[u8], p: usize, ng: u16, nfd: usize, i: usize, c0: usize) -> (r: (usize, usize))
    requires
        wf_fdselect(t@, p as int, ng as int, nfd as int),
        i < ng,
        t@[p as int] != 0 ==> c0 < u16_at(t@, p + 1) && fds_first(t@, p as int, c0 as int) <= i,
    ensures
        r.0 == glyph_fd(t@, p as int, i as int),
        r.0 < nfd,
        t@[p as int] != 0 ==> r.1 < u16_at(t@, p + 1) && fds_first(t@, p as int, r.1 as int) <= i,
{
    if rd8(t, p) == 0 {
        assert(p + 1 + ng <= t.len());
        return (rd8(t, p + 1 + i) as usize, c0);
    }
    let n = rd16(t, p + 1) as usize;
    let mut c = c0;
    while c + 1 < n && rd16(t, p + 3 + 3 * (c + 1)) as usize <= i
        invariant
            c < n,
            n == u16_at(t@, p + 1),
            p + 5 + 3 * n <= t.len(),
            fds_first(t@, p as int, c as int) <= i,
        decreases n - c,
    {
        c += 1;
    }
    proof {
        lemma_fds3(t@, p as int, n as int, nfd as int, c as int, n - 1, i as int);
        assert(fds_range_ok(t@, p as int, c as int, nfd as int));
    }
    (rd8(t, p + 3 + 3 * c + 2) as usize, c)
}

/// Once a glyph fails, the font fails.
proof fn lemma_cs_all_none(t: Seq<u8>, top: Dict, g: int, k: int, n: int, sm: int)
    requires
        0 <= k <= n,
        cs_all(t, top, g, k, sm) is None,
    ensures
        cs_all(t, top, g, n, sm) is None,
    decreases n - k,
{
    if k < n {
        lemma_cs_all_none(t, top, g, k, n - 1, sm);
    }
}

/// Decides [`wf_charstrings`], given the rest of the table is well formed.
pub fn check_charstrings(t: &[u8], d: &DictX, g: usize, ng: u16, sm: usize) -> (b: bool)
    requires
        wf_index(t@, g as int),
        wf_cff_parts(t@, d@, ng as int, sm as int),
    ensures
        b == wf_charstrings(t@, d@, g as int, ng as int, sm as int),
{
    let cs = d.charstrings as usize;
    let n = ng as usize;
    let mut fdl: Vec<usize> = Vec::new();
    let mut l0: usize = 0;
    let mut fsel: usize = 0;
    let mut nfd: usize = 0;
    if d.cid {
        let fa = d.fdarray as usize;
        nfd = rd16(t, fa) as usize;
        fdl = fd_table(t, fa, nfd, sm);
        fsel = d.fdselect as usize;
    } else {
        l0 = priv_subrs_x(t, d.priv_size, d.priv_off);
    }
    let mut cur: usize = 0;
    let mut st = CsX { stack: Vec::new(), width: false, stems: 0, hint: 0, ops: 0 };
    let ops: u32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ng,
            wf_index(t@, g as int),
            wf_cff_parts(t@, d@, ng as int, sm as int),
            cs == d@.charstrings,
            d.cid ==> fsel == d@.fdselect && nfd == index_count(t@, d@.fdarray) && fdl@.len() == nfd
                && (forall|k: int|
                0 <= k < nfd ==> (#[trigger] fdl@[k]) == fd_subrs(t@, d@.fdarray, k, sm as int) && (fdl@[k]
                    != 0 ==> wf_index(t@, fdl@[k] as int))) && (t@[fsel as int] != 0 ==> cur
                < u16_at(t@, fsel + 1) && fds_first(t@, fsel as int, cur as int) <= i),
            !d.cid ==> l0 == priv_subrs(t@, d@.priv_size, d@.priv_off) && (l0 != 0 ==> wf_index(
                t@,
                l0 as int,
            )),
            ops <= MAX_CS_OPS,
            cs_all(t@, d@, g as int, i as int, sm as int) == Some(ops as int),
        decreases n - i,
    {
        let l = if d.cid {
            let (f, c) = glyph_fd_x(t, fsel, ng, nfd, i, cur);
            cur = c;
            fdl[f]
        } else {
            l0
        };
        assert(l == glyph_lsubrs(t@, d@, i as int, sm as int));
        let (a, b) = index_range_x(t, cs, i);
        if b - a > 65535 {
            proof {
                assert(cs_glyph(t@, d@, g as int, i as int, ops as int, sm as int) is None);
                lemma_cs_all_none(t@, d@, g as int, i + 1, n as int, sm as int);
            }
            return false;
        }
        st.stack.clear();
        st.width = false;
        st.stems = 0;
        st.hint = 0;
        st.ops = 0;
        assert(st.v() == cs_init(0));
        let r = run_x(t, g, l, a, b, 0, &mut st);
        if r != 2 {
            proof {
                assert(cs_glyph(t@, d@, g as int, i as int, ops as int, sm as int) is None);
                lemma_cs_all_none(t@, d@, g as int, i + 1, n as int, sm as int);
            }
            return false;
        }
        assert(cs_glyph(t@, d@, g as int, i as int, ops as int, sm as int) == Some(ops as int));
        i += 1;
    }
    true
}

} // verus!
