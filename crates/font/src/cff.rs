//! Verified check of the `CFF ` table: decides [`wf_cff`] exactly.
use crate::prims::*;
use crate::spec::*;
use crate::spec_cff::*;
use vstd::prelude::*;

verus! {

/// An unsigned big-endian number of `n` bytes at `i`.
#[inline]
fn rdn(t: &[u8], i: usize, n: usize) -> (r: u32)
    requires
        1 <= n <= 4,
        i + n <= t.len(),
    ensures
        r as int == un_at(t@, i as int, n as int),
{
    if n == 1 {
        rd8(t, i) as u32
    } else if n == 2 {
        rd16(t, i) as u32
    } else if n == 3 {
        rd24(t, i)
    } else {
        rd32(t, i)
    }
}

/// Offset `i` of the INDEX at `p`.
fn index_off_x(t: &[u8], p: usize, i: usize) -> (r: usize)
    requires
        p + 3 <= t.len(),
        1 <= t@[p + 2] <= 4,
        i <= index_count(t@, p as int),
        index_base(t@, p as int) + 1 <= t.len(),
    ensures
        r as int == index_off(t@, p as int, i as int),
{
    let os = rd8(t, p + 2) as usize;
    assert(i * os + os <= (index_count(t@, p as int) + 1) * os) by (nonlinear_arith)
        requires
            i <= index_count(t@, p as int),
            os >= 1,
    ;
    assert(0 <= i * os <= 65536 * 4) by (nonlinear_arith)
        requires
            i <= 65535,
            os <= 4,
    ;
    rdn(t, p + 3 + i * os, os) as usize
}

/// Decides [`wf_index`] and finds the INDEX's end.
pub fn check_index(t: &[u8], p: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(e) => wf_index(t@, p as int) && e == index_end(t@, p as int) && p + 2 <= e
                <= t.len(),
            None => !wf_index(t@, p as int),
        },
{
    if p > t.len() || 2 > t.len() - p {
        return None;
    }
    let cnt = rd16(t, p) as usize;
    if cnt == 0 {
        return Some(p + 2);
    }
    if 3 > t.len() - p {
        return None;
    }
    let os = rd8(t, p + 2) as usize;
    if os < 1 || os > 4 {
        return None;
    }
    assert(0 <= (cnt + 1) * os <= 65536 * 4) by (nonlinear_arith)
        requires
            cnt <= 65535,
            1 <= os <= 4,
    ;
    let arr = (cnt + 1) * os;
    if arr + 3 > t.len() - p {
        return None;
    }
    let base = p + 2 + arr;
    let mut prev = index_off_x(t, p, 0);
    if prev != 1 {
        return None;
    }
    let mut i: usize = 0;
    while i < cnt
        invariant
            i <= cnt,
            cnt == index_count(t@, p as int),
            cnt != 0,
            p + 3 <= t.len(),
            1 <= t@[p + 2] <= 4,
            base == index_base(t@, p as int),
            base + 1 <= t.len(),
            index_off(t@, p as int, 0) == 1,
            prev as int == index_off(t@, p as int, i as int),
            forall|k: int| 0 <= k < i ==> #[trigger] index_step(t@, p as int, k),
        decreases cnt - i,
    {
        let next = index_off_x(t, p, i + 1);
        if next < prev {
            assert(!index_step(t@, p as int, i as int));
            return None;
        }
        prev = next;
        i += 1;
    }
    if prev > t.len() - base {
        return None;
    }
    Some(base + prev)
}

/// In a well-formed INDEX the offsets are in order.
pub proof fn lemma_index_mono(t: Seq<u8>, p: int, i: int, j: int)
    requires
        wf_index(t, p),
        index_count(t, p) != 0,
        0 <= i <= j <= index_count(t, p),
    ensures
        1 <= index_off(t, p, i) <= index_off(t, p, j),
    decreases j - i, i,
{
    if i < j {
        lemma_index_mono(t, p, i, j - 1);
        assert(index_step(t, p, j - 1));
    } else if i > 0 {
        lemma_index_mono(t, p, i - 1, i - 1);
        assert(index_step(t, p, i - 1));
    }
}

/// Where object `i` of a well-formed INDEX starts and ends.
pub fn index_range_x(t: &[u8], p: usize, i: usize) -> (r: (usize, usize))
    requires
        wf_index(t@, p as int),
        i < index_count(t@, p as int),
    ensures
        r.0 == index_base(t@, p as int) + index_off(t@, p as int, i as int),
        r.1 == index_base(t@, p as int) + index_off(t@, p as int, i + 1),
        r.0 <= r.1 <= t.len(),
{
    assert(p + 2 <= t.len());
    let cnt = rd16(t, p) as usize;
    let os = rd8(t, p + 2) as usize;
    assert(0 <= (cnt + 1) * os <= 65536 * 4) by (nonlinear_arith)
        requires
            cnt <= 65535,
            1 <= os <= 4,
    ;
    let base = p + 2 + (cnt + 1) * os;
    let a = index_off_x(t, p, i);
    let b = index_off_x(t, p, i + 1);
    proof {
        lemma_index_mono(t@, p as int, i as int, i + 1);
        lemma_index_mono(t@, p as int, i + 1, cnt as int);
    }
    (base + a, base + b)
}

/// Object `i` of a well-formed INDEX.
pub fn index_obj_x<'a>(t: &'a [u8], p: usize, i: usize) -> (r: &'a [u8])
    requires
        wf_index(t@, p as int),
        i < index_count(t@, p as int),
    ensures
        r@ == index_obj(t@, p as int, i as int),
{
    assert(p + 2 <= t.len());
    let cnt = rd16(t, p) as usize;
    let os = rd8(t, p + 2) as usize;
    assert(0 <= (cnt + 1) * os <= 65536 * 4) by (nonlinear_arith)
        requires
            cnt <= 65535,
            1 <= os <= 4,
    ;
    let base = p + 2 + (cnt + 1) * os;
    let a = index_off_x(t, p, i);
    let b = index_off_x(t, p, i + 1);
    proof {
        lemma_index_mono(t@, p as int, i as int, i + 1);
        lemma_index_mono(t@, p as int, i + 1, cnt as int);
    }
    slice(t, base + a, base + b)
}

/// The executable counterpart of [`Dict`].
#[derive(Clone, Copy)]
pub struct DictX {
    pub bad: bool,
    pub started: bool,
    pub cid: bool,
    pub charset: i64,
    pub encoding: i64,
    pub has_cs: bool,
    pub charstrings: i64,
    pub has_priv: bool,
    pub priv_size: i64,
    pub priv_off: i64,
    pub has_fda: bool,
    pub fdarray: i64,
    pub has_fds: bool,
    pub fdselect: i64,
}

impl View for DictX {
    type V = Dict;

    open spec fn view(&self) -> Dict {
        Dict {
            bad: self.bad,
            started: self.started,
            cid: self.cid,
            charset: self.charset as int,
            encoding: self.encoding as int,
            has_cs: self.has_cs,
            charstrings: self.charstrings as int,
            has_priv: self.has_priv,
            priv_size: self.priv_size as int,
            priv_off: self.priv_off as int,
            has_fda: self.has_fda,
            fdarray: self.fdarray as int,
            has_fds: self.has_fds,
            fdselect: self.fdselect as int,
        }
    }
}

/// What a real number counts as: [`REAL`].
const REAL_X: i64 = 0x1_0000_0000;

fn sid_ok_x(v: i64, sm: usize) -> (b: bool)
    ensures
        b == sid_ok(v as int, sm as int),
{
    v != REAL_X && v >= 0 && v as u64 <= sm as u64
}

fn off_ok_x(v: i64, len: usize) -> (b: bool)
    ensures
        b == off_ok(v as int, len as int),
{
    v != REAL_X && v >= 0 && (v as u64) < len as u64
}

fn need_x(st: DictX, c: bool) -> (r: DictX)
    ensures
        r@ == need(st@, c),
{
    let mut r = st;
    r.bad = st.bad || !c;
    r.started = true;
    r
}

#[verifier::rlimit(80)]
fn dict_apply_x(
    st: DictX,
    fd: bool,
    sm: usize,
    len: usize,
    op: u32,
    n: usize,
    c: i64,
    a: i64,
    b: i64,
) -> (r: DictX)
    ensures
        r@ == dict_apply(
            st@,
            fd,
            sm as int,
            len as int,
            op as int,
            n as int,
            c as int,
            a as int,
            b as int,
        ),
{
    if op == 0 || op == 1 || op == 2 || op == 3 || op == 4 || op == 256 || op == 256 + 21 || op
        == 256 + 22 || op == 256 + 38 {
        need_x(st, n == 1 && sid_ok_x(b, sm))
    } else if op == 5 || op == 14 || op == 256 + 7 || op == 256 + 23 {
        need_x(st, n >= 1)
    } else if op == 13 || op == 256 + 2 || op == 256 + 3 || op == 256 + 4 || op == 256 + 5 || op
        == 256 + 8 || op == 256 + 20 {
        need_x(st, n == 1)
    } else if 256 + 31 <= op && op <= 256 + 35 {
        need_x(st, n == 1 && st.cid && !fd)
    } else if op == 256 + 6 {
        need_x(st, n == 1 && b == 2)
    } else if op == 256 + 1 {
        need_x(st, n == 1 && (b == 0 || b == 1))
    } else if op == 15 {
        if !fd && n == 1 && 0 <= b && b <= 2 {
            need_x(st, true)
        } else {
            let mut r = need_x(st, !fd && n == 1 && off_ok_x(b, len) && st.charset == 0);
            r.charset = b;
            r
        }
    } else if op == 16 {
        if !fd && n == 1 && 0 <= b && b <= 1 {
            need_x(st, true)
        } else {
            let mut r = need_x(st, !fd && n == 1 && off_ok_x(b, len) && st.encoding == 0);
            r.encoding = b;
            r
        }
    } else if op == 17 {
        let mut r = need_x(st, !fd && n == 1 && off_ok_x(b, len) && !st.has_cs);
        r.has_cs = true;
        r.charstrings = b;
        r
    } else if op == 18 {
        let mut r = need_x(
            st,
            n == 2 && a != REAL_X && b != REAL_X && 0 <= a && (a as u64) < len as u64 && 0 <= b
                && b as u64 <= len as u64 && a as i128 + b as i128 <= len as i128 && !st.has_priv,
        );
        r.has_priv = true;
        r.priv_size = a;
        r.priv_off = b;
        r
    } else if op == 256 + 30 {
        let mut r = need_x(st, !fd && !st.started && n == 3 && sid_ok_x(c, sm) && sid_ok_x(a, sm));
        r.cid = true;
        r
    } else if op == 256 + 36 {
        let mut r = need_x(st, !fd && n == 1 && off_ok_x(b, len) && !st.has_fda);
        r.has_fda = true;
        r.fdarray = b;
        r
    } else if op == 256 + 37 {
        let mut r = need_x(st, !fd && n == 1 && off_ok_x(b, len) && !st.has_fds);
        r.has_fds = true;
        r.fdselect = b;
        r
    } else {
        need_x(st, false)
    }
}

fn real_end_x(d: &[u8], p0: usize) -> (r: Option<usize>)
    requires
        p0 <= d.len(),
    ensures
        match r {
            Some(e) => real_end(d@, p0 as int, 0, false, false, 0) == Some(e as int) && p0 < e
                <= d.len(),
            None => real_end(d@, p0 as int, 0, false, false, 0) is None,
        },
{
    let mut i: usize = 0;
    let mut low = false;
    let mut point = false;
    let mut e = false;
    let mut exp: u32 = 0;
    loop
        invariant
            p0 <= d.len(),
            i <= d.len() - p0,
            exp < 120,
            real_end(
                d@,
                p0 as int,
                2 * i + if low {
                    1int
                } else {
                    0int
                },
                point,
                e,
                exp as int,
            ) == real_end(d@, p0 as int, 0, false, false, 0),
        decreases 2 * (d.len() - p0 - i) - if low {
            1int
        } else {
            0int
        },
    {
        if i >= d.len() - p0 {
            return None;
        }
        let ghost k = 2 * i + if low {
            1int
        } else {
            0int
        };
        assert(k / 2 == i);
        let byte = rd8(d, p0 + i);
        let x = if low {
            byte & 0x0f
        } else {
            byte >> 4
        };
        assert(x as int == nib(d@, p0 as int, k));
        assert(byte >> 4 <= 15) by (bit_vector);
        assert(byte & 0x0f <= 15) by (bit_vector);
        if x == 15 {
            if !low {
                assert((k + 1) / 2 == i);
                assert(nib(d@, p0 as int, k + 1) == (byte & 0x0f) as int);
                if byte & 0x0f != 15 {
                    return None;
                }
            }
            return Some(p0 + i + 1);
        } else if x == 13 {
            return None;
        } else if x == 14 {
            if i != 0 || low {
                return None;
            }
        } else if x == 10 {
            if point || e {
                return None;
            }
            point = true;
        } else if x == 11 || x == 12 {
            if e {
                return None;
            }
            e = true;
        } else if e {
            if exp * 10 + x as u32 >= 120 {
                return None;
            }
            exp = exp * 10 + x as u32;
        }
        if low {
            i += 1;
            low = false;
        } else {
            low = true;
        }
    }
}

/// The executable counterpart of [`Tok`].
pub enum TokX {
    Num(i64, usize),
    Op(u32, usize),
    Bad,
}

impl View for TokX {
    type V = Tok;

    open spec fn view(&self) -> Tok {
        match *self {
            TokX::Num(v, q) => Tok::Num(v as int, q as int),
            TokX::Op(o, q) => Tok::Op(o as int, q as int),
            TokX::Bad => Tok::Bad,
        }
    }
}

fn dict_tok_x(d: &[u8], p: usize) -> (r: TokX)
    requires
        p < d.len(),
    ensures
        r@ == dict_tok(d@, p as int),
        r matches TokX::Num(_, q) ==> p < q <= d.len(),
        r matches TokX::Op(_, q) ==> p < q <= d.len(),
{
    let b = rd8(d, p);
    let room = d.len() - p;
    if b == 12 {
        if room >= 2 {
            let x = rd8(d, p + 1);
            if x <= 14 || (17 <= x && x <= 23) || (30 <= x && x <= 38) {
                TokX::Op(256 + x as u32, p + 2)
            } else {
                TokX::Bad
            }
        } else {
            TokX::Bad
        }
    } else if b <= 21 {
        TokX::Op(b as u32, p + 1)
    } else if b == 28 {
        if room >= 3 {
            TokX::Num(rdi16(d, p + 1) as i64, p + 3)
        } else {
            TokX::Bad
        }
    } else if b == 29 {
        if room >= 5 {
            let v = rd32(d, p + 1) as i64;
            TokX::Num(
                if v >= 0x8000_0000 {
                    v - 0x1_0000_0000
                } else {
                    v
                },
                p + 5,
            )
        } else {
            TokX::Bad
        }
    } else if b == 30 {
        match real_end_x(d, p + 1) {
            Some(e) => TokX::Num(REAL_X, e),
            None => TokX::Bad,
        }
    } else if 32 <= b && b <= 246 {
        TokX::Num(b as i64 - 139, p + 1)
    } else if 247 <= b && b <= 250 {
        if room >= 2 {
            TokX::Num((b as i64 - 247) * 256 + rd8(d, p + 1) as i64 + 108, p + 2)
        } else {
            TokX::Bad
        }
    } else if 251 <= b && b <= 254 {
        if room >= 2 {
            TokX::Num(-(b as i64 - 251) * 256 - rd8(d, p + 1) as i64 - 108, p + 2)
        } else {
            TokX::Bad
        }
    } else {
        TokX::Bad
    }
}

/// Reads a Top DICT or Font DICT: see [`dict_read`].
pub fn dict_read_x(d: &[u8], fd: bool, sm: usize, len: usize) -> (r: Option<DictX>)
    ensures
        match r {
            Some(x) => dict_read(d@, fd, sm as int, len as int) == Some(x@),
            None => dict_read(d@, fd, sm as int, len as int) is None,
        },
{
    let mut st = DictX {
        bad: false,
        started: false,
        cid: false,
        charset: 0,
        encoding: 0,
        has_cs: false,
        charstrings: 0,
        has_priv: false,
        priv_size: 0,
        priv_off: 0,
        has_fda: false,
        fdarray: 0,
        has_fds: false,
        fdselect: 0,
    };
    let mut p: usize = 0;
    let mut n: usize = 0;
    let mut c: i64 = 0;
    let mut a: i64 = 0;
    let mut b: i64 = 0;
    while p < d.len()
        invariant
            p <= d.len(),
            n <= 47,
            dict_read(d@, fd, sm as int, len as int) == dict_scan(
                d@,
                fd,
                sm as int,
                len as int,
                p as int,
                n as int,
                c as int,
                a as int,
                b as int,
                st@,
            ),
        decreases d.len() - p,
    {
        match dict_tok_x(d, p) {
            TokX::Num(v, q) => {
                if n >= 47 {
                    return None;
                }
                n += 1;
                c = a;
                a = b;
                b = v;
                p = q;
            },
            TokX::Op(op, q) => {
                st = dict_apply_x(st, fd, sm, len, op, n, c, a, b);
                n = 0;
                c = 0;
                a = 0;
                b = 0;
                p = q;
            },
            TokX::Bad => {
                return None;
            },
        }
    }
    if n == 0 {
        Some(st)
    } else {
        None
    }
}

/// The executable counterpart of [`Priv`].
#[derive(Clone, Copy)]
pub struct PrivX {
    pub bad: bool,
    pub has_subrs: bool,
    pub subrs: i64,
}

impl View for PrivX {
    type V = Priv;

    open spec fn view(&self) -> Priv {
        Priv { bad: self.bad, has_subrs: self.has_subrs, subrs: self.subrs as int }
    }
}

fn priv_apply_x(st: PrivX, op: u32, n: usize, b: i64) -> (r: PrivX)
    ensures
        r@ == priv_apply(st@, op as int, n as int, b as int),
{
    let mut r = st;
    if op == 6 || op == 7 || op == 8 || op == 9 {
        r.bad = st.bad || n % 2 != 0;
    } else if op == 256 + 12 || op == 256 + 13 {
        r.bad = st.bad || n < 1;
    } else if op == 10 || op == 11 || op == 20 || op == 21 || op == 256 + 9 || op == 256 + 10 || op
        == 256 + 11 || op == 256 + 17 || op == 256 + 18 || op == 256 + 19 {
        r.bad = st.bad || n != 1;
    } else if op == 19 {
        r.bad = st.bad || !(n == 1 && b != REAL_X && 0 <= b && b < 0x4000_0000 && !st.has_subrs);
        r.has_subrs = true;
        r.subrs = b;
    } else if op == 256 + 14 {
        r.bad = st.bad || !(n == 1 && (b == 0 || b == 1));
    } else {
        r.bad = true;
    }
    r
}

/// Reads a Private DICT: see [`priv_read`].
pub fn priv_read_x(d: &[u8]) -> (r: Option<PrivX>)
    ensures
        match r {
            Some(x) => priv_read(d@) == Some(x@),
            None => priv_read(d@) is None,
        },
{
    let mut st = PrivX { bad: false, has_subrs: false, subrs: 0 };
    let mut p: usize = 0;
    let mut n: usize = 0;
    let mut b: i64 = 0;
    while p < d.len()
        invariant
            p <= d.len(),
            n <= 47,
            priv_read(d@) == priv_scan(d@, p as int, n as int, b as int, st@),
        decreases d.len() - p,
    {
        match dict_tok_x(d, p) {
            TokX::Num(v, q) => {
                if n >= 47 {
                    return None;
                }
                n += 1;
                b = v;
                p = q;
            },
            TokX::Op(op, q) => {
                st = priv_apply_x(st, op, n, b);
                n = 0;
                b = 0;
                p = q;
            },
            TokX::Bad => {
                return None;
            },
        }
    }
    if n == 0 {
        Some(st)
    } else {
        None
    }
}

/// `v` as a position in a table of length `len`, if it is one.
fn pos(v: i64, len: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(u) => u == v && u <= len,
            None => v < 0 || v > len,
        },
{
    if v < 0 || v as u64 > len as u64 {
        None
    } else {
        Some(v as usize)
    }
}

fn check_charset_ranges(t: &[u8], p0: usize, w: usize, left0: usize, sm: usize) -> (b: bool)
    requires
        1 <= w <= 2,
        p0 <= t.len(),
        left0 <= 65535,
    ensures
        b == charset_ranges(t@, p0 as int, w as int, left0 as int, sm as int),
{
    let mut p = p0;
    let mut left = left0;
    while left > 0
        invariant
            1 <= w <= 2,
            p <= t.len(),
            left <= 65535,
            charset_ranges(t@, p0 as int, w as int, left0 as int, sm as int) == charset_ranges(
                t@,
                p as int,
                w as int,
                left as int,
                sm as int,
            ),
        decreases left,
    {
        if 2 + w > t.len() - p {
            return false;
        }
        let nl = rdn(t, p + 2, w) as usize;
        if 1 + nl > left || rd16(t, p) as usize + nl > sm {
            return false;
        }
        left = left - 1 - nl;
        p = p + 2 + w;
    }
    true
}

fn check_charset(t: &[u8], v: i64, ng: u16, sm: usize) -> (b: bool)
    requires
        ng >= 1,
    ensures
        b == wf_charset(t@, v as int, ng as int, sm as int),
{
    let p = match pos(v, t.len()) {
        Some(p) => p,
        None => {
            return false;
        },
    };
    if p >= t.len() {
        return false;
    }
    let f = rd8(t, p);
    let n = ng as usize - 1;
    if f == 0 {
        if 2 * n > t.len() - p - 1 {
            return false;
        }
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                n == ng - 1,
                p + 1 + 2 * n <= t.len(),
                t@[p as int] == 0,
                p == v,
                forall|x: int| 0 <= x < j ==> #[trigger] charset_sid(t@, p as int, x) <= sm,
            decreases n - j,
        {
            if rd16(t, p + 1 + 2 * j) as usize > sm {
                assert(charset_sid(t@, p as int, j as int) > sm);
                return false;
            }
            assert(charset_sid(t@, p as int, j as int) <= sm);
            j += 1;
        }
        true
    } else if f == 1 {
        check_charset_ranges(t, p + 1, 1, n, sm)
    } else if f == 2 {
        check_charset_ranges(t, p + 1, 2, n, sm)
    } else {
        false
    }
}

fn check_encoding(t: &[u8], v: i64) -> (b: bool)
    ensures
        b == wf_encoding(t@, v as int),
{
    let p = match pos(v, t.len()) {
        Some(p) => p,
        None => {
            return false;
        },
    };
    if 2 > t.len() - p {
        return false;
    }
    let f = rd8(t, p);
    let k = rd8(t, p + 1) as usize;
    if f != 0 && f != 1 {
        return false;
    }
    let sz = if f == 0 {
        k
    } else {
        2 * k
    };
    sz <= t.len() - p - 2
}

fn check_fdselect(t: &[u8], v: i64, ng: u16, nfd: usize) -> (b: bool)
    ensures
        b == wf_fdselect(t@, v as int, ng as int, nfd as int),
{
    let p = match pos(v, t.len()) {
        Some(p) => p,
        None => {
            return false;
        },
    };
    if p >= t.len() {
        return false;
    }
    let f = rd8(t, p);
    if f == 0 {
        let n = ng as usize;
        if n > t.len() - p - 1 {
            return false;
        }
        let mut g: usize = 0;
        while g < n
            invariant
                g <= n,
                n == ng,
                p + 1 + n <= t.len(),
                t@[p as int] == 0,
                p == v,
                forall|x: int| 0 <= x < g ==> (#[trigger] t@[p + 1 + x]) < nfd,
            decreases n - g,
        {
            if rd8(t, p + 1 + g) as usize >= nfd {
                return false;
            }
            g += 1;
        }
        true
    } else {
        if f != 3 || 3 > t.len() - p {
            return false;
        }
        let n = rd16(t, p + 1) as usize;
        if n < 1 || 5 + 3 * n > t.len() - p {
            return false;
        }
        if rd16(t, p + 3) != 0 || rd16(t, p + 3 + 3 * n) != ng {
            return false;
        }
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                p + 5 + 3 * n <= t.len(),
                t@[p as int] == 3,
                p == v,
                n == u16_at(t@, p + 1),
                n >= 1,
                u16_at(t@, p + 3) == 0,
                u16_at(t@, p + 3 + 3 * n) == ng,
                forall|x: int| 0 <= x < k ==> #[trigger] fds_range_ok(t@, p as int, x, nfd as int),
            decreases n - k,
        {
            let r = p + 3 + 3 * k;
            if rd16(t, r) >= rd16(t, r + 3) || rd8(t, r + 2) as usize >= nfd {
                assert(!fds_range_ok(t@, p as int, k as int, nfd as int));
                return false;
            }
            assert(fds_range_ok(t@, p as int, k as int, nfd as int));
            k += 1;
        }
        true
    }
}

fn check_private(t: &[u8], size: i64, off: i64) -> (b: bool)
    ensures
        b == wf_private(t@, size as int, off as int),
{
    let o = match pos(off, t.len()) {
        Some(o) => o,
        None => {
            return false;
        },
    };
    if size < 0 || size as u64 > (t.len() - o) as u64 {
        return false;
    }
    match priv_read_x(slice(t, o, o + size as usize)) {
        Some(d) => {
            if d.bad {
                return false;
            }
            if d.has_subrs {
                if d.subrs <= 0 {
                    return false;
                }
                let q = off as i128 + d.subrs as i128;
                if q > t.len() as i128 {
                    return false;
                }
                check_index(t, q as usize).is_some()
            } else {
                true
            }
        },
        None => false,
    }
}

fn check_fontdict(t: &[u8], fa: usize, i: usize, sm: usize) -> (b: bool)
    requires
        wf_index(t@, fa as int),
        i < index_count(t@, fa as int),
    ensures
        b == wf_fontdict(t@, fa as int, i as int, sm as int),
{
    match dict_read_x(index_obj_x(t, fa, i), true, sm, t.len()) {
        Some(d) => !d.bad && d.has_priv && check_private(t, d.priv_size, d.priv_off),
        None => false,
    }
}

fn check_fontdicts(t: &[u8], fa: usize, nfd: usize, sm: usize) -> (b: bool)
    requires
        wf_index(t@, fa as int),
        nfd == index_count(t@, fa as int),
    ensures
        b == forall|k: int| 0 <= k < nfd ==> #[trigger] wf_fontdict(t@, fa as int, k, sm as int),
{
    let mut i: usize = 0;
    while i < nfd
        invariant
            i <= nfd,
            wf_index(t@, fa as int),
            nfd == index_count(t@, fa as int),
            forall|k: int| 0 <= k < i ==> #[trigger] wf_fontdict(t@, fa as int, k, sm as int),
        decreases nfd - i,
    {
        if !check_fontdict(t, fa, i, sm) {
            return false;
        }
        i += 1;
    }
    true
}

fn check_cff_top(t: &[u8], d: &DictX, ng: u16, sm: usize) -> (b: bool)
    ensures
        b == wf_cff_parts(t@, d@, ng as int, sm as int),
{
    if d.bad || ng < 2 || !d.has_cs || d.charstrings <= 0 {
        return false;
    }
    let cs = match pos(d.charstrings, t.len()) {
        Some(p) => p,
        None => {
            return false;
        },
    };
    if check_index(t, cs).is_none() || rd16(t, cs) != ng {
        return false;
    }
    if d.charset != 0 && !check_charset(
        t,
        d.charset,
        ng,
        if d.cid {
            65535
        } else {
            sm
        },
    ) {
        return false;
    }
    if d.encoding != 0 && !check_encoding(t, d.encoding) {
        return false;
    }
    if !check_private(t, d.priv_size, d.priv_off) {
        return false;
    }
    if d.cid {
        if !d.has_fda || d.fdarray <= 0 {
            return false;
        }
        let fa = match pos(d.fdarray, t.len()) {
            Some(p) => p,
            None => {
                return false;
            },
        };
        if check_index(t, fa).is_none() {
            return false;
        }
        let nfd = rd16(t, fa) as usize;
        if nfd < 1 || nfd > 256 {
            return false;
        }
        if !check_fontdicts(t, fa, nfd, sm) {
            return false;
        }
        d.has_fds && d.fdselect > 0 && check_fdselect(t, d.fdselect, ng, nfd)
    } else {
        !d.has_fda && !d.has_fds
    }
}

fn check_name(x: &[u8]) -> (b: bool)
    ensures
        b == (x@.len() <= 127 && forall|i: int| 0 <= i < x@.len() ==> #[trigger] name_byte_ok(x@, i)),
{
    if x.len() > 127 {
        return false;
    }
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] name_byte_ok(x@, k),
        decreases x.len() - i,
    {
        let c = rd8(x, i);
        let ok = (i == 0 && c == 0) || (33 <= c && c <= 126 && c != 0x5B && c != 0x5D && c != 0x28
            && c != 0x29 && c != 0x7B && c != 0x7D && c != 0x3C && c != 0x3E && c != 0x2F && c
            != 0x25);
        if !ok {
            assert(!name_byte_ok(x@, i as int));
            return false;
        }
        i += 1;
    }
    true
}

/// Decides [`wf_cff`].
pub fn check_cff(t: &[u8], ng: u16) -> (b: bool)
    ensures
        b == wf_cff(t@, ng as int),
{
    if t.len() < 4 {
        return false;
    }
    if rd8(t, 0) != 1 || rd8(t, 1) != 0 || rd8(t, 2) != 4 || rd8(t, 3) < 1 || rd8(t, 3) > 4 {
        return false;
    }
    let name: usize = 4;
    let top = match check_index(t, name) {
        Some(e) => e,
        None => {
            return false;
        },
    };
    if rd16(t, name) != 1 {
        return false;
    }
    if !check_name(index_obj_x(t, name, 0)) {
        return false;
    }
    let strings = match check_index(t, top) {
        Some(e) => e,
        None => {
            return false;
        },
    };
    if rd16(t, top) != 1 {
        return false;
    }
    let gsubrs = match check_index(t, strings) {
        Some(e) => e,
        None => {
            return false;
        },
    };
    let ns = rd16(t, strings) as usize;
    if ns >= 65000 - 390 {
        return false;
    }
    let sm = ns + 390;
    if check_index(t, gsubrs).is_none() {
        return false;
    }
    match dict_read_x(index_obj_x(t, top, 0), false, sm, t.len()) {
        Some(d) => check_cff_top(t, &d, ng, sm) && crate::cs::check_charstrings(
            t,
            &d,
            gsubrs,
            ng,
            sm,
        ),
        None => false,
    }
}

} // verus!
