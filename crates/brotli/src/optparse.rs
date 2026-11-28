//! Optimal parsing for qualities 10 and 11 (not trusted, like every
//! parse: `cwrite::check_cmds` checks its commands before they are
//! written). The matches at every position of a block are found once;
//! then a shortest path over the block, with bit costs from the symbol
//! counts of the previous parse, picks literals and copies. Two rounds.
use crate::compress::*;
use crate::mblock::*;
use crate::spec::{INS_EXTRA, CPY_EXTRA};
use verilith_core::lz::eq_len;
use verilith_core::prims::{get, get32, store_at};
use vstd::prelude::*;

verus! {

const INF: u32 = 0xFFFF_FFFF;
/// Matches at least this long are taken whole, with no search inside.
const LONG: usize = 325;
/// At most this many matches are kept per position.
const KEEP: usize = 24;

/// `16 log2(x)`, roughly, for `x >= 1`.
fn log2_16(x: u32) -> (r: u32)
    ensures
        r <= 16 * 33,
{
    if x <= 1 {
        return 0;
    }
    let b = crate::pcode::bitlen_exec(x);
    proof {
        crate::pcode::lemma_bitlen_bound(x as nat);
    }
    if b == 0 || b > 32 {
        return 0;
    }
    let e = b - 1;
    // The four bits after the leading one.
    let f: u32 = if e >= 4 { (x >> (e - 4)) & 15 } else { (x << (4 - e)) & 15 };
    let t: [u32; 16] = [0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 14, 15, 16];
    if f >= 16 {
        return 16 * e;
    }
    16 * e + t[f as usize]
}

/// Bit costs, in sixteenths of a bit, from symbol counts.
pub struct Costs {
    pub lit: Vec<u32>,
    pub cmd: Vec<u32>,
    pub dist: Vec<u32>,
}

fn costs_of(f: &Vec<u32>, n: usize) -> (r: Vec<u32>)
    ensures
        r@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] r@[i] <= 16 * 40,
{
    let mut total: u32 = 0;
    let mut i: usize = 0;
    while i < f.len()
        invariant
            total < 0x2000_0000,
        decreases f.len() - i,
    {
        if total < 0x1000_0000 && f[i] < 0x1000_0000 {
            total = total + f[i];
        }
        i = i + 1;
    }
    let lt = log2_16(total + n as u32 % 0x1000);
    let mut r: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            r@.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] r@[j] <= 16 * 40,
        decreases n - i,
    {
        let x = if i < f.len() && f[i] < 0x1000_0000 { f[i] } else { 0 };
        let lx = log2_16(x + 1);
        let c = if lt > lx { lt - lx } else { 0 };
        // A floor: no symbol is free, and unseen ones are dear.
        let c = if c < 8 { 8 } else if x == 0 && c < 16 * 4 { 16 * 4 } else { c };
        let c = if c > 16 * 40 { 16 * 40 } else { c };
        r.push(c);
        i = i + 1;
    }
    r
}

pub fn costs_from(lf: &Vec<u32>, cf: &Vec<u32>, df: &Vec<u32>) -> (r: Costs)
    ensures
        r.lit@.len() == 256,
        r.cmd@.len() == 704,
        r.dist@.len() == 64,
        forall|i: int| 0 <= i < 256 ==> #[trigger] r.lit@[i] <= 16 * 40,
        forall|i: int| 0 <= i < 704 ==> #[trigger] r.cmd@[i] <= 16 * 40,
        forall|i: int| 0 <= i < 64 ==> #[trigger] r.dist@[i] <= 16 * 40,
{
    Costs { lit: costs_of(lf, 256), cmd: costs_of(cf, 704), dist: costs_of(df, 64) }
}

#[inline(always)]
fn set_child(mf: &mut Mf, n: usize, right: bool, v: u32)
    requires
        old(mf).bt,
        n < old(mf).prev@.len(),
        n < old(mf).right@.len(),
    ensures
        final(mf).head@ == old(mf).head@,
        final(mf).num@ == old(mf).num@,
        final(mf).prev@.len() == old(mf).prev@.len(),
        final(mf).right@.len() == old(mf).right@.len(),
        final(mf).quick == old(mf).quick,
        final(mf).ways == old(mf).ways,
        final(mf).bt == old(mf).bt,
        final(mf).wmax == old(mf).wmax,
        final(mf).depth == old(mf).depth,
{
    if right {
        store_at(&mut mf.right, n, v);
    } else {
        store_at(&mut mf.prev, n, v);
    }
}

/// Puts `i` at the root of the binary tree of its hash (google/brotli's
/// H10), and with `find` pushes the matches longer than any before
/// (and than 3) to `ms`. Returns the longest.
fn bt_step(mf: &mut Mf, data: &[u8], i: usize, max: usize, find: bool, ms: &mut Vec<(u32, u32)>) -> (best: usize)
    requires
        old(mf).wf(data@.len()),
        old(mf).bt,
        i + max <= data@.len(),
        data@.len() - i >= 4,
    ensures
        final(mf).wf(data@.len()),
        final(mf).bt,
        final(mf).wmax == old(mf).wmax,
        best <= max || best == 3,
{
    let reroot = max >= 128;
    let cmp = if max < 128 { max } else { 128 };
    let h = crate::compress::hash4(data, i);
    let mut c = get32(mf.head.as_slice(), h);
    if reroot {
        store_at(&mut mf.head, h, i as u32);
    }
    // The child slots to fill: `prev` (left) or `right` of a node.
    let mut ln: usize = i;
    let mut lr = false;
    let mut rn: usize = i;
    let mut rr = true;
    let mut bl: usize = 0;
    let mut br: usize = 0;
    let mut best: usize = 3;
    let mut d: u32 = 0;
    while d < mf.depth
        invariant
            mf.wf(data@.len()),
            mf.bt,
            mf.wmax == old(mf).wmax,
            i + max <= data@.len(),
            data@.len() - i >= 4,
            ln < data@.len(),
            rn < data@.len(),
            bl <= cmp,
            br <= cmp,
            cmp <= max,
            best <= max || best == 3,
        decreases mf.depth - d,
    {
        if c == 0xFFFF_FFFF || (c as usize) >= i || i - (c as usize) > mf.wmax {
            break;
        }
        let cu = c as usize;
        let dist = i - cu;
        let cl = if bl < br { bl } else { br };
        let len = cl + eq_len(data, cu + cl, i + cl, max - cl);
        if find && len > best && eq_len(data, cu, i, cl) == cl {
            best = len;
            ms.push((len as u32, dist as u32));
        }
        if len >= cmp {
            if reroot {
                let a = get32(mf.prev.as_slice(), cu);
                let b = get32(mf.right.as_slice(), cu);
                set_child(mf, ln, lr, a);
                set_child(mf, rn, rr, b);
            }
            return best;
        }
        if get(data, i + len) > get(data, cu + len) {
            bl = len;
            if reroot {
                set_child(mf, ln, lr, c);
            }
            ln = cu;
            lr = true;
            c = get32(mf.right.as_slice(), cu);
        } else {
            br = len;
            if reroot {
                set_child(mf, rn, rr, c);
            }
            rn = cu;
            rr = false;
            c = get32(mf.prev.as_slice(), cu);
        }
        d = d + 1;
    }
    if reroot {
        set_child(mf, ln, lr, 0xFFFF_FFFF);
        set_child(mf, rn, rr, 0xFFFF_FFFF);
    }
    best
}

/// The matches at each position of `data[start..end]`: for position `i`,
/// `ms[offs[i - start] .. offs[i - start + 1]]`, as (length, distance) with
/// lengths increasing. Inserts every position into the chains.
pub fn all_matches(mf: &mut Mf, data: &[u8], start: usize, end: usize, ms: &mut Vec<(u32, u32)>, offs: &mut Vec<u32>)
    requires
        old(mf).wf(data@.len()),
        start <= end <= data@.len(),
    ensures
        final(mf).wf(data@.len()),
        final(mf).wmax == old(mf).wmax,
{
    ms.clear();
    offs.clear();
    let mut i = start;
    // Inside a long match the parser jumps, so it needs no matches there.
    let mut skip: usize = 0;
    while i < end
        invariant
            mf.wf(data@.len()),
            mf.wmax == old(mf).wmax,
            start <= i <= end <= data@.len(),
        decreases end - i,
    {
        if ms.len() >= 0xFFFF_0000 {
            break;
        }
        offs.push(ms.len() as u32);
        let max = if end - i > 0xFFFF { 0xFFFF } else { end - i };
        let mut best: usize = 3;
        if mf.bt {
            if data.len() - i >= 4 && max >= 4 {
                if i >= skip {
                    best = bt_step(mf, data, i, max, true, ms);
                    if best >= LONG {
                        skip = i + best;
                    }
                } else if skip - i <= 64 {
                    bt_step(mf, data, i, max, false, ms);
                }
            }
            i = i + 1;
            continue;
        }
        if !mf.quick && max >= 4 && data.len() - i >= 4 {
            let h = crate::compress::hash4(data, i);
            let mut c = mf.head[h];
            let mut d: u32 = 0;
            let mut kept: usize = 0;
            while d < mf.depth && c != 0xFFFF_FFFF && (c as usize) < i && kept < KEEP
                invariant
                    mf.wf(data@.len()),
                    i + max <= data@.len(),
                    max <= 0xFFFF,
                    !mf.quick,
                decreases mf.depth - d,
            {
                let cu = c as usize;
                let dist = i - cu;
                if dist > mf.wmax {
                    break;
                }
                if best < max && data[cu + best] == data[i + best] {
                    let k = eq_len(data, cu, i, max);
                    if k > best {
                        best = k;
                        ms.push((k as u32, dist as u32));
                        kept = kept + 1;
                        if k == max {
                            break;
                        }
                    }
                }
                c = mf.prev[cu];
                d = d + 1;
            }
        }
        mf.insert(data, i);
        i = i + 1;
    }
    while offs.len() < end - start + 1
        invariant
            start <= end <= data@.len(),
            data@.len() < 0xFFFF_FFFF,
        decreases end - start + 1 - offs.len(),
    {
        offs.push(ms.len() as u32);
    }
}

/// Copy length codes for lengths up to `0xFFFF`, 24 when there is none.
pub fn cpy_table() -> (r: Vec<u8>)
    ensures
        r@.len() == 0x1_0000,
{
    let mut t: Vec<u8> = Vec::with_capacity(0x1_0000);
    let mut l: u32 = 0;
    while l < 0x1_0000
        invariant
            t@.len() == l,
            l <= 0x1_0000,
        decreases 0x1_0000 - l,
    {
        let c = match cpy_code_of(l) {
            Some(c) => c as u8,
            None => 24,
        };
        t.push(c);
        l = l + 1;
    }
    t
}

/// The next length after `l` that is the last of its copy code, or `len`.
#[inline(always)]
fn next_end(ct: &Vec<u8>, l: usize, len: usize) -> (r: usize)
    requires
        l < len,
    ensures
        l < r <= len,
{
    if len >= 0x1_0000 || l + 1 >= ct.len() {
        return len;
    }
    let mut k = l + 1;
    while k < len && k + 1 < ct.len() && ct[k + 1] == ct[k]
        invariant
            l < k <= len,
        decreases len - k,
    {
        k = k + 1;
    }
    k
}

#[inline(always)]
fn dist_cost(co: &Costs, d: u32, dr: [u32; 4]) -> (r: u32)
    requires
        co.dist@.len() == 64,
        forall|i: int| 0 <= i < 64 ==> #[trigger] co.dist@[i] <= 16 * 40,
    ensures
        r <= 16 * 100,
{
    if d == dr[0] {
        co.dist[0]
    } else if d == dr[1] {
        co.dist[1]
    } else if d == dr[2] {
        co.dist[2]
    } else if d == dr[3] {
        co.dist[3]
    } else if d >= 1 && d < 0x100_0000 {
        let (dc, _ex, nb) = dist_code(d);
        co.dist[dc as usize] + 16 * nb
    } else {
        16 * 100
    }
}

/// Command costs by insert code and copy code (`ic * 24 + cc`), with an
/// explicit distance and with the last one.
fn cmd_tables(co: &Costs) -> (r: (Vec<u32>, Vec<u32>))
    requires
        co.cmd@.len() == 704,
        forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
    ensures
        r.0@.len() == 576,
        r.1@.len() == 576,
        forall|i: int| 0 <= i < 576 ==> #[trigger] r.0@[i] <= 16 * 100,
        forall|i: int| 0 <= i < 576 ==> #[trigger] r.1@[i] <= 16 * 100,
{
    proof {
        crate::mblock::lemma_tables_small();
    }
    let mut e: Vec<u32> = Vec::with_capacity(576);
    let mut m: Vec<u32> = Vec::with_capacity(576);
    let mut ic: usize = 0;
    while ic < 24
        invariant
            e@.len() == ic * 24,
            m@.len() == ic * 24,
            ic <= 24,
            co.cmd@.len() == 704,
            forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
            forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && crate::spec::INS_BASE[i] <= 22594,
            forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= crate::spec::CPY_BASE[i] <= 2118,
            forall|i: int| 0 <= i < e@.len() ==> #[trigger] e@[i] <= 16 * 100,
            forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i] <= 16 * 100,
        decreases 24 - ic,
    {
        let mut cc: usize = 0;
        while cc < 24
            invariant
                e@.len() == ic * 24 + cc,
                m@.len() == ic * 24 + cc,
                ic < 24,
                cc <= 24,
                co.cmd@.len() == 704,
                forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
                forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && crate::spec::INS_BASE[i] <= 22594,
                forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= crate::spec::CPY_BASE[i] <= 2118,
                forall|i: int| 0 <= i < e@.len() ==> #[trigger] e@[i] <= 16 * 100,
                forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i] <= 16 * 100,
            decreases 24 - cc,
        {
            let x = 16 * (INS_EXTRA[ic] as u32 + CPY_EXTRA[cc] as u32);
            let ce = co.cmd[cmd_sym(ic, cc, false) as usize] + x;
            let ci = if ic < 8 && cc < 16 { co.cmd[cmd_sym(ic, cc, true) as usize] + x } else { ce };
            e.push(ce);
            m.push(ci);
            cc = cc + 1;
        }
        assert(ic * 24 + 24 == (ic + 1) * 24);
        ic = ic + 1;
    }
    (e, m)
}

/// The cheapest parse of `data[start..end]` with costs `co`, from the
/// matches `ms`/`offs` and last distances `dr0`.
pub fn shortest(data: &[u8], start: usize, end: usize, ms: &Vec<(u32, u32)>, offs: &Vec<u32>, co: &Costs, ct: &Vec<u8>, dr0: [u32; 4]) -> (r: Vec<Lz>)
    requires
        start <= end <= data@.len(),
        co.lit@.len() == 256,
        co.cmd@.len() == 704,
        co.dist@.len() == 64,
        forall|i: int| 0 <= i < 256 ==> #[trigger] co.lit@[i] <= 16 * 40,
        forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
        forall|i: int| 0 <= i < 64 ==> #[trigger] co.dist@[i] <= 16 * 40,
        ct@.len() == 0x1_0000,
{
    let m = end - start;
    if m == 0 || m >= 0x1000_0000 || offs.len() != m + 1 {
        return Vec::new();
    }
    let mut cost: Vec<u32> = vec![INF; m + 1];
    let mut flen: Vec<u32> = vec![0; m + 1];
    let mut fdist: Vec<u32> = vec![0; m + 1];
    let mut lit: Vec<u32> = vec![0; m + 1];
    let mut drs_: Vec<[u32; 4]> = vec![dr0; m + 1];
    cost.set(0, 0);
    let (te, tl) = cmd_tables(co);
    let mut i: usize = 0;
    while i < m
        invariant
            te@.len() == 576,
            tl@.len() == 576,
            forall|i: int| 0 <= i < 576 ==> #[trigger] te@[i] <= 16 * 100,
            forall|i: int| 0 <= i < 576 ==> #[trigger] tl@[i] <= 16 * 100,
            m == end - start,
            start <= end <= data@.len(),
            cost@.len() == m + 1,
            flen@.len() == m + 1,
            fdist@.len() == m + 1,
            lit@.len() == m + 1,
            drs_@.len() == m + 1,
            offs@.len() == m + 1,
            co.lit@.len() == 256,
            co.cmd@.len() == 704,
            co.dist@.len() == 64,
            forall|i: int| 0 <= i < 256 ==> #[trigger] co.lit@[i] <= 16 * 40,
            forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
            forall|i: int| 0 <= i < 64 ==> #[trigger] co.dist@[i] <= 16 * 40,
            ct@.len() == 0x1_0000,
            i <= m,
            m < 0x1000_0000,
        decreases m - i,
    {
        let c0 = cost[i];
        if c0 >= 0xF000_0000 {
            i = i + 1;
            continue;
        }
        let dr = drs_[i];
        let li = lit[i];
        let ic = match ins_code_of(li) {
            Some(c) => c,
            None => 23,
        };
        // A literal.
        let cl = c0 + co.lit[data[start + i] as usize];
        if cl < cost[i + 1] {
            cost.set(i + 1, cl);
            flen.set(i + 1, 0);
            lit.set(i + 1, if li < 0x1000_0000 { li + 1 } else { li });
            drs_.set(i + 1, dr);
        }
        // The last distance.
        let mut jump: usize = 0;
        let rest = m - i;
        let d0 = dr[0] as usize;
        if d0 >= 1 && d0 <= start + i && rest >= 2 {
            let mx = if rest > 0xFFFF { 0xFFFF } else { rest };
            let k = eq_len(data, start + i - d0, start + i, mx);
            let mut l: usize = 2;
            while l <= k
                invariant
                    k <= rest,
                    i + rest == m,
                    m < 0x1000_0000,
                    cost@.len() == m + 1,
                    flen@.len() == m + 1,
                    fdist@.len() == m + 1,
                    drs_@.len() == m + 1,
                    co.cmd@.len() == 704,
                    co.dist@.len() == 64,
                    forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
                    forall|i: int| 0 <= i < 64 ==> #[trigger] co.dist@[i] <= 16 * 40,
                    ct@.len() == 0x1_0000,
                    c0 < 0xF000_0000,
                    te@.len() == 576,
                    tl@.len() == 576,
                    forall|i: int| 0 <= i < 576 ==> #[trigger] te@[i] <= 16 * 100,
                    forall|i: int| 0 <= i < 576 ==> #[trigger] tl@[i] <= 16 * 100,
                    ic < 24,
                    l >= 2,
                decreases k + 1 - l,
            {
                let cc = if l < 0x1_0000 { ct[l] as usize } else { 24 };
                if cc < 24 {
                    let c = c0 + tl[ic * 24 + cc];
                    if c < cost[i + l] {
                        cost.set(i + l, c);
                        flen.set(i + l, l as u32);
                        fdist.set(i + l, d0 as u32);
                        drs_.set(i + l, dr);
                    }
                }
                l = if l >= 32 && l < k { next_end(ct, l, k) } else { l + 1 };
            }
        }
        // The matches found.
        let a = offs[i] as usize;
        let b = offs[i + 1] as usize;
        let mut prev: usize = 3;
        let mut j = a;
        while j < b && j < ms.len() && jump == 0
            invariant
                i + rest == m,
                m < 0x1000_0000,
                cost@.len() == m + 1,
                flen@.len() == m + 1,
                fdist@.len() == m + 1,
                drs_@.len() == m + 1,
                co.cmd@.len() == 704,
                co.dist@.len() == 64,
                forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
                forall|i: int| 0 <= i < 64 ==> #[trigger] co.dist@[i] <= 16 * 40,
                ct@.len() == 0x1_0000,
                c0 < 0xF000_0000,
                te@.len() == 576,
                tl@.len() == 576,
                forall|i: int| 0 <= i < 576 ==> #[trigger] te@[i] <= 16 * 100,
                forall|i: int| 0 <= i < 576 ==> #[trigger] tl@[i] <= 16 * 100,
                ic < 24,
            decreases b - j,
        {
            let (len, dist) = ms[j];
            let len = len as usize;
            j = j + 1;
            if len > rest || len <= prev || dist == 0 {
                continue;
            }
            let dc = dist_cost(co, dist, dr);
            let nd = if dist == dr[0] { dr } else { [dist, dr[0], dr[1], dr[2]] };
            let from = if len >= LONG { len } else { prev + 1 };
            let mut l = from;
            while l <= len
                invariant
                    len <= rest,
                    i + rest == m,
                    m < 0x1000_0000,
                    cost@.len() == m + 1,
                    flen@.len() == m + 1,
                    fdist@.len() == m + 1,
                    drs_@.len() == m + 1,
                    co.cmd@.len() == 704,
                    forall|i: int| 0 <= i < 704 ==> #[trigger] co.cmd@[i] <= 16 * 40,
                    ct@.len() == 0x1_0000,
                    c0 < 0xF000_0000,
                    dc <= 16 * 100,
                    te@.len() == 576,
                    tl@.len() == 576,
                    forall|i: int| 0 <= i < 576 ==> #[trigger] te@[i] <= 16 * 100,
                    forall|i: int| 0 <= i < 576 ==> #[trigger] tl@[i] <= 16 * 100,
                    ic < 24,
                decreases len + 1 - l,
            {
                let cc = if l < 0x1_0000 { ct[l] as usize } else { 24 };
                if cc < 24 {
                    let c = c0 + (if dist == dr[0] { tl[ic * 24 + cc] } else { te[ic * 24 + cc] }) + dc;
                    if c < cost[i + l] {
                        cost.set(i + l, c);
                        flen.set(i + l, l as u32);
                        fdist.set(i + l, dist);
                        drs_.set(i + l, nd);
                    }
                }
                // Past 32, only the longest length of each copy code: the
                // shorter ones cost the same and reach less far.
                l = if l >= 32 && l < len { next_end(ct, l, len) } else { l + 1 };
            }
            if len >= LONG {
                jump = len;
            }
            prev = len;
        }
        i = if jump > 0 && jump <= m - i { i + jump } else { i + 1 };
    }
    // Back from the end.
    let mut rev: Vec<(u32, u32)> = Vec::new();
    let mut p = m;
    let mut lits: u32 = 0;
    let mut pend: u32 = 0;
    while p > 0
        invariant
            p <= m,
            flen@.len() == m + 1,
            fdist@.len() == m + 1,
        decreases p,
    {
        let l = flen[p] as usize;
        if l == 0 || l > p {
            p = p - 1;
            if lits < 0x1000_0000 {
                lits = lits + 1;
            }
        } else {
            // A copy ending at p; the literals after it come with the next.
            rev.push((l as u32, fdist[p]));
            rev.push((pend, lits));
            pend = 1;
            lits = 0;
            p = p - l;
        }
    }
    // `rev` holds (len, dist), then the literal count after it (marked
    // with 1 once a copy followed); forwards now.
    let mut out: Vec<Lz> = Vec::new();
    let mut k = rev.len();
    let mut ins = lits;
    while k >= 2
        invariant
            k <= rev@.len(),
        decreases k,
    {
        let (_mark, after) = rev[k - 1];
        let (l, d) = rev[k - 2];
        out.push(Lz { ins, clen: l, dist: d });
        ins = after;
        k = k - 2;
    }
    if ins > 0 {
        out.push(Lz { ins, clen: 0, dist: 0 });
    }
    out
}


/// The optimal parse of `data[start..end]`, with last distances `dr`.
pub fn parse_opt(mf: &mut Mf, data: &[u8], start: usize, end: usize, dr: [u32; 4]) -> (r: Vec<Lz>)
    requires
        old(mf).wf(data@.len()),
        start <= end <= data@.len(),
    ensures
        final(mf).wf(data@.len()),
        final(mf).wmax == old(mf).wmax,
{
    let mut ms: Vec<(u32, u32)> = Vec::new();
    let mut offs: Vec<u32> = Vec::new();
    all_matches(mf, data, start, end, &mut ms, &mut offs);
    let ct = cpy_table();
    // First round: literal costs from the block's bytes, the rest flat.
    let mut lf = vec![0u32; 256];
    let mut k = start;
    while k < end
        invariant
            lf@.len() == 256,
            end <= data@.len(),
        decreases end - k,
    {
        let b = data[k] as usize;
        let v = lf[b];
        if v < 0xFFFF_FFFF {
            lf.set(b, v + 1);
        }
        k = k + 1;
    }
    let cf = vec![1u32; 704];
    let df = vec![1u32; 64];
    let co = costs_from(&lf, &cf, &df);
    let mut lz = shortest(data, start, end, &ms, &offs, &co, &ct, dr);
    // Then twice with the counts of the parse before.
    let mut round: u32 = 0;
    while round < 2
        invariant
            start <= end <= data@.len(),
            ct@.len() == 0x1_0000,
        decreases 2 - round,
    {
        let mut lf = vec![0u32; 256];
        let mut cf = vec![0u32; 704];
        let mut df = vec![0u32; 64];
        if symbols(&lz, data, start, dr, mf.wmax, &mut lf, &mut cf, &mut df).is_none() {
            break;
        }
        let co = costs_from(&lf, &cf, &df);
        lz = shortest(data, start, end, &ms, &offs, &co, &ct, dr);
        round = round + 1;
    }
    lz
}

} // verus!
