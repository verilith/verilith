//! The verified zip reader: `parse_zip` computes `spec::zip` exactly.
use crate::spec::*;
use verilith_core::sort::order_by;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// One archive member.
#[derive(Debug)]
pub struct Entry {
    pub name: Vec<u8>,
    pub kind: Kind,
    pub link: Vec<u8>,
    pub method: u16,
    pub encrypted: bool,
    pub crc: u32,
    pub has_crc: bool,
    pub hdr_off: usize,
    pub data_off: usize,
    pub csize: usize,
    pub size: u64,
    pub mode: u32,
    pub mtime: i64,
}

impl Entry {
    /// The member this is, in the specification's terms.
    pub open spec fn sv(&self) -> SEntry {
        SEntry {
            name: self.name@,
            kind: self.kind,
            link: self.link@,
            method: self.method as int,
            encrypted: self.encrypted,
            crc: self.crc as int,
            has_crc: self.has_crc,
            hdr_off: self.hdr_off as int,
            data_off: self.data_off as int,
            csize: self.csize as int,
            size: self.size as int,
            mode: self.mode as int,
            mtime: self.mtime as int,
        }
    }
}

pub open spec fn views(v: Seq<Entry>) -> Seq<SEntry> {
    Seq::new(v.len(), |i: int| v[i].sv())
}

#[inline]
pub fn rd16(b: &[u8], i: usize) -> (r: u16)
    requires
        i + 2 <= b@.len(),
    ensures
        r as int == le16(b@, i as int),
{
    let _ = b.len();
    b[i] as u16 + 256 * (b[i + 1] as u16)
}

#[inline]
pub fn rd32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as int == le32(b@, i as int),
{
    let _ = b.len();
    rd16(b, i) as u32 + 0x1_0000 * (rd16(b, i + 2) as u32)
}

#[inline]
pub fn rd64(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
    ensures
        r as int == le64(b@, i as int),
{
    let _ = b.len();
    rd32(b, i) as u64 + 0x1_0000_0000 * (rd32(b, i + 4) as u64)
}

/// Whether the `n` bytes at `a` equal the `n` bytes at `c`.
pub fn eq_range(b: &[u8], a: usize, c: usize, n: usize) -> (r: bool)
    requires
        a + n <= b@.len(),
        c + n <= b@.len(),
    ensures
        r == (b@.subrange(a as int, a + n) == b@.subrange(c as int, c + n)),
{
    let _ = b.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            b@.len() <= usize::MAX,
            a + n <= b@.len(),
            c + n <= b@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] b@[a + k] == b@[c + k],
        decreases n - i,
    {
        if b[a + i] != b[c + i] {
            proof {
                assert(b@.subrange(a as int, a + n)[i as int] != b@.subrange(c as int, c + n)[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        let x = b@.subrange(a as int, a + n);
        let y = b@.subrange(c as int, c + n);
        assert forall|k: int| 0 <= k < n implies x[k] == y[k] by {
            assert(b@[a + k] == b@[c + k]);
        }
        assert(x =~= y);
    }
    true
}

/// A copy of the `n` bytes at `a`.
pub fn copy_range(b: &[u8], a: usize, n: usize) -> (v: Vec<u8>)
    requires
        a + n <= b@.len(),
    ensures
        v@ == b@.subrange(a as int, a + n),
{
    let _ = b.len();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(slice_subrange(b, a, a + n));
    v
}

fn find_eocd(b: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => eocd_pos(b@) == Some(p as int) && eocd_at(b@, p as int),
            None => eocd_pos(b@) is None,
        },
{
    let n = b.len();
    if n < 22 {
        return None;
    }
    let lo = if n >= 22 + 65535 {
        n - 22 - 65535
    } else {
        0
    };
    let mut p = n - 22;
    loop
        invariant
            n == b@.len(),
            n >= 22,
            lo <= p <= n - 22,
            eocd_pos(b@) == eocd_scan(b@, p as int, lo as int),
        decreases p,
    {
        if rd32(b, p) == 0x06054b50 && rd16(b, p + 20) as usize == n - 22 - p {
            return Some(p);
        }
        if p == lo {
            proof {
                assert(!eocd_at(b@, p as int));
                assert(eocd_scan(b@, p - 1, lo as int) is None);
            }
            return None;
        }
        proof {
            assert(!eocd_at(b@, p as int));
        }
        p -= 1;
    }
}

/// The end record, in machine integers.
pub struct EndRec {
    pub n: u64,
    pub cd_off: usize,
    pub cd_size: usize,
    pub end: usize,
}

impl EndRec {
    pub open spec fn sv(&self) -> End {
        End { n: self.n as int, cd_off: self.cd_off as int, cd_size: self.cd_size as int, end: self.end as int }
    }
}

fn zip64_end_exec(b: &[u8], p: usize) -> (r: Option<(u64, u64, u64, usize)>)
    requires
        eocd_at(b@, p as int),
        p >= 20,
    ensures
        match r {
            Some((n, cd_off, cd_size, end)) => zip64_end(b@, p as int) == Some(
                End { n: n as int, cd_off: cd_off as int, cd_size: cd_size as int, end: end as int },
            ) && end <= p,
            None => zip64_end(b@, p as int) is None,
        },
{
    proof {
        reveal(zip64_end);
    }
    let _ = b.len();
    let l = p - 20;
    let q = rd64(b, l + 8);
    if rd32(b, l + 4) != 0 || rd32(b, l + 16) > 1 || q > l as u64 || l as u64 - q < 56 {
        return None;
    }
    let q = q as usize;
    if rd32(b, q) != 0x06064b50 {
        return None;
    }
    if rd32(b, q + 16) != 0 || rd32(b, q + 20) != 0 || rd64(b, q + 24) != rd64(b, q + 32) {
        return None;
    }
    let n = rd64(b, q + 32);
    let cd_size = rd64(b, q + 40);
    let cd_off = rd64(b, q + 48);
    let c1 = rd16(b, p + 4);
    let c2 = rd16(b, p + 6);
    let c3 = rd16(b, p + 8);
    let c4 = rd16(b, p + 10);
    let c5 = rd32(b, p + 12);
    let c6 = rd32(b, p + 16);
    if (c1 == 0 || c1 == 0xffff) && (c2 == 0 || c2 == 0xffff) && (c3 as u64 == n || c3 == 0xffff) && (c4 as u64 == n
        || c4 == 0xffff) && (c5 as u64 == cd_size || c5 == 0xffff_ffff) && (c6 as u64 == cd_off || c6
        == 0xffff_ffff) {
        Some((n, cd_off, cd_size, q))
    } else {
        None
    }
}

fn parse_end(b: &[u8]) -> (r: Option<EndRec>)
    ensures
        match r {
            Some(e) => zip_end(b@) == Some(e.sv()) && e.cd_off + e.cd_size <= e.end <= b@.len(),
            None => zip_end(b@) is None,
        },
{
    let _ = b.len();
    let p = match find_eocd(b) {
        Some(p) => p,
        None => return None,
    };
    let (n, cd_off, cd_size, end) = if p >= 20 && rd32(b, p - 20) == 0x07064b50 {
        match zip64_end_exec(b, p) {
            Some(t) => t,
            None => return None,
        }
    } else {
        if rd16(b, p + 4) != 0 || rd16(b, p + 6) != 0 || rd16(b, p + 8) != rd16(b, p + 10) {
            return None;
        }
        (rd16(b, p + 10) as u64, rd32(b, p + 16) as u64, rd32(b, p + 12) as u64, p)
    };
    if cd_off > end as u64 || cd_size > end as u64 - cd_off {
        return None;
    }
    Some(EndRec { n, cd_off: cd_off as usize, cd_size: cd_size as usize, end })
}

fn find_extra_exec(x: &[u8], id: u16) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((o, l)) => find_extra(x@, 0, id as int) == Some((o as int, l as int)) && o + l <= x@.len(),
            None => find_extra(x@, 0, id as int) is None,
        },
{
    let n = x.len();
    let mut i: usize = 0;
    loop
        invariant
            n == x@.len(),
            i <= n,
            find_extra(x@, 0, id as int) == find_extra(x@, i as int, id as int),
        decreases n - i,
    {
        if n - i < 4 {
            return None;
        }
        let l = rd16(x, i + 2) as usize;
        if n - i - 4 < l {
            return None;
        }
        if rd16(x, i) == id {
            return Some((i + 4, l));
        }
        i = i + 4 + l;
    }
}

fn zip64_fields_exec(x: &[u8], usize32: u32, csize32: u32, lho32: u32, disk16: u16) -> (r: Option<
    (u64, u64, u64, u32),
>)
    ensures
        match r {
            Some((s, c, l, d)) => zip64_fields(x@, usize32 as int, csize32 as int, lho32 as int, disk16 as int)
                == Some((s as int, c as int, l as int, d as int)),
            None => zip64_fields(x@, usize32 as int, csize32 as int, lho32 as int, disk16 as int) is None,
        },
{
    proof {
        reveal(zip64_fields);
    }
    let _ = x.len();
    let nu = usize32 == 0xffff_ffff;
    let nc = csize32 == 0xffff_ffff;
    let nl = lho32 == 0xffff_ffff;
    let nd = disk16 == 0xffff;
    if !nu && !nc && !nl && !nd {
        return Some((usize32 as u64, csize32 as u64, lho32 as u64, disk16 as u32));
    }
    let (o, l) = match find_extra_exec(x, 1) {
        Some(t) => t,
        None => return None,
    };
    let need: usize = (if nu { 8usize } else { 0 }) + (if nc { 8usize } else { 0 }) + (if nl { 8usize } else { 0 }) + (if nd { 4usize } else { 0 });
    if need > l {
        return None;
    }
    let o1 = o + if nu { 8 } else { 0 };
    let o2 = o1 + if nc { 8 } else { 0 };
    let o3 = o2 + if nl { 8 } else { 0 };
    Some(
        (
            if nu { rd64(x, o) } else { usize32 as u64 },
            if nc { rd64(x, o1) } else { csize32 as u64 },
            if nl { rd64(x, o2) } else { lho32 as u64 },
            if nd { rd32(x, o3) } else { disk16 as u32 },
        ),
    )
}

fn zip_entry_exec(b: &[u8], p: usize, eo: &EndRec) -> (r: Option<(Entry, usize)>)
    requires
        eo.cd_off + eo.cd_size <= eo.end <= b@.len(),
        p <= eo.cd_off + eo.cd_size,
    ensures
        match r {
            Some((e, next)) => zip_entry(b@, p as int, eo.sv()) == Some((e.sv(), next as int)) && next <= eo.cd_off
                + eo.cd_size && e.hdr_off + 30 <= e.data_off && e.data_off + e.csize <= eo.cd_off,
            None => zip_entry(b@, p as int, eo.sv()) is None,
        },
{
    proof {
        reveal(zip_entry);
    }
    let _ = b.len();
    let cd_end = eo.cd_off + eo.cd_size;
    if cd_end - p < 46 || rd32(b, p) != 0x02014b50 {
        return None;
    }
    let made = rd16(b, p + 4);
    let flags = rd16(b, p + 8);
    let method = rd16(b, p + 10);
    let nlen = rd16(b, p + 28) as usize;
    let xlen = rd16(b, p + 30) as usize;
    let clen = rd16(b, p + 32) as usize;
    if cd_end - p - 46 < nlen + xlen + clen {
        return None;
    }
    let next = p + 46 + nlen + xlen + clen;
    let x = slice_subrange(b, p + 46 + nlen, p + 46 + nlen + xlen);
    let (size, csize, lho, disk) = match zip64_fields_exec(
        x,
        rd32(b, p + 24),
        rd32(b, p + 20),
        rd32(b, p + 42),
        rd16(b, p + 34),
    ) {
        Some(t) => t,
        None => return None,
    };
    if disk != 0 || lho > eo.cd_off as u64 || eo.cd_off as u64 - lho < 30 {
        return None;
    }
    let lho = lho as usize;
    if rd32(b, lho) != 0x04034b50 {
        return None;
    }
    let ln = rd16(b, lho + 26) as usize;
    let lx = rd16(b, lho + 28) as usize;
    let room = eo.cd_off - lho - 30;
    if room < ln + lx {
        return None;
    }
    let data = lho + 30 + ln + lx;
    if csize > (eo.cd_off - data) as u64 || ln != nlen {
        return None;
    }
    if !eq_range(b, lho + 30, p + 46, nlen) || rd16(b, lho + 8) != method || rd16(b, lho + 6) % 2 != flags % 2 {
        return None;
    }
    let xattr = rd32(b, p + 38);
    let name = copy_range(b, p + 46, nlen);
    let unix = made / 256 == 3;
    let kind = if nlen > 0 && b[p + 46 + nlen - 1] == 0x2f {
        Kind::Dir
    } else if unix && (xattr / 0x1_0000) / 4096 == 10 {
        Kind::Symlink
    } else {
        Kind::File
    };
    let mode = if unix {
        (xattr / 0x1_0000) % 4096
    } else {
        0
    };
    let e = Entry {
        name,
        kind,
        link: Vec::new(),
        method,
        encrypted: flags % 2 == 1,
        crc: rd32(b, p + 16),
        has_crc: true,
        hdr_off: lho,
        data_off: data,
        csize: csize as usize,
        size,
        mode,
        mtime: rd16(b, p + 14) as i64 * 0x1_0000 + rd16(b, p + 12) as i64,
    };
    proof {
        assert(e.link@ =~= Seq::<u8>::empty());
    }
    Some((e, next))
}

// ---------------------------------------------------------------------
// No two members overlap.
// ---------------------------------------------------------------------
/// Every member's range is non-empty and inside the archive.
pub open spec fn ranges_ok(es: Seq<Entry>, len: int) -> bool {
    forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i]).hdr_off < es[i].data_off && es[i].data_off + es[i].csize <= len
}

proof fn lemma_chain(s: Seq<int>, e: Seq<int>, a: int, c: int)
    requires
        s.len() == e.len(),
        0 <= a < c < s.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] < e[k],
        forall|k: int| 0 <= k < s.len() - 1 ==> #[trigger] e[k] <= s[k + 1],
    ensures
        e[a] <= s[c],
    decreases c - a,
{
    if a + 1 < c {
        lemma_chain(s, e, a + 1, c);
        assert(e[a] <= s[a + 1]);
        assert(s[a + 1] < e[a + 1]);
    } else {
        assert(e[a] <= s[a + 1]);
    }
}

/// The members' positions, sorted by header offset (verilith-core's merge
/// sort). `check_order` checks it again, in linear time, as it decides
/// whether the members overlap.
fn order_by_offset(es: &Vec<Entry>) -> (r: Vec<usize>) {
    let le = |i: usize, j: usize| -> (r: bool)
        requires
            i < es@.len(),
            j < es@.len(),
        ensures
            r == (es@[i as int].hdr_off <= es@[j as int].hdr_off),
        { es[i].hdr_off <= es[j].hdr_off };
    order_by(es.len(), &le, Ghost(|i: usize, j: usize| es@[i as int].hdr_off <= es@[j as int].hdr_off))
}

enum Order {
    Disjoint,
    Overlap,
    /// `ord` is not a permutation sorted by header offset.
    Unusable,
}

/// Decides `disjoint` from an order sorted by header offset, in linear
/// time; or reports that `ord` is not such an order.
fn check_order(es: &Vec<Entry>, ord: &Vec<usize>, Ghost(len): Ghost<int>) -> (r: Order)
    requires
        ranges_ok(es@, len),
        len <= usize::MAX,
    ensures
        r is Disjoint ==> disjoint(views(es@)),
        r is Overlap ==> !disjoint(views(es@)),
{
    let n = es.len();
    if ord.len() != n {
        return Order::Unusable;
    }
    // inv[i] is where member i sits in `ord`.
    let mut inv: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            inv@.len() == i,
            forall|k: int| 0 <= k < i ==> inv@[k] == n,
        decreases n - i,
    {
        inv.push(n);
        i += 1;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == es@.len(),
            ord@.len() == n,
            inv@.len() == n,
            forall|m: int| #![auto] 0 <= m < k ==> ord@[m] < n && inv@[ord@[m] as int] == m,
            forall|i: int| #![auto] 0 <= i < n ==> inv@[i] == n || (inv@[i] < k && ord@[inv@[i] as int] == i),
        decreases n - k,
    {
        let i = ord[k];
        if i >= n || inv[i] != n {
            return Order::Unusable;
        }
        inv.set(i, k);
        k += 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            inv@.len() == n,
            forall|j: int| 0 <= j < i ==> inv@[j] < n,
        decreases n - i,
    {
        if inv[i] >= n {
            return Order::Unusable;
        }
        i += 1;
    }
    let ghost vs = views(es@);
    let ghost s = Seq::new(n as nat, |k: int| es@[ord@[k] as int].hdr_off as int);
    let ghost e = Seq::new(n as nat, |k: int| es@[ord@[k] as int].data_off + es@[ord@[k] as int].csize);
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k,
            n == es@.len(),
            ord@.len() == n,
            ranges_ok(es@, len),
            len <= usize::MAX,
            vs == views(es@),
            s == Seq::new(n as nat, |k: int| es@[ord@[k] as int].hdr_off as int),
            e == Seq::new(n as nat, |k: int| es@[ord@[k] as int].data_off + es@[ord@[k] as int].csize),
            forall|m: int| #![auto] 0 <= m < n ==> ord@[m] < n && inv@[ord@[m] as int] == m,
            forall|m: int| 0 <= m < k - 1 ==> #[trigger] e[m] <= s[m + 1],
        decreases n - k,
    {
        let a = &es[ord[k - 1]];
        let c = &es[ord[k]];
        if a.hdr_off > c.hdr_off {
            return Order::Unusable;
        }
        if a.data_off + a.csize > c.hdr_off {
            proof {
                let i = ord@[k - 1] as int;
                let j = ord@[k as int] as int;
                assert(inv@[i] == k - 1 && inv@[j] == k);
                assert(i != j);
                assert(vs[i].end() > vs[j].hdr_off);
                assert(vs[j].end() > vs[i].hdr_off);
            }
            return Order::Overlap;
        }
        proof {
            assert(e[k - 1] <= s[k as int]);
        }
        k += 1;
    }
    proof {
        assert forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && i != j implies #[trigger] vs[i].end()
            <= (#[trigger] vs[j]).hdr_off || vs[j].end() <= vs[i].hdr_off by {
            let a = inv@[i] as int;
            let c = inv@[j] as int;
            assert(ord@[a] == i && ord@[c] == j);
            assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] < e[k] by {
                assert(es@[ord@[k] as int].hdr_off < es@[ord@[k] as int].data_off);
            }
            if a < c {
                lemma_chain(s, e, a, c);
            } else {
                lemma_chain(s, e, c, a);
            }
        }
    }
    Order::Disjoint
}

/// Decides `disjoint` by comparing every pair. Reached only if
/// `order_by_offset` did not sort.
fn check_pairs(es: &Vec<Entry>, Ghost(len): Ghost<int>) -> (r: bool)
    requires
        ranges_ok(es@, len),
        len <= usize::MAX,
    ensures
        r == disjoint(views(es@)),
{
    let n = es.len();
    let ghost vs = views(es@);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == es@.len(),
            vs == views(es@),
            ranges_ok(es@, len),
            len <= usize::MAX,
            forall|a: int, c: int|
                0 <= a < i && 0 <= c < n && a != c ==> #[trigger] vs[a].end() <= (#[trigger] vs[c]).hdr_off
                    || vs[c].end() <= vs[a].hdr_off,
        decreases n - i,
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < n,
                j <= n,
                n == es@.len(),
                vs == views(es@),
                ranges_ok(es@, len),
            len <= usize::MAX,
                forall|c: int|
                    0 <= c < j && i != c ==> vs[i as int].end() <= (#[trigger] vs[c]).hdr_off || vs[c].end()
                        <= vs[i as int].hdr_off,
            decreases n - j,
        {
            if i != j {
                let a = &es[i];
                let c = &es[j];
                if !(a.data_off + a.csize <= c.hdr_off || c.data_off + c.csize <= a.hdr_off) {
                    proof {
                        assert(!(vs[i as int].end() <= vs[j as int].hdr_off || vs[j as int].end() <= vs[i as int].hdr_off));
                    }
                    return false;
                }
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert forall|a: int, c: int| 0 <= a < vs.len() && 0 <= c < vs.len() && a != c implies #[trigger] vs[a].end()
            <= (#[trigger] vs[c]).hdr_off || vs[c].end() <= vs[a].hdr_off by {
            if a < c {
            }
        }
    }
    true
}

fn check_disjoint(es: &Vec<Entry>, Ghost(len): Ghost<int>) -> (r: bool)
    requires
        ranges_ok(es@, len),
        len <= usize::MAX,
    ensures
        r == disjoint(views(es@)),
{
    // Archives are normally written in directory order: try that first.
    let n = es.len();
    let mut ident: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i,
    {
        ident.push(i);
        i += 1;
    }
    match check_order(es, &ident, Ghost(len)) {
        Order::Disjoint => return true,
        Order::Overlap => return false,
        Order::Unusable => {},
    }
    let ord = order_by_offset(es);
    match check_order(es, &ord, Ghost(len)) {
        Order::Disjoint => true,
        Order::Overlap => false,
        Order::Unusable => check_pairs(es, Ghost(len)),
    }
}

/// **The zip reader.** Returns the members of `b` exactly when `b` is a
/// zip archive by `spec::zip`, and `None` exactly when it is not.
///
/// So for a returned list: every member's header and data lie inside `b`
/// (`in_bounds`), before the central directory, and no two members share a
/// byte (`disjoint`).
pub fn parse_zip(b: &[u8]) -> (r: Option<Vec<Entry>>)
    ensures
        match r {
            Some(es) => zip(b@) == Some(views(es@)) && disjoint(views(es@)) && in_bounds(views(es@), b@.len() as int),
            None => zip(b@) is None,
        },
{
    let eo = match parse_end(b) {
        Some(e) => e,
        None => return None,
    };
    let mut es: Vec<Entry> = Vec::new();
    let mut p = eo.cd_off;
    let mut k: u64 = 0;
    proof {
        assert(views(es@) =~= Seq::<SEntry>::empty());
        match zip_entries(b@, p as int, eo.n as nat, eo.sv()) {
            Some(x) => {
                assert(views(es@) + x =~= x);
            },
            None => {},
        }
    }
    while k < eo.n
        invariant
            k <= eo.n,
            zip_end(b@) == Some(eo.sv()),
            eo.cd_off + eo.cd_size <= eo.end <= b@.len(),
            p <= eo.cd_off + eo.cd_size,
            ranges_ok(es@, eo.cd_off as int),
            zip_entries(b@, eo.cd_off as int, eo.n as nat, eo.sv()) == (match zip_entries(
                b@,
                p as int,
                (eo.n - k) as nat,
                eo.sv(),
            ) {
                Some(rest) => Some(views(es@) + rest),
                None => None,
            }),
        decreases eo.n - k,
    {
        let ghost old_es = es@;
        match zip_entry_exec(b, p, &eo) {
            None => {
                proof {
                    assert(zip_entries(b@, p as int, (eo.n - k) as nat, eo.sv()) is None);
                }
                return None;
            },
            Some((e, next)) => {
                proof {
                    let rest = zip_entries(b@, next as int, (eo.n - k - 1) as nat, eo.sv());
                    if rest is Some {
                        assert(views(old_es.push(e)) + rest.unwrap() =~= views(old_es) + (seq![e.sv()] + rest.unwrap()));
                    }
                }
                es.push(e);
                p = next;
            },
        }
        k += 1;
    }
    if p != eo.cd_off + eo.cd_size {
        return None;
    }
    proof {
        assert(views(es@) + Seq::<SEntry>::empty() =~= views(es@));
        assert(zip_listed(b@) == Some(views(es@)));
    }
    if !check_disjoint(&es, Ghost(eo.cd_off as int)) {
        return None;
    }
    Some(es)
}

} // verus!
