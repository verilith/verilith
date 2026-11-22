//! The verified tar reader: `parse_tar` computes `spec::tar` exactly.
use crate::spec::*;
use crate::zip::{copy_range, Entry};
#[cfg(verus_only)]
use crate::zip::views;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

fn cstr_exec(f: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == cstr(f@),
{
    let n = f.len();
    let mut i: usize = 0;
    while i < n && f[i] != 0
        invariant
            i <= n,
            n == f@.len(),
            nul_from(f@, 0) == nul_from(f@, i as int),
        decreases n - i,
    {
        i += 1;
    }
    copy_range(f, 0, i)
}

fn octal_exec(f: &[u8]) -> (r: Option<u64>)
    ensures
        match r {
            Some(v) => octal(f@) == Some(v as int) && v < 0x8000_0000_0000_0000,
            None => octal(f@) is None,
        },
{
    let n = f.len();
    let mut i: usize = 0;
    while i < n && f[i] == 0x20
        invariant
            i <= n,
            n == f@.len(),
            skip_sp(f@, 0) == skip_sp(f@, i as int),
        decreases n - i,
    {
        i += 1;
    }
    let mut acc: u64 = 0;
    loop
        invariant
            i <= n,
            n == f@.len(),
            acc < 0x8000_0000_0000_0000,
            octal(f@) == oct_from(f@, i as int, acc as int),
        decreases n - i,
    {
        if i >= n {
            return Some(acc);
        }
        let c = f[i];
        if 0x30 <= c && c <= 0x37 {
            if acc >= 0x1000_0000_0000_0000 {
                return None;
            }
            acc = acc * 8 + (c - 0x30) as u64;
            i += 1;
        } else if c == 0x20 || c == 0 {
            return Some(acc);
        } else {
            return None;
        }
    }
}

fn tar_num_exec(f: &[u8]) -> (r: Option<u64>)
    ensures
        match r {
            Some(v) => tar_num(f@) == Some(v as int) && v < 0x8000_0000_0000_0000,
            None => tar_num(f@) is None,
        },
{
    let n = f.len();
    if n > 0 && f[0] >= 0x80 {
        if f[0] != 0x80 {
            return None;
        }
        let mut i: usize = 1;
        let mut acc: u64 = 0;
        loop
            invariant
                1 <= i <= n,
                n == f@.len(),
                acc < 0x8000_0000_0000_0000,
                tar_num(f@) == be_from(f@, i as int, acc as int),
            decreases n - i,
        {
            if i >= n {
                return Some(acc);
            }
            if acc >= 0x80_0000_0000_0000 {
                return None;
            }
            acc = acc * 256 + f[i] as u64;
            i += 1;
        }
    } else {
        octal_exec(f)
    }
}

fn sum_exec(h: &[u8], n: usize) -> (s: u64)
    requires
        n <= h@.len(),
        n <= 512,
    ensures
        s as int == sum_to(h@, n as int),
        s <= 255 * n,
{
    let mut s: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= h@.len(),
            n <= 512,
            s as int == sum_to(h@, i as int),
            s <= 255 * i,
        decreases n - i,
    {
        s = s + h[i] as u64;
        i += 1;
    }
    s
}

fn all_zero_exec(h: &[u8]) -> (r: bool)
    ensures
        r == all_zero(h@),
{
    let n = h.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == h@.len(),
            forall|k: int| 0 <= k < i ==> h@[k] == 0,
        decreases n - i,
    {
        if h[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

pub struct Hdr {
    pub name: Vec<u8>,
    pub mode: u32,
    pub size: u64,
    pub mtime: i64,
    pub typeflag: u8,
    pub linkname: Vec<u8>,
}

impl Hdr {
    pub open spec fn sv(&self) -> THeader {
        THeader {
            name: self.name@,
            mode: self.mode as int,
            size: self.size as int,
            mtime: self.mtime as int,
            typeflag: self.typeflag,
            linkname: self.linkname@,
        }
    }
}

fn header_exec(h: &[u8]) -> (r: Option<Hdr>)
    requires
        h@.len() == 512,
    ensures
        match r {
            Some(hd) => tar_header(h@) == Some(hd.sv()) && hd.size < 0x8000_0000_0000_0000,
            None => tar_header(h@) is None,
        },
{
    proof {
        reveal(tar_header);
    }
    let c = match octal_exec(slice_subrange(h, 148, 156)) {
        Some(c) => c,
        None => return None,
    };
    let s148 = sum_exec(h, 148);
    let s156 = sum_exec(h, 156);
    let s512 = sum_exec(h, 512);
    if c > 0x10_0000 || c + s156 != s148 + 256 + s512 {
        proof {
            assert(sum_to(h@, 148) <= 255 * 148);
            assert(sum_to(h@, 512) <= 255 * 512);
            assert(sum_to(h@, 156) >= 0);
        }
        return None;
    }
    let size = match tar_num_exec(slice_subrange(h, 124, 136)) {
        Some(s) => s,
        None => return None,
    };
    let nm = cstr_exec(slice_subrange(h, 0, 100));
    let pf = cstr_exec(slice_subrange(h, 345, 500));
    let ustar = h[257] == 0x75 && h[258] == 0x73 && h[259] == 0x74 && h[260] == 0x61 && h[261] == 0x72 && h[262]
        == 0;
    let name = if ustar && pf.len() > 0 {
        let ghost pf0 = pf@;
        let mut v = pf;
        v.push(0x2f);
        v.extend_from_slice(nm.as_slice());
        proof {
            assert(v@ =~= pf0 + seq![0x2fu8] + nm@);
        }
        v
    } else {
        nm
    };
    let mode = match octal_exec(slice_subrange(h, 100, 108)) {
        Some(m) => (m % 4096) as u32,
        None => 0,
    };
    let mtime = match tar_num_exec(slice_subrange(h, 136, 148)) {
        Some(t) => t as i64,
        None => 0,
    };
    let linkname = cstr_exec(slice_subrange(h, 157, 257));
    Some(Hdr { name, mode, size, mtime, typeflag: h[156], linkname })
}

// ---------------------------------------------------------------------
// pax extended headers
// ---------------------------------------------------------------------
pub struct PendX {
    pub path: Option<Vec<u8>>,
    pub link: Option<Vec<u8>>,
    pub size: Option<u64>,
}

pub open spec fn ov(o: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

impl PendX {
    pub open spec fn sv(&self) -> Pend {
        Pend {
            path: ov(self.path),
            link: ov(self.link),
            size: match self.size {
                Some(s) => Some(s as int),
                None => None,
            },
        }
    }
}

fn dec_exec(d: &[u8], i0: usize) -> (r: Option<(u64, usize)>)
    requires
        i0 <= d@.len(),
    ensures
        match r {
            Some((v, j)) => dec_from(d@, i0 as int, 0) == Some((v as int, j as int)) && i0 <= j <= d@.len() && v
                < 0x8000_0000_0000_0000,
            None => dec_from(d@, i0 as int, 0) is None,
        },
{
    let n = d.len();
    let mut i = i0;
    let mut acc: u64 = 0;
    loop
        invariant
            i0 <= i <= n,
            n == d@.len(),
            acc < 0x8000_0000_0000_0000,
            dec_from(d@, i0 as int, 0) == dec_from(d@, i as int, acc as int),
        decreases n - i,
    {
        if i < n && 0x30 <= d[i] && d[i] <= 0x39 {
            if acc >= 0x800_0000_0000_0000 {
                return None;
            }
            acc = acc * 10 + (d[i] - 0x30) as u64;
            i += 1;
        } else {
            return Some((acc, i));
        }
    }
}

pub fn find_byte_exec(d: &[u8], i0: usize, end: usize, c: u8) -> (r: usize)
    requires
        i0 <= end <= d@.len(),
    ensures
        r == find_byte(d@, i0 as int, end as int, c),
        i0 <= r <= end,
{
    let mut i = i0;
    while i < end && d[i] != c
        invariant
            i0 <= i <= end,
            end <= d@.len(),
            find_byte(d@, i0 as int, end as int, c) == find_byte(d@, i as int, end as int, c),
        decreases end - i,
    {
        i += 1;
    }
    i
}

/// (start of keyword, index of `=`, end of value, next record).
fn pax_record_exec(d: &[u8], i: usize) -> (r: Option<(usize, usize, usize, usize)>)
    requires
        i < d@.len(),
    ensures
        match r {
            Some((a, eq, end, next)) => pax_record(d@, i as int) == Some(
                (d@.subrange(a as int, eq as int), d@.subrange(eq + 1, end as int), next as int),
            ) && a <= eq < end < next <= d@.len() && i < next,
            None => pax_record(d@, i as int) is None,
        },
{
    let n = d.len();
    let (l, j) = match dec_exec(d, i) {
        Some(t) => t,
        None => return None,
    };
    if j == i || j >= n || d[j] != 0x20 || l > (n - i) as u64 || l < 3 || l - 3 < (j - i) as u64 {
        return None;
    }
    let l = l as usize;
    let end = i + l - 1;
    if d[end] != 0x0a {
        return None;
    }
    let eq = find_byte_exec(d, j + 1, end, 0x3d);
    if eq == end {
        return None;
    }
    Some((j + 1, eq, end, i + l))
}

fn is_path(k: &[u8]) -> (r: bool)
    ensures
        r == key_path(k@),
{
    k.len() == 4 && k[0] == 0x70 && k[1] == 0x61 && k[2] == 0x74 && k[3] == 0x68
}

fn is_linkpath(k: &[u8]) -> (r: bool)
    ensures
        r == key_linkpath(k@),
{
    k.len() == 8 && k[0] == 0x6c && k[1] == 0x69 && k[2] == 0x6e && k[3] == 0x6b && is_path(slice_subrange(k, 4, 8))
}

fn is_size(k: &[u8]) -> (r: bool)
    ensures
        r == key_size(k@),
{
    k.len() == 4 && k[0] == 0x73 && k[1] == 0x69 && k[2] == 0x7a && k[3] == 0x65
}

fn pax_exec(d: &[u8], pend: PendX) -> (r: Option<PendX>)
    ensures
        match r {
            Some(p) => pax_from(d@, 0, pend.sv()) == Some(p.sv()),
            None => pax_from(d@, 0, pend.sv()) is None,
        },
{
    let n = d.len();
    let mut p = pend;
    let mut i: usize = 0;
    loop
        invariant
            i <= n,
            n == d@.len(),
            pax_from(d@, 0, pend.sv()) == pax_from(d@, i as int, p.sv()),
        decreases n - i,
    {
        if i >= n {
            return Some(p);
        }
        let (a, eq, end, next) = match pax_record_exec(d, i) {
            Some(t) => t,
            None => return None,
        };
        let k = slice_subrange(d, a, eq);
        let v = slice_subrange(d, eq + 1, end);
        if is_path(k) {
            p = PendX { path: Some(copy_range(d, eq + 1, end - eq - 1)), link: p.link, size: p.size };
        } else if is_linkpath(k) {
            p = PendX { path: p.path, link: Some(copy_range(d, eq + 1, end - eq - 1)), size: p.size };
        } else if is_size(k) {
            match dec_exec(v, 0) {
                Some((s, j)) => {
                    if j == v.len() && j > 0 {
                        p = PendX { path: p.path, link: p.link, size: Some(s) };
                    } else {
                        return None;
                    }
                },
                None => return None,
            }
        }
        i = next;
    }
}

pub enum StepX {
    End,
    Bad,
    Meta(PendX, usize),
    Member(Entry, usize),
}

fn step_exec(b: &[u8], pos: usize, pend: PendX) -> (r: StepX)
    requires
        pos <= b@.len(),
    ensures
        match r {
            StepX::End => tar_step(b@, pos as int, pend.sv()) is End,
            StepX::Bad => tar_step(b@, pos as int, pend.sv()) is Bad,
            StepX::Meta(p, next) => tar_step(b@, pos as int, pend.sv()) == Step::Meta(p.sv(), next as int) && pos
                < next <= b@.len(),
            StepX::Member(e, next) => tar_step(b@, pos as int, pend.sv()) == Step::Member(e.sv(), next as int)
                && e.hdr_off == pos && pos < e.data_off && e.data_off + e.csize <= next <= b@.len(),
        },
{
    proof {
        reveal(tar_step);
    }
    let n = b.len();
    if pos == n {
        return StepX::End;
    }
    if n - pos < 512 {
        return StepX::Bad;
    }
    let h = slice_subrange(b, pos, pos + 512);
    if all_zero_exec(h) {
        return StepX::End;
    }
    let hd = match header_exec(h) {
        Some(hd) => hd,
        None => return StepX::Bad,
    };
    let t = hd.typeflag;
    let meta = t == 0x78 || t == 0x67 || t == 0x4c || t == 0x4b || t == 0x56;
    let size: u64 = if 0x31 <= t && t <= 0x36 {
        0
    } else if meta {
        hd.size
    } else {
        match pend.size {
            Some(s) => s,
            None => hd.size,
        }
    };
    let data = pos + 512;
    let room = n - data;
    if size > room as u64 {
        return StepX::Bad;
    }
    let size = size as usize;
    let blocks = size / 512 + if size % 512 != 0 { 1usize } else { 0 };
    if blocks > room / 512 {
        return StepX::Bad;
    }
    let next = data + blocks * 512;
    proof {
        assert(blocks * 512 == ((size + 511) / 512) * 512);
    }
    if t == 0x78 {
        match pax_exec(slice_subrange(b, data, data + size), pend) {
            Some(p) => StepX::Meta(p, next),
            None => StepX::Bad,
        }
    } else if t == 0x67 || t == 0x56 {
        StepX::Meta(pend, next)
    } else if t == 0x4c {
        let v = cstr_exec(slice_subrange(b, data, data + size));
        StepX::Meta(PendX { path: Some(v), link: pend.link, size: pend.size }, next)
    } else if t == 0x4b {
        let v = cstr_exec(slice_subrange(b, data, data + size));
        StepX::Meta(PendX { path: pend.path, link: Some(v), size: pend.size }, next)
    } else if t == 0x53 || t == 0x4d {
        StepX::Bad
    } else {
        let name = match pend.path {
            Some(p) => p,
            None => hd.name,
        };
        let link = match pend.link {
            Some(l) => l,
            None => hd.linkname,
        };
        let nl = name.len();
        let kind = if t == 0x30 || t == 0 || t == 0x37 {
            if nl > 0 && name[nl - 1] == 0x2f {
                Kind::Dir
            } else {
                Kind::File
            }
        } else if t == 0x31 {
            Kind::Hardlink
        } else if t == 0x32 {
            Kind::Symlink
        } else if t == 0x35 {
            Kind::Dir
        } else {
            Kind::Other
        };
        StepX::Member(
            Entry {
                name,
                kind,
                link,
                method: 0,
                encrypted: false,
                crc: 0,
                has_crc: false,
                hdr_off: pos,
                data_off: data,
                csize: size,
                size: size as u64,
                mode: hd.mode,
                mtime: hd.mtime,
            },
            next,
        )
    }
}

/// **The tar reader.** Returns the members of `b` exactly when `b` is a
/// tar archive by `spec::tar`, and `None` exactly when it is not.
///
/// For a returned list: every member's header and data lie inside `b`
/// (`in_bounds`) and no two members share a byte (`disjoint`).
pub fn parse_tar(b: &[u8]) -> (r: Option<Vec<Entry>>)
    ensures
        match r {
            Some(es) => tar(b@) == Some(views(es@)) && disjoint(views(es@)) && in_bounds(views(es@), b@.len() as int),
            None => tar(b@) is None,
        },
{
    let n = b.len();
    let mut pos: usize = 0;
    let mut pend = PendX { path: None, link: None, size: None };
    let mut es: Vec<Entry> = Vec::new();
    proof {
        assert(views(es@) =~= Seq::<SEntry>::empty());
        match tar(b@) {
            Some(x) => {
                assert(views(es@) + x =~= x);
            },
            None => {},
        }
    }
    loop
        invariant
            pos <= n,
            n == b@.len(),
            tar(b@) == (match tar_from(b@, pos as int, pend.sv()) {
                Some(rest) => Some(views(es@) + rest),
                None => None,
            }),
            forall|i: int|
                0 <= i < es@.len() ==> (#[trigger] es@[i]).hdr_off < es@[i].data_off && es@[i].data_off + es@[i].csize
                    <= pos,
            forall|i: int, j: int|
                0 <= i < j < es@.len() ==> (#[trigger] es@[i]).data_off + es@[i].csize <= (#[trigger] es@[j]).hdr_off,
        decreases n - pos,
    {
        match step_exec(b, pos, pend) {
            StepX::End => {
                proof {
                    lemma_done(es@, n as int);
                }
                return Some(es);
            },
            StepX::Bad => {
                return None;
            },
            StepX::Meta(p, next) => {
                pend = p;
                pos = next;
            },
            StepX::Member(e, next) => {
                proof {
                    let rest = tar_from(b@, next as int, Pend { path: None, link: None, size: None });
                    if rest is Some {
                        assert(views(es@.push(e)) + rest.unwrap() =~= views(es@) + (seq![e.sv()] + rest.unwrap()));
                    }
                }
                es.push(e);
                pend = PendX { path: None, link: None, size: None };
                pos = next;
            },
        }
    }
}

proof fn lemma_done(es: Seq<Entry>, n: int)
    requires
        forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i]).hdr_off < es[i].data_off && es[i].data_off + es[i].csize <= n,
        forall|i: int, j: int|
            0 <= i < j < es.len() ==> (#[trigger] es[i]).data_off + es[i].csize <= (#[trigger] es[j]).hdr_off,
    ensures
        disjoint(views(es)),
        in_bounds(views(es), n),
        views(es) + Seq::<SEntry>::empty() == views(es),
{
    let vs = views(es);
    assert(vs + Seq::<SEntry>::empty() =~= vs);
    assert forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() && i != j implies #[trigger] vs[i].end() <= (
    #[trigger] vs[j]).hdr_off || vs[j].end() <= vs[i].hdr_off by {
        if i < j {
            assert(es[i].data_off + es[i].csize <= es[j].hdr_off);
        } else {
            assert(es[j].data_off + es[j].csize <= es[i].hdr_off);
        }
    }
    assert forall|i: int| 0 <= i < vs.len() implies 0 <= (#[trigger] vs[i]).hdr_off < vs[i].data_off && vs[i].csize >= 0
        && vs[i].end() <= n by {
        assert(es[i].hdr_off < es[i].data_off);
    }
}

} // verus!
