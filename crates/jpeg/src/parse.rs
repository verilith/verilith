//! The marker segments of a file, from SOI to EOI.
use crate::bits::*;
use crate::num::*;
use crate::scan::*;
use crate::spec::*;
use crate::stream::*;
use crate::types::*;
use vstd::prelude::*;

verus! {

/// The decoder's state between marker segments.
pub struct DecX {
    pub t: Tabs,
    pub has_f: bool,
    pub f: FrameX,
    pub g: Geom,
    pub jfif: bool,
    pub has_adobe: bool,
    pub adobe: u8,
    pub started: bool,
    pub multi: bool,
    /// 0 gray, 1 YCbCr, 2 RGB.
    pub color: u8,
    pub ql: [[u16; 64]; 3],
    pub qset: [bool; 3],
    pub co: Coefs,
}

pub open spec fn color_v(c: u8) -> Color {
    if c == 0 {
        Color::Gray
    } else if c == 1 {
        Color::YCbCr
    } else {
        Color::Rgb
    }
}

impl View for DecX {
    type V = Dec;

    open spec fn view(&self) -> Dec {
        Dec {
            t: self.t@,
            f: if self.has_f {
                Some(self.f@)
            } else {
                None
            },
            jfif: self.jfif,
            adobe: if self.has_adobe {
                Some(self.adobe)
            } else {
                None
            },
            started: self.started,
            multi: self.multi,
            color: color_v(self.color),
            ql: seq![self.ql@[0]@, self.ql@[1]@, self.ql@[2]@],
            qset: self.qset@,
            a: if self.started {
                self.co.view(self.f@.nc)
            } else {
                Seq::empty()
            },
        }
    }
}

impl DecX {
    pub open spec fn wf(&self) -> bool {
        &&& self.has_f ==> frame_ok(self.f@) && frame_basic(self.f@) && self.g.wf(self.f@)
        &&& self.started ==> self.has_f && self.co.wf(self.f@) && self.color <= 2 && (self.color == 0) == (self.f.nc
            == 1)
        &&& !self.started ==> !self.co.stream
        // A streamed scan is the file's only one: its samples are final.
        &&& self.started && self.co.stream ==> !self.multi && self.co.row == stotal(self.f@) && self.co.sqv() == seq![
            self.ql[0]@,
            self.ql[1]@,
            self.ql[2]@,
        ]
    }
}

pub fn std_tab(a: &[u8]) -> (r: HuffTab)
    requires
        16 <= a.len() <= 272,
    ensures
        r@ == std_table(a@),
{
    let mut counts = [0u8; 16];
    let mut vals = [0u8; 256];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16 <= a.len(),
            forall|j: int| 0 <= j < i ==> counts[j] == a[j],
        decreases 16 - i,
    {
        counts[i] = a[i];
        i += 1;
    }
    let mut k: usize = 0;
    while 16 + k < a.len()
        invariant
            16 + k <= a.len() <= 272,
            forall|j: int| 0 <= j < k ==> vals[j] == a[16 + j],
            forall|j: int| k <= j < 256 ==> vals[j] == 0,
        decreases a.len() - k,
    {
        vals[k] = a[16 + k];
        k += 1;
    }
    proof {
        assert(counts@ =~= a@.subrange(0, 16));
        assert(vals@ =~= std_table(a@).vals);
    }
    HuffTab { counts, vals }
}

pub fn dec_new() -> (r: DecX)
    ensures
        r@ == dec_init(),
        r.wf(),
{
    let none = HuffTab { counts: [0; 16], vals: [0; 256] };
    let c0 = Comp { id: 0, h: 1, v: 1, tq: 0 };
    let r = DecX {
        t: Tabs {
            q: [[0; 64]; 4],
            qdef: [false; 4],
            dc: [none; 4],
            dcdef: [false; 4],
            ac: [none; 4],
            acdef: [false; 4],
            ri: 0,
        },
        has_f: false,
        f: FrameX { prog: false, w: 1, h: 1, nc: 1, comps: [c0; 3] },
        g: Geom { maxh: 1, maxv: 1, mcux: 1, mcuy: 1, cw: [0; 3], ch: [0; 3], wb: [0; 3], hb: [0; 3], dw: [0; 3], dh: [0; 3] },
        jfif: false,
        has_adobe: false,
        adobe: 0,
        started: false,
        multi: false,
        color: 0,
        ql: [[0; 64]; 3],
        qset: [false; 3],
        co: Coefs {
            a0: Vec::new(),
            a1: Vec::new(),
            a2: Vec::new(),
            stream: false,
            row: 0,
            g0: Ghost(Seq::empty()),
            g1: Ghost(Seq::empty()),
            g2: Ghost(Seq::empty()),
            p0: Vec::new(),
            p1: Vec::new(),
            p2: Vec::new(),
            sq: [[0u16; 64]; 3],
            rl: [0u8; 1024],
            kt: [0i16; 24],
        },
    };
    proof {
        assert forall|i: int| 0 <= i < 4 implies r.t.q@[i]@ =~= zeros64() by {}
        assert forall|i: int| 0 <= i < 3 implies r.ql@[i]@ =~= zeros64() by {}
        let nt = no_tables();
        let nv = HuffTable { counts: Seq::new(16, |i: int| 0u8), vals: Seq::new(256, |i: int| 0u8) };
        assert(none@.counts =~= nv.counts);
        assert(none@.vals =~= nv.vals);
        assert(none@ == nv);
        assert(r.t@.q =~= nt.q);
        assert(r.t@.qdef =~= nt.qdef);
        assert(r.t@.dc =~= nt.dc);
        assert(r.t@.dcdef =~= nt.dcdef);
        assert(r.t@.ac =~= nt.ac);
        assert(r.t@.acdef =~= nt.acdef);
        assert(r@.ql =~= dec_init().ql);
        assert(r@.qset =~= dec_init().qset);
    }
    r
}

/// The DQT segment whose contents start at `p` and are `rem` bytes long.
pub fn dqt_x(data: &[u8], p: usize, rem: i32, t: &mut Tabs) -> (ok: bool)
    requires
        len_ok(data@),
        p <= data@.len() + 16,
        -2 <= rem <= 65535,
    ensures
        ok == dqt(data@, p as int, rem as int, old(t)@) is Some,
        ok ==> final(t)@ == dqt(data@, p as int, rem as int, old(t)@)->0,
{
    let ghost d = data@;
    let ghost t0 = t@;
    let mut pp = p;
    let mut rr = rem;
    while rr > 0
        invariant
            len_ok(d),
            d == data@,
            p <= d.len() + 16,
            pp + rr == p + rem,
            rr <= rem <= 65535,
            t0 == old(t)@,
            dqt(d, pp as int, rr as int, t@) == dqt(d, p as int, rem as int, t0),
        decreases rr + 200,
    {
        let ghost t1 = t@;
        let b = rd(data, pp);
        let wide = b >= 16;
        let n = (b % 16) as usize;
        if n >= 4 {
            return false;
        }
        let mut q = t.q[n];
        assert(t1.q[n as int] == q@);
        let mut i: usize = 0;
        while i < 64
            invariant
                i <= 64,
                n < 4,
                t1.q.len() == 4,
                len_ok(d),
                d == data@,
                pp <= d.len() + 0x1_0100,
                dqt_fill(d, pp + 1, wide, i as int, q@) == dqt_fill(d, pp + 1, wide, 0, t1.q[n as int]),
            decreases 64 - i,
        {
            let v = if wide {
                rd16(data, pp + 1 + 2 * i)
            } else {
                rd(data, pp + 1 + i) as u16
            };
            q[zzx(i)] = v;
            i += 1;
        }
        t.q[n] = q;
        t.qdef[n] = true;
        let size: usize = if wide {
            129
        } else {
            65
        };
        proof {
            let t2 = Tables { q: t1.q.update(n as int, q@), qdef: t1.qdef.update(n as int, true), ..t1 };
            assert(t@.q =~= t2.q);
            assert(t@.qdef =~= t2.qdef);
            assert(t@.dc =~= t2.dc);
            assert(t@.ac =~= t2.ac);
            assert(t@ == t2);
        }
        pp += size;
        rr -= size as i32;
    }
    rr == 0
}

/// The DHT segment whose contents start at `p` and are `rem` bytes long.
pub fn dht_x(data: &[u8], p: usize, rem: i32, t: &mut Tabs) -> (ok: bool)
    requires
        len_ok(data@),
        p <= data@.len() + 16,
        -2 <= rem <= 65535,
    ensures
        ok == dht(data@, p as int, rem as int, old(t)@) is Some,
        ok ==> final(t)@ == dht(data@, p as int, rem as int, old(t)@)->0,
{
    let ghost d = data@;
    let ghost t0 = t@;
    let mut pp = p;
    let mut rr = rem;
    while rr > 16
        invariant
            len_ok(d),
            d == data@,
            p <= d.len() + 16,
            pp + rr == p + rem,
            rr <= rem <= 65535,
            t0 == old(t)@,
            dht(d, pp as int, rr as int, t@) == dht(d, p as int, rem as int, t0),
        decreases rr,
    {
        let ghost t1 = t@;
        let tc = rd(data, pp) as usize;
        let mut counts = [0u8; 16];
        let mut total: usize = 0;
        let mut i: usize = 0;
        while i < 16
            invariant
                i <= 16,
                d == data@,
                pp <= d.len() + 0x1_0100,
                len_ok(d),
                total == dht_total(d, pp + 1, i as int),
                total <= 255 * i,
                forall|j: int| 0 <= j < i ==> counts[j] == byte(d, pp + 1 + j),
            decreases 16 - i,
        {
            counts[i] = rd(data, pp + 1 + i);
            total += counts[i] as usize;
            i += 1;
        }
        let ac = tc >= 16;
        let idx = if ac {
            tc - 16
        } else {
            tc
        };
        if total > 256 || total as i32 > rr - 17 || idx >= 4 {
            return false;
        }
        let mut vals = [0u8; 256];
        let mut k: usize = 0;
        while k < total
            invariant
                k <= total <= 256,
                d == data@,
                pp <= d.len() + 0x1_0100,
                len_ok(d),
                forall|j: int| 0 <= j < k ==> vals[j] == byte(d, pp + 17 + j),
                forall|j: int| k <= j < 256 ==> vals[j] == 0,
            decreases total - k,
        {
            vals[k] = rd(data, pp + 17 + k);
            k += 1;
        }
        let h = HuffTab { counts, vals };
        proof {
            let hs = dht_table(d, pp + 1, total as int);
            assert(h@.counts =~= hs.counts);
            assert(h@.vals =~= hs.vals);
            assert(h@ == hs);
        }
        if ac {
            t.ac[idx] = h;
            t.acdef[idx] = true;
            proof {
                let t2 = Tables { ac: t1.ac.update(idx as int, h@), acdef: t1.acdef.update(idx as int, true), ..t1 };
                assert(t@.q =~= t2.q);
                assert(t@.dc =~= t2.dc);
                assert(t@.ac =~= t2.ac);
                assert(t@.acdef =~= t2.acdef);
                assert(t@ == t2);
            }
        } else {
            t.dc[idx] = h;
            t.dcdef[idx] = true;
            proof {
                let t2 = Tables { dc: t1.dc.update(idx as int, h@), dcdef: t1.dcdef.update(idx as int, true), ..t1 };
                assert(t@.q =~= t2.q);
                assert(t@.dc =~= t2.dc);
                assert(t@.ac =~= t2.ac);
                assert(t@.dcdef =~= t2.dcdef);
                assert(t@ == t2);
            }
        }
        pp += 17 + total;
        rr -= 17 + total as i32;
    }
    rr == 0
}

/// The frame header at `q`.
pub fn sof_x(data: &[u8], q: usize, prog: bool) -> (r: Option<FrameX>)
    requires
        len_ok(data@),
        q <= data@.len() + 16,
    ensures
        r is Some == sof(data@, q as int, prog) is Some,
        r matches Some(f) ==> f@ == sof(data@, q as int, prog)->0 && frame_ok(f@) && frame_basic(f@),
{
    let ghost d = data@;
    let len = rd16(data, q);
    let nc = rd(data, q + 7);
    let ghost sf = sof_frame(d, q as int, prog);
    if rd(data, q + 2) != 8 || (nc != 1 && nc != 3) || len != 8 + 3 * nc as u16 {
        return None;
    }
    let h = rd16(data, q + 3);
    let w = rd16(data, q + 5);
    if w < 1 || w > 65500 || h < 1 || h > 65500 {
        return None;
    }
    let mut comps = [Comp { id: 0, h: 1, v: 1, tq: 0 };3];
    let mut c: usize = 0;
    while c < nc as usize
        invariant
            c <= nc <= 3,
            d == data@,
            len_ok(d),
            q <= d.len() + 16,
            sf.nc == nc,
            sf == sof_frame(d, q as int, prog),
            sf.comps.len() == nc,
            forall|j: int| 0 <= j < nc ==> (#[trigger] sf.comps[j]) == (Comp {
                id: byte(d, q + 8 + 3 * j),
                h: byte(d, q + 9 + 3 * j) / 16,
                v: byte(d, q + 9 + 3 * j) % 16,
                tq: byte(d, q + 10 + 3 * j),
            }),
            forall|j: int| 0 <= j < c ==> (#[trigger] comps[j]) == sf.comps[j] && 1 <= comps[j].h <= 4 && 1 <= comps[j].v <= 4,
        decreases nc - c,
    {
        let hv = rd(data, q + 9 + 3 * c);
        let ch = hv / 16;
        let cv = hv % 16;
        if ch < 1 || ch > 4 || cv < 1 || cv > 4 {
            proof {
                let x = sf.comps[c as int];
                assert(!frame_ok(sf));
            }
            return None;
        }
        comps[c] = Comp { id: rd(data, q + 8 + 3 * c), h: ch, v: cv, tq: rd(data, q + 10 + 3 * c) };
        c += 1;
    }
    let f = FrameX { prog, w, h, nc, comps };
    proof {
        assert(f@.comps =~= sf.comps);
        assert(f@ == sf);
        assert forall|j: int| 0 <= j < sf.nc implies 1 <= (#[trigger] sf.comps[j]).h <= 4 && 1 <= sf.comps[j].v <= 4 by {
            let x = comps[j];
        }
    }
    let g = geom(&f);
    let mut c: usize = 0;
    while c < nc as usize
        invariant
            c <= nc <= 3,
            f@ == sf,
            sf.nc == nc,
            d == data@,
            sf == sof_frame(d, q as int, prog),
            frame_basic(sf),
            g.wf(sf),
            f.comps == comps,
            forall|j: int| 0 <= j < c ==> maxh(sf) % (#[trigger] sf.comps[j]).h as int == 0 && maxv(sf) % sf.comps[j].v as int == 0,
        decreases nc - c,
    {
        assert(sf.comps[c as int] == comps[c as int]);
        if g.maxh % comps[c].h as u32 != 0 || g.maxv % comps[c].v as u32 != 0 {
            assert(!frame_ok(sf));
            return None;
        }
        c += 1;
    }
    assert(frame_ok(sf));
    Some(f)
}

pub proof fn lemma_find_from(f: Frame, id: u8, i: int, c: int)
    requires
        0 <= c <= i,
    ensures
        find_comp(f, id, i, c) == find_comp(f, id, i, i),
    decreases i - c,
{
    if c < i {
        lemma_find_from(f, id, i, c + 1);
        if c >= f.nc {
            lemma_find_past(f, id, i, c + 1);
            lemma_find_past(f, id, i, i);
        }
    }
}

pub proof fn lemma_find_past(f: Frame, id: u8, i: int, c: int)
    requires
        c >= f.nc,
    ensures
        find_comp(f, id, i, c) == -1,
{
}

/// The scan header at `q`.
pub fn sos_x(data: &[u8], q: usize, f: &FrameX) -> (r: Option<ScanX>)
    requires
        len_ok(data@),
        q <= data@.len() + 16,
        frame_basic(f@),
    ensures
        match r {
            Some(s) => sos(data@, q as int, f@) == Some(s@) && scan_struct(f@, s@) && s.ns <= 3,
            None => sos(data@, q as int, f@) is None || !scan_struct(f@, sos(data@, q as int, f@)->0),
        },
{
    let ghost d = data@;
    let ghost fv = f@;
    let len = rd16(data, q);
    let ns = rd(data, q + 2);
    if len != 2 * ns as u16 + 6 || ns < 1 || ns > 4 || ns > f.nc {
        return None;
    }
    let ghost sp = sos(d, q as int, fv)->0;
    let mut s = ScanX { ns, ci: [0; 3], td: [0; 3], ta: [0; 3], ss: 0, se: 0, ah: 0, al: 0 };
    let mut i: usize = 0;
    while i < ns as usize
        invariant
            i <= ns <= 3,
            ns <= f.nc,
            d == data@,
            fv == f@,
            frame_basic(fv),
            len_ok(d),
            q <= d.len() + 16,
            sos(d, q as int, fv) == Some(sp),
            sp.ns == ns,
            sp.ci.len() == ns,
            sp.td.len() == ns,
            sp.ta.len() == ns,
            s.ns == ns,
            forall|j: int|
                0 <= j < i ==> {
                    &&& (#[trigger] s.ci[j]) as int == sp.ci[j]
                    &&& s.ci[j] < fv.nc
                    &&& s.td[j] as int == sp.td[j]
                    &&& s.ta[j] as int == sp.ta[j]
                },
            forall|j: int, k: int| 0 <= j < k < i ==> sp.ci[j] != sp.ci[k],
        decreases ns - i,
    {
        let id = rd(data, q + 3 + 2 * i);
        let mut c: usize = i;
        proof {
            lemma_find_from(fv, id, i as int, 0);
        }
        while c < f.nc as usize && f.comps[c].id != id
            invariant
                i <= c <= f.nc <= 3,
                fv == f@,
                find_comp(fv, id, i as int, c as int) == find_comp(fv, id, i as int, 0),
            decreases f.nc - c,
        {
            assert(fv.comps[c as int] == f.comps[c as int]);
            c += 1;
        }
        if c >= f.nc as usize {
            proof {
                assert(sp.ci[i as int] == -1);
                assert(!scan_struct(fv, sp));
            }
            return None;
        }
        assert(fv.comps[c as int] == f.comps[c as int]);
        assert(sp.ci[i as int] == c);
        // No component twice.
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i < ns <= 3,
                sp.ns == ns,
                fv == f@,
                d == data@,
                sos(d, q as int, fv) == Some(sp),
                sp.ci.len() == ns,
                sp.ci[i as int] == c,
                forall|k: int| 0 <= k < i ==> (#[trigger] s.ci[k]) as int == sp.ci[k],
                forall|k: int| 0 <= k < j ==> sp.ci[k] != c,
            decreases i - j,
        {
            if s.ci[j] as usize == c {
                proof {
                    assert(sp.ci[j as int] == sp.ci[i as int]);
                    assert(!scan_struct(fv, sp));
                }
                return None;
            }
            j += 1;
        }
        let tt = rd(data, q + 4 + 2 * i);
        s.ci[i] = c as u8;
        s.td[i] = tt / 16;
        s.ta[i] = tt % 16;
        i += 1;
    }
    let nsz = ns as usize;
    s.ss = rd(data, q + 3 + 2 * nsz);
    s.se = rd(data, q + 4 + 2 * nsz);
    let a = rd(data, q + 5 + 2 * nsz);
    s.ah = a / 16;
    s.al = a % 16;
    proof {
        assert forall|j: int| 0 <= j < ns implies s.td[j] as int == sp.td[j] && s.ta[j] as int == sp.ta[j] by {
            let x = s.ci[j];
        }
        assert(s@.ci =~= sp.ci);
        assert(s@.td =~= sp.td);
        assert(s@.ta =~= sp.ta);
        assert(s@ == sp);
        assert forall|j: int| 0 <= j < sp.ns implies 0 <= (#[trigger] sp.ci[j]) < fv.nc by {
            let x = s.ci[j];
        }
    }
    Some(s)
}

/// The progression parameters of a scan are ones the decoder takes.
pub fn scan_params_ok(f: &FrameX, s: &ScanX) -> (ok: bool)
    ensures
        ok == scan_params(f@, s@),
{
    if !f.prog {
        true
    } else if s.ss == 0 {
        s.se == 0 && s.al <= 13 && (s.ah == 0 || s.al == s.ah - 1)
    } else {
        s.ss <= s.se && s.se < 64 && s.ns == 1 && s.al <= 13 && (s.ah == 0 || s.al == s.ah - 1)
    }
}

/// A vector of `n` zeros, or `None` if there is no memory for it. This and
/// `alloc_u8` are trusted: large allocations come from `calloc`, which maps
/// zeroed pages lazily, and Verus has no specification for that.
#[verifier::external_body]
pub fn alloc_i16(n: usize) -> (r: Option<Vec<i16>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0i16),
{
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match std::alloc::Layout::array::<i16>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    // SAFETY: `layout` has non-zero size. On success the block holds `n`
    // initialised (zero) values allocated by the global allocator with the
    // layout `Vec<i16>` uses for capacity `n`.
    unsafe {
        let p = std::alloc::alloc_zeroed(layout) as *mut i16;
        if p.is_null() {
            return None;
        }
        Some(Vec::from_raw_parts(p, n, n))
    }
}

/// A vector of `n` zero bytes, or `None` if there is no memory for it.
#[verifier::external_body]
pub fn alloc_u8(n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u8),
{
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match std::alloc::Layout::array::<u8>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    // SAFETY: as in `alloc_i16`.
    unsafe {
        let p = std::alloc::alloc_zeroed(layout);
        if p.is_null() {
            return None;
        }
        Some(Vec::from_raw_parts(p, n, n))
    }
}

/// The zeroed coefficient array of component `c`.
fn alloc_coef(g: &Geom, c: usize, Ghost(f): Ghost<Frame>) -> (r: Option<Vec<i16>>)
    requires
        g.wf(f),
        c < f.nc <= 3,
    ensures
        r matches Some(v) ==> v@ == Seq::new((64 * cw(f, c as int) * ch(f, c as int)) as nat, |j: int| 0i16) && v.len()
            == csize(f, c as int),
{
    reveal(csize);
    assert(g.cw[c as int] == cw(f, c as int) && g.ch[c as int] == ch(f, c as int));
    let a = g.cw[c] as u64;
    let b = g.ch[c] as u64;
    assert(a * b <= 0x4_0080 * 0x4_0080 && 64 * a * b == 64 * (a * b)) by (nonlinear_arith)
        requires
            a <= 0x4_0080,
            b <= 0x4_0080,
    ;
    let n = a * b * 64;
    if n > usize::MAX as u64 {
        return None;
    }
    alloc_i16(n as usize)
}

/// The component tables as the specification has them.
pub open spec fn qlv(ql: [[u16; 64]; 3]) -> Seq<Seq<u16>> {
    seq![ql@[0]@, ql@[1]@, ql@[2]@]
}

/// The typical Huffman tables, where the file has defined none.
fn install_std(t: &mut Tabs)
    ensures
        final(t)@ == with_std(old(t)@),
{
    let ghost t0 = t@;
    if !t.dcdef[0] {
        t.dc[0] = std_tab(&STD_DC_L);
        t.dcdef[0] = true;
    }
    if !t.dcdef[1] {
        t.dc[1] = std_tab(&STD_DC_C);
        t.dcdef[1] = true;
    }
    if !t.acdef[0] {
        t.ac[0] = std_tab(&STD_AC_L);
        t.acdef[0] = true;
    }
    if !t.acdef[1] {
        t.ac[1] = std_tab(&STD_AC_C);
        t.acdef[1] = true;
    }
    proof {
        let w = with_std(t0);
        assert(t@.q =~= w.q);
        assert(t@.qdef =~= w.qdef);
        assert(t@.dc =~= w.dc);
        assert(t@.dcdef =~= w.dcdef);
        assert(t@.ac =~= w.ac);
        assert(t@.acdef =~= w.acdef);
        assert(t@ == w);
    }
}

/// Latches the quantization tables of the scan's components that have
/// none yet. Returns false if one names a table that is not defined.
fn latch_x(f: &FrameX, t: &Tabs, s: &ScanX, ql: &mut [[u16; 64]; 3], qset: &mut [bool; 3]) -> (ok: bool)
    requires
        frame_basic(f@),
        scan_struct(f@, s@),
        s.ns <= 3,
    ensures
        ok == latch(f@, t@, s@, qlv(*old(ql)), old(qset)@, 0) is Some,
        ok ==> (qlv(*final(ql)), final(qset)@) == latch(f@, t@, s@, qlv(*old(ql)), old(qset)@, 0)->0,
{
    let ghost fv = f@;
    let ghost tv = t@;
    let ghost sv = s@;
    let mut i: usize = 0;
    while i < s.ns as usize
        invariant
            i <= s.ns <= 3,
            sv == s@,
            fv == f@,
            tv == t@,
            scan_struct(fv, sv),
            frame_basic(fv),
            latch(fv, tv, sv, qlv(*ql), qset@, i as int) == latch(fv, tv, sv, qlv(*old(ql)), old(qset)@, 0),
        decreases s.ns - i,
    {
        let ghost ql1 = qlv(*ql);
        let ghost qs1 = qset@;
        let c = s.ci[i] as usize;
        assert(sv.ci[i as int] == c);
        assert(fv.comps[c as int] == f.comps[c as int]);
        if !qset[c] {
            let n = f.comps[c].tq as usize;
            if n >= 4 || !t.qdef[n] {
                return false;
            }
            ql[c] = t.q[n];
            qset[c] = true;
            proof {
                assert(qlv(*ql) =~= ql1.update(c as int, tv.q[n as int]));
                assert(qset@ =~= qs1.update(c as int, true));
            }
        }
        i += 1;
    }
    true
}

/// The color space of a frame.
fn color_x(f: &FrameX, jfif: bool, has_adobe: bool, adobe: u8) -> (r: u8)
    requires
        frame_basic(f@),
    ensures
        r <= 2,
        (r == 0) == (f.nc == 1),
        color_v(r) == color_of(
            f@,
            jfif,
            if has_adobe {
                Some(adobe)
            } else {
                None
            },
        ),
{
    if f.nc == 1 {
        0
    } else {
        assert(f@.comps[0] == f.comps[0] && f@.comps[1] == f.comps[1] && f@.comps[2] == f.comps[2]);
        if jfif {
            1
        } else if has_adobe {
            if adobe == 0 {
                2
            } else {
                1
            }
        } else if f.comps[0].id == 82 && f.comps[1].id == 71 && f.comps[2].id == 66 {
            2
        } else {
            1
        }
    }
}

/// The coefficients of a frame before its first scan: zeros.
pub open spec fn zero_coefs(f: Frame) -> Seq<Seq<i16>> {
    Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16))
}

/// Allocates the coefficient arrays. Returns false if there is no memory.
fn alloc_all(g: &Geom, f: &FrameX, co: &mut Coefs) -> (ok: bool)
    requires
        frame_basic(f@),
        g.wf(f@),
        !old(co).stream,
    ensures
        !final(co).stream,
        ok ==> final(co).wf(f@) && final(co).view(f@.nc) == zero_coefs(f@),
{
    co.a0 = match alloc_coef(g, 0, Ghost(f@)) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    if f.nc == 3 {
        co.a1 = match alloc_coef(g, 1, Ghost(f@)) {
            Some(v) => v,
            None => {
                return false;
            },
        };
        co.a2 = match alloc_coef(g, 2, Ghost(f@)) {
            Some(v) => v,
            None => {
                return false;
            },
        };
    }
    proof {
        assert(co.view(f@.nc) =~= zero_coefs(f@));
    }
    true
}

/// The window and the plane of component `c` for a streamed scan.
fn alloc_win(g: &Geom, c: usize, vr: usize, Ghost(f): Ghost<Frame>, Ghost(q): Ghost<Seq<u16>>) -> (r: Option<
    (Vec<i16>, Vec<u8>),
>)
    requires
        frame_ok(f),
        frame_basic(f),
        g.wf(f),
        c < f.nc,
        vr == srows(f, c as int),
    ensures
        r matches Some(w) ==> {
            &&& 64 * cw(f, c as int) * ch(f, c as int) <= usize::MAX
            &&& win_ok(
                w.0@,
                Seq::new((64 * cw(f, c as int) * ch(f, c as int)) as nat, |j: int| 0i16),
                w.1@,
                q,
                cw(f, c as int),
                ch(f, c as int),
                wb(f, c as int),
                hb(f, c as int),
                vr as int,
                0,
            )
        },
{
    let ghost ci = c as int;
    proof {
        crate::decode::lemma_comp_geom(f, ci);
    }
    assert(g.cw[ci] == cw(f, ci) && g.ch[ci] == ch(f, ci) && g.wb[ci] == wb(f, ci) && g.hb[ci] == hb(f, ci));
    let cwc = g.cw[c] as u64;
    let chc = g.ch[c] as u64;
    let wbc = g.wb[c] as u64;
    let hbc = g.hb[c] as u64;
    let v = vr as u64;
    assert(1 <= vr <= 4 && vr <= chc) by {
        assert(1 <= f.comps[ci].v <= 4);
        if f.nc != 1 {
            assert(chc == mcuy(f) * vr);
            assert(mcuy(f) >= 1) by (nonlinear_arith)
                requires
                    chc == mcuy(f) * vr,
                    chc >= 1,
                    vr >= 1,
                    mcuy(f) >= 0,
            ;
            assert(vr <= mcuy(f) * vr) by (nonlinear_arith)
                requires
                    mcuy(f) >= 1,
                    vr >= 1,
            ;
        }
    }
    assert(cwc * chc <= 0x4_0080 * 0x4_0080 && 64 * cwc * chc == 64 * (cwc * chc) && cwc * v <= 0x4_0080 * 4 && 64 * (cwc
        * v) <= 64 * (cwc * chc) && (8 * wbc) * (8 * hbc) <= 0x20_0400 * 0x20_0400) by (nonlinear_arith)
        requires
            1 <= wbc <= cwc <= 0x4_0080,
            1 <= hbc <= chc <= 0x4_0080,
            1 <= v <= 4,
            v <= chc,
    ;
    if 64 * cwc * chc > usize::MAX as u64 || (8 * wbc) * (8 * hbc) > usize::MAX as u64 {
        return None;
    }
    let a = match alloc_i16((64 * (cwc * v)) as usize) {
        Some(a) => a,
        None => {
            return None;
        },
    };
    let pl = match alloc_u8(((8 * wbc) * (8 * hbc)) as usize) {
        Some(p) => p,
        None => {
            return None;
        },
    };
    proof {
        let gz = Seq::new((64 * cw(f, ci) * ch(f, ci)) as nat, |j: int| 0i16);
        assert(wbase(cw(f, ci), vr as int, 0) == 0) by (nonlinear_arith)
            requires
                wbase(cw(f, ci), vr as int, 0) == 64 * (cw(f, ci) * (vr * 0)),
        ;
        assert(8 * (vr * 0) == 0) by (nonlinear_arith);
        assert forall|j: int| 0 <= j < pl@.len() && j / (8 * wb(f, ci)) < 0 implies (#[trigger] pl@[j]) == crate::idct::psample(
            gz,
            q,
            cw(f, ci),
            j / (8 * wb(f, ci)),
            j % (8 * wb(f, ci)),
        ) by {
            assert(j / (8 * wb(f, ci)) >= 0) by (nonlinear_arith)
                requires
                    j >= 0,
                    wb(f, ci) >= 1,
            ;
        }
    }
    Some((a, pl))
}

/// Sets up streaming for the one scan of a sequential file: windows and
/// planes instead of whole coefficient arrays. Returns false if there is
/// no memory.
fn begin_stream(g: &Geom, f: &FrameX, ql: &[[u16; 64]; 3], co: &mut Coefs) -> (ok: bool)
    requires
        frame_ok(f@),
        frame_basic(f@),
        g.wf(f@),
        !old(co).stream,
    ensures
        ok ==> {
            &&& final(co).wf(f@)
            &&& final(co).stream
            &&& final(co).row == 0
            &&& final(co).sqv() == seq![ql[0]@, ql[1]@, ql[2]@]
            &&& final(co).view(f@.nc) == zero_coefs(f@)
        },
        !ok ==> !final(co).stream,
{
    reveal(Coefs::swf);
    reveal(Coefs::sqv);
    let ghost fv = f@;
    assert(fv.comps[0] == f.comps[0]);
    let nc = f.nc;
    let vr0: usize = if nc == 1 {
        1
    } else {
        f.comps[0].v as usize
    };
    let w0 = match alloc_win(g, 0, vr0, Ghost(fv), Ghost(ql[0]@)) {
        Some(w) => w,
        None => {
            return false;
        },
    };
    co.a0 = w0.0;
    co.p0 = w0.1;
    co.g0 = Ghost(Seq::new((64 * cw(fv, 0) * ch(fv, 0)) as nat, |j: int| 0i16));
    if nc == 3 {
        assert(fv.comps[1] == f.comps[1] && fv.comps[2] == f.comps[2]);
        let w1 = match alloc_win(g, 1, f.comps[1].v as usize, Ghost(fv), Ghost(ql[1]@)) {
            Some(w) => w,
            None => {
                return false;
            },
        };
        let w2 = match alloc_win(g, 2, f.comps[2].v as usize, Ghost(fv), Ghost(ql[2]@)) {
            Some(w) => w,
            None => {
                return false;
            },
        };
        co.a1 = w1.0;
        co.p1 = w1.1;
        co.g1 = Ghost(Seq::new((64 * cw(fv, 1) * ch(fv, 1)) as nat, |j: int| 0i16));
        co.a2 = w2.0;
        co.p2 = w2.1;
        co.g2 = Ghost(Seq::new((64 * cw(fv, 2) * ch(fv, 2)) as nat, |j: int| 0i16));
    }
    co.sq = *ql;
    co.rl = crate::idct::range_table();
    co.kt = crate::idct16::idct_consts();
    co.row = 0;
    co.stream = true;
    proof {
        assert(co.view(fv.nc) =~= zero_coefs(fv));
    }
    true
}

/// The scan whose header is at `q`. Returns a position from which the
/// next marker is the one after the scan.
pub fn do_scan_x(data: &[u8], q: usize, st: &mut DecX) -> (r: Result<usize, Error>)
    requires
        len_ok(data@),
        q <= data@.len() + 2,
        old(st).wf(),
    ensures
        match r {
            Ok(p) => {
                &&& do_scan(data@, q as int, old(st)@) is Some
                &&& final(st)@ == (do_scan(data@, q as int, old(st)@)->0).0
                &&& marker_after(data@, p as int) == marker_after(data@, (do_scan(data@, q as int, old(st)@)->0).1)
                &&& q <= p <= data@.len() + 0x1_0010
                &&& final(st).wf()
                &&& final(st).started
            },
            Err(Error::Invalid) => do_scan(data@, q as int, old(st)@) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    let ghost d = data@;
    let ghost s0 = st@;
    if !st.has_f {
        return Err(Error::Invalid);
    }
    let f = st.f;
    let g = st.g;
    let ghost fv = f@;
    let first = !st.started;
    let ghost tv = if first && !fv.prog {
        with_std(s0.t)
    } else {
        s0.t
    };
    let s = match sos_x(data, q, &f) {
        Some(s) => s,
        None => {
            proof {
                if sos(d, q as int, fv) is Some {
                    lemma_scan_ok(fv, tv, sos(d, q as int, fv)->0);
                }
            }
            return Err(Error::Invalid);
        },
    };
    let ghost sv = s@;
    if first && !f.prog {
        install_std(&mut st.t);
    }
    assert(st.t@ == tv);
    proof {
        lemma_scan_ok(fv, tv, sv);
    }
    if !scan_params_ok(&f, &s) || (!first && !st.multi) {
        return Err(Error::Invalid);
    }
    if !latch_x(&f, &st.t, &s, &mut st.ql, &mut st.qset) {
        return Err(Error::Invalid);
    }
    if first {
        st.multi = f.prog || s.ns < f.nc;
        st.color = color_x(&f, st.jfif, st.has_adobe, st.adobe);
        // The one scan of a sequential file is streamed; anything else
        // needs the whole coefficient arrays.
        if !f.prog && s.ns == f.nc {
            if !begin_stream(&g, &f, &st.ql, &mut st.co) {
                return Err(Error::OutOfMemory);
            }
        } else if !alloc_all(&g, &f, &mut st.co) {
            return Err(Error::OutOfMemory);
        }
    }
    let ghost a_in = st.co.view(fv.nc);
    assert(a_in == if first {
        zero_coefs(fv)
    } else {
        s0.a
    });
    let p0 = q + rd16(data, q) as usize;
    match scan_x(data, &f, &g, &st.t, &s, &mut st.co, p0) {
        Some(p) => {
            st.started = true;
            proof {
                let want = (do_scan(d, q as int, s0)->0).0;
                assert(st@.ql =~= want.ql);
                assert(st@.qset =~= want.qset);
                assert(st@ == want);
                assert(st.co.wf(st.f@));
                assert(st.co.stream ==> !st.multi);
                assert(st.co.stream ==> st.co.row == stotal(st.f@));
                
                assert(st.wf());
            }
            Ok(p)
        },
        None => Err(Error::Invalid),
    }
}

/// The five bytes at `p` are `tag`.
pub fn has_tag_x(data: &[u8], p: usize, tag: [u8; 5]) -> (r: bool)
    requires
        len_ok(data@),
        p <= data@.len() + 16,
    ensures
        r == has_tag(data@, p as int, tag@),
{
    let mut i: usize = 0;
    while i < 5
        invariant
            i <= 5,
            len_ok(data@),
            p <= data@.len() + 16,
            forall|j: int| 0 <= j < i ==> byte(data@, p + j) == tag[j],
        decreases 5 - i,
    {
        if rd(data, p + i) != tag[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// `run` looks at the input from a position on, and so does not tell
/// apart two positions with the same marker after them.
pub proof fn lemma_run_marker(d: Seq<u8>, st: Dec, p: int, p2: int)
    requires
        marker_after(d, p) == marker_after(d, p2),
    ensures
        run(d, st, p) == run(d, st, p2),
{
}

/// Whether the `n` bytes at `p` are a well-formed DAC payload.
pub fn dac_x(data: &[u8], p: usize, n: isize) -> (r: bool)
    requires
        len_ok(data@),
        p <= data@.len() + 0x8000,
        -2 <= n <= 0xFFFF,
    ensures
        r == dac(data@, p as int, n as int),
{
    let mut k: isize = n;
    let mut i: usize = p;
    while k > 0
        invariant
            len_ok(data@),
            p <= data@.len() + 0x8000,
            n <= 0xFFFF,
            i as int + k as int <= p as int + n as int + 1,
            -2 <= k <= 0xFFFF,
            dac(data@, p as int, n as int) == dac(data@, i as int, k as int),
        decreases k + 2,
    {
        let t = rd(data, i);
        let v = rd(data, i + 1);
        if !(t < 32 && (t >= 16 || (v & 0x0F) <= (v >> 4))) {
            return false;
        }
        i = i + 2;
        k = k - 2;
    }
    k == 0
}

/// One marker segment at `p`. Returns the position after it, or `None` at
/// EOI.
pub fn step_x(data: &[u8], st: &mut DecX, p: usize) -> (r: Result<Option<usize>, Error>)
    requires
        len_ok(data@),
        p <= data@.len() + 0x1_0010,
        old(st).wf(),
    ensures
        match r {
            Ok(None) => run(data@, old(st)@, p as int) == Some(final(st)@) && final(st).wf() && final(st).started,
            Ok(Some(p2)) => {
                &&& run(data@, old(st)@, p as int) == run(data@, final(st)@, p2 as int)
                &&& final(st).wf()
                &&& p < p2 <= data@.len() + 0x1_0010
                &&& p < data@.len()
            },
            Err(Error::Invalid) => run(data@, old(st)@, p as int) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    let ghost d = data@;
    let ghost s0 = st@;
    proof {
        lemma_marker_after(d, p as int);
    }
    let (m, q) = marker_after_x(data, p);
    if p >= data.len() || m == 0xD9 {
        if st.started {
            Ok(None)
        } else {
            Err(Error::Invalid)
        }
    } else if m == 0xDA {
        match do_scan_x(data, q, st) {
            Ok(p2) => {
                proof {
                    let (st2, sp) = do_scan(d, q as int, s0)->0;
                    lemma_run_marker(d, st2, sp, p2 as int);
                }
                Ok(Some(p2))
            },
            Err(e) => Err(e),
        }
    } else if m == 0xDB {
        let len = rd16(data, q);
        if dqt_x(data, q + 2, len as i32 - 2, &mut st.t) {
            Ok(Some(q + len as usize))
        } else {
            Err(Error::Invalid)
        }
    } else if m == 0xC4 {
        let len = rd16(data, q);
        if dht_x(data, q + 2, len as i32 - 2, &mut st.t) {
            Ok(Some(q + len as usize))
        } else {
            Err(Error::Invalid)
        }
    } else if m == 0xDD {
        if rd16(data, q) != 4 {
            Err(Error::Invalid)
        } else {
            let ghost t1 = st.t@;
            st.t.ri = rd16(data, q + 2);
            proof {
                let t2 = Tables { ri: be16(d, q + 2), ..t1 };
                assert(st.t@ == t2);
            }
            Ok(Some(q + 4))
        }
    } else if m == 0xC0 || m == 0xC1 || m == 0xC2 {
        match sof_x(data, q, m == 0xC2) {
            None => Err(Error::Invalid),
            Some(f) => {
                if st.has_f {
                    Err(Error::Invalid)
                } else {
                    st.has_f = true;
                    st.f = f;
                    st.g = geom(&f);
                    Ok(Some(q + rd16(data, q) as usize))
                }
            },
        }
    } else if m == 0xE0 {
        let len = rd16(data, q);
        if len >= 16 && has_tag_x(data, q + 2, [0x4A, 0x46, 0x49, 0x46, 0]) {
            st.jfif = true;
        }
        proof {
            assert([0x4Au8, 0x46u8, 0x49u8, 0x46u8, 0u8]@ =~= seq![0x4Au8, 0x46u8, 0x49u8, 0x46u8, 0u8]);
        }
        Ok(Some(q + if len < 2 { 2 } else { len as usize }))
    } else if m == 0xEE {
        let len = rd16(data, q);
        if len >= 14 && has_tag_x(data, q + 2, [0x41, 0x64, 0x6F, 0x62, 0x65]) {
            st.has_adobe = true;
            st.adobe = rd(data, q + 13);
        }
        proof {
            assert([0x41u8, 0x64u8, 0x6Fu8, 0x62u8, 0x65u8]@ =~= seq![0x41u8, 0x64u8, 0x6Fu8, 0x62u8, 0x65u8]);
        }
        Ok(Some(q + if len < 2 { 2 } else { len as usize }))
    } else if m == 0xCC {
        let len = rd16(data, q);
        if dac_x(data, q + 2, len as isize - 2) {
            Ok(Some(q + if len < 2 { 2 } else { len as usize }))
        } else {
            Err(Error::Invalid)
        }
    } else if (0xE1 <= m && m <= 0xEF) || m == 0xFE || m == 0xDC {
        let len = rd16(data, q);
        Ok(Some(q + if len < 2 { 2 } else { len as usize }))
    } else if (0xD0 <= m && m <= 0xD7) || m == 0x01 {
        Ok(Some(q))
    } else {
        Err(Error::Invalid)
    }
}

/// All the marker segments from `p` to EOI.
pub fn run_x(data: &[u8], st: &mut DecX, p: usize) -> (r: Result<(), Error>)
    requires
        len_ok(data@),
        p <= data@.len() + 0x1_0010,
        old(st).wf(),
    ensures
        match r {
            Ok(()) => run(data@, old(st)@, p as int) == Some(final(st)@) && final(st).wf() && final(st).started,
            Err(Error::Invalid) => run(data@, old(st)@, p as int) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    let mut pp = p;
    loop
        invariant
            len_ok(data@),
            pp <= data@.len() + 0x1_0010,
            st.wf(),
            run(data@, st@, pp as int) == run(data@, old(st)@, p as int),
        decreases left(data@, pp as int),
    {
        match step_x(data, st, pp) {
            Err(e) => {
                return Err(e);
            },
            Ok(None) => {
                return Ok(());
            },
            Ok(Some(p2)) => {
                pp = p2;
            },
        }
    }
}

} // verus!
