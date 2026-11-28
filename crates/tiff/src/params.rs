//! The image parameters from IFD 0, proven against `spec::params`.
use crate::ifd::*;
use crate::spec::*;
use crate::work::*;
use vstd::prelude::*;

verus! {

/// `spec::Params`, with the strip or tile offsets and byte counts left in
/// the file.
#[derive(Clone, Copy)]
pub struct ParamsX {
    /// Whether the file is little-endian ("II").
    pub le: bool,
    /// Image width, in pixels.
    pub width: u32,
    /// Image height, in pixels.
    pub height: u32,
    /// Bits per sample.
    pub bps: u32,
    /// Samples per pixel.
    pub spp: u32,
    /// The Compression tag.
    pub compression: u32,
    /// The PhotometricInterpretation tag.
    pub photometric: u32,
    /// 1 unsigned, 2 signed, 3 floating point, 4 undefined.
    pub sample_format: u32,
    /// 1: the samples of a pixel are together; 2: one plane per sample.
    pub planar: u32,
    /// 2 for horizontal differencing, else 1.
    pub predictor: u32,
    /// Whether the image is in tiles rather than strips.
    pub tiled: bool,
    /// Rows per strip.
    pub rps: u32,
    /// Tile width, in pixels.
    pub tw: u32,
    /// Tile height, in pixels.
    pub th: u32,
    /// The StripOffsets or TileOffsets field.
    pub offsets: Field,
    /// The StripByteCounts or TileByteCounts field.
    pub counts: Field,
}

impl ParamsX {
    pub open spec fn view(self, b: Seq<u8>) -> Params {
        Params {
            le: self.le,
            width: self.width as nat,
            height: self.height as nat,
            bps: self.bps as nat,
            spp: self.spp as nat,
            compression: self.compression as nat,
            photometric: self.photometric as nat,
            sample_format: self.sample_format as nat,
            planar: self.planar as nat,
            predictor: self.predictor as nat,
            tiled: self.tiled,
            rps: self.rps as nat,
            tw: self.tw as nat,
            th: self.th as nat,
            offsets: self.offsets.values(b, self.le),
            counts: self.counts.values(b, self.le),
        }
    }

    pub open spec fn ok(self, b: Seq<u8>) -> bool {
        self.offsets.ok(b) && self.counts.ok(b)
    }
}

/// `spec::div_up`.
pub fn div_up_exec(a: u64, d: u64) -> (r: u64)
    requires
        1 <= d,
        a <= u32::MAX,
        d <= u32::MAX,
    ensures
        r as nat == div_up(a as nat, d as nat),
        r <= a,
{
    proof {
        vstd::arithmetic::mul::lemma_mul_inequality(1, d as int, a as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, d as int);
        vstd::arithmetic::div_mod::lemma_div_is_ordered((a + d - 1) as int, a as int * d as int + (d - 1) as int, d as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            a as int * d as int + (d - 1) as int, d as int, a as int, (d - 1) as int);
    }
    (a + d - 1) / d
}

/// Strips or tiles in the file (`Params::chunks`).
pub fn chunks_exec(p: &ParamsX) -> (r: u128)
    requires
        p.width >= 1,
        p.height >= 1,
        p.spp >= 1,
        p.rps >= 1,
        p.tiled ==> p.tw >= 1 && p.th >= 1,
    ensures
        r as nat == p.view(seq![]).chunks(),
{
    let planes: u128 = if p.planar == 2 { p.spp as u128 } else { 1 };
    if p.tiled {
        let ta = div_up_exec(p.width as u64, p.tw as u64) as u128;
        let td = div_up_exec(p.height as u64, p.th as u64) as u128;
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(ta as int, u32::MAX as int, td as int);
            vstd::arithmetic::mul::lemma_mul_inequality(td as int, u32::MAX as int, u32::MAX as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(ta as int, td as int);
            vstd::arithmetic::mul::lemma_mul_inequality(planes as int, u32::MAX as int, (ta * td) as int);
            vstd::arithmetic::mul::lemma_mul_inequality((ta * td) as int, 0xffff_ffff_ffff_ffff, u32::MAX as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(planes as int, (ta * td) as int);
        }
        planes * (ta * td)
    } else {
        let s = div_up_exec(p.height as u64, p.rps as u64) as u128;
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(planes as int, u32::MAX as int, s as int);
            vstd::arithmetic::mul::lemma_mul_inequality(s as int, u32::MAX as int, u32::MAX as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(planes as int, s as int);
        }
        planes * s
    }
}

/// A field inside the file has at most one value per byte of it.
pub proof fn lemma_count_le(b: Seq<u8>, f: Field)
    requires
        f.ok(b),
    ensures
        f.count <= b.len(),
{
    let ts = type_size(f.ty as nat);
    assert(ts >= 1);
    assert(f.count <= f.count * ts) by (nonlinear_arith)
        requires
            ts >= 1,
    ;
}

/// Whether every value of `f` equals its first (`spec::all_same`).
pub fn same_exec(b: &[u8], le: bool, f: Field, Tracked(m): Tracked<&mut Meter>) -> (r: bool)
    requires
        f.ok(b@),
        f.count >= 1,
    ensures
        r == all_same(f.values(b@, le)),
        final(m).n <= old(m).n + unit(b@.len()),
{
    proof {
        lemma_count_le(b@, f);
    }
    let ghost v = f.values(b@, le);
    let v0 = value_exec(b, le, f, 0);
    let mut k: u32 = 1;
    while k < f.count
        invariant
            f.ok(b@),
            v == f.values(b@, le),
            1 <= k <= f.count,
            v0 == v[0],
            forall|j: int| 0 <= j < k ==> #[trigger] v[j] == v[0],
            m.n <= old(m).n + k,
        decreases f.count - k,
    {
        proof {
            m.n = m.n + 1;
        }
        if value_exec(b, le, f, k) != v0 {
            assert(v[k as int] != v[0]);
            return false;
        }
        k = k + 1;
    }
    true
}

/// `spec::bits_per_sample`.
fn bits_exec(b: &[u8], le: bool, f: Option<Field>, spp: u32, Tracked(m): Tracked<&mut Meter>) -> (r: Option<u32>)
    requires
        f matches Some(f) ==> f.ok(b@),
    ensures
        match bits_per_sample(fview(b@, le, f), spp as nat) {
            Some(x) => r == Some(x as u32) && 1 <= x <= 32,
            None => r is None,
        },
        final(m).n <= old(m).n + unit(b@.len()),
{
    let f = match f {
        None => return Some(1),
        Some(f) => f,
    };
    if f.count == 0 || f.count != spp || !same_exec(b, le, f, Tracked(m)) {
        return None;
    }
    let v0 = value_exec(b, le, f, 0);
    if 1 <= v0 && v0 <= 32 {
        Some(v0)
    } else {
        None
    }
}

/// A field as `spec::field` gives it.
pub open spec fn fview(b: Seq<u8>, le: bool, f: Option<Field>) -> Option<Seq<nat>> {
    match f {
        Some(f) => Some(f.values(b, le)),
        None => None,
    }
}

/// The image's parameters from the IFD at `o` (`spec::params`).
pub fn params_exec(b: &[u8], le: bool, o: u32) -> (r: Option<ParamsX>)
    ensures
        match params(b@, le, o as nat) {
            Some(p) => r matches Some(x) && x.view(b@) == p && x.ok(b@) && x.le == le && p.wf(),
            None => r is None,
        },
{
    let tracked mut m = Meter { n: 0 };
    params_counted(b, le, o, Tracked(&mut m))
}

/// `params_exec`, counting its steps: at most 30 walks of the IFD or of
/// a field's values.
// The default budget is too small for z3's Arm build here; x86 needs less.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn params_counted(b: &[u8], le: bool, o: u32, Tracked(m): Tracked<&mut Meter>) -> (r: Option<ParamsX>)
    ensures
        match params(b@, le, o as nat) {
            Some(p) => r matches Some(x) && x.view(b@) == p && x.ok(b@) && x.le == le && p.wf(),
            None => r is None,
        },
        final(m).n <= old(m).n + 30 * unit(b@.len()),
{
    let l = b.len();
    if (o as u64) + 2 > l as u64 {
        return None;
    }
    let o = o as usize;
    let n = u16_exec(b, le, o) as usize;
    if n == 0 || (o as u64) + 2 + 12 * (n as u64) > l as u64 {
        return None;
    }
    if !sorted_exec(b, le, o, n, Tracked(m)) {
        return None;
    }
    let ghost bb = b@;
    let ghost on = o as nat;
    let ghost nn = n as nat;
    let wf = match field_counted(b, le, o, n, 256, Tracked(m)) {
        Ok(Some(f)) => f,
        _ => return None,
    };
    let hf = match field_counted(b, le, o, n, 257, Tracked(m)) {
        Ok(Some(f)) => f,
        _ => return None,
    };
    let spp = match scalar_exec(b, le, o, n, 277, 1, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let comp = match scalar_exec(b, le, o, n, 259, 1, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let planar = match scalar_exec(b, le, o, n, 284, 1, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let pred = match scalar_exec(b, le, o, n, 317, 1, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let fill = match scalar_exec(b, le, o, n, 266, 1, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let rps = match scalar_exec(b, le, o, n, 278, 0xffff_ffff, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let ph = match field_counted(b, le, o, n, 262, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let bf = match field_counted(b, le, o, n, 258, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let bps = match bits_exec(b, le, bf, spp, Tracked(m)) {
        Some(x) => x,
        None => return None,
    };
    let ghost wv = wf.values(bb, le);
    let ghost hv = hf.values(bb, le);
    proof {
        assert(params(bb, le, on) == params2(bb, le, on, nn, wv, hv, spp as nat, comp as nat, planar as nat,
            pred as nat, fill as nat, rps as nat, fview(bb, le, ph), bps as nat));
    }
    params2_exec(b, le, o, n, wf, hf, spp, comp, planar, pred, fill, rps, ph, bps, Tracked(m))
}

/// The rest of `params_exec` (`spec::params2`).
fn params2_exec(
    b: &[u8],
    le: bool,
    o: usize,
    n: usize,
    wf: Field,
    hf: Field,
    spp: u32,
    comp: u32,
    planar: u32,
    pred: u32,
    fill: u32,
    rps: u32,
    ph: Option<Field>,
    bps: u32,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Option<ParamsX>)
    requires
        ifd_ok(b@, o as nat, n as nat),
        wf.ok(b@),
        hf.ok(b@),
        ph matches Some(f) ==> f.ok(b@),
        1 <= bps <= 32,
    ensures
        match params2(b@, le, o as nat, n as nat, wf.values(b@, le), hf.values(b@, le), spp as nat, comp as nat,
            planar as nat, pred as nat, fill as nat, rps as nat, fview(b@, le, ph), bps as nat) {
            Some(p) => r matches Some(x) && x.view(b@) == p && x.ok(b@) && x.le == le && p.wf(),
            None => r is None,
        },
        final(m).n <= old(m).n + 15 * unit(b@.len()),
{
    let ghost bb = b@;
    let uses = comp == 5 || comp == 8;
    let predictor = if uses { pred } else { 1 };
    if wf.count != 1 || hf.count != 1 {
        return None;
    }
    let width = value_exec(b, le, wf, 0);
    let height = value_exec(b, le, hf, 0);
    if width == 0 || height == 0 || spp == 0
        || !(comp == 1 || comp == 5 || comp == 8 || comp == 32773)
        || (planar != 1 && planar != 2) || rps == 0 {
        return None;
    }
    if fill != 1 {
        return None;
    }
    if predictor != 1 && !(predictor == 2 && (bps == 8 || bps == 16 || bps == 32)) {
        return None;
    }
    let photometric = match ph {
        Some(f) => if f.count == 1 {
            value_exec(b, le, f, 0)
        } else {
            return None;
        },
        None => return None,
    };
    let twf = match field_counted(b, le, o, n, 322, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let thf = match field_counted(b, le, o, n, 323, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let fmt = match extras_exec(b, le, o, n, spp, bps, photometric, Tracked(m)) {
        Some(f) => f,
        None => return None,
    };
    let none = Field { ty: 1, count: 0, pos: 0 };
    let base = ParamsX {
        le,
        width,
        height,
        bps,
        spp,
        compression: comp,
        photometric,
        sample_format: fmt,
        planar,
        predictor,
        tiled: false,
        rps,
        tw: 0,
        th: 0,
        offsets: none,
        counts: none,
    };
    proof {
        assert(none.values(bb, le) =~= Seq::<nat>::empty());
        assert(base.view(bb).offsets =~= Seq::<nat>::empty());
    }
    layout_exec(b, le, o, n, base, twf, thf, Tracked(m))
}

/// `spec::colours_ok`.
fn colours_exec(ph: u32, spp: u32, bps: u32, m: Option<u32>, inks: u32) -> (r: bool)
    ensures
        r == colours_ok(ph as nat, spp as nat, bps as nat, match m {
            Some(x) => Some(x as nat),
            None => None,
        }, inks as nat),
{
    if ph == 8 {
        match m {
            None => true,
            Some(m) => m <= spp && (spp - m == 1 || spp - m == 3),
        }
    } else if ph <= 5 {
        let c: u32 = if ph == 2 { 3 } else if ph == 5 { inks } else { 1 };
        let m_ok = match m {
            Some(m) => spp >= c && m == spp - c,
            None => true,
        };
        c >= 1 && spp >= c && m_ok && (ph != 3 || spp == 1) && (ph != 4 || (spp == 1 && bps == 1))
    } else {
        false
    }
}

/// SMinSampleValue or SMaxSampleValue (`spec::sample_values_ok`).
fn sample_values_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16, spp: u32, Tracked(m): Tracked<&mut Meter>) -> (r: bool)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        r == sample_values_ok(b@, le, o as nat, n as nat, tag as nat, spp as nat),
        final(m).n <= old(m).n + unit(b@.len()),
{
    let l = b.len();
    let i = match find_exec(b, le, o, n, tag, Tracked(m)) {
        None => return true,
        Some(i) => i,
    };
    let e = o + 2 + 12 * i;
    let ty = u16_exec(b, le, e + 2);
    let cnt = u32_exec(b, le, e + 4);
    let ts: u64 = if ty == 1 || ty == 6 {
        1
    } else if ty == 3 || ty == 8 {
        2
    } else if ty == 4 || ty == 9 || ty == 11 {
        4
    } else if ty == 5 || ty == 10 || ty == 12 {
        8
    } else {
        0
    };
    if cnt != spp || ts == 0 {
        return false;
    }
    proof {
        assert(cnt as int * ts as int <= 0xffff_ffff * 8) by (nonlinear_arith)
            requires cnt as int <= 0xffff_ffff, ts as int <= 8;
    }
    let size = cnt as u64 * ts;
    let pos: u64 = if size <= 4 { e as u64 + 8 } else { u32_exec(b, le, e + 8) as u64 };
    pos + size <= l as u64
}

/// `spec::extras`.
#[verifier::loop_isolation(false)]
fn extras_exec(b: &[u8], le: bool, o: usize, n: usize, spp: u32, bps: u32, photometric: u32, Tracked(m): Tracked<&mut Meter>) -> (r: Option<u32>)
    requires
        ifd_ok(b@, o as nat, n as nat),
        1 <= bps <= 32,
    ensures
        match extras(b@, le, o as nat, n as nat, spp as nat, bps as nat, photometric as nat) {
            Some(f) => r == Some(f as u32),
            None => r is None,
        },
        final(m).n <= old(m).n + 8 * unit(b@.len()),
{
    let ghost m0 = m.n;
    let inks = if photometric == 5 {
        match scalar_exec(b, le, o, n, 334, 4, Tracked(m)) {
            Some(x) => x,
            None => return None,
        }
    } else {
        4
    };
    let sf = match field_counted(b, le, o, n, 339, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let es = match field_counted(b, le, o, n, 338, Tracked(m)) {
        Ok(x) => x,
        Err(()) => return None,
    };
    let fmt = match sf {
        None => 1,
        Some(f) => {
            if f.count == 0 || f.count != spp || !same_exec(b, le, f, Tracked(m)) {
                return None;
            }
            value_exec(b, le, f, 0)
        },
    };
    if !(1 <= fmt && fmt <= 4) {
        return None;
    }
    let mx: Option<u32> = match es {
        None => None,
        Some(f) => Some(f.count),
    };
    if let Some(f) = es {
        let ghost v = f.values(b@, le);
        let ghost m1 = m.n;
        proof {
            lemma_count_le(b@, f);
        }
        let mut k: u32 = 0;
        while k < f.count
            invariant
                f.ok(b@),
                v == f.values(b@, le),
                k <= f.count,
                forall|j: int| 0 <= j < k ==> #[trigger] v[j] <= 2,
                m.n <= m1 + k,
            decreases f.count - k,
        {
            proof {
                m.n = m.n + 1;
            }
            if value_exec(b, le, f, k) > 2 {
                assert(!(v[k as int] <= 2));
                assert(!extra_values_ok(v));
                return None;
            }
            k = k + 1;
        }
    }
    if !colours_exec(photometric, spp, bps, mx, inks) {
        return None;
    }
    if photometric == 3 {
        proof {
            verilith_core::bits::lemma_mask(bps as u64);
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(bps as nat, 33);
            vstd::arithmetic::power2::lemma2_to64();
        }
        let need = 3 * (1u64 << bps as u64);
        match field_counted(b, le, o, n, 320, Tracked(m)) {
            Ok(Some(f)) => if f.count as u64 != need {
                return None;
            },
            _ => return None,
        }
    }
    let blen = b.len();
    if !sample_values_exec(b, le, o, n, 340, spp, Tracked(m)) || !sample_values_exec(b, le, o, n, 341, spp, Tracked(m)) {
        return None;
    }
    Some(fmt)
}

/// Where the strips or tiles are (`spec::layout`).
fn layout_exec(b: &[u8], le: bool, o: usize, n: usize, base: ParamsX, twf: Option<Field>, thf: Option<Field>, Tracked(m): Tracked<&mut Meter>) -> (r: Option<ParamsX>)
    requires
        ifd_ok(b@, o as nat, n as nat),
        twf matches Some(f) ==> f.ok(b@),
        thf matches Some(f) ==> f.ok(b@),
        base.le == le,
        !base.tiled,
        base.width >= 1,
        base.height >= 1,
        base.spp >= 1,
        base.rps >= 1,
        1 <= base.bps <= 32,
        base.planar == 1 || base.planar == 2,
        compression_ok(base.compression as nat),
        base.predictor == 1 || (base.predictor == 2 && (base.bps == 8 || base.bps == 16 || base.bps == 32)),
    ensures
        match layout(b@, le, o as nat, n as nat, base.view(b@), fview(b@, le, twf), fview(b@, le, thf)) {
            Some(p) => r matches Some(x) && x.view(b@) == p && x.ok(b@) && x.le == le && p.wf(),
            None => r is None,
        },
        final(m).n <= old(m).n + 5 * unit(b@.len()),
{
    let ghost bb = b@;
    let (tiled, offt, cntt): (bool, u16, u16) = match (twf, thf) {
        (None, None) => {
            if present_exec(b, le, o, n, 324, Tracked(m)) || present_exec(b, le, o, n, 325, Tracked(m)) {
                return None;
            }
            (false, 273, 279)
        },
        (Some(_), Some(_)) => {
            if present_exec(b, le, o, n, 273, Tracked(m)) || present_exec(b, le, o, n, 279, Tracked(m)) || present_exec(b, le, o, n, 278, Tracked(m)) {
                return None;
            }
            (true, 324, 325)
        },
        _ => return None,
    };
    let offs = match field_counted(b, le, o, n, offt, Tracked(m)) {
        Ok(Some(f)) => f,
        _ => return None,
    };
    let cnts = match field_counted(b, le, o, n, cntt, Tracked(m)) {
        Ok(Some(f)) => f,
        _ => return None,
    };
    let mut p = ParamsX { tiled, offsets: offs, counts: cnts, ..base };
    if tiled {
        let (tw, th) = match (twf, thf) {
            (Some(a), Some(c)) => (a, c),
            _ => return None,
        };
        if tw.count != 1 || th.count != 1 {
            return None;
        }
        let tw = value_exec(b, le, tw, 0);
        let th = value_exec(b, le, th, 0);
        if tw == 0 || th == 0 || tw % 16 != 0 || th % 16 != 0 {
            return None;
        }
        p.tw = tw;
        p.th = th;
        let sc: u128 = if p.planar == 2 { 1 } else { p.spp as u128 };
        let bps = p.bps;
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(tw as int, u32::MAX as int, sc as int);
            vstd::arithmetic::mul::lemma_mul_inequality(sc as int, u32::MAX as int, u32::MAX as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(tw as int, sc as int);
            vstd::arithmetic::mul::lemma_mul_inequality((tw * sc) as int, 0xffff_ffff_ffff_ffff, bps as int);
            vstd::arithmetic::mul::lemma_mul_inequality(bps as int, 32, 0xffff_ffff_ffff_ffff);
            vstd::arithmetic::mul::lemma_mul_is_commutative((tw * sc) as int, bps as int);
        }
        if (tw as u128 * sc * bps as u128) % 8 != 0 {
            return None;
        }
    }
    let k = chunks_exec(&p);
    proof {
        let bv = base.view(bb);
        let sp = if tiled {
            Params { tiled: true, tw: p.tw as nat, th: p.th as nat, offsets: offs.values(bb, le), counts: cnts.values(bb, le), ..bv }
        } else {
            Params { offsets: offs.values(bb, le), counts: cnts.values(bb, le), ..bv }
        };
        assert(sp == p.view(bb));
        assert(p.view(seq![]).chunks() == p.view(bb).chunks());
        assert(offs.values(bb, le).len() == offs.count);
    }
    if offs.count as u128 != k || cnts.count as u128 != k {
        return None;
    }
    proof {
        assert(p.view(bb) =~= layout(bb, le, o as nat, n as nat, base.view(bb), fview(bb, le, twf), fview(bb, le, thf))->Some_0);
    }
    Some(p)
}

} // verus!
