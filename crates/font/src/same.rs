//! The verified check that a sanitized font draws the same as the tables
//! it was made from: [`check_same`] says yes only when `draws_same`
//! holds, and always says yes when the output holds exactly the input's
//! tables.
use crate::build::*;
use crate::font::get_table;
use crate::glyf::*;
use crate::prims::*;
use crate::spec::*;
use crate::spec_same::*;
use crate::tables::*;
use vstd::prelude::*;

verus! {

/// The input table with tag `t`.
pub fn in_get<'a>(ts: &'a Vec<Table>, t: u32) -> (r: Option<&'a [u8]>)
    ensures
        r is Some == in_has(tview(ts@), t as int),
        r matches Some(x) ==> x@ == in_table(tview(ts@), t as int),
{
    match lookup(ts, t) {
        Some(i) => {
            proof {
                assert(tview(ts@)[i as int] == (ts@[i as int].tag, ts@[i as int].data@));
            }
            Some(ts[i].data.as_slice())
        },
        None => None,
    }
}

pub open spec fn eq_at(a: Seq<u8>, ai: int, b: Seq<u8>, bi: int, j: int) -> bool {
    a[ai + j] == b[bi + j]
}

/// Whether `a[ai..ai + n] == b[bi..bi + n]`.
pub fn eq_range(a: &[u8], ai: usize, b: &[u8], bi: usize, n: usize) -> (r: bool)
    requires
        ai + n <= a.len(),
        bi + n <= b.len(),
    ensures
        r == (forall|j: int| 0 <= j < n ==> #[trigger] eq_at(a@, ai as int, b@, bi as int, j)),
{
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            ai + n <= a.len(),
            bi + n <= b.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] eq_at(a@, ai as int, b@, bi as int, k),
        decreases n - j,
    {
        if rd8(a, ai + j) != rd8(b, bi + j) {
            assert(!eq_at(a@, ai as int, b@, bi as int, j as int));
            return false;
        }
        j += 1;
    }
    true
}

/// Whether `a == b`.
pub fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let r = eq_range(a, 0, b, 0, a.len());
    proof {
        if r {
            assert forall|j: int| 0 <= j < a@.len() implies a@[j] == b@[j] by {
                assert(eq_at(a@, 0, b@, 0, j));
            }
            assert(a@ =~= b@);
        } else if a@ == b@ {
            assert forall|j: int| 0 <= j < a@.len() implies #[trigger] eq_at(a@, 0, b@, 0, j) by {}
        }
    }
    r
}

/// Decides `prefix_of`.
pub fn check_prefix(o: &[u8], i: &[u8]) -> (r: bool)
    ensures
        r == prefix_of(o@, i@),
{
    if o.len() > i.len() {
        return false;
    }
    let r = eq_range(o, 0, i, 0, o.len());
    proof {
        if r {
            assert forall|j: int| 0 <= j < o@.len() implies o@[j] == i@.subrange(0, o@.len() as int)[j] by {
                assert(eq_at(o@, 0, i@, 0, j));
            }
            assert(o@ =~= i@.subrange(0, o@.len() as int));
        } else if prefix_of(o@, i@) {
            assert forall|j: int| 0 <= j < o@.len() implies #[trigger] eq_at(o@, 0, i@, 0, j) by {
                assert(o@[j] == i@.subrange(0, o@.len() as int)[j]);
            }
        }
    }
    r
}

/// Decides `same_head`.
fn check_head_same(i: &[u8], o: &[u8]) -> (r: bool)
    ensures
        r == same_head(i@, o@),
{
    if i.len() < 54 || o.len() != 54 {
        return false;
    }
    let a = eq_range(o, 0, i, 0, 8);
    let b = eq_range(o, 12, i, 12, 38);
    let c = eq_range(o, 52, i, 52, 2);
    proof {
        if a && b && c {
            assert forall|j: int| 0 <= j < 54 && !(8 <= j < 12) && !(50 <= j < 52) implies #[trigger] o@[j]
                == i@[j] by {
                if j < 8 {
                    assert(eq_at(o@, 0, i@, 0, j));
                } else if j < 50 {
                    assert(eq_at(o@, 12, i@, 12, j - 12));
                } else {
                    assert(eq_at(o@, 52, i@, 52, j - 52));
                }
            }
        }
        if same_head(i@, o@) {
            assert forall|j: int| 0 <= j < 8 implies #[trigger] eq_at(o@, 0, i@, 0, j) by {
                assert(o@[j] == i@[j]);
            }
            assert forall|j: int| 0 <= j < 38 implies #[trigger] eq_at(o@, 12, i@, 12, j) by {
                assert(o@[12 + j] == i@[12 + j]);
            }
            assert forall|j: int| 0 <= j < 2 implies #[trigger] eq_at(o@, 52, i@, 52, j) by {
                assert(o@[52 + j] == i@[52 + j]);
            }
        }
    }
    a && b && c
}

/// Decides `same_maxp`.
fn check_maxp_same(i: &[u8], o: &[u8], tt: bool) -> (r: bool)
    ensures
        r == same_maxp(i@, o@, tt),
{
    if i.len() < 6 || o.len() < 6 || rd16(o, 4) != rd16(i, 4) {
        return false;
    }
    if !tt {
        return true;
    }
    if i.len() < 32 || o.len() < 32 {
        return false;
    }
    let z = rd16(i, 14);
    let cz: u16 = if z < 1 {
        1
    } else if z > 2 {
        2
    } else {
        z
    };
    let a = eq_range(o, 16, i, 16, 10);
    proof {
        if a {
            assert forall|j: int| 16 <= j < 26 implies #[trigger] o@[j] == i@[j] by {
                assert(eq_at(o@, 16, i@, 16, j - 16));
            }
        }
        if same_maxp(i@, o@, tt) {
            assert forall|j: int| 0 <= j < 10 implies #[trigger] eq_at(o@, 16, i@, 16, j) by {
                assert(o@[16 + j] == i@[16 + j]);
            }
        }
    }
    a && rd16(o, 14) == cz
}

/// Decides `same_os2`.
fn check_os2_same(i: &[u8], o: &[u8]) -> (r: bool)
    ensures
        r == same_os2(i@, o@),
{
    if o.len() < 2 || o.len() > i.len() {
        return false;
    }
    let a = eq_range(o, 2, i, 2, o.len() - 2);
    proof {
        if a {
            assert forall|j: int| 2 <= j < o@.len() implies #[trigger] o@[j] == i@[j] by {
                assert(eq_at(o@, 2, i@, 2, j - 2));
            }
        }
        if same_os2(i@, o@) {
            assert forall|j: int| 0 <= j < o@.len() - 2 implies #[trigger] eq_at(o@, 2, i@, 2, j) by {
                assert(o@[2 + j] == i@[2 + j]);
            }
        }
    }
    a
}

/// Glyph `g`'s outline, as the place in `glyf` where it starts and its
/// length: see `outline`.
pub fn outline_of(glyf: &[u8], loca: &[u8], fmt: u16, g: usize, ng: u16) -> (r: Option<(usize, usize)>)
    requires
        g < 0x10000,
    ensures
        match r {
            None => outline(glyf@, loca@, fmt as int, g as int, ng as int) is None,
            Some((a, e)) => a + e <= glyf.len() && outline(glyf@, loca@, fmt as int, g as int, ng as int)
                == Some(glyf@.subrange(a as int, a + e)),
        },
{
    if fmt > 1 {
        return None;
    }
    let w: usize = if fmt == 0 {
        2
    } else {
        4
    };
    if loca.len() < (g + 2) * w {
        return None;
    }
    let a = loca_get(loca, fmt, g);
    let b = loca_get(loca, fmt, g + 1);
    if a > b || b > glyf.len() {
        return None;
    }
    if a == b {
        assert(glyf@.subrange(0, 0) =~= Seq::<u8>::empty());
        return Some((0, 0));
    }
    let r = slice(glyf, a, b);
    if r.len() < 10 {
        return None;
    }
    if rd16(r, 0) == 0 {
        assert(glyf@.subrange(0, 0) =~= Seq::<u8>::empty());
        return Some((0, 0));
    }
    match find_glyph_end(r, ng) {
        Some(e) => {
            assert(r@.subrange(0, e as int) =~= glyf@.subrange(a as int, a + e));
            Some((a, e))
        },
        None => None,
    }
}

/// Whether glyph `g` has the same outline in both fonts.
fn same_glyph(
    ig: &[u8],
    il: &[u8],
    ifmt: u16,
    og: &[u8],
    ol: &[u8],
    ofmt: u16,
    g: usize,
    ng: u16,
) -> (r: bool)
    requires
        g < 0x10000,
    ensures
        r == (outline(ig@, il@, ifmt as int, g as int, ng as int) == outline(
            og@,
            ol@,
            ofmt as int,
            g as int,
            ng as int,
        )),
{
    match (outline_of(ig, il, ifmt, g, ng), outline_of(og, ol, ofmt, g, ng)) {
        (None, None) => true,
        (Some((a, e)), Some((c, f))) => {
            if e != f {
                assert(ig@.subrange(a as int, a + e).len() != og@.subrange(c as int, c + f).len());
                return false;
            }
            let x = eq_range(ig, a, og, c, e);
            proof {
                if x {
                    let x1 = ig@.subrange(a as int, a + e);
                    let x2 = og@.subrange(c as int, c + f);
                    assert forall|j: int| 0 <= j < e implies #[trigger] x1[j] == x2[j] by {
                        assert(eq_at(ig@, a as int, og@, c as int, j));
                    }
                    assert(x1 =~= x2);
                } else if ig@.subrange(a as int, a + e) == og@.subrange(c as int, c + f) {
                    assert forall|j: int| 0 <= j < e implies #[trigger] eq_at(ig@, a as int, og@, c as int, j) by {
                        assert(ig@.subrange(a as int, a + e)[j] == og@.subrange(c as int, c + f)[j]);
                    }
                }
            }
            x
        },
        _ => false,
    }
}

/// Decides `kept_as_is` for table `t`.
fn check_kept(ts: &Vec<Table>, s: &[u8], t: u32) -> (r: bool)
    requires
        wf_directory(s@),
        fits(s@),
    ensures
        r == kept_as_is(tview(ts@), s@, t as int),
{
    match get_table(s, t) {
        Some(o) => match in_get(ts, t) {
            Some(i) => eq_bytes(o, i),
            None => false,
        },
        None => true,
    }
}

/// Decides `same_hinting`.
fn check_hinting(ts: &Vec<Table>, s: &[u8], ng: u16) -> (r: bool)
    requires
        wf_directory(s@),
        fits(s@),
    ensures
        r == same_hinting(tview(ts@), s@, ng as int),
{
    if !check_kept(ts, s, T_FPGM) || !check_kept(ts, s, T_PREP) || !check_kept(ts, s, T_CVT)
        || !check_kept(ts, s, T_GASP) || !check_kept(ts, s, T_KERN) {
        return false;
    }
    let tt = get_table(s, T_GLYF).is_some();
    if tt {
        match in_get(ts, T_FPGM) {
            Some(x) => {
                if x.len() > 0 && get_table(s, T_FPGM).is_none() {
                    return false;
                }
            },
            None => {},
        }
        match in_get(ts, T_PREP) {
            Some(x) => {
                if x.len() > 0 && get_table(s, T_PREP).is_none() {
                    return false;
                }
            },
            None => {},
        }
        match in_get(ts, T_CVT) {
            Some(x) => {
                if x.len() > 0 && check_cvt(x) && get_table(s, T_CVT).is_none() {
                    return false;
                }
            },
            None => {},
        }
        match in_get(ts, T_GASP) {
            Some(x) => {
                if check_gasp(x) && get_table(s, T_GASP).is_none() {
                    return false;
                }
            },
            None => {},
        }
    }
    match in_get(ts, T_KERN) {
        Some(x) => {
            if check_kern(x, ng) && get_table(s, T_KERN).is_none() {
                return false;
            }
        },
        None => {},
    }
    true
}

/// Decides `same_vertical`.
fn check_vertical(ts: &Vec<Table>, s: &[u8], ng: u16) -> (r: bool)
    requires
        wf_font(s@),
        fits(s@),
    ensures
        r == same_vertical(tview(ts@), s@, ng as int),
{
    let ivh = in_get(ts, T_VHEA);
    let ivm = in_get(ts, T_VMTX);
    match get_table(s, T_VHEA) {
        Some(ovh) => match (ivh, ivm, get_table(s, T_VMTX)) {
            (Some(vh), Some(vm), Some(ovm)) => check_prefix(ovh, vh) && check_prefix(ovm, vm),
            _ => false,
        },
        None => match (ivh, ivm) {
            (Some(vh), Some(vm)) => {
                if vh.len() >= 36 && check_vhea(slice(vh, 0, 36), ng) {
                    let nvm = rd16(vh, 34) as usize;
                    let want = 4 * nvm + 2 * (ng as usize - nvm);
                    !(vm.len() >= want)
                } else {
                    true
                }
            },
            _ => true,
        },
    }
}


/// Whether every glyph has the same outline in both fonts.
fn same_glyphs(ig: &[u8], il: &[u8], ifmt: u16, og: &[u8], ol: &[u8], ofmt: u16, ng: u16) -> (r: bool)
    ensures
        r == forall|k: int|
            0 <= k < ng ==> #[trigger] outline(ig@, il@, ifmt as int, k, ng as int) == outline(
                og@,
                ol@,
                ofmt as int,
                k,
                ng as int,
            ),
{
    let mut g: usize = 0;
    while g < ng as usize
        invariant
            g <= ng,
            forall|k: int|
                0 <= k < g ==> #[trigger] outline(ig@, il@, ifmt as int, k, ng as int) == outline(
                    og@,
                    ol@,
                    ofmt as int,
                    k,
                    ng as int,
                ),
        decreases ng - g,
    {
        if !same_glyph(ig, il, ifmt, og, ol, ofmt, g, ng) {
            return false;
        }
        g += 1;
    }
    true
}

/// Decides `same_outlines`.
fn check_outlines_same(ts: &Vec<Table>, s: &[u8], ng: u16) -> (r: bool)
    requires
        wf_font(s@),
        fits(s@),
        ng as int == num_glyphs(table(s@, T_MAXP as int)),
        in_has(tview(ts@), T_HEAD as int),
        in_table(tview(ts@), T_HEAD as int).len() >= 54,
    ensures
        r == same_outlines(tview(ts@), s@, ng as int),
{
    let ghost tv = tview(ts@);
    let og = get_table(s, T_GLYF);
    let ig = in_get(ts, T_GLYF);
    if og.is_some() != ig.is_some() {
        return false;
    }
    match (og, ig) {
        (Some(og), Some(ig)) => {
            let il = match in_get(ts, T_LOCA) {
                Some(x) => x,
                None => {
                    return false;
                },
            };
            let ol = get_table(s, T_LOCA).unwrap();
            let ih = in_get(ts, T_HEAD).unwrap();
            let oh = get_table(s, T_HEAD).unwrap();
            let ifmt = rd16(ih, 50);
            let ofmt = rd16(oh, 50);
            if !same_glyphs(ig, il, ifmt, og, ol, ofmt, ng) {
                return false;
            }
        },
        _ => {},
    }
    match get_table(s, T_CFF) {
        Some(oc) => match in_get(ts, T_CFF) {
            Some(ic) => eq_bytes(oc, ic),
            None => false,
        },
        None => true,
    }
}

/// The length of the `cmap` subtable at `oo`, if the table holds it.
fn sub_len_of(o: &[u8], oo: usize, Ghost(ng): Ghost<int>) -> (r: Option<usize>)
    ensures
        r matches Some(l) ==> l == sub_len(o@, oo as int) && oo + l <= o.len(),
        wf_cmap_sub(o@, oo as int, ng) ==> r is Some,
{
    if oo > o.len() || o.len() - oo < 2 {
        return None;
    }
    let f = rd16(o, oo);
    let l: u64 = if f == 0 {
        262
    } else if f == 4 {
        if o.len() - oo < 4 {
            return None;
        }
        rd16(o, oo + 2) as u64
    } else if f == 12 || f == 13 {
        if o.len() - oo < 16 {
            return None;
        }
        16 + 12 * rd32(o, oo + 12) as u64
    } else {
        if o.len() - oo < 6 {
            return None;
        }
        rd32(o, oo + 2) as u64
    };
    if l > (o.len() - oo) as u64 {
        return None;
    }
    Some(l as usize)
}

/// Where the format 4 repair of the subtable at `o` writes: see
/// `repair4_at`.
fn repair_at(t: &[u8], o: usize) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            None => repair4_at(t@, o as int) is None,
            Some((d, ro)) => repair4_at(t@, o as int) == Some((d as int, ro as int)) && ro + 2 <= t.len()
                && d + 2 <= ro,
        },
{
    if o > t.len() || t.len() - o < 16 || rd16(t, o) != 4 {
        return None;
    }
    let sc = (rd16(t, o + 6) / 2) as usize;
    if sc < 1 || 16 + 8 * sc > t.len() - o {
        return None;
    }
    let k = sc - 1;
    let end = o + 14 + 2 * k;
    let start = o + 16 + 2 * sc + 2 * k;
    let delta = o + 16 + 4 * sc + 2 * k;
    let ro = o + 16 + 6 * sc + 2 * k;
    if rd16(t, end) == 0xFFFF && rd16(t, start) == 0xFFFF && rd16(t, ro) == 0xFFFF {
        Some((delta, ro))
    } else {
        None
    }
}

/// Whether `o[oo..oo + l]` is `i[oi..oi + l]` after the format 4 repair
/// of the subtable at `oi`.
fn eq_repaired(o: &[u8], oo: usize, i: &[u8], oi: usize, l: usize) -> (r: bool)
    requires
        oo + l <= o.len(),
        oi + l <= i.len(),
    ensures
        r ==> o@.subrange(oo as int, oo + l) == repair4(i@, oi as int).subrange(oi as int, oi + l),
{
    match repair_at(i, oi) {
        None => false,
        Some((d, ro)) => {
            let ghost rep = repair4(i@, oi as int);
            assert(rep == i@.update(d as int, 0).update(d + 1, 1).update(ro as int, 0).update(ro + 1, 0));
            let mut q: usize = 0;
            while q < l
                invariant
                    q <= l,
                    oo + l <= o.len(),
                    oi + l <= i.len(),
                    rep.len() == i@.len(),
                    rep == i@.update(d as int, 0).update(d + 1, 1).update(ro as int, 0).update(ro + 1, 0),
                    ro + 2 <= i.len(),
                    d + 2 <= ro,
                    forall|k: int| 0 <= k < q ==> #[trigger] eq_at(o@, oo as int, rep, oi as int, k),
                decreases l - q,
            {
                let p = oi + q;
                let want: u8 = if p == d {
                    0
                } else if p == d + 1 {
                    1
                } else if p == ro || p == ro + 1 {
                    0
                } else {
                    rd8(i, p)
                };
                assert(rep[p as int] == want);
                if rd8(o, oo + q) != want {
                    return false;
                }
                q += 1;
            }
            proof {
                let x1 = o@.subrange(oo as int, oo + l);
                let x2 = rep.subrange(oi as int, oi + l);
                assert forall|k: int| 0 <= k < l implies #[trigger] x1[k] == x2[k] by {
                    assert(eq_at(o@, oo as int, rep, oi as int, k));
                }
                assert(x1 =~= x2);
            }
            true
        },
    }
}

/// Says yes only if `same_cmap` holds, and whenever the two tables are
/// the same well-formed `cmap`.
fn check_cmap_same(i: &[u8], o: &[u8], Ghost(ng): Ghost<int>) -> (r: bool)
    ensures
        r ==> same_cmap(i@, o@),
        (i@ == o@ && wf_cmap(o@, ng)) ==> r,
{
    if o.len() < 4 || i.len() < 4 {
        return false;
    }
    let no = rd16(o, 2) as usize;
    let ni = rd16(i, 2) as usize;
    if 4 + 8 * no > o.len() {
        return false;
    }
    let ghost same = i@ == o@ && wf_cmap(o@, ng);
    let mut j: usize = 0;
    let mut k: usize = 0;
    while k < no
        invariant
            k <= no,
            4 + 8 * no <= o.len(),
            o.len() >= 4,
            no == u16_at(o@, 2),
            ni == u16_at(i@, 2),
            same == (i@ == o@ && wf_cmap(o@, ng)),
            forall|kk: int| 0 <= kk < k ==> #[trigger] cmap_rec_kept(i@, o@, kk),
            same ==> j == k,
        decreases no - k,
    {
        let ro = 4 + 8 * k;
        let pe = rd32(o, ro);
        let oo = rd32(o, ro + 4) as usize;
        proof {
            if same {
                assert(cmap_rec_ok(o@, k as int, ng));
            }
        }
        let l = match sub_len_of(o, oo, Ghost(ng)) {
            Some(l) => l,
            None => {
                return false;
            },
        };
        let mut found = false;
        while j < ni && !found
            invariant
                k < no,
                ro == 4 + 8 * k,
                4 + 8 * no <= o.len(),
                ni == u16_at(i@, 2),
                same == (i@ == o@ && wf_cmap(o@, ng)),
                pe as int == u32_at(o@, ro as int),
                oo as int == u32_at(o@, ro + 4),
                l == sub_len(o@, oo as int),
                oo + l <= o.len(),
                found ==> cmap_rec_kept(i@, o@, k as int),
                same ==> if found {
                    j == k + 1
                } else {
                    j == k
                },
            decreases ni - j,
        {
            let ri = 4 + 8 * j;
            if ri + 8 > i.len() {
                return false;
            }
            if rd32(i, ri) == pe {
                let oi = rd32(i, ri + 4) as usize;
                if oi <= i.len() && l <= i.len() - oi {
                    let plain = eq_range(o, oo, i, oi, l);
                    if plain || eq_repaired(o, oo, i, oi, l) {
                        found = true;
                        proof {
                            if plain {
                                let x1 = o@.subrange(oo as int, oo + l);
                                let x2 = i@.subrange(oi as int, oi + l);
                                assert forall|q: int| 0 <= q < l implies #[trigger] x1[q] == x2[q] by {
                                    assert(eq_at(o@, oo as int, i@, oi as int, q));
                                }
                                assert(x1 =~= x2);
                            }
                            assert(cmap_rec_same(i@, j as int, o@, k as int));
                        }
                    }
                    proof {
                        if same && j == k {
                            assert forall|q: int| 0 <= q < l implies #[trigger] eq_at(o@, oo as int, i@, oi as int, q) by {}
                        }
                    }
                }
            }
            j += 1;
        }
        if !found {
            return false;
        }
        k += 1;
    }
    true
}

/// The bounds `dls_fix` asks of script record `r`.
pub open spec fn dls_bounds(i: Seq<u8>, r: int) -> bool {
    let sl = u16_at(i, 4);
    let so = sl + u16_at(i, sl + 2 + 6 * r + 4);
    &&& 6 <= i.len()
    &&& sl + 2 <= i.len()
    &&& 0 <= r < u16_at(i, sl)
    &&& sl + 2 + 6 * r + 6 <= i.len()
    &&& so + 2 <= i.len()
}

/// Byte `p` may be cleared by the repair of script `r`'s default
/// language system.
pub open spec fn z0(i: Seq<u8>, r: int, p: int) -> bool {
    let sl = u16_at(i, 4);
    let so = sl + u16_at(i, sl + 2 + 6 * r + 4);
    let d = u16_at(i, so);
    let l = so + d;
    dls_bounds(i, r) && ((so <= p < so + 2) || (d != 0 && l <= p < l + 2))
}

/// Byte `p` may be set to 0xFF by that repair.
pub open spec fn zf(i: Seq<u8>, r: int, p: int) -> bool {
    let sl = u16_at(i, 4);
    let so = sl + u16_at(i, sl + 2 + 6 * r + 4);
    let d = u16_at(i, so);
    let l = so + d;
    dls_bounds(i, r) && d != 0 && l + 2 <= p < l + 4
}

/// `m0[p]`: byte `p` may be cleared; `mf[p]`: it may be set to 0xFF.
pub open spec fn mask_ok(i: Seq<u8>, m0: Seq<bool>, mf: Seq<bool>) -> bool {
    &&& forall|p: int| 0 <= p < m0.len() && #[trigger] m0[p] ==> exists|r: int| #[trigger] z0(i, r, p)
    &&& forall|p: int| 0 <= p < mf.len() && #[trigger] mf[p] ==> exists|r: int| #[trigger] zf(i, r, p)
}

fn set_mask(i: &[u8], m0: &mut Vec<bool>, mf: &mut Vec<bool>, p: usize, ff: bool, Ghost(r): Ghost<int>)
    requires
        mask_ok(i@, old(m0)@, old(mf)@),
        !ff ==> z0(i@, r, p as int),
        ff ==> zf(i@, r, p as int),
    ensures
        final(m0)@.len() == old(m0)@.len(),
        final(mf)@.len() == old(mf)@.len(),
        mask_ok(i@, final(m0)@, final(mf)@),
{
    if !ff && p < m0.len() {
        m0.set(p, true);
        proof {
            assert forall|q: int| 0 <= q < m0@.len() && #[trigger] m0@[q] implies exists|r: int| #[trigger] z0(i@, r, q) by {
                if q == p {
                    assert(z0(i@, r, q));
                } else {
                    assert(m0@[q] == old(m0)@[q]);
                }
            }
        }
    }
    if ff && p < mf.len() {
        mf.set(p, true);
        proof {
            assert forall|q: int| 0 <= q < mf@.len() && #[trigger] mf@[q] implies exists|r: int| #[trigger] zf(i@, r, q) by {
                if q == p {
                    assert(zf(i@, r, q));
                } else {
                    assert(mf@[q] == old(mf)@[q]);
                }
            }
        }
    }
}

/// Marks the bytes that the repair of script `r`'s default language
/// system may change.
fn mark_script(i: &[u8], m0: &mut Vec<bool>, mf: &mut Vec<bool>, sl: usize, r: usize)
    requires
        old(m0)@.len() == i.len(),
        old(mf)@.len() == i.len(),
        mask_ok(i@, old(m0)@, old(mf)@),
        i.len() >= 6,
        sl as int == u16_at(i@, 4),
        sl + 2 <= i.len(),
        r < u16_at(i@, sl as int),
        sl + 2 + 6 * r + 6 <= i.len(),
    ensures
        final(m0)@.len() == i.len(),
        final(mf)@.len() == i.len(),
        mask_ok(i@, final(m0)@, final(mf)@),
{
    let n = i.len();
    let so = sl + rd16(i, sl + 2 + 6 * r + 4) as usize;
    if so + 2 > n {
        return;
    }
    let ghost gr = r as int;
    assert(dls_bounds(i@, gr));
    set_mask(i, m0, mf, so, false, Ghost(gr));
    set_mask(i, m0, mf, so + 1, false, Ghost(gr));
    let d = rd16(i, so) as usize;
    if d != 0 {
        let l = so + d;
        set_mask(i, m0, mf, l, false, Ghost(gr));
        set_mask(i, m0, mf, l + 1, false, Ghost(gr));
        set_mask(i, m0, mf, l + 2, true, Ghost(gr));
        set_mask(i, m0, mf, l + 3, true, Ghost(gr));
    }
}

/// Says yes only if the layout table `o` is `i` but for `layout_fix`,
/// and whenever the two are the same.
fn check_layout_same(i: &[u8], o: &[u8], gdef: bool) -> (r: bool)
    requires
        i.len() <= TABLE_MAX,
    ensures
        r ==> o@.len() == i@.len() && forall|j: int|
            0 <= j < o@.len() ==> (#[trigger] o@[j] == i@[j] || layout_fix(i@, o@, gdef, j)),
        i@ == o@ ==> r,
{
    if o.len() != i.len() {
        return false;
    }
    let n = i.len();
    let mut m0: Vec<bool> = Vec::new();
    let mut mf: Vec<bool> = Vec::new();
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n,
            m0@.len() == q,
            mf@.len() == q,
            forall|p: int| 0 <= p < q ==> !(#[trigger] m0@[p]),
            forall|p: int| 0 <= p < q ==> !(#[trigger] mf@[p]),
        decreases n - q,
    {
        m0.push(false);
        mf.push(false);
        q += 1;
    }
    assert(mask_ok(i@, m0@, mf@));
    if !gdef && n >= 6 {
        let sl = rd16(i, 4) as usize;
        if sl + 2 <= n {
            let ns = rd16(i, sl) as usize;
            let mut r: usize = 0;
            while r < ns
                invariant
                    m0@.len() == n,
                    mf@.len() == n,
                    n == i.len(),
                    n >= 6,
                    n <= TABLE_MAX,
                    mask_ok(i@, m0@, mf@),
                    ns as int == u16_at(i@, sl as int),
                    sl as int == u16_at(i@, 4),
                    sl + 2 <= n,
                    r <= ns,
                decreases ns - r,
            {
                if sl + 2 + 6 * r + 6 > n {
                    break;
                }
                mark_script(i, &mut m0, &mut mf, sl, r);
                r += 1;
            }
        }
    }
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == i.len(),
            n == o.len(),
            m0@.len() == n,
            mf@.len() == n,
            mask_ok(i@, m0@, mf@),
            forall|k: int| 0 <= k < j ==> (#[trigger] o@[k] == i@[k] || layout_fix(i@, o@, gdef, k)),
            i@ == o@ ==> true,
        decreases n - j,
    {
        let a = rd8(o, j);
        let b = rd8(i, j);
        if a != b {
            let var = if gdef {
                14 <= j && j < 18
            } else {
                10 <= j && j < 14
            };
            let ok = (a == 0 && var) || (!gdef && ((m0[j] && a == 0) || (mf[j] && a == 0xFF)));
            if !ok {
                return false;
            }
            proof {
                if !(a == 0 && var) {
                    if m0@[j as int] && a == 0 {
                        let r = choose|r: int| #[trigger] z0(i@, r, j as int);
                        assert(dls_fix(i@, o@, r, j as int));
                    } else {
                        let r = choose|r: int| #[trigger] zf(i@, r, j as int);
                        assert(dls_fix(i@, o@, r, j as int));
                    }
                }
            }
        }
        j += 1;
    }
    true
}

/// Decides `same_name_post`.
fn check_name_post(ts: &Vec<Table>, s: &[u8], ng: u16) -> (r: bool)
    requires
        wf_font(s@),
        fits(s@),
        in_has(tview(ts@), T_NAME as int),
        in_has(tview(ts@), T_POST as int),
    ensures
        r == same_name_post(tview(ts@), s@, ng as int),
{
    let iname = in_get(ts, T_NAME).unwrap();
    let ipost = in_get(ts, T_POST).unwrap();
    let oname = get_table(s, T_NAME).unwrap();
    let opost = get_table(s, T_POST).unwrap();
    if check_name(iname) && !eq_bytes(oname, iname) {
        return false;
    }
    if check_post(ipost, ng) && !eq_bytes(opost, ipost) {
        return false;
    }
    if ipost.len() < 32 || opost.len() < 32 {
        return false;
    }
    let a = eq_range(opost, 4, ipost, 4, 28);
    proof {
        if a {
            assert forall|j: int| 4 <= j < 32 implies #[trigger] opost@[j] == ipost@[j] by {
                assert(eq_at(opost@, 4, ipost@, 4, j - 4));
            }
        }
        if same_name_post(tview(ts@), s@, ng as int) {
            assert forall|j: int| 0 <= j < 28 implies #[trigger] eq_at(opost@, 4, ipost@, 4, j) by {
                assert(opost@[4 + j] == ipost@[4 + j]);
            }
        }
    }
    a
}


/// Says yes only if `same_layout` holds for `t`, and whenever the output
/// table is the input's.
fn check_layout_tbl(ts: &Vec<Table>, s: &[u8], t: u32, gdef: bool) -> (r: bool)
    requires
        wf_directory(s@),
        fits(s@),
    ensures
        r ==> same_layout(tview(ts@), s@, t as int, gdef),
        same_one(tview(ts@), s@, t) && t != T_HEAD ==> r,
{
    match (get_table(s, t), in_get(ts, t)) {
        (Some(o), Some(i)) => {
            if i.len() > TABLE_MAX {
                return false;
            }
            check_layout_same(i, o, gdef)
        },
        (None, None) => true,
        _ => false,
    }
}

/// A font holding exactly the input's tables passes every part of the
/// check.
proof fn lemma_identical(tv: Tables, s: Seq<u8>)
    requires
        wf_font(s),
        same_tables(tv, s),
    ensures
        same_head(in_table(tv, T_HEAD as int), table(s, T_HEAD as int)),
        same_maxp(in_table(tv, T_MAXP as int), table(s, T_MAXP as int), has_table(s, T_GLYF as int)),
        prefix_of(table(s, T_HHEA as int), in_table(tv, T_HHEA as int)),
        prefix_of(table(s, T_HMTX as int), in_table(tv, T_HMTX as int)),
        same_os2(in_table(tv, T_OS2 as int), table(s, T_OS2 as int)),
        same_vertical(tv, s, num_glyphs(table(s, T_MAXP as int))),
        same_outlines(tv, s, num_glyphs(table(s, T_MAXP as int))),
        same_hinting(tv, s, num_glyphs(table(s, T_MAXP as int))),
        in_table(tv, T_CMAP as int) == table(s, T_CMAP as int),
        wf_cmap(table(s, T_CMAP as int), num_glyphs(table(s, T_MAXP as int))),
        same_name_post(tv, s, num_glyphs(table(s, T_MAXP as int))),
        in_table(tv, T_HEAD as int).len() >= 54,
{
    let ih = in_table(tv, T_HEAD as int);
    let oh = table(s, T_HEAD as int);
    assert(same_one(tv, s, T_HEAD));
    assert(head_eq(oh, ih));
    assert(wf_head(oh));
    assert forall|j: int| 0 <= j < 54 && !(8 <= j < 12) && !(50 <= j < 52) implies #[trigger] oh[j] == ih[j] by {
        assert(oh[j] == ih[j]);
    }
    assert(u16_at(oh, 50) == u16_at(ih, 50)) by {
        assert(oh[50] == ih[50] && oh[51] == ih[51]);
    }
    let x = table(s, T_HHEA as int);
    assert(x =~= x.subrange(0, x.len() as int));
    let y = table(s, T_HMTX as int);
    assert(y =~= y.subrange(0, y.len() as int));
    if has_table(s, T_VHEA as int) {
        let a = table(s, T_VHEA as int);
        let b = table(s, T_VMTX as int);
        assert(a =~= a.subrange(0, a.len() as int));
        assert(b =~= b.subrange(0, b.len() as int));
    }
}

/// Says yes only if the output font `s` draws the same as the input
/// tables `ts` (`draws_same`), and always says yes when `s` holds exactly
/// the input's known tables.
pub fn check_same(ts: &Vec<Table>, s: &[u8]) -> (b: bool)
    requires
        wf_font(s@),
        fits(s@),
    ensures
        b ==> draws_same(tview(ts@), s@),
        same_tables(tview(ts@), s@) ==> b,
{
    let ghost tv = tview(ts@);
    proof {
        if same_tables(tv, s@) {
            lemma_identical(tv, s@);
        }
    }
    let ih = match in_get(ts, T_HEAD) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let im = match in_get(ts, T_MAXP) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let ihh = match in_get(ts, T_HHEA) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let ihm = match in_get(ts, T_HMTX) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let ios = match in_get(ts, T_OS2) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let icm = match in_get(ts, T_CMAP) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if in_get(ts, T_NAME).is_none() || in_get(ts, T_POST).is_none() {
        return false;
    }
    let oh = get_table(s, T_HEAD).unwrap();
    let om = get_table(s, T_MAXP).unwrap();
    let ohh = get_table(s, T_HHEA).unwrap();
    let ohm = get_table(s, T_HMTX).unwrap();
    let oos = get_table(s, T_OS2).unwrap();
    let ocm = get_table(s, T_CMAP).unwrap();
    let tt = get_table(s, T_GLYF).is_some();
    if !check_head_same(ih, oh) || !check_maxp_same(im, om, tt) || !check_prefix(ohh, ihh)
        || !check_prefix(ohm, ihm) || !check_os2_same(ios, oos) {
        return false;
    }
    let ng = rd16(om, 4);
    if !check_vertical(ts, s, ng) || !check_outlines_same(ts, s, ng) || !check_hinting(ts, s, ng) {
        return false;
    }
    if !check_cmap_same(icm, ocm, Ghost(ng as int)) {
        return false;
    }
    if !check_layout_tbl(ts, s, T_GDEF, true) || !check_layout_tbl(ts, s, T_GSUB, false)
        || !check_layout_tbl(ts, s, T_GPOS, false) {
        return false;
    }
    check_name_post(ts, s, ng)
}

} // verus!
