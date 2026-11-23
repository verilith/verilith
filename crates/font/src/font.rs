//! The verified check of a whole font: [`check_font`] decides
//! `wf_font` exactly.
use crate::cmap::*;
use crate::dir::*;
use crate::glyf::*;
use crate::prims::*;
use crate::spec::*;
use crate::layout::*;
use crate::tables::*;
use vstd::prelude::*;

verus! {

#[inline]
pub fn is_known_tag(t: u32) -> (b: bool)
    ensures
        b == known_tag(t as int),
{
    t == T_CFF || t == T_CMAP || t == T_CVT || t == T_FPGM || t == T_GASP || t == T_GLYF || t == T_HEAD || t
        == T_HHEA || t == T_HMTX || t == T_LOCA || t == T_MAXP || t == T_NAME || t == T_OS2 || t
        == T_POST || t == T_PREP || t == T_KERN || t == T_VHEA || t == T_VMTX || t == T_GDEF || t == T_GPOS
        || t == T_GSUB
}

/// The bytes of the table of record `i`.
pub fn table_at<'a>(s: &'a [u8], i: usize) -> (t: &'a [u8])
    requires
        wf_directory(s@),
        i < num_tables(s@),
    ensures
        t@ == s@.subrange(rec_off(s@, i as int), rec_end(s@, i as int)),
        t.len() <= 0xFFFF_FFFF,
{
    assert(rec_ok(s@, i as int));
    let r = 12 + 16 * i;
    let off = rd32(s, r + 8) as usize;
    let len = rd32(s, r + 12) as usize;
    slice(s, off, off + len)
}

/// The table with tag `t`, if the font has one.
pub fn get_table<'a>(s: &'a [u8], t: u32) -> (r: Option<&'a [u8]>)
    requires
        wf_directory(s@),
    ensures
        r is Some == has_table(s@, t as int),
        r matches Some(x) ==> x@ == table(s@, t as int) && x.len() <= 0xFFFF_FFFF,
{
    let i = find(s, t);
    if i < rd16(s, 4) as usize {
        Some(table_at(s, i))
    } else {
        None
    }
}

/// Decides [`wf_core`].
fn check_core(s: &[u8]) -> (b: bool)
    requires
        wf_directory(s@),
        has_required(s@),
    ensures
        b == wf_core(s@),
{
    let head = get_table(s, T_HEAD).unwrap();
    let maxp = get_table(s, T_MAXP).unwrap();
    let hhea = get_table(s, T_HHEA).unwrap();
    let hmtx = get_table(s, T_HMTX).unwrap();
    let cmap = get_table(s, T_CMAP).unwrap();
    let name = get_table(s, T_NAME).unwrap();
    let post = get_table(s, T_POST).unwrap();
    let os2 = get_table(s, T_OS2).unwrap();
    let tt = get_table(s, T_GLYF).is_some();
    if !check_head(head) || !check_maxp(maxp, tt) {
        return false;
    }
    let ng = rd16(maxp, 4);
    if !check_hhea(hhea, ng) {
        return false;
    }
    let nhm = rd16(hhea, 34);
    check_hmtx(hmtx, ng, nhm) && check_cmap(cmap, ng) && check_name(name) && check_post(post, ng)
        && check_os2(os2)
}

/// Decides [`wf_outlines`], given the core tables are well formed.
fn check_outlines(s: &[u8]) -> (b: bool)
    requires
        wf_directory(s@),
        has_required(s@),
        wf_core(s@),
    ensures
        b == wf_outlines(s@),
{
    let head = get_table(s, T_HEAD).unwrap();
    let maxp = get_table(s, T_MAXP).unwrap();
    let ng = rd16(maxp, 4);
    let fmt = rd16(head, 50);
    let glyf = get_table(s, T_GLYF);
    let loca = get_table(s, T_LOCA);
    let cff = get_table(s, T_CFF);
    let ver = rd32(s, 0);
    match glyf {
        Some(glyf) => {
            if ver != TAG_TRUETYPE || cff.is_some() {
                return false;
            }
            match loca {
                Some(loca) => check_loca(loca, fmt, ng, glyf.len()) && check_glyf(glyf, loca, fmt, ng)
                    && crate::graph::check_glyf_limits(glyf, loca, fmt, ng, maxp),
                None => false,
            }
        },
        None => {
            if ver != TAG_OTTO || loca.is_some() {
                return false;
            }
            match cff {
                Some(cff) => crate::cff::check_cff(cff, ng),
                None => false,
            }
        },
    }
}

/// Decides [`wf_extras`], given the core tables are well formed.
fn check_extras(s: &[u8]) -> (b: bool)
    requires
        wf_directory(s@),
        has_required(s@),
        wf_core(s@),
    ensures
        b == wf_extras(s@),
{
    let maxp = get_table(s, T_MAXP).unwrap();
    let ng = rd16(maxp, 4);
    let mut ms: usize = 0x10000;
    match get_table(s, T_GDEF) {
        Some(t) => {
            if !check_gdef(t, ng as usize) {
                return false;
            }
            ms = mark_sets(t, Ghost(ng as int));
        },
        None => {},
    }
    match get_table(s, T_GSUB) {
        Some(t) => {
            if !check_layout(t, false, ng as usize, ms) {
                return false;
            }
        },
        None => {},
    }
    match get_table(s, T_GPOS) {
        Some(t) => {
            if !check_layout(t, true, ng as usize, ms) {
                return false;
            }
        },
        None => {},
    }
    match get_table(s, T_CVT) {
        Some(t) => {
            if !check_cvt(t) {
                return false;
            }
        },
        None => {},
    }
    match get_table(s, T_GASP) {
        Some(t) => {
            if !check_gasp(t) {
                return false;
            }
        },
        None => {},
    }
    match get_table(s, T_KERN) {
        Some(t) => {
            if !check_kern(t, ng) {
                return false;
            }
        },
        None => {},
    }
    let vmtx = get_table(s, T_VMTX);
    match get_table(s, T_VHEA) {
        Some(vhea) => {
            if !check_vhea(vhea, ng) {
                return false;
            }
            match vmtx {
                Some(vmtx) => check_hmtx(vmtx, ng, rd16(vhea, 34)),
                None => false,
            }
        },
        None => vmtx.is_none(),
    }
}

/// Decides [`wf_tables`], given the directory is well formed and the
/// required tables are present.
fn check_tables(s: &[u8]) -> (b: bool)
    requires
        wf_directory(s@),
        has_required(s@),
    ensures
        b == wf_tables(s@),
{
    check_core(s) && check_outlines(s) && check_extras(s)
}

/// Whether every tag in the directory is a known one.
fn check_known(s: &[u8]) -> (b: bool)
    requires
        s.len() >= 12,
        12 + 16 * num_tables(s@) <= s.len(),
    ensures
        b == forall|k: int| 0 <= k < num_tables(s@) ==> known_tag(#[trigger] rec_tag(s@, k)),
{
    let n = rd16(s, 4) as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == num_tables(s@),
            12 + 16 * n <= s.len(),
            forall|k: int| 0 <= k < i ==> known_tag(#[trigger] rec_tag(s@, k)),
        decreases n - i,
    {
        if !is_known_tag(rd32(s, 12 + 16 * i)) {
            assert(!known_tag(rec_tag(s@, i as int)));
            return false;
        }
        i += 1;
    }
    true
}

/// Decides `wf_font`: `true` exactly when `s` is a well-formed font.
pub fn check_font(s: &[u8]) -> (b: bool)
    ensures
        b == wf_font(s@),
{
    if !check_directory(s) {
        return false;
    }
    if sum_words(s, 0, s.len() / 4) != 0xB1B0_AFBA {
        return false;
    }
    let n = rd16(s, 4) as usize;
    if !check_known(s) {
        return false;
    }
    if n <= find(s, T_HEAD) || n <= find(s, T_MAXP) || n <= find(s, T_HHEA) || n <= find(s, T_HMTX)
        || n <= find(s, T_CMAP) || n <= find(s, T_NAME) || n <= find(s, T_POST) || n <= find(
        s,
        T_OS2,
    ) {
        return false;
    }
    check_tables(s)
}

} // verus!
