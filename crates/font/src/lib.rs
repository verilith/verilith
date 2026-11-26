#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_braces, unused_mut, unused_assignments, unused_parens))]
// A formally verified (Verus) OpenType font sanitizer.
//
// [`sanitize`] takes the bytes of a font and returns either a font it
// has rebuilt or nothing. The theorems, checked by Verus: every font it
// returns satisfies [`spec::wf_font`] and draws the same as its input
// ([`spec_same::draws_same`]), and every valid font is accepted
// ([`spec_same::valid_tables`]).

// The table-size arithmetic is proven with 64-bit usize. Only where it
// holds, so that a 32-bit build stops at the error above rather than at the
// size check this generates.
#[cfg(target_pointer_width = "64")]
vstd::prelude::verus! {
global size_of usize == 8;
}
#[cfg(target_pointer_width = "32")]
vstd::prelude::verus! {
global size_of usize == 4;
}

#[doc(hidden)]
pub mod build;
#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod cff;
#[doc(hidden)]
pub mod cmap;
#[doc(hidden)]
pub mod cs;
#[doc(hidden)]
pub mod dir;
#[doc(hidden)]
pub mod font;
#[doc(hidden)]
pub mod glyf;
#[doc(hidden)]
pub mod lay;
#[doc(hidden)]
pub mod layout;
#[doc(hidden)]
pub mod graph;
#[doc(hidden)]
pub mod prims;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod spec_cff;
#[doc(hidden)]
pub mod spec_cs;
#[doc(hidden)]
pub mod spec_layout;
#[doc(hidden)]
pub mod spec_same;
#[doc(hidden)]
pub mod same;
#[doc(hidden)]
pub mod relayout;
#[doc(hidden)]
pub mod tables;
#[doc(hidden)]
pub mod woff2;

use vstd::prelude::*;

verus! {

/// Sanitizes a font: plain OpenType or TrueType, WOFF, WOFF2, or the
/// first font of a TrueType Collection. `None` means the input was
/// refused.
///
/// Every font returned is well formed. For a plain OpenType file or a
/// collection, it also draws the same as the input, and a valid input is
/// never refused (see `spec_same`).
pub fn sanitize(input: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@),
        r matches Some(out) ==> (spec_same::input_tables(input@, 0) matches Some(t) ==> spec_same::draws_same(
            t,
            out@,
        )),
        (spec_same::input_tables(input@, 0) matches Some(t) && spec_same::valid_tables(t)) ==> r is Some,
{
    sanitize_index(input, 0)
}

/// As [`sanitize`], choosing font `index` of a TrueType Collection.
pub fn sanitize_index(input: &[u8], index: u32) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@),
        r matches Some(out) ==> (spec_same::input_tables(input@, index as int) matches Some(t)
            ==> spec_same::draws_same(t, out@)),
        (spec_same::input_tables(input@, index as int) matches Some(t) && spec_same::valid_tables(t)) ==> r is Some,
{
    let ts = build::read_font(input, index)?;
    sanitize_tables(&ts)
}

/// Sanitizes a font given as the tables a container reader found.
///
/// Every font returned is well formed and draws the same as `ts`, and if
/// `ts` is a valid font it is not refused.
pub fn sanitize_tables(ts: &Vec<build::Table>) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@) && spec_same::draws_same(build::tview(ts@), out@),
        spec_same::valid_tables(build::tview(ts@)) ==> r is Some,
{
    match rebuild(ts) {
        Some(out) => {
            if font::check_font(out.as_slice()) && same::check_same(ts, out.as_slice()) {
                return Some(out);
            }
        },
        None => {},
    }
    relay(ts)
}

/// The font the builder makes: each table read, repaired or rebuilt, and
/// the result laid out. Not trusted: `sanitize_tables` checks it.
fn rebuild(ts: &Vec<build::Table>) -> Option<Vec<u8>> {
    let out_tables = build::build_tables(ts)?;
    let version = if build::lookup(ts, spec::T_GLYF).is_some() {
        spec::TAG_TRUETYPE
    } else {
        spec::TAG_OTTO
    };
    build::assemble(&out_tables, version)
}

/// The input's known tables laid out again unchanged, if that makes a
/// well-formed font. It does whenever the input is valid.
#[doc(hidden)]
pub fn relay(ts: &Vec<build::Table>) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@) && spec_same::draws_same(build::tview(ts@), out@),
        spec_same::valid_tables(build::tview(ts@)) ==> r is Some,
{
    let ghost tv = build::tview(ts@);
    let c = relayout::canon_tables(ts);
    let version = if build::lookup(ts, spec::T_GLYF).is_some() {
        spec::TAG_TRUETYPE
    } else {
        spec::TAG_OTTO
    };
    proof {
        if spec_same::valid_tables(tv) {
            relayout::lemma_can_assemble(tv, c@);
        }
    }
    let out = build::assemble(&c, version)?;
    proof {
        let cv = build::tview(c@);
        assert forall|k: int| 0 <= k < cv.len() implies #[trigger] spec::rec_tag(out@, k) == cv[k].0 by {
            assert(cv[k] == (c@[k].tag, c@[k].data@));
        }
        relayout::lemma_relaid(tv, cv, out@);
        if spec_same::valid_tables(tv) {
            relayout::lemma_relaid_wf(tv, out@);
            build::lemma_body_len(cv, 0, cv.len() as int);
            assert(prims::fits(out@));
        }
    }
    if font::check_font(out.as_slice()) && same::check_same(ts, out.as_slice()) {
        Some(out)
    } else {
        None
    }
}

} // verus!
