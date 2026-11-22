#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, unused_braces, unused_mut, unused_assignments, unused_parens))]
//! A formally verified (Verus) OpenType font sanitizer.
//!
//! [`sanitize`] takes the bytes of a font and returns either a font it
//! has rebuilt or nothing. The theorem, checked by Verus: every font it
//! returns satisfies [`spec::wf_font`].
pub mod build;
pub mod capi;
pub mod cff;
pub mod cmap;
pub mod cs;
pub mod dir;
pub mod font;
pub mod glyf;
pub mod lay;
pub mod layout;
pub mod graph;
pub mod prims;
pub mod spec;
pub mod spec_cff;
pub mod spec_cs;
pub mod spec_layout;
pub mod tables;
pub mod woff2;

use vstd::prelude::*;

verus! {

/// Sanitizes a font: plain OpenType or TrueType, WOFF, or the first font
/// of a TrueType Collection. `None` means the input was refused.
pub fn sanitize(input: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@),
{
    sanitize_index(input, 0)
}

/// As [`sanitize`], choosing font `index` of a TrueType Collection.
pub fn sanitize_index(input: &[u8], index: u32) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> spec::wf_font(out@),
{
    let ts = build::read_font(input, index)?;
    let out_tables = build::build_tables(&ts)?;
    let version = if build::lookup(&ts, spec::T_GLYF).is_some() {
        spec::TAG_TRUETYPE
    } else {
        spec::TAG_OTTO
    };
    let out = build::assemble(&out_tables, version)?;
    if font::check_font(out.as_slice()) {
        Some(out)
    } else {
        None
    }
}

} // verus!
