//! The specification of imgproxy's URLs: what `url::parse` returns for a
//! request path, as total functions over `Seq<u8>`, and of choosing a
//! decoder from a file's first bytes. Part of the trusted base with
//! `spec.rs`; it reuses verilith-text's specifications of percent-decoding
//! and base64.
//!
//! ```text
//! /%signature/%option/.../plain/%source_url[@%extension]
//! /%signature/%option/.../%base64url_source_url[.%extension]
//! /%signature/%option/.../upload[@%extension]
//! ```
//!
//! An option is a path segment `name:arg:arg...` (one that has a `:` and
//! does not start with `http` or `local`); options apply left to right,
//! and a later one overrides an earlier one.
use crate::fit::Mode;
#[cfg(verus_only)]
use crate::spec_geom::F1;
use crate::spec_geom::{GKind, Geo, Gravity};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// What a URL asks for
// ---------------------------------------------------------------------------

/// An output format: each made by a verified encoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    Png,
    Jpeg,
    /// Lossless WebP (VP8L).
    Webp,
}

/// A resampling filter: imgproxy's `resizing_algorithm` values, plus the
/// area average this crate had first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Filter {
    /// `lanczos3`, imgproxy's default.
    Lanczos3,
    Lanczos2,
    /// `cubic`: Catmull-Rom, as libvips's `VIPS_KERNEL_CUBIC`.
    Cubic,
    /// `linear`: a triangle.
    Linear,
    /// `nearest`: one source pixel for each output pixel, as libvips.
    Nearest,
    /// `area` (not imgproxy's): the exact area average of `spec::resize`.
    Area,
}

/// What to do to the image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Options {
    pub mode: Mode,
    pub w: u32,
    pub h: u32,
    pub enlarge: bool,
    pub background: Option<[u8; 3]>,
    /// The output format; PNG when the URL names none.
    pub format: Format,
    /// JPEG and lossy WebP quality, 1 to 100 (0: the default, 80).
    pub quality: u32,
    /// The resampling filter (`resizing_algorithm`).
    pub filter: Filter,
    /// `gravity`.
    pub gravity: Gravity,
    /// `crop`: width and height (`F1` units), and its gravity.
    pub crop_w: u32,
    pub crop_h: u32,
    pub crop_g: Option<Gravity>,
    /// `extend` and its gravity.
    pub extend: bool,
    pub extend_g: Option<Gravity>,
    /// `padding`: top, right, bottom, left.
    pub pad: [u32; 4],
    /// `dpr`, `F1` units.
    pub dpr: u32,
    /// `rotate`, in clockwise quarter turns (0 to 3).
    pub rotate: u32,
    /// `flip`: left-right, top-bottom.
    pub flip_h: bool,
    pub flip_v: bool,
    /// `auto_rotate`: turn upright as the EXIF orientation says (on by
    /// default, as imgproxy's `IMGPROXY_AUTO_ROTATE`).
    pub auto_rotate: bool,
    /// `expires`: a Unix time after which the URL is refused; 0 is never.
    pub expires: u64,
    /// `return_attachment`: `Content-Disposition: attachment`.
    pub attachment: bool,
    /// `raw`: send the source as it is, without processing or checks.
    pub raw: bool,
    /// `skip_processing`: the source formats sent as they are, one bit
    /// each (`kind_bit`).
    pub skip: u32,
    /// `blur` and `sharpen`: the Gaussian's sigma, `F1` units (0: none).
    pub blur: u32,
    pub sharpen: u32,
    /// `pixelate`: the block size in pixels (0 or 1: none).
    pub pixelate: u32,
    /// `watermark`: opacity (`F1` units; 0 is none), where (`wm_g`, or
    /// tiled with `wm_g`'s offsets as the spacing), and the size as a
    /// fraction of the result's width (`F1` units; 0 keeps its size).
    pub wm_op: u32,
    pub wm_g: Gravity,
    pub wm_tile: bool,
    pub wm_scale: u32,
}

/// The geometry options.
pub open spec fn geo(o: Options) -> Geo {
    Geo {
        mode: o.mode,
        w: o.w,
        h: o.h,
        enlarge: o.enlarge,
        gravity: o.gravity,
        crop_w: o.crop_w,
        crop_h: o.crop_h,
        crop_g: o.crop_g,
        extend: o.extend,
        extend_g: o.extend_g,
        pad: o.pad,
        dpr: o.dpr,
    }
}

/// The options before any are applied.
pub open spec fn defaults() -> Options {
    Options {
        mode: Mode::Fit,
        w: 0,
        h: 0,
        enlarge: false,
        background: None,
        format: Format::Png,
        quality: 0,
        filter: Filter::Lanczos3,
        gravity: Gravity { kind: GKind::Ce, x: 0, y: 0 },
        crop_w: 0,
        crop_h: 0,
        crop_g: None,
        extend: false,
        extend_g: None,
        pad: [0u32, 0u32, 0u32, 0u32],
        dpr: 10000,
        rotate: 0,
        flip_h: false,
        flip_v: false,
        auto_rotate: true,
        expires: 0,
        attachment: false,
        raw: false,
        skip: 0,
        blur: 0,
        sharpen: 0,
        pixelate: 0,
        wm_op: 0,
        wm_g: Gravity { kind: GKind::Ce, x: 0, y: 0 },
        wm_tile: false,
        wm_scale: 0,
    }
}

/// Where the image comes from.
pub enum Src {
    /// `local:///path`: the path after `local://`.
    Local(Seq<u8>),
    /// An `http://` or `https://` URL.
    Http(Seq<u8>),
    /// The request body.
    Upload,
}

/// A parsed path: the signature is bytes 1 to `sig_end` of the path, and
/// the signed part is from `sig_end` on.
pub struct Url {
    pub sig_end: int,
    pub opts: Options,
    pub src: Src,
    /// `filename`: the last one given, decoded.
    pub filename: Option<Seq<u8>>,
}

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// The first index from `i` on that holds `c`, or the length.
pub open spec fn find(s: Seq<u8>, c: u8, i: int) -> int
    decreases s.len() - i,
{
    if i >= s.len() {
        s.len() as int
    } else if s[i] == c {
        i
    } else {
        find(s, c, i + 1)
    }
}

/// The last index that holds `c`, or -1.
pub open spec fn rfind(s: Seq<u8>, c: u8) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        -1
    } else if s.last() == c {
        s.len() - 1
    } else {
        rfind(s.drop_last(), c)
    }
}

/// `find` is at least where it starts.
pub proof fn lemma_find_from(s: Seq<u8>, c: u8, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= find(s, c, i),
    decreases s.len() - i,
{
    if i < s.len() && s[i] != c {
        lemma_find_from(s, c, i + 1);
    }
}

#[via_fn]
proof fn split_decreases(s: Seq<u8>, c: u8) {
    lemma_find_from(s, c, 0);
}

/// `s` split at every `c` (`[]` splits to `[[]]`).
pub open spec fn split(s: Seq<u8>, c: u8) -> Seq<Seq<u8>>
    decreases s.len(),
    via split_decreases
{
    let i = find(s, c, 0);
    if i >= s.len() {
        seq![s]
    } else {
        seq![s.take(i)] + split(s.skip(i + 1), c)
    }
}

/// The pieces joined with `c` between them.
pub open spec fn join(p: Seq<Seq<u8>>, c: u8) -> Seq<u8>
    decreases p.len(),
{
    if p.len() == 0 {
        Seq::empty()
    } else if p.len() == 1 {
        p[0]
    } else {
        join(p.drop_last(), c) + seq![c] + p.last()
    }
}

/// The pieces end to end.
pub open spec fn concat(p: Seq<Seq<u8>>) -> Seq<u8>
    decreases p.len(),
{
    if p.len() == 0 {
        Seq::empty()
    } else {
        concat(p.drop_last()) + p.last()
    }
}

pub open spec fn starts(s: Seq<u8>, p: Seq<u8>) -> bool {
    p.len() <= s.len() && s.take(p.len() as int) == p
}

// ---------------------------------------------------------------------------
// Option arguments
// ---------------------------------------------------------------------------

pub open spec fn is_digit(c: u8) -> bool {
    b'0' <= c <= b'9'
}

/// The decimal value of a string of digits.
pub open spec fn dec(s: Seq<u8>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        10 * dec(s.drop_last()) + (s.last() - b'0')
    }
}

/// A size: digits up to 65535; empty is 0.
pub open spec fn num(s: Seq<u8>) -> Option<u32> {
    if (forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i])) && dec(s) <= 65535 {
        Some(dec(s) as u32)
    } else {
        None
    }
}

/// `1`, `t`, `true`; `0`, `f`, `false` or empty.
pub open spec fn boolean(s: Seq<u8>) -> Option<bool> {
    if s == seq![b'1'] || s == seq![b't'] || s == seq![b't', b'r', b'u', b'e'] {
        Some(true)
    } else if s.len() == 0 || s == seq![b'0'] || s == seq![b'f'] || s == seq![b'f', b'a', b'l', b's', b'e'] {
        Some(false)
    } else {
        None
    }
}

/// `fit`, `fill` or `force`.
pub open spec fn mode(s: Seq<u8>) -> Option<Mode> {
    if s == seq![b'f', b'i', b't'] {
        Some(Mode::Fit)
    } else if s == seq![b'f', b'i', b'l', b'l'] {
        Some(Mode::Fill)
    } else if s == seq![b'f', b'o', b'r', b'c', b'e'] {
        Some(Mode::Force)
    } else {
        None
    }
}

/// A hexadecimal digit's value (either case), or -1.
pub open spec fn hexv(c: u8) -> int {
    if b'0' <= c <= b'9' {
        c - b'0'
    } else if b'a' <= c <= b'f' {
        c - b'a' + 10
    } else if b'A' <= c <= b'F' {
        c - b'A' + 10
    } else {
        -1
    }
}

/// The byte two hex digits at `i` give.
pub open spec fn hexbyte(s: Seq<u8>, i: int) -> u8 {
    (16 * hexv(s[i]) + hexv(s[i + 1])) as u8
}

/// A colour component: 1 to 3 digits, at most 255.
pub open spec fn comp(s: Seq<u8>) -> Option<u8> {
    match num(s) {
        Some(v) if s.len() > 0 && v <= 255 => Some(v as u8),
        _ => None,
    }
}

/// `background`'s arguments: none (or one empty one) for no background,
/// `RRGGBB` in hex, or `R:G:B` in decimal.
pub open spec fn background(a: Seq<Seq<u8>>) -> Option<Option<[u8; 3]>> {
    if a.len() == 0 || (a.len() == 1 && a[0].len() == 0) {
        Some(None)
    } else if a.len() == 1 && a[0].len() == 6 {
        if forall|i: int| 0 <= i < 6 ==> hexv(#[trigger] a[0][i]) >= 0 {
            Some(Some([hexbyte(a[0], 0), hexbyte(a[0], 2), hexbyte(a[0], 4)]))
        } else {
            None
        }
    } else if a.len() == 3 {
        match (comp(a[0]), comp(a[1]), comp(a[2])) {
            (Some(r), Some(g), Some(b)) => Some(Some([r, g, b])),
            _ => None,
        }
    } else {
        None
    }
}

/// The format an extension names: empty keeps `f`; `png` and `best` are
/// PNG; `jpg` and `jpeg` are JPEG; `webp` is WebP.
pub open spec fn format(f: Format, s: Seq<u8>) -> Option<Format> {
    if s.len() == 0 {
        Some(f)
    } else if s == seq![b'p', b'n', b'g'] || s == seq![b'b', b'e', b's', b't'] {
        Some(Format::Png)
    } else if s == seq![b'j', b'p', b'g'] || s == seq![b'j', b'p', b'e', b'g'] {
        Some(Format::Jpeg)
    } else if s == seq![b'w', b'e', b'b', b'p'] {
        Some(Format::Webp)
    } else {
        None
    }
}

/// `resizing_algorithm`'s names.
pub open spec fn filter(s: Seq<u8>) -> Option<Filter> {
    if s == seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'3'] {
        Some(Filter::Lanczos3)
    } else if s == seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'2'] {
        Some(Filter::Lanczos2)
    } else if s == seq![b'c', b'u', b'b', b'i', b'c'] {
        Some(Filter::Cubic)
    } else if s == seq![b'l', b'i', b'n', b'e', b'a', b'r'] {
        Some(Filter::Linear)
    } else if s == seq![b'n', b'e', b'a', b'r', b'e', b's', b't'] {
        Some(Filter::Nearest)
    } else if s == seq![b'a', b'r', b'e', b'a'] {
        Some(Filter::Area)
    } else {
        None
    }
}


/// `10^n` for `n` from 0 to 4.
pub open spec fn pow10(n: int) -> int {
    if n <= 0 {
        1
    } else if n == 1 {
        10
    } else if n == 2 {
        100
    } else if n == 3 {
        1000
    } else {
        10000
    }
}

pub open spec fn all_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i])
}

/// A decimal with up to 4 places, at most 65535.9999, in `F1` units
/// (`2`, `1.5`, `.25`); `None` for anything else, the empty string too.
pub open spec fn fixed4(s: Seq<u8>) -> Option<int> {
    let d = find(s, b'.', 0);
    let ip = s.take(d);
    let fp = if d < s.len() { s.skip(d + 1) } else { Seq::empty() };
    if all_digits(ip) && all_digits(fp) && fp.len() <= 4 && dec(ip) <= 65535 && s.len() > 0 && (ip.len() > 0
        || fp.len() > 0) {
        Some(dec(ip) * F1 + dec(fp) * pow10(4 - fp.len()))
    } else {
        None
    }
}

/// `fixed4`, with the empty string 0.
pub open spec fn fixed4z(s: Seq<u8>) -> Option<int> {
    if s.len() == 0 {
        Some(0)
    } else {
        fixed4(s)
    }
}

/// An offset: a size, or `-` and a size.
pub open spec fn sint(s: Seq<u8>) -> Option<int> {
    if s.len() > 0 && s[0] == b'-' {
        match num(s.skip(1)) {
            Some(v) if s.len() > 1 => Some(-(v as int)),
            _ => None,
        }
    } else {
        match num(s) {
            Some(v) => Some(v as int),
            None => None,
        }
    }
}

/// The gravity types (empty is the centre).
pub open spec fn gkind(s: Seq<u8>) -> Option<GKind> {
    if s.len() == 0 || s == seq![b'c', b'e'] {
        Some(GKind::Ce)
    } else if s == seq![b'n', b'o'] {
        Some(GKind::No)
    } else if s == seq![b's', b'o'] {
        Some(GKind::So)
    } else if s == seq![b'e', b'a'] {
        Some(GKind::Ea)
    } else if s == seq![b'w', b'e'] {
        Some(GKind::We)
    } else if s == seq![b'n', b'o', b'e', b'a'] {
        Some(GKind::NoEa)
    } else if s == seq![b'n', b'o', b'w', b'e'] {
        Some(GKind::NoWe)
    } else if s == seq![b's', b'o', b'e', b'a'] {
        Some(GKind::SoEa)
    } else if s == seq![b's', b'o', b'w', b'e'] {
        Some(GKind::SoWe)
    } else if s == seq![b'f', b'p'] {
        Some(GKind::Fp)
    } else if s == seq![b's', b'm'] {
        Some(GKind::Sm)
    } else {
        None
    }
}

/// A gravity from arguments `i` on: the type, then `x` and `y` (pixel
/// offsets, or for `fp` fractions from 0 to 1).
pub open spec fn gravity(a: Seq<Seq<u8>>, i: int) -> Option<Gravity> {
    match gkind(arg(a, i)) {
        None => None,
        Some(GKind::Fp) => match (fixed4(arg(a, i + 1)), fixed4(arg(a, i + 2))) {
            (Some(x), Some(y)) if x <= F1 && y <= F1 => Some(Gravity { kind: GKind::Fp, x: x as i32, y: y as i32 }),
            _ => None,
        },
        Some(k) => match (sint(arg(a, i + 1)), sint(arg(a, i + 2))) {
            (Some(x), Some(y)) => Some(Gravity { kind: k, x: x as i32, y: y as i32 }),
            _ => None,
        },
    }
}

/// A gravity from arguments `i` on, or `None` inside if argument `i` is
/// empty (the default).
pub open spec fn ogravity(a: Seq<Seq<u8>>, i: int) -> Option<Option<Gravity>> {
    if arg(a, i).len() == 0 {
        Some(None)
    } else {
        match gravity(a, i) {
            Some(g) => Some(Some(g)),
            None => None,
        }
    }
}

/// `padding`'s CSS-style lengths (at most four): top, then right (default top), bottom
/// (default top), left (default right).
pub open spec fn padding(a: Seq<Seq<u8>>) -> Option<[u32; 4]> {
    let t = num(arg(a, 0));
    let r = if arg(a, 1).len() == 0 { t } else { num(arg(a, 1)) };
    let b = if arg(a, 2).len() == 0 { t } else { num(arg(a, 2)) };
    let l = if arg(a, 3).len() == 0 { r } else { num(arg(a, 3)) };
    match (t, r, b, l) {
        (Some(t), Some(r), Some(b), Some(l)) if a.len() <= 4 => Some([t, r, b, l]),
        _ => None,
    }
}

/// `resize` and `size` end with `extend`'s arguments, from argument `i`
/// on; when they are not given, `extend` is left as it was.
pub open spec fn ext(o: Options, a: Seq<Seq<u8>>, i: int) -> Option<Options> {
    if arg(a, i).len() == 0 {
        Some(o)
    } else {
        match (boolean(arg(a, i)), ogravity(a, i + 1)) {
            (Some(e), Some(g)) => Some(Options { extend: e, extend_g: g, ..o }),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------------

/// Argument `i`, or empty past the last.
pub open spec fn arg(a: Seq<Seq<u8>>, i: int) -> Seq<u8> {
    if i < a.len() {
        a[i]
    } else {
        Seq::empty()
    }
}

/// Whether `n` is the long or the short name.
pub open spec fn named(n: Seq<u8>, long: Seq<u8>, short: Seq<u8>) -> bool {
    n == long || n == short
}

/// `o` with the option `seg` applied, or `None` if `seg` is not one this
/// crate does.
pub open spec fn apply(o: Options, seg: Seq<u8>) -> Option<Options> {
    let p = split(seg, b':');
    let n = p[0];
    let a = p.skip(1);
    if named(n, seq![b'r', b'e', b's', b'i', b'z', b'e'], seq![b'r', b's']) {
        let m = if arg(a, 0).len() == 0 { Some(o.mode) } else { mode(arg(a, 0)) };
        match (m, num(arg(a, 1)), num(arg(a, 2)), boolean(arg(a, 3))) {
            (Some(m), Some(w), Some(h), Some(e)) => ext(Options { mode: m, w, h, enlarge: e, ..o }, a, 4),
            _ => None,
        }
    } else if named(n, seq![b's', b'i', b'z', b'e'], seq![b's']) {
        match (num(arg(a, 0)), num(arg(a, 1)), boolean(arg(a, 2))) {
            (Some(w), Some(h), Some(e)) => ext(Options { w, h, enlarge: e, ..o }, a, 3),
            _ => None,
        }
    } else if named(
        n,
        seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b't', b'y', b'p', b'e'],
        seq![b'r', b't'],
    ) {
        match mode(arg(a, 0)) {
            Some(m) => Some(Options { mode: m, ..o }),
            None => None,
        }
    } else if named(n, seq![b'w', b'i', b'd', b't', b'h'], seq![b'w']) {
        match num(arg(a, 0)) {
            Some(w) => Some(Options { w, ..o }),
            None => None,
        }
    } else if named(n, seq![b'h', b'e', b'i', b'g', b'h', b't'], seq![b'h']) {
        match num(arg(a, 0)) {
            Some(h) => Some(Options { h, ..o }),
            None => None,
        }
    } else if named(n, seq![b'e', b'n', b'l', b'a', b'r', b'g', b'e'], seq![b'e', b'l']) {
        match boolean(arg(a, 0)) {
            Some(e) => Some(Options { enlarge: e, ..o }),
            None => None,
        }
    } else if named(
        n,
        seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b'a', b'l', b'g', b'o', b'r', b'i', b't', b'h', b'm'],
        seq![b'r', b'a'],
    ) {
        match filter(arg(a, 0)) {
            Some(f) => Some(Options { filter: f, ..o }),
            None => None,
        }
    } else if named(n, seq![b'b', b'a', b'c', b'k', b'g', b'r', b'o', b'u', b'n', b'd'], seq![b'b', b'g']) {
        match background(a) {
            Some(b) => Some(Options { background: b, ..o }),
            None => None,
        }
    } else if named(n, seq![b'q', b'u', b'a', b'l', b'i', b't', b'y'], seq![b'q']) {
        match num(arg(a, 0)) {
            Some(q) if q <= 100 => Some(Options { quality: q, ..o }),
            _ => None,
        }
    } else if named(
        n,
        seq![b's', b't', b'r', b'i', b'p', b'_', b'm', b'e', b't', b'a', b'd', b'a', b't', b'a'],
        seq![b's', b'm'],
    ) || named(n, seq![b'c', b'a', b'c', b'h', b'e', b'b', b'u', b's', b't', b'e', b'r'], seq![b'c', b'b']) {
        // Accepted and ignored: the encoders write no metadata.
        Some(o)
    } else if named(n, seq![b'f', b'o', b'r', b'm', b'a', b't'], seq![b'f']) || n == seq![b'e', b'x', b't'] {
        match format(o.format, arg(a, 0)) {
            Some(f) => Some(Options { format: f, ..o }),
            None => None,
        }
    } else if named(n, seq![b'g', b'r', b'a', b'v', b'i', b't', b'y'], seq![b'g']) {
        match gravity(a, 0) {
            Some(g) => Some(Options { gravity: g, ..o }),
            None => None,
        }
    } else if named(n, seq![b'c', b'r', b'o', b'p'], seq![b'c']) {
        match (fixed4z(arg(a, 0)), fixed4z(arg(a, 1)), ogravity(a, 2)) {
            (Some(w), Some(h), Some(g)) => Some(Options { crop_w: w as u32, crop_h: h as u32, crop_g: g, ..o }),
            _ => None,
        }
    } else if named(n, seq![b'e', b'x', b't', b'e', b'n', b'd'], seq![b'e', b'x']) {
        match (boolean(arg(a, 0)), ogravity(a, 1)) {
            (Some(e), Some(g)) => Some(Options { extend: e, extend_g: g, ..o }),
            _ => None,
        }
    } else if named(n, seq![b'p', b'a', b'd', b'd', b'i', b'n', b'g'], seq![b'p', b'd']) {
        match padding(a) {
            Some(p) => Some(Options { pad: p, ..o }),
            None => None,
        }
    } else if n == seq![b'd', b'p', b'r'] {
        match fixed4(arg(a, 0)) {
            Some(d) if 1 <= d <= 8 * F1 => Some(Options { dpr: d as u32, ..o }),
            _ => None,
        }
    } else if named(n, seq![b'r', b'o', b't', b'a', b't', b'e'], seq![b'r', b'o', b't']) {
        match num(arg(a, 0)) {
            Some(r) if r % 90 == 0 => Some(Options { rotate: ((r / 90) % 4) as u32, ..o }),
            _ => None,
        }
    } else if named(n, seq![b'f', b'l', b'i', b'p'], seq![b'f', b'l']) {
        match (boolean(arg(a, 0)), boolean(arg(a, 1))) {
            (Some(h), Some(v)) => Some(Options { flip_h: h, flip_v: v, ..o }),
            _ => None,
        }
    } else {
        apply2(o, n, a)
    }
}

/// The options about the response, and `auto_rotate`.
pub open spec fn apply2(o: Options, n: Seq<u8>, a: Seq<Seq<u8>>) -> Option<Options> {
    if named(n, seq![b'a', b'u', b't', b'o', b'_', b'r', b'o', b't', b'a', b't', b'e'], seq![b'a', b'r']) {
        match boolean(arg(a, 0)) {
            Some(v) => Some(Options { auto_rotate: v, ..o }),
            None => None,
        }
    } else if named(n, seq![b'e', b'x', b'p', b'i', b'r', b'e', b's'], seq![b'e', b'x', b'p']) {
        match num64(arg(a, 0)) {
            Some(t) => Some(Options { expires: t, ..o }),
            None => None,
        }
    } else if named(
        n,
        seq![b'r', b'e', b't', b'u', b'r', b'n', b'_', b'a', b't', b't', b'a', b'c', b'h', b'm', b'e', b'n', b't'],
        seq![b'a', b't', b't'],
    ) {
        match boolean(arg(a, 0)) {
            Some(v) => Some(Options { attachment: v, ..o }),
            None => None,
        }
    } else if n == seq![b'r', b'a', b'w'] {
        match boolean(arg(a, 0)) {
            Some(v) => Some(Options { raw: v, ..o }),
            None => None,
        }
    } else if named(
        n,
        seq![b's', b'k', b'i', b'p', b'_', b'p', b'r', b'o', b'c', b'e', b's', b's', b'i', b'n', b'g'],
        seq![b's', b'k', b'p'],
    ) {
        match kinds(a, a.len() as int) {
            Some(m) => Some(Options { skip: m, ..o }),
            None => None,
        }
    } else if named(n, seq![b'w', b'a', b't', b'e', b'r', b'm', b'a', b'r', b'k'], seq![b'w', b'm']) {
        match watermark_opt(a) {
            Some((op, g, t, sc)) => Some(Options { wm_op: op, wm_g: g, wm_tile: t, wm_scale: sc, ..o }),
            None => None,
        }
    } else if named(n, seq![b'b', b'l', b'u', b'r'], seq![b'b', b'l']) {
        match fixed4z(arg(a, 0)) {
            Some(v) => Some(Options { blur: v as u32, ..o }),
            None => None,
        }
    } else if named(n, seq![b's', b'h', b'a', b'r', b'p', b'e', b'n'], seq![b's', b'h']) {
        match fixed4z(arg(a, 0)) {
            Some(v) => Some(Options { sharpen: v as u32, ..o }),
            None => None,
        }
    } else if named(n, seq![b'p', b'i', b'x', b'e', b'l', b'a', b't', b'e'], seq![b'p', b'i', b'x']) {
        match num(arg(a, 0)) {
            Some(v) => Some(Options { pixelate: v, ..o }),
            None => None,
        }
    } else if named(n, seq![b'f', b'i', b'l', b'e', b'n', b'a', b'm', b'e'], seq![b'f', b'n']) {
        // Checked here; the name itself is `Url::filename`.
        match fname_arg(a) {
            Some(_) => Some(o),
            None => None,
        }
    } else {
        None
    }
}

/// `watermark`'s arguments: opacity (0 to 1), position (a gravity, or
/// `re` to tile), x and y offsets (the spacing when tiled), scale.
pub open spec fn watermark_opt(a: Seq<Seq<u8>>) -> Option<(u32, Gravity, bool, u32)> {
    let tile = arg(a, 1) == seq![b'r', b'e'];
    let g = if tile {
        match (sint(arg(a, 2)), sint(arg(a, 3))) {
            (Some(x), Some(y)) => Some(Gravity { kind: GKind::Ce, x: x as i32, y: y as i32 }),
            _ => None,
        }
    } else {
        gravity(a, 1)
    };
    match (fixed4(arg(a, 0)), g, fixed4z(arg(a, 4))) {
        (Some(op), Some(g), Some(sc)) if op <= F1 => Some((op as u32, g, tile, sc as u32)),
        _ => None,
    }
}

/// A Unix time: digits (at least one) up to `i64::MAX`.
pub open spec fn num64(s: Seq<u8>) -> Option<u64> {
    if s.len() > 0 && all_digits(s) && dec(s) <= 0x7fff_ffff_ffff_ffff {
        Some(dec(s) as u64)
    } else {
        None
    }
}

/// The bit `skip_processing` keeps for a format.
pub open spec fn kind_bit(k: Kind) -> u32 {
    match k {
        Kind::Jpeg => 1,
        Kind::Png => 2,
        Kind::Webp => 4,
        Kind::Gif => 8,
    }
}

/// A format's name, as `skip_processing` takes it.
pub open spec fn kind_name(s: Seq<u8>) -> Option<Kind> {
    if s == seq![b'j', b'p', b'g'] || s == seq![b'j', b'p', b'e', b'g'] {
        Some(Kind::Jpeg)
    } else if s == seq![b'p', b'n', b'g'] {
        Some(Kind::Png)
    } else if s == seq![b'w', b'e', b'b', b'p'] {
        Some(Kind::Webp)
    } else if s == seq![b'g', b'i', b'f'] {
        Some(Kind::Gif)
    } else {
        None
    }
}

/// The bits of the first `n` of `a`, each a format's name.
pub open spec fn kinds(a: Seq<Seq<u8>>, n: int) -> Option<u32>
    decreases n,
{
    if n <= 0 {
        Some(0)
    } else {
        match (kinds(a, n - 1), kind_name(a[n - 1])) {
            (Some(m), Some(k)) => Some(m | kind_bit(k)),
            _ => None,
        }
    }
}

/// base64url, unpadded (one trailing `=` ignored), or else padded, as for
/// sources.
pub open spec fn unb64(body: Seq<u8>) -> Option<Seq<u8>> {
    let unpadded = if body.len() > 0 && body.last() == b'=' { body.drop_last() } else { body };
    match verilith_text::base64::spec::decode(b64(true, false), unpadded) {
        Some(u) => Some(u),
        None => verilith_text::base64::spec::decode(b64(true, true), body),
    }
}

/// `filename`'s name: base64url when the second argument is true, else
/// percent-decoded.
pub open spec fn fname_arg(a: Seq<Seq<u8>>) -> Option<Seq<u8>> {
    match boolean(arg(a, 1)) {
        Some(true) => unb64(arg(a, 0)),
        Some(false) => Some(verilith_text::percent::decode(arg(a, 0))),
        None => None,
    }
}

/// The name a segment gives, if it is a `filename` option.
pub open spec fn fname_of(seg: Seq<u8>) -> Option<Seq<u8>> {
    let p = split(seg, b':');
    if named(p[0], seq![b'f', b'i', b'l', b'e', b'n', b'a', b'm', b'e'], seq![b'f', b'n']) {
        fname_arg(p.skip(1))
    } else {
        None
    }
}

/// The name the last `filename` among the first `n` segments gives.
pub open spec fn last_fname(segs: Seq<Seq<u8>>, n: int) -> Option<Seq<u8>>
    decreases n,
{
    if n <= 0 || n > segs.len() {
        None
    } else {
        match fname_of(segs[n - 1]) {
            Some(f) => Some(f),
            None => last_fname(segs, n - 1),
        }
    }
}

/// Whether a segment is an option rather than the start of the source.
pub open spec fn is_option(seg: Seq<u8>) -> bool {
    find(seg, b':', 0) < seg.len() && !starts(seg, seq![b'h', b't', b't', b'p']) && !starts(
        seg,
        seq![b'l', b'o', b'c', b'a', b'l'],
    )
}

/// How many segments from the first are options.
pub open spec fn nopts(segs: Seq<Seq<u8>>, i: int) -> int
    decreases segs.len() - i,
{
    if i >= segs.len() || !is_option(segs[i]) {
        i
    } else {
        nopts(segs, i + 1)
    }
}

/// The defaults with the first `n` segments applied as options.
pub open spec fn apply_all(segs: Seq<Seq<u8>>, n: int) -> Option<Options>
    decreases n,
{
    if n <= 0 {
        Some(defaults())
    } else {
        match apply_all(segs, n - 1) {
            Some(o) => apply(o, segs[n - 1]),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Sources
// ---------------------------------------------------------------------------

/// A decoded source URL: `local://` or `http(s)://`.
pub open spec fn source(u: Seq<u8>) -> Option<Src> {
    if starts(u, seq![b'l', b'o', b'c', b'a', b'l', b':', b'/', b'/']) {
        Some(Src::Local(u.skip(8)))
    } else if starts(u, seq![b'h', b't', b't', b'p', b':', b'/', b'/']) || starts(
        u,
        seq![b'h', b't', b't', b'p', b's', b':', b'/', b'/'],
    ) {
        Some(Src::Http(u))
    } else {
        None
    }
}

/// `plain/` sources: the segments after it joined back with `/`, the last
/// `@` starting the extension, percent-decoded.
pub open spec fn plain(o: Options, rest: Seq<Seq<u8>>) -> Option<(Options, Src)> {
    let u = join(rest, b'/');
    let at = rfind(u, b'@');
    let f = if at >= 0 { format(o.format, u.skip(at + 1)) } else { Some(o.format) };
    let body = if at >= 0 { u.take(at) } else { u };
    match (f, source(verilith_text::percent::decode(body))) {
        (Some(f), Some(s)) => Some((Options { format: f, ..o }, s)),
        _ => None,
    }
}

/// base64url's two forms (unpadded and padded).
pub open spec fn b64(url: bool, pad: bool) -> verilith_text::base64::spec::Config {
    verilith_text::base64::spec::Config { url, pad }
}

/// Base64url sources: the segments concatenated, the first `.` starting
/// the extension; unpadded base64url (one trailing `=` ignored), or else
/// padded.
pub open spec fn encoded(o: Options, segs: Seq<Seq<u8>>) -> Option<(Options, Src)> {
    let e = concat(segs);
    let dot = find(e, b'.', 0);
    let f = if dot < e.len() { format(o.format, e.skip(dot + 1)) } else { Some(o.format) };
    let body = e.take(dot);
    let unpadded = if body.len() > 0 && body.last() == b'=' { body.drop_last() } else { body };
    let u = match verilith_text::base64::spec::decode(b64(true, false), unpadded) {
        Some(u) => Some(u),
        None => verilith_text::base64::spec::decode(b64(true, true), body),
    };
    match (f, u) {
        (Some(f), Some(u)) => match source(u) {
            Some(s) => Some((Options { format: f, ..o }, s)),
            None => None,
        },
        _ => None,
    }
}

pub open spec fn upload_lit() -> Seq<u8> {
    seq![b'u', b'p', b'l', b'o', b'a', b'd']
}

/// The request a path makes, or `None` if it is not one this crate
/// answers.
pub open spec fn parse(path: Seq<u8>) -> Option<Url> {
    if path.len() == 0 || path[0] != b'/' {
        None
    } else {
        let rest = path.skip(1);
        let k = find(rest, b'/', 0);
        if k >= rest.len() {
            None
        } else {
            let segs = split(rest.skip(k + 1), b'/');
            let n = nopts(segs, 0);
            match apply_all(segs, n) {
                None => None,
                Some(o) => if n >= segs.len() {
                    None
                } else {
                    let first = segs[n];
                    let r = if first == seq![b'p', b'l', b'a', b'i', b'n'] {
                        plain(o, segs.skip(n + 1))
                    } else if starts(first, upload_lit()) && n + 1 == segs.len() {
                        if first == upload_lit() {
                            Some((o, Src::Upload))
                        } else if first[6] == b'@' {
                            match format(o.format, first.skip(7)) {
                                Some(f) => Some((Options { format: f, ..o }, Src::Upload)),
                                None => None,
                            }
                        } else {
                            None
                        }
                    } else {
                        encoded(o, segs.skip(n))
                    };
                    match r {
                        Some((o, s)) => Some(Url { sig_end: k + 1, opts: o, src: s, filename: last_fname(segs, n) }),
                        None => None,
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Choosing a decoder
// ---------------------------------------------------------------------------

/// The formats this crate decodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Jpeg,
    Png,
    Webp,
    Gif,
}

/// The format a file's first bytes name: JPEG's SOI and a marker, PNG's
/// signature, RIFF with a WEBP form type, or GIF87a/GIF89a.
pub open spec fn kind(d: Seq<u8>) -> Option<Kind> {
    if starts(d, seq![0xffu8, 0xd8, 0xff]) {
        Some(Kind::Jpeg)
    } else if starts(d, seq![0x89u8, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a]) {
        Some(Kind::Png)
    } else if d.len() >= 12 && starts(d, seq![b'R', b'I', b'F', b'F']) && d.subrange(8, 12) == seq![
        b'W',
        b'E',
        b'B',
        b'P',
    ] {
        Some(Kind::Webp)
    } else if starts(d, seq![b'G', b'I', b'F', b'8', b'7', b'a']) || starts(d, seq![b'G', b'I', b'F', b'8', b'9', b'a']) {
        Some(Kind::Gif)
    } else {
        None
    }
}

/// imgproxy's shrink-on-load factor for a JPEG (`calcJpegShink`): the
/// largest of 8, 4 and 2 that the scale from `sw` by `sh` down to `rw` by
/// `rh` allows (in whole times, per side), or 1.
pub open spec fn jpeg_shrink(sw: int, sh: int, rw: int, rh: int) -> int {
    let a = sw / (if rw < 1 { 1 } else { rw });
    let b = sh / (if rh < 1 { 1 } else { rh });
    let s = if a < b { a } else { b };
    if s >= 8 {
        8
    } else if s >= 4 {
        4
    } else if s >= 2 {
        2
    } else {
        1
    }
}

} // verus!
