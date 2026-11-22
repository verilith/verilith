//! Lossy WebP: locating the VP8 frame and the optional ALPH chunk in the
//! container (libwebp 1.6.0's `ParseHeadersInternal` with all data
//! present), decoding the alpha plane (`src/dec/alpha_dec.c`,
//! `src/dsp/filters.c`), and putting it together with the frame.
use crate::bitreader::*;
use crate::container::*;
use crate::container::{is_tag, le24, le32};
use crate::spec::*;
use crate::decode::*;
use crate::image::*;
use crate::pixels::Error;
use crate::transform::*;
use crate::undo::*;
use crate::vp8frame::*;
use crate::vp8spec::*;
use crate::vp8yuv::*;
use verilith_core::prims::*;
use vstd::prelude::*;

verus! {

/// Where a lossy file's parts are.
pub struct Layout {
    /// The VP8 frame tag.
    pub off: usize,
    /// The ALPH chunk's payload (offset and size), if there is one.
    pub alpha: Option<(usize, usize)>,
    /// The frame size, and whether VP8X or ALPH says there is alpha.
    pub width: usize,
    pub height: usize,
    pub has_alpha: bool,
}

/// An exec ALPH payload as the specification writes it.
pub open spec fn aview(a: Option<(usize, usize)>) -> Option<(nat, nat)> {
    match a {
        Some((o, s)) => Some((o as nat, s as nat)),
        None => None,
    }
}

/// `ParseHeadersInternal` (with `have_all_data`) for a lossy file: the
/// layout, or `None` where libwebp rejects the headers.
///
/// A layout is the container specification's: the headers are those of a
/// lossy file (`spec::parse_headers`), the frame is where `lossy_off` puts
/// it, and the alpha payload is the last ALPH chunk before it. The one
/// exception is a bare bitstream that also passes the VP8L signature
/// check, which `parse_headers` sends to the lossless decoder; the callers
/// reach this function only after `parse_headers` said lossy.
pub fn lossy_layout(d: &[u8]) -> (r: Option<Layout>)
    ensures
        r matches Some(l) ==> {
            &&& l.off + 10 <= d@.len()
            &&& (l.alpha matches Some((o, s)) ==> o + s <= d@.len())
            &&& l.off == lossy_off(d@)
            &&& aview(l.alpha) == lossy_alpha(d@)
            &&& l.width == frame_width(d@, l.off as int)
            &&& l.height == frame_height(d@, l.off as int)
            &&& parse_headers(d@) == Parsed::Lossy || vp8l_signature(d@, l.off as nat)
        },
{
    hide(parse_headers);
    hide(ph_tail);
    hide(skip_chunks);
    hide(find_alph);
    proof {
        assert(d@.len() == d.len());
        lemma_ph_split(d@);
        assert(alph_tag() == seq![0x41u8, 0x4c, 0x50, 0x48]);
        assert(vp8_tag() == seq![0x56u8, 0x50, 0x38, 0x20]);
        assert(vp8l_tag() == seq![0x56u8, 0x50, 0x38, 0x4c]);
    }
    let n = d.len();
    if n < 12 {
        return None;
    }
    let riff = is_tag(d, 0, 0x52, 0x49, 0x46, 0x46);
    let mut riff_size: u64 = 0;
    let mut p: usize = 0;
    if riff {
        if !is_tag(d, 8, 0x57, 0x45, 0x42, 0x50) {
            return None;
        }
        let size = le32(d, 4);
        if size < 12 || size > 0xffff_fff6 || size > (n - 8) as u64 {
            return None;
        }
        riff_size = size;
        p = 12;
    }
    if n - p < 8 {
        return None;
    }
    let vp8x = is_tag(d, p, 0x56, 0x50, 0x38, 0x58);
    let mut cw: u64 = 0;
    let mut ch: u64 = 0;
    let mut has_alpha = false;
    if vp8x {
        if le32(d, p + 4) != 10 || n - p < 18 {
            return None;
        }
        let flags = le32(d, p + 8);
        cw = 1 + le24(d, p + 12);
        ch = 1 + le24(d, p + 15);
        proof {
            assert(cw * ch <= 0x100_0000 * 0x100_0000) by (nonlinear_arith)
                requires 1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000;
            assert(((flags >> 1u64) & 1 == 1) == ((flags / 2) % 2 == 1)) by (bit_vector);
        }
        if cw * ch >= 0x1_0000_0000 {
            return None;
        }
        if (flags >> 1u64) & 1 == 1 {
            // Animation.
            return None;
        }
        has_alpha = (flags >> 4u64) & 1 == 1;
        p = p + 18;
    }
    if !riff && vp8x {
        return None;
    }
    if n - p < 4 {
        return None;
    }
    proof {
        assert(riff == ph_riff(d@));
        assert(riff_size == ph_riff_size(d@));
        assert(vp8x == ph_vp8x(d@));
        assert(p == ph_p1(d@));
        assert(!ph_bad_riff(d@));
        assert(!ph_bad_vp8x(d@));
        assert(vp8x ==> cw == ph_cw(d@) && ch == ph_ch(d@));
    }
    let mut alpha: Option<(usize, usize)> = None;
    let skip = (riff && vp8x) || (!riff && !vp8x && is_tag(d, p, 0x41, 0x4c, 0x50, 0x48));
    let ghost p1 = p;
    proof {
        assert(skip == ph_skip(d@));
    }
    if skip {
        let ghost res = skip_chunks(d@, p as nat, riff_size as nat, 22);
        let ghost ares = find_alph(d@, p as nat, riff_size as nat, 22, None);
        let mut total: u64 = 22;
        loop
            invariant_except_break
                skip_chunks(d@, p as nat, riff_size as nat, total as nat) == res,
                find_alph(d@, p as nat, riff_size as nat, total as nat, aview(alpha)) == ares,
            invariant
                d@.len() <= usize::MAX,
                p <= n == d@.len(),
                total < 0x1_0000_0000,
                riff_size <= 0xffff_fff6,
                alpha matches Some((o, s)) ==> o + s <= n,
            ensures
                res == Some(p as nat),
                ares == aview(alpha),
            decreases n - p,
        {
            proof {
                reveal(skip_chunks);
                reveal(find_alph);
            }
            if n - p < 8 {
                return None;
            }
            let size = le32(d, p + 4);
            if size > 0xffff_fff6 {
                return None;
            }
            let disk = (8 + size + 1) / 2 * 2;
            let ghost total0 = total;
            total = (total + disk) % 0x1_0000_0000;
            if riff_size > 0 && total > riff_size {
                return None;
            }
            if is_tag(d, p, 0x56, 0x50, 0x38, 0x20) || is_tag(d, p, 0x56, 0x50, 0x38, 0x4c) {
                break;
            }
            if ((n - p) as u64) < disk {
                return None;
            }
            if is_tag(d, p, 0x41, 0x4c, 0x50, 0x48) {
                alpha = Some((p + 8, size as usize));
            }
            p = p + disk as usize;
        }
    }
    let ghost p2 = p;
    proof {
        assert(lossy_p2(d@) == Some(p2 as nat));
        assert(aview(alpha) == lossy_alpha(d@));
        assert(parse_headers(d@) == ph_tail(d@, p2 as nat, ph_riff_size(d@), ph_vp8x(d@), ph_cw(d@), ph_ch(d@)));
        reveal(ph_tail);
    }
    if n - p < 8 {
        return None;
    }
    let csize: u64;
    if is_tag(d, p, 0x56, 0x50, 0x38, 0x20) || is_tag(d, p, 0x56, 0x50, 0x38, 0x4c) {
        if is_tag(d, p, 0x56, 0x50, 0x38, 0x4c) {
            return None;
        }
        let size = le32(d, p + 4);
        if (riff_size >= 12 && size > riff_size - 12) || size > (n - p - 8) as u64 {
            return None;
        }
        csize = size;
        p = p + 8;
    } else {
        csize = (n - p) as u64;
    }
    if csize > 0xffff_fff6 {
        return None;
    }
    // `VP8GetInfo`.
    if n - p < 10 {
        return None;
    }
    let bits = le24(d, p);
    if d[p + 3] != 0x9d || d[p + 4] != 0x01 || d[p + 5] != 0x2a {
        return None;
    }
    if bits & 1 != 0 || (bits >> 1u64) & 7 > 3 || (bits >> 4u64) & 1 == 0 || (bits >> 5u64) >= csize {
        return None;
    }
    let w = (d[p + 7] as usize % 64) * 256 + d[p + 6] as usize;
    let h = (d[p + 9] as usize % 64) * 256 + d[p + 8] as usize;
    if w == 0 || h == 0 {
        return None;
    }
    if vp8x && (cw != w as u64 || ch != h as u64) {
        return None;
    }
    Some(Layout { off: p, alpha, width: w, height: h, has_alpha: has_alpha || alpha.is_some() })
}

/// `alph_unf` at value `i` of row `y`, unfolded.
proof fn lemma_unf_step(raw: Seq<u8>, w: int, filter: int, y: int, i: int)
    requires
        0 <= i < w,
        0 <= y,
    ensures
        0 <= y * w + i,
        0 <= alph_unf(raw, w, filter, y * w + i) < 256,
        alph_unf(raw, w, filter, y * w + i) == (raw[y * w + i] as int + (if filter == 0 {
            0
        } else if y == 0 {
            if i == 0 {
                0
            } else {
                alph_unf(raw, w, filter, y * w + i - 1)
            }
        } else if filter == 2 || i == 0 {
            alph_unf(raw, w, filter, y * w + i - w)
        } else if filter == 1 {
            alph_unf(raw, w, filter, y * w + i - 1)
        } else {
            alph_clip(
                alph_unf(raw, w, filter, y * w + i - 1) + alph_unf(raw, w, filter, y * w + i - w) - alph_unf(
                    raw,
                    w,
                    filter,
                    y * w + i - w - 1,
                ),
            )
        })) % 256,
{
    let k = y * w + i;
    assert(0 <= y * w) by (nonlinear_arith)
        requires 0 <= y, 0 <= w;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k, w, y, i);
    assert(y == 0 <==> k < w) by (nonlinear_arith)
        requires k == y * w + i, 0 <= i < w, 0 <= y;
    assert(y == 0 && i == 0 <==> k == 0) by (nonlinear_arith)
        requires k == y * w + i, 0 <= i < w, 0 <= y;
    assert(k == w ==> i == 0) by (nonlinear_arith)
        requires k == y * w + i, 0 <= i < w, 0 <= y;
}

/// The plane `a` has its first `n` values unfiltered and the rest as
/// read.
pub open spec fn unf_upto(a: Seq<u8>, raw: Seq<u8>, w: int, filter: int, n: int) -> bool {
    &&& a.len() == raw.len()
    &&& forall|k: int| 0 <= k < n && k < a.len() ==> #[trigger] a[k] as int == alph_unf(raw, w, filter, k)
    &&& forall|k: int| n <= k < a.len() ==> #[trigger] a[k] == raw[k]
}

/// `WebPUnfilters[filter](prev, row, row, w)` on the row at `o`, with the
/// row above at `o - w` unless `o == 0`.
#[verifier::loop_isolation(false)]
#[verifier::rlimit(30)]
fn unfilter_row(a: &mut Vec<u8>, o: usize, w: usize, filter: u8, Ghost(raw): Ghost<Seq<u8>>, Ghost(y): Ghost<int>)
    requires
        o + w <= old(a)@.len(),
        o == 0 || o >= w,
        w >= 1,
        filter < 4,
        0 <= y,
        o == y * w,
        unf_upto(old(a)@, raw, w as int, filter as int, o as int),
    ensures
        final(a)@.len() == old(a)@.len(),
        unf_upto(final(a)@, raw, w as int, filter as int, o + w),
{
    hide(alph_unf);
    hide(alph_clip);
    proof { assert(a@.len() == a.len()); }
    let ghost wi = w as int;
    let ghost fi = filter as int;
    proof {
        assert(y == 0 <==> o == 0) by (nonlinear_arith)
            requires o == y * w, w >= 1, 0 <= y;
    }
    if filter == 0 {
        proof {
            assert forall|k: int| o <= k < o + w implies #[trigger] a@[k] as int == alph_unf(raw, wi, fi, k) by {
                lemma_unf_step(raw, wi, fi, y, k - o);
            }
        }
        return;
    }
    if o == 0 || filter == 1 {
        let mut pred: u8 = if o == 0 {
            0
        } else {
            a[o - w]
        };
        let mut i: usize = 0;
        while i < w
            invariant
                i <= w,
                o + w <= a@.len(),
                a@.len() == old(a)@.len(),
                unf_upto(a@, raw, wi, fi, o + i),
                i > 0 ==> pred == a@[o + i - 1],
                i == 0 ==> pred == (if o == 0 { 0u8 } else { a@[o - w] }),
            decreases w - i,
        {
            proof {
                lemma_unf_step(raw, wi, fi, y, i as int);
            }
            let v = ((pred as u32 + a[o + i] as u32) % 256) as u8;
            store_at(a, o + i, v);
            pred = v;
            i = i + 1;
        }
    } else if filter == 2 {
        let mut i: usize = 0;
        while i < w
            invariant
                i <= w,
                o >= w,
                o + w <= a@.len(),
                a@.len() == old(a)@.len(),
                unf_upto(a@, raw, wi, fi, o + i),
            decreases w - i,
        {
            proof {
                lemma_unf_step(raw, wi, fi, y, i as int);
            }
            let v = ((a[o - w + i] as u32 + a[o + i] as u32) % 256) as u8;
            store_at(a, o + i, v);
            i = i + 1;
        }
    } else {
        let mut top_left = a[o - w] as i32;
        let mut left = top_left;
        let mut i: usize = 0;
        while i < w
            invariant
                i <= w,
                o >= w,
                o + w <= a@.len(),
                a@.len() == old(a)@.len(),
                0 <= top_left < 256,
                0 <= left < 256,
                unf_upto(a@, raw, wi, fi, o + i),
                i == 0 ==> left == a@[o - w] && top_left == a@[o - w],
                i > 0 ==> left == a@[o + i - 1] && top_left == a@[o - w + i - 1],
            decreases w - i,
        {
            proof {
                lemma_unf_step(raw, wi, fi, y, i as int);
            }
            let top = a[o - w + i] as i32;
            proof {
                reveal(alph_clip);
            }
            let g = left + top - top_left;
            let g = if g < 0 {
                0
            } else if g > 255 {
                255
            } else {
                g
            };
            left = (a[o + i] as i32 + g) % 256;
            top_left = top;
            store_at(a, o + i, left as u8);
            i = i + 1;
        }
    }
}

/// Decodes the alpha plane of a `w` by `h` frame from the ALPH payload
/// `d[o..o + size]` (`ALPHInit`, `ALPHDecode`): `spec::alpha_plane`.
#[verifier::loop_isolation(false)]
pub fn decode_alpha(d: &[u8], o: usize, size: usize, w: usize, h: usize) -> (r: Result<Vec<u8>, Error>)
    requires
        o + size <= d@.len(),
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        r matches Ok(a) ==> a@.len() == w * h,
        match alpha_plane(d@.subrange(o as int, o + size), w as nat, h as nat) {
            Some(pl) => (r matches Ok(a) && a@ == pl) || r == Err::<Vec<u8>, Error>(Error::OutOfMemory),
            None => r is Err,
        },
{
    hide(vp8l_headless);
    hide(alph_unf);
    proof {assert(d@.len() == d.len());}
    let ghost pay = d@.subrange(o as int, o + size);
    if size <= 1 {
        return Err(Error::Bitstream);
    }
    let hb = get(d, o);
    let method = hb & 3;
    let filter = (hb >> 2u8) & 3;
    let pre = (hb >> 4u8) & 3;
    let rsrv = hb >> 6u8;
    proof {
        assert(pay[0] == hb);
        assert(hb & 3 == hb % 4 && (hb >> 2u8) & 3 == (hb / 4) % 4 && (hb >> 4u8) & 3 == (hb / 16) % 4 && hb >> 6u8 == hb
            / 64) by (bit_vector);
    }
    if method > 1 || pre > 1 || rsrv != 0 {
        return Err(Error::Bitstream);
    }
    let src = o + 1;
    let n = size - 1;
    proof {
        assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires 1 <= w <= 16384, 1 <= h <= 16384;
    }
    let npx = w * h;
    let mut a: Vec<u8>;
    let ghost raw: Seq<u8>;
    if method == 0 {
        if n < npx {
            return Err(Error::Bitstream);
        }
        a = match alloc_u8(npx) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        copy_in(a.as_mut_slice(), 0, d, src, npx);
        proof {
            raw = pay.subrange(1, 1 + npx);
            assert(a@ =~= raw);
        }
    } else {
        let sub = vstd::slice::slice_subrange(d, src, src + n);
        proof {
            assert(sub@ =~= pay.subrange(1, pay.len() as int));
            assert(sub@.len() >= 8 ==> pad(sub@) == sub@);
        }
        let px = if sub.len() < 8 {
            let v = pad_exec(sub);
            vp8l_image(v.as_slice(), w, h)
        } else {
            vp8l_image(sub, w, h)
        };
        let px = match px {
            Ok(p) => p,
            Err(e) => return Err(e),
        };
        a = match alloc_u8(npx) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        let mut i: usize = 0;
        while i < npx
            invariant
                d@.len() <= usize::MAX,
                i <= npx,
                a@.len() == npx,
                px@.len() == npx,
                forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == ((px@[j] / 256) % 256) as u8,
            decreases npx - i,
        {
            let v = px[i];
            proof {
                assert(((v >> 8u32) & 0xff) as u8 == ((v / 256) % 256) as u8) by (bit_vector);
            }
            store_at(&mut a, i, ((v >> 8u32) & 0xff) as u8);
            i = i + 1;
        }
        proof {
            raw = Seq::new(npx as nat, |i: int| ((px@[i] / 256) % 256) as u8);
            assert(a@ =~= raw);
        }
    }
    let mut y: usize = 0;
    while y < h
        invariant
            d@.len() <= usize::MAX,
            y <= h,
            a@.len() == w * h,
            unf_upto(a@, raw, w as int, filter as int, y * w),
        decreases h - y,
    {
        proof {
            assert(y * w + w <= w * h) by (nonlinear_arith) requires y < h;
            assert(y == 0 || y * w >= w) by (nonlinear_arith) requires w >= 1;
            assert((y + 1) * w == y * w + w) by (nonlinear_arith);
        }
        unfilter_row(&mut a, y * w, w, filter, Ghost(raw), Ghost(y as int));
        y = y + 1;
    }
    proof {
        let pl = Seq::new(npx as nat, |k: int| alph_unf(raw, w as int, filter as int, k) as u8);
        assert(h * w == w * h) by (nonlinear_arith);
        assert(y == h);
        assert forall|k: int| 0 <= k < npx implies a@[k] == pl[k] by {
            assert(a@[k] as int == alph_unf(raw, w as int, filter as int, k));
        }
        assert(a@ =~= pl);
    }
    Ok(a)
}

/// A VP8L image stream without the VP8L header (an ALPH payload): the
/// transforms, the entropy-coded image and its inverse transforms.
fn vp8l_image(b: &[u8], w: usize, h: usize) -> (r: Result<Vec<u32>, Error>)
    requires
        b@.len() >= 8,
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        r matches Ok(px) ==> px@.len() == w * h,
        match vp8l_headless(b@, w as nat, h as nat) {
            Some(px) => (r matches Ok(v) && v@ == px) || r == Err::<Vec<u32>, Error>(Error::OutOfMemory),
            None => r is Err,
        },
{
    hide(read_transforms);
    hide(decode_main);
    hide(undo_all);
    proof {assert(b@.len() == b.len());}
    let mut br = BitReader::new(b);
    let (ts, xw) = match read_transforms_exec(&mut br, b, w, h) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let px = match decode_main_exec(&mut br, b, xw, h) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    match undo_all_exec(&ts, px, Ghost(w as nat), h) {
        Some(out) => Ok(out),
        None => Err(Error::OutOfMemory),
    }
}

/// A lossy file's decoded frame and alpha plane, before conversion to RGB.
pub struct LossyPlanes {
    pub pl: Planes,
    pub alpha: Vec<u8>,
    pub has_alpha: bool,
}

impl LossyPlanes {
    pub open spec fn ok(&self) -> bool {
        &&& self.pl.ok()
        &&& self.has_alpha ==> self.alpha@.len() >= self.pl.width * self.pl.height
    }

    /// The planes are those of the VP8 frame at `d[off..]`: its size, and,
    /// for a frame the pixel theorem covers (`vp8_plain`), its bytes. The
    /// alpha plane is the one the ALPH payload `alp` holds, if there is
    /// one.
    pub open spec fn at(&self, d: Seq<u8>, off: int, alp: Option<(nat, nat)>) -> bool {
        &&& self.pl.width == frame_width(d, off)
        &&& self.pl.height == frame_height(d, off)
        &&& vp8_plain(d, off) ==> self.pl.yuv() == vp8_yuv(d, off)
        &&& self.has_alpha == alp.is_some()
        &&& Some(self.alpha@) == file_alpha(d, off, alp)
    }
}

/// The alpha plane of the frame at `d[off..]` whose ALPH payload is `alp`
/// (offset and size): `spec::alpha_plane` of it, or no bytes when the file
/// has no ALPH chunk. `None` if the payload does not decode.
pub open spec fn file_alpha(d: Seq<u8>, off: int, alp: Option<(nat, nat)>) -> Option<Seq<u8>> {
    match alp {
        Some((o, s)) => alpha_plane(
            d.subrange(o as int, (o + s) as int),
            frame_width(d, off) as nat,
            frame_height(d, off) as nat,
        ),
        None => Some(Seq::empty()),
    }
}

/// `im` is the VP8 frame at `d[off..]` as ARGB, with the alpha of the
/// ALPH payload `alp`, or opaque: its size, and, for a frame the pixel
/// theorem covers, the RGB specification's image of its planes and that
/// alpha plane.
pub open spec fn lossy_argb(d: Seq<u8>, off: int, alp: Option<(nat, nat)>, im: Decoded) -> bool {
    &&& im.w == frame_width(d, off)
    &&& im.h == frame_height(d, off)
    &&& im.px@.len() == im.w * im.h
    &&& file_alpha(d, off, alp) is Some
    &&& vp8_plain(d, off) ==> rgb_image_argb(vp8_yuv(d, off), file_alpha(d, off, alp)->Some_0, alp.is_some(), im.px@)
}

/// The frame and alpha plane of a lossy file laid out as `l`.
#[inline(always)]
pub fn layout_planes(d: &[u8], l: &Layout) -> (r: Result<LossyPlanes, Error>)
    requires
        l.off + 10 <= d@.len(),
        l.alpha matches Some((o, s)) ==> o + s <= d@.len(),
    ensures
        r matches Ok(p) ==> p.ok() && p.at(d@, l.off as int, aview(l.alpha)),
{
    let pl = match decode_frame(d, l.off) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    let w = pl.width;
    let h = pl.height;
    let (alpha, has) = match l.alpha {
        Some((o, s)) => match decode_alpha(d, o, s, w, h) {
            Ok(a) => (a, true),
            Err(e) => return Err(e),
        },
        None => (Vec::new(), false),
    };
    Ok(LossyPlanes { pl, alpha, has_alpha: has })
}

/// A lossy file laid out as `l`, decoded to ARGB.
#[inline(always)]
pub fn layout_argb(d: &[u8], l: &Layout) -> (r: Result<Decoded, Error>)
    requires
        l.off + 10 <= d@.len(),
        l.alpha matches Some((o, s)) ==> o + s <= d@.len(),
    ensures
        r matches Ok(im) ==> lossy_argb(d@, l.off as int, aview(l.alpha), im),
{
    hide(rgb_image_argb);
    hide(vp8_yuv);
    hide(vp8_plain);
    hide(Planes::yuv);
    let p = match layout_planes(d, l) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    match planes_to_argb(&p.pl, &p.alpha, p.has_alpha) {
        Ok(px) => {
            let im = Decoded { w: p.pl.width, h: p.pl.height, px };
            proof {
                let off = l.off as int;
                assert(p.at(d@, off, aview(l.alpha)));
                assert(im.w == frame_width(d@, off));
                assert(im.h == frame_height(d@, off));
                assert(im.px@.len() == im.w * im.h);
                if vp8_plain(d@, off) {
                    assert(p.pl.yuv() == vp8_yuv(d@, off));
                    assert(rgb_image_argb(vp8_yuv(d@, off), p.alpha@, p.has_alpha, im.px@));
                }
            }
            Ok(im)
        },
        Err(e) => Err(e),
    }
}

/// Decodes a lossy WebP file's frame and alpha plane: those of the VP8
/// frame `lossy_layout` finds in it (`layout_planes`).
pub fn decode_lossy_planes(d: &[u8]) -> (r: Result<LossyPlanes, Error>)
    ensures
        r matches Ok(p) ==> p.ok(),
        r matches Ok(p) ==> lossy_off(d@) + 10 <= d@.len() && p.at(d@, lossy_off(d@) as int, lossy_alpha(d@)),
{
    hide(vp8_yuv);
    hide(vp8_plain);
    hide(Planes::yuv);
    let l = match lossy_layout(d) {
        Some(l) => l,
        None => return Err(Error::Bitstream),
    };
    let r = layout_planes(d, &l);
    proof {
        if r is Ok {
            assert((r->Ok_0).at(d@, l.off as int, aview(l.alpha)));
        }
    }
    r
}

/// Decodes a lossy WebP file to ARGB: the image of the VP8 frame at
/// `container::lossy_off`, where the container specification puts it.
pub fn decode_lossy(d: &[u8]) -> (r: Result<Decoded, Error>)
    ensures
        r matches Ok(im) ==> lossy_off(d@) + 10 <= d@.len() && lossy_argb(
            d@,
            lossy_off(d@) as int,
            lossy_alpha(d@),
            im,
        ),
{
    hide(rgb_image_argb);
    hide(vp8_yuv);
    hide(vp8_plain);
    let l = match lossy_layout(d) {
        Some(l) => l,
        None => return Err(Error::Bitstream),
    };
    let r = layout_argb(d, &l);
    proof {
        if r is Ok {
            assert(lossy_argb(d@, l.off as int, aview(l.alpha), r->Ok_0));
        }
    }
    r
}

} // verus!
