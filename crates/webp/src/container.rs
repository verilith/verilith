//! The WebP container (RIFF, VP8X, optional chunks, the VP8L chunk), proven
//! to compute `spec::parse_headers` and `spec::webp_decode`.
use crate::bitreader::*;
use crate::decode::*;
use crate::pixels::Error;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// What the headers say (`spec::Parsed`).
pub enum ParsedX {
    Lossless(usize),
    Lossy,
    Fail,
}

pub open spec fn pview(p: ParsedX) -> Parsed {
    match p {
        ParsedX::Lossless(o) => Parsed::Lossless(o as nat),
        ParsedX::Lossy => Parsed::Lossy,
        ParsedX::Fail => Parsed::Fail,
    }
}

/// `le_n(d, i, 4)`.
pub(crate) fn le32(d: &[u8], i: usize) -> (r: u64)
    requires
        i + 4 <= d@.len(),
    ensures
        r as nat == le_n(d@, i as nat, 4),
        r < 0x1_0000_0000,
{
    proof {
        reveal_with_fuel(le_n, 5);
    }
    d[i] as u64 + 256 * (d[i + 1] as u64 + 256 * (d[i + 2] as u64 + 256 * (d[i + 3] as u64)))
}

/// `le_n(d, i, 3)`.
pub(crate) fn le24(d: &[u8], i: usize) -> (r: u64)
    requires
        i + 3 <= d@.len(),
    ensures
        r as nat == le_n(d@, i as nat, 3),
        r < 0x100_0000,
{
    proof {
        reveal_with_fuel(le_n, 4);
    }
    d[i] as u64 + 256 * (d[i + 1] as u64 + 256 * (d[i + 2] as u64))
}

/// `tag(d, i, [a, b, c, e])`.
pub(crate) fn is_tag(d: &[u8], i: usize, a: u8, b: u8, c: u8, e: u8) -> (r: bool)
    ensures
        r == tag(d@, i as int, seq![a, b, c, e]),
{
    if i > d.len() || d.len() - i < 4 {
        return false;
    }
    let r = d[i] == a && d[i + 1] == b && d[i + 2] == c && d[i + 3] == e;
    proof {
        let s = d@.subrange(i as int, i + 4);
        if r {
            assert(s =~= seq![a, b, c, e]);
        } else if s == seq![a, b, c, e] {
            assert(s[0] == a && s[1] == b && s[2] == c && s[3] == e);
        }
    }
    r
}

/// Skips optional chunks (`spec::skip_chunks`).
fn skip_chunks_exec(d: &[u8], p: usize, riff: u64, total: u64) -> (r: Option<usize>)
    requires
        p <= d@.len(),
        total < 0x1_0000_0000,
        riff <= MAX_PAYLOAD,
    ensures
        match skip_chunks(d@, p as nat, riff as nat, total as nat) {
            Some(q) => r matches Some(q2) && q2 == q,
            None => r is None,
        },
        r matches Some(q) ==> q + 8 <= d@.len(),
{
    let ghost res = skip_chunks(d@, p as nat, riff as nat, total as nat);
    let mut q = p;
    let mut tot = total;
    loop
        invariant
            q <= d@.len(),
            tot < 0x1_0000_0000,
            riff <= MAX_PAYLOAD,
            skip_chunks(d@, q as nat, riff as nat, tot as nat) == res,
            res == skip_chunks(d@, p as nat, riff as nat, total as nat),
        decreases d@.len() - q,
    {
        if d.len() - q < 8 {
            assert(skip_chunks(d@, q as nat, riff as nat, tot as nat) is None);
            return None;
        }
        let size = le32(d, q + 4);
        let disk = 2 * ((9 + size) / 2);
        let t = (tot + disk) % 0x1_0000_0000;
        if size > 0xffff_fff6 || (riff > 0 && t > riff) {
            assert(skip_chunks(d@, q as nat, riff as nat, tot as nat) is None);
            return None;
        }
        if is_tag(d, q, 0x56, 0x50, 0x38, 0x20) || is_tag(d, q, 0x56, 0x50, 0x38, 0x4c) {
            return Some(q);
        }
        if ((d.len() - q) as u64) < disk {
            return None;
        }
        q = q + disk as usize;
        tot = t;
    }
}

/// `pad` for a short bitstream.
pub fn pad_exec(s: &[u8]) -> (v: Vec<u8>)
    requires
        s@.len() < 8,
    ensures
        v@ == pad(s@),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 8
        invariant
            s@.len() < 8,
            i <= 8,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == if j < s@.len() {
                s@[j]
            } else {
                0u8
            },
        decreases 8 - i,
    {
        if i < s.len() {
            v.push(s[i]);
        } else {
            v.push(0);
        }
        i = i + 1;
    }
    assert(v@ =~= pad(s@));
    v
}

/// The VP8L header (`spec::vp8l_header`) of a padded bitstream.
pub fn header_exec(b: &[u8]) -> (r: Option<(u32, u32, u32)>)
    requires
        b@.len() >= 8,
    ensures
        match vp8l_header(b@) {
            Some((w, h, a)) => r == Some((w as u32, h as u32, a as u32)) && 1 <= w <= 16384 && 1 <= h <= 16384,
            None => r is None,
        },
{
    let mut br = BitReader::new(b);
    let sig = br.take(b, 8);
    let wm = br.take(b, 14);
    let hm = br.take(b, 14);
    let a = br.take(b, 1);
    let v = br.take(b, 3);
    proof {
        assert(rd(b@, 0, 8) is Some && rd(b@, 8, 14) is Some && rd(b@, 22, 14) is Some && rd(b@, 36, 1) is Some && rd(
            b@,
            37,
            3,
        ) is Some);
        verilith_core::bits::lemma_bits_bound(b@, 8, 14);
        verilith_core::bits::lemma_bits_bound(b@, 22, 14);
        vstd::arithmetic::power2::lemma2_to64();
    }
    match (sig, wm, hm, a, v) {
        (Some(sig), Some(wm), Some(hm), Some(a), Some(v)) => if sig == 0x2f && v == 0 {
            Some((wm + 1, hm + 1, a))
        } else {
            None
        },
        _ => None,
    }
}

/// The end of `parse_headers`, from the VP8/VP8L chunk header at `p2`.
pub open spec fn ph_tail(d: Seq<u8>, p2: nat, riff_size: nat, is_vp8x: bool, cw: nat, ch: nat) -> Parsed {
    if d.len() < p2 + 8 {
        Parsed::Fail
    } else {
        let chunk = tag(d, p2 as int, vp8_tag()) || tag(d, p2 as int, vp8l_tag());
        let size = le_n(d, p2 + 4, 4);
        if chunk && ((riff_size >= 12 && size > riff_size - 12) || size > d.len() - p2 - 8) {
            Parsed::Fail
        } else {
            let p3: nat = if chunk {
                p2 + 8
            } else {
                p2
            };
            let lossless = if chunk {
                tag(d, p2 as int, vp8l_tag())
            } else {
                vp8l_signature(d, p2)
            };
            let csize: nat = if chunk {
                size
            } else {
                (d.len() - p2) as nat
            };
            if csize > MAX_PAYLOAD {
                Parsed::Fail
            } else if !lossless {
                Parsed::Lossy
            } else if d.len() < p3 + 5 || !vp8l_signature(d, p3) {
                Parsed::Fail
            } else {
                match vp8l_header(pad(d.subrange(p3 as int, d.len() as int))) {
                    None => Parsed::Fail,
                    Some((w, h, a)) => if is_vp8x && (w != cw || h != ch) {
                        Parsed::Fail
                    } else {
                        Parsed::Lossless(p3)
                    },
                }
            }
        }
    }
}

pub open spec fn ph_riff(d: Seq<u8>) -> bool {
    tag(d, 0, riff_tag())
}

pub open spec fn ph_riff_size(d: Seq<u8>) -> nat {
    if ph_riff(d) {
        le_n(d, 4, 4)
    } else {
        0
    }
}

pub open spec fn ph_p0(d: Seq<u8>) -> nat {
    if ph_riff(d) {
        12
    } else {
        0
    }
}

pub open spec fn ph_vp8x(d: Seq<u8>) -> bool {
    tag(d, ph_p0(d) as int, vp8x_tag())
}

pub open spec fn ph_cw(d: Seq<u8>) -> nat {
    1 + le_n(d, ph_p0(d) + 12, 3)
}

pub open spec fn ph_ch(d: Seq<u8>) -> nat {
    1 + le_n(d, ph_p0(d) + 15, 3)
}

pub open spec fn ph_p1(d: Seq<u8>) -> nat {
    if ph_vp8x(d) {
        ph_p0(d) + 18
    } else {
        ph_p0(d)
    }
}

pub open spec fn ph_bad_riff(d: Seq<u8>) -> bool {
    let riff = le_n(d, 4, 4);
    ph_riff(d) && (!tag(d, 8, webp_tag()) || riff < 12 || riff > MAX_PAYLOAD || riff > d.len() - 8)
}

pub open spec fn ph_bad_vp8x(d: Seq<u8>) -> bool {
    let p0 = ph_p0(d);
    ph_vp8x(d) && (le_n(d, p0 + 4, 4) != 10 || d.len() < p0 + 18 || ph_cw(d) * ph_ch(d) >= 0x1_0000_0000 || (le_n(
        d,
        p0 + 8,
        4,
    ) / 2) % 2 == 1 || !ph_riff(d))
}

pub open spec fn ph_skip(d: Seq<u8>) -> bool {
    (ph_riff(d) && ph_vp8x(d)) || (!ph_riff(d) && !ph_vp8x(d) && tag(d, ph_p1(d) as int, alph_tag()))
}

/// Where the VP8 or VP8L chunk header (or a bare bitstream) begins, after
/// the optional chunks.
pub open spec fn lossy_p2(d: Seq<u8>) -> Option<nat> {
    if ph_skip(d) {
        skip_chunks(d, ph_p1(d), ph_riff_size(d), 22)
    } else {
        Some(ph_p1(d))
    }
}

/// Where a lossy file's VP8 frame begins: after the chunk header, if it
/// has one.
pub open spec fn lossy_off(d: Seq<u8>) -> nat {
    match lossy_p2(d) {
        Some(q) => if tag(d, q as int, vp8_tag()) || tag(d, q as int, vp8l_tag()) {
            q + 8
        } else {
            q
        },
        None => 0,
    }
}

/// The payload of a lossy file's last ALPH chunk before the frame.
pub open spec fn lossy_alpha(d: Seq<u8>) -> Option<(nat, nat)> {
    if ph_skip(d) {
        find_alph(d, ph_p1(d), ph_riff_size(d), 22, None)
    } else {
        None
    }
}

/// `parse_headers`, step by step.
pub proof fn lemma_ph_split(d: Seq<u8>)
    ensures
        d.len() < 12 ==> parse_headers(d) == Parsed::Fail,
        d.len() >= 12 && ph_bad_riff(d) ==> parse_headers(d) == Parsed::Fail,
        d.len() >= 12 && !ph_bad_riff(d) && d.len() < ph_p0(d) + 8 ==> parse_headers(d) == Parsed::Fail,
        d.len() >= 12 && !ph_bad_riff(d) && d.len() >= ph_p0(d) + 8 && ph_bad_vp8x(d) ==> parse_headers(d)
            == Parsed::Fail,
        d.len() >= 12 && !ph_bad_riff(d) && d.len() >= ph_p0(d) + 8 && !ph_bad_vp8x(d) && d.len() < ph_p1(d) + 4
            ==> parse_headers(d) == Parsed::Fail,
        d.len() >= 12 && !ph_bad_riff(d) && d.len() >= ph_p0(d) + 8 && !ph_bad_vp8x(d) && d.len() >= ph_p1(d) + 4
            ==> parse_headers(d) == match (if ph_skip(d) {
            skip_chunks(d, ph_p1(d), ph_riff_size(d), 22)
        } else {
            Some(ph_p1(d))
        }) {
            None => Parsed::Fail,
            Some(q) => ph_tail(d, q, ph_riff_size(d), ph_vp8x(d), ph_cw(d), ph_ch(d)),
        },
{
}

pub proof fn lemma_ph_tail_nox(d: Seq<u8>, p2: nat, rs: nat, cw1: nat, ch1: nat, cw2: nat, ch2: nat)
    ensures
        ph_tail(d, p2, rs, false, cw1, ch1) == ph_tail(d, p2, rs, false, cw2, ch2),
{
}

/// Parses the headers (`spec::parse_headers`).
pub fn parse_headers_exec(d: &[u8]) -> (r: ParsedX)
    ensures
        pview(r) == parse_headers(d@),
        r matches ParsedX::Lossless(p) ==> p + 5 <= d@.len(),
{
    hide(parse_headers);
    hide(ph_tail);
    hide(skip_chunks);
    proof {
        lemma_ph_split(d@);
    }
    let n = d.len();
    if n < 12 {
        return ParsedX::Fail;
    }
    let is_riff = is_tag(d, 0, 0x52, 0x49, 0x46, 0x46);
    let riff = le32(d, 4);
    if is_riff && (!is_tag(d, 8, 0x57, 0x45, 0x42, 0x50) || riff < 12 || riff > 0xffff_fff6 || riff > (n - 8) as u64) {
        return ParsedX::Fail;
    }
    let riff_size: u64 = if is_riff {
        riff
    } else {
        0
    };
    let p0: usize = if is_riff {
        12
    } else {
        0
    };
    if n < p0 + 8 {
        return ParsedX::Fail;
    }
    let is_vp8x = is_tag(d, p0, 0x56, 0x50, 0x38, 0x58);
    let mut cw: u64 = 0;
    let mut ch: u64 = 0;
    if is_vp8x {
        if le32(d, p0 + 4) != 10 || n < p0 + 18 {
            return ParsedX::Fail;
        }
        let flags = le32(d, p0 + 8);
        cw = 1 + le24(d, p0 + 12);
        ch = 1 + le24(d, p0 + 15);
        proof {
            assert(cw * ch <= 0x100_0000 * 0x100_0000) by (nonlinear_arith)
                requires
                    cw <= 0x100_0000,
                    ch <= 0x100_0000,
            ;
        }
        if cw * ch >= 0x1_0000_0000 || (flags / 2) % 2 == 1 || !is_riff {
            return ParsedX::Fail;
        }
    }
    let p1: usize = if is_vp8x {
        p0 + 18
    } else {
        p0
    };
    if n < p1 + 4 {
        return ParsedX::Fail;
    }
    let skip = (is_riff && is_vp8x) || (!is_riff && !is_vp8x && is_tag(d, p1, 0x41, 0x4c, 0x50, 0x48));
    proof {
        assert(alph_tag() == seq![0x41u8, 0x4c, 0x50, 0x48]);
    }
    let p2 = if skip {
        skip_chunks_exec(d, p1, riff_size, 22)
    } else {
        Some(p1)
    };
    proof {
        assert(skip == ph_skip(d@));
        let sp = if ph_skip(d@) {
            skip_chunks(d@, ph_p1(d@), ph_riff_size(d@), 22)
        } else {
            Some(ph_p1(d@))
        };
        assert(p2 matches Some(q) ==> sp == Some(q as nat));
        assert(p2 is None ==> sp is None);
    }
    let p2 = match p2 {
        None => return ParsedX::Fail,
        Some(p) => p,
    };
    proof {
        if !is_vp8x {
            lemma_ph_tail_nox(d@, p2 as nat, riff_size as nat, cw as nat, ch as nat, ph_cw(d@), ph_ch(d@));
        }
        assert(is_riff == ph_riff(d@));
        assert(riff_size == ph_riff_size(d@));
        assert(p0 == ph_p0(d@));
        assert(is_vp8x == ph_vp8x(d@));
        assert(p1 == ph_p1(d@));
        assert(!ph_bad_riff(d@));
        assert(!ph_bad_vp8x(d@));
        assert(is_vp8x ==> cw == ph_cw(d@) && ch == ph_ch(d@));
        assert(parse_headers(d@) == ph_tail(d@, p2 as nat, riff_size as nat, is_vp8x, cw as nat, ch as nat));
    }
    ph_tail_exec(d, p2, riff_size, is_vp8x, cw, ch)
}

/// The end of `parse_headers` (`ph_tail`).
fn ph_tail_exec(d: &[u8], p2: usize, riff_size: u64, is_vp8x: bool, cw: u64, ch: u64) -> (r: ParsedX)
    requires
        p2 + 8 <= d@.len(),
        riff_size <= MAX_PAYLOAD,
    ensures
        pview(r) == ph_tail(d@, p2 as nat, riff_size as nat, is_vp8x, cw as nat, ch as nat),
        r matches ParsedX::Lossless(p) ==> p + 5 <= d@.len(),
{
    let n = d.len();
    let chunk = is_tag(d, p2, 0x56, 0x50, 0x38, 0x20) || is_tag(d, p2, 0x56, 0x50, 0x38, 0x4c);
    let size = le32(d, p2 + 4);
    if chunk && ((riff_size >= 12 && size > riff_size - 12) || size > (n - p2 - 8) as u64) {
        return ParsedX::Fail;
    }
    let p3: usize = if chunk {
        p2 + 8
    } else {
        p2
    };
    let lossless = if chunk {
        is_tag(d, p2, 0x56, 0x50, 0x38, 0x4c)
    } else {
        n - p2 >= 5 && d[p2] == 0x2f && d[p2 + 4] / 32 == 0
    };
    let csize: u64 = if chunk {
        size
    } else {
        (n - p2) as u64
    };
    if csize > 0xffff_fff6 {
        return ParsedX::Fail;
    }
    if !lossless {
        return ParsedX::Lossy;
    }
    if n - p3 < 5 || !(d[p3] == 0x2f && d[p3 + 4] / 32 == 0) {
        return ParsedX::Fail;
    }
    let sub = vstd::slice::slice_subrange(d, p3, n);
    let hdr = if sub.len() < 8 {
        let v = pad_exec(sub);
        header_exec(v.as_slice())
    } else {
        header_exec(sub)
    };
    match hdr {
        None => ParsedX::Fail,
        Some((w, h, a)) => if is_vp8x && (w as u64 != cw || h as u64 != ch) {
            ParsedX::Fail
        } else {
            ParsedX::Lossless(p3)
        },
    }
}

/// Decodes a WebP file (`spec::webp_decode`); `Unsupported` exactly for
/// lossy files. Also returns the work done.
pub fn webp_decode_exec(d: &[u8]) -> (r: (Result<Decoded, Error>, Ghost<nat>))
    ensures
        match webp_decode(d@) {
            Some(img) => (r.0 matches Ok(x) && x.w == img.w && x.h == img.h && x.px@ == img.px) || r.0
                == Err::<Decoded, Error>(Error::OutOfMemory),
            None => r.0 is Err,
        },
        r.0 == Err::<Decoded, Error>(Error::Unsupported) <==> parse_headers(d@) == Parsed::Lossy,
        r.0 matches Ok(x) ==> x.px@.len() == x.w * x.h && 1 <= x.w <= 16384 && 1 <= x.h <= 16384,
        r.1@ <= decode_cost(d@.len() + 8, 16384, 16384),
{
    hide(parse_headers);
    hide(decode_cost);
    hide(read_transforms);
    hide(decode_main);
    hide(undo_all);
    match parse_headers_exec(d) {
        ParsedX::Lossless(p) => {
            let sub = vstd::slice::slice_subrange(d, p, d.len());
            let r = if sub.len() < 8 {
                let v = pad_exec(sub);
                vp8l_decode_bits(v.as_slice())
            } else {
                vp8l_decode_bits(sub)
            };
            proof {
                let s = d@.subrange(p as int, d@.len() as int);
                assert(s.len() >= 8 ==> pad(s) == s);
                assert(vp8l_decode(s) == vp8l_bits(pad(s)));
                assert(webp_decode(d@) == vp8l_decode(s));
                lemma_hdr_dims(pad(s));
                lemma_decode_cost_mono(pad(s).len(), d@.len() + 8, hdr_dims(pad(s)).0, hdr_dims(pad(s)).1);
            }
            r
        },
        ParsedX::Lossy => (Err(Error::Unsupported), Ghost(0)),
        ParsedX::Fail => (Err(Error::Bitstream), Ghost(0)),
    }
}

pub proof fn lemma_hdr_dims(b: Seq<u8>)
    ensures
        1 <= hdr_dims(b).0 <= 16384,
        1 <= hdr_dims(b).1 <= 16384,
{
    if let Some((w, h, a)) = vp8l_header(b) {
        verilith_core::bits::lemma_bits_bound(b, 8, 14);
        verilith_core::bits::lemma_bits_bound(b, 22, 14);
        vstd::arithmetic::power2::lemma2_to64();
    }
}

pub proof fn lemma_decode_cost_mono(len: nat, dlen: nat, w: nat, h: nat)
    requires
        len <= dlen,
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        decode_cost(len, w, h) <= decode_cost(dlen, 16384, 16384),
{
    crate::transform::lemma_xc_mono(w, 16384, h);
    assert(16384 * h <= 16384 * 16384) by (nonlinear_arith)
        requires
            h <= 16384,
    ;
    assert(crate::pixels::pix_cost() * (16384 * h + 512) <= crate::pixels::pix_cost() * (16384 * 16384 + 512))
        by (nonlinear_arith)
        requires
            16384 * h <= 16384 * 16384,
    ;
    assert(w * h <= 16384 * 16384) by (nonlinear_arith)
        requires
            w <= 16384,
            h <= 16384,
    ;
    assert(crate::pixels::pix_cost() * crate::image::main_pix(w, h) <= crate::pixels::pix_cost()
        * crate::image::main_pix(16384, 16384)) by (nonlinear_arith)
        requires
            w * h <= 16384 * 16384,
            crate::image::main_pix(w, h) == 3 * (w * h),
            crate::image::main_pix(16384, 16384) == 3 * (16384 * 16384),
    ;
    assert(crate::image::bit_cost() * (8 * len) <= crate::image::bit_cost() * (8 * dlen)) by (nonlinear_arith)
        requires
            len <= dlen,
    ;
}

} // verus!
