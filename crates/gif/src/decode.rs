//! The decoder's entry point, proven to compute `spec::decode`.
use crate::blocks::*;
use crate::interlace::deinterlace_exec;
use crate::lzw::{lzw_exec, SLACK};
use crate::prims::alloc_zeroed;
use crate::spec;
use crate::spec::*;
use verilith_core::prims::{alloc_u32, get};
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Error {
    /// The file is not a GIF file that the specification accepts.
    Invalid,
    /// The images need more memory than the caller's limit allows.
    TooLarge,
    /// An allocation failed.
    OutOfMemory,
}

/// A graphic control extension (`spec::Gce`).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Gce {
    /// Disposal method, 0 to 7.
    pub disposal: u8,
    pub user_input: bool,
    /// Delay time, in hundredths of a second.
    pub delay: u16,
    /// The transparent colour index, if there is one.
    pub transparent: Option<u8>,
}

impl Gce {
    pub open spec fn view(self) -> spec::Gce {
        spec::Gce {
            disposal: self.disposal as nat,
            user_input: self.user_input,
            delay: self.delay as nat,
            transparent: match self.transparent {
                Some(t) => Some(t as nat),
                None => None,
            },
        }
    }
}

pub open spec fn gce_view(g: Option<Gce>) -> Option<spec::Gce> {
    match g {
        Some(x) => Some(x.view()),
        None => None,
    }
}

pub open spec fn table_view(t: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match t {
        Some(v) => Some(v@),
        None => None,
    }
}

/// One image (`spec::Image`).
#[derive(Debug)]
pub struct Frame {
    pub left: u16,
    pub top: u16,
    pub width: u16,
    pub height: u16,
    /// The packed fields byte of the image descriptor: local colour table
    /// flag (0x80), interlace flag (0x40), sort flag (0x20), size of the
    /// local colour table (0x07).
    pub flags: u8,
    /// The local colour table, 3 bytes per entry.
    pub lct: Option<Vec<u8>>,
    pub gce: Option<Gce>,
    /// The LZW minimum code size.
    pub min_code: u8,
    /// The colour index of each pixel, `width` per row, top row first
    /// (deinterlaced).
    pub pixels: Vec<u8>,
}

impl Frame {
    pub open spec fn view(self) -> spec::Image {
        spec::Image {
            left: self.left as nat,
            top: self.top as nat,
            width: self.width as nat,
            height: self.height as nat,
            flags: self.flags,
            lct: table_view(self.lct),
            gce: gce_view(self.gce),
            min_code: self.min_code as nat,
            pixels: self.pixels@,
        }
    }
}

/// A decoded GIF file (`spec::Gif`).
#[derive(Debug)]
pub struct Gif {
    /// The logical screen.
    pub width: u16,
    pub height: u16,
    /// The packed fields byte of the logical screen descriptor: global
    /// colour table flag (0x80), colour resolution (0x70), sort flag
    /// (0x08), size of the global colour table (0x07).
    pub flags: u8,
    /// The background colour index.
    pub bg: u8,
    /// The pixel aspect ratio byte.
    pub aspect: u8,
    /// The global colour table, 3 bytes per entry.
    pub gct: Option<Vec<u8>>,
    /// The images, in the order of the file.
    pub frames: Vec<Frame>,
}

pub open spec fn frames_view(f: Seq<Frame>) -> Seq<spec::Image> {
    f.map_values(|x: Frame| x.view())
}

impl Gif {
    pub open spec fn screen_view(self) -> spec::Screen {
        spec::Screen {
            width: self.width as nat,
            height: self.height as nat,
            flags: self.flags,
            bg: self.bg as nat,
            aspect: self.aspect as nat,
            gct: table_view(self.gct),
        }
    }

    pub open spec fn view(self) -> spec::Gif {
        spec::Gif { screen: self.screen_view(), images: frames_view(self.frames@) }
    }
}

#[inline(always)]
fn le16_exec(b: &[u8], i: usize) -> (r: u16)
    requires
        i + 1 < b@.len(),
    ensures
        r as nat == le16(b@, i as int),
{
    let n = b.len();
    get(b, i) as u16 + 256 * get(b, i + 1) as u16
}

/// The bytes in a colour table with size field `k` (`spec::table_len`).
fn table_len_exec(k: u8) -> (r: usize)
    requires
        k < 8,
    ensures
        r == table_len(k as nat),
        r <= 768,
{
    proof {
        lemma2_to64();
    }
    match k {
        0 => 6,
        1 => 12,
        2 => 24,
        3 => 48,
        4 => 96,
        5 => 192,
        6 => 384,
        _ => 768,
    }
}

/// The colour table flagged by bit 0x80 of `flags`, with size field
/// `flags & 7`: its length in bytes, or 0.
fn flagged_table_len(flags: u8) -> (r: usize)
    ensures
        r == (if flags & 0x80 != 0 { table_len((flags & 7) as nat) as int } else { 0 }),
        r <= 768,
{
    if flags & 0x80 != 0 {
        assert(flags & 7 < 8) by (bit_vector);
        table_len_exec(flags & 7)
    } else {
        0
    }
}

/// The header, logical screen descriptor and global colour table
/// (`spec::screen`), and the position after them.
pub fn screen_exec(b: &[u8]) -> (r: Option<(Gif, usize)>)
    ensures
        match screen(b@) {
            Some((s, p)) => r matches Some((g, q)) && g.screen_view() == s && q == p && g.frames@.len() == 0,
            None => r is None,
        },
{
    if b.len() < 13 || get(b, 0) != 0x47 || get(b, 1) != 0x49 || get(b, 2) != 0x46 {
        return None;
    }
    let flags = get(b, 10);
    let n = flagged_table_len(flags);
    if b.len() - 13 < n {
        return None;
    }
    let gct = if flags & 0x80 != 0 {
        Some(slice_to_vec(slice_subrange(b, 13, 13 + n)))
    } else {
        None
    };
    let g = Gif {
        width: le16_exec(b, 6),
        height: le16_exec(b, 8),
        flags,
        bg: get(b, 11),
        aspect: get(b, 12),
        gct,
        frames: Vec::new(),
    };
    Some((g, 13 + n))
}

/// The graphic control block whose first sub-block, at `q`, is in a
/// chain that ends inside the file (`spec::gce_at`).
fn gce_exec(b: &[u8], q: usize) -> (r: Option<Gce>)
    requires
        sub_blocks(b@, q as int) is Some,
        b@[q as int] != 0,
    ensures
        gce_view(r) == gce_at(b@, q as int),
{
    let blen = b.len();
    proof {
        reveal_with_fuel(sub_blocks, 1);
    }
    if get(b, q) != 4 {
        return None;
    }
    let f = get(b, q + 1);
    Some(
        Gce {
            disposal: (f >> 2) & 7,
            user_input: f & 2 != 0,
            delay: le16_exec(b, q + 2),
            transparent: if f & 1 != 0 { Some(get(b, q + 4)) } else { None },
        },
    )
}

/// The image whose descriptor is at `p` (`spec::image_at`), and the
/// position after its data. The image may use at most `room` bytes of
/// pixels; `off` and `len` are scratch space for the LZW decoder.
pub fn image_exec(b: &[u8], p: usize, gce: Option<Gce>, room: usize, off: &mut [u32], len: &mut [u32]) -> (r: Result<(Frame, usize), Error>)
    requires
        p <= b@.len(),
        old(off)@.len() == MAX_CODES,
        old(len)@.len() == MAX_CODES,
    ensures
        final(off)@.len() == MAX_CODES,
        final(len)@.len() == MAX_CODES,
        match r {
            Ok((f, e)) => image_at(b@, p as int, gce_view(gce)) == Some((f.view(), e as int))
                && f.pixels@.len() <= room && p < e <= b@.len(),
            Err(Error::Invalid) => image_at(b@, p as int, gce_view(gce)) is None,
            Err(_) => true,
        },
{
    if b.len() - p < 9 {
        return Err(Error::Invalid);
    }
    let w = le16_exec(b, p + 4);
    let h = le16_exec(b, p + 6);
    let flags = get(b, p + 8);
    let n = flagged_table_len(flags);
    if w == 0 || h == 0 {
        return Err(Error::Invalid);
    }
    proof {
        lemma_mul_inequality(w as int, 65535, h as int);
        lemma_mul_inequality(h as int, 65535, 65535);
        lemma_mul_is_commutative(w as int, h as int);
    }
    let px = w as u64 * h as u64;
    if px > 0x7fff_ffff {
        return Err(Error::Invalid);
    }
    let need = px as usize;
    if b.len() - p - 9 <= n {
        return Err(Error::Invalid);
    }
    let c = p + 9 + n;
    let m = get(b, c);
    if m < 2 || m > 8 {
        return Err(Error::Invalid);
    }
    let e = match skip_blocks(b, c + 1) {
        Some(e) => e,
        None => return Err(Error::Invalid),
    };
    if need > room {
        return Err(Error::TooLarge);
    }
    proof {
        lemma_sub_blocks_end(b@, c + 1);
        lemma_mul_inequality(1, w as int, h as int);
    }
    let data = gather(b, c + 1, e);
    let mut out = match alloc_zeroed(need + SLACK) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    if !lzw_exec(data.as_slice(), m, need, out.as_mut_slice(), off, len) {
        return Err(Error::Invalid);
    }
    out.truncate(need);
    let pixels = if flags & 0x40 != 0 {
        match deinterlace_exec(out.as_slice(), w as usize, h as usize) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        }
    } else {
        out
    };
    let lct = if flags & 0x80 != 0 {
        Some(slice_to_vec(slice_subrange(b, p + 9, c)))
    } else {
        None
    };
    let f = Frame {
        left: le16_exec(b, p),
        top: le16_exec(b, p + 2),
        width: w,
        height: h,
        flags,
        lct,
        gce,
        min_code: m,
        pixels,
    };
    proof {
        lemma_sub_blocks_end(b@, c + 1);
        let d = deinterlace(out@, w as nat, h as nat);
        assert(f.view().pixels.len() == need);
    }
    Ok((f, e))
}

/// Decodes a GIF file. The images' pixels may take at most `limit` bytes
/// in all.
///
/// The result is the specification's: `Ok` exactly with the spec's screen
/// and images; `Invalid` exactly when the spec rejects the file.
/// `TooLarge` and `OutOfMemory` are the only other results.
pub fn decode(b: &[u8], limit: usize) -> (r: Result<Gif, Error>)
    ensures
        match r {
            Ok(g) => spec::decode(b@) == Some(g.view()),
            Err(Error::Invalid) => spec::decode(b@) is None,
            Err(_) => true,
        },
{
    let (mut gif, start) = match screen_exec(b) {
        Some(x) => x,
        None => return Err(Error::Invalid),
    };
    let mut off = match alloc_u32(4096) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut len = match alloc_u32(4096) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let ghost s = gif.screen_view();
    let mut p = start;
    let mut gce: Option<Option<Gce>> = None;
    let mut room = limit;
    proof {
        assert(frames_view(gif.frames@) =~= Seq::empty());
    }
    while p < b.len()
        invariant
            p <= b@.len(),
            off@.len() == MAX_CODES,
            len@.len() == MAX_CODES,
            gif.screen_view() == s,
            screen(b@) == Some((s, start as int)),
            walk(b@, start as int, None, Seq::empty()) == walk(
                b@,
                p as int,
                match gce {
                    Some(g) => Some(gce_view(g)),
                    None => None,
                },
                frames_view(gif.frames@),
            ),
        decreases b@.len() - p,
    {
        let ghost gv = match gce {
            Some(g) => Some(gce_view(g)),
            None => None,
        };
        let ghost fv = frames_view(gif.frames@);
        let t = get(b, p);
        if t == 0x3B {
            if gif.frames.len() > 0 {
                return Ok(gif);
            }
            return Err(Error::Invalid);
        } else if t == 0x21 {
            if b.len() - p <= 2 {
                return Err(Error::Invalid);
            }
            let e = match skip_blocks(b, p + 2) {
                Some(e) => e,
                None => return Err(Error::Invalid),
            };
            proof {
                lemma_sub_blocks_end(b@, p + 2);
            }
            if gce.is_none() && get(b, p + 1) == 0xF9 && get(b, p + 2) != 0 {
                gce = Some(gce_exec(b, p + 2));
            }
            p = e;
        } else if t == 0x2C {
            let g = match gce {
                Some(g) => g,
                None => None,
            };
            let (f, e) = match image_exec(b, p + 1, g, room, off.as_mut_slice(), len.as_mut_slice()) {
                Ok(x) => x,
                Err(err) => return Err(err),
            };
            proof {
                assert(frames_view(gif.frames@.push(f)) =~= fv.push(f.view()));
            }
            room = room - f.pixels.len();
            gif.frames.push(f);
            gce = None;
            p = e;
        } else {
            return Err(Error::Invalid);
        }
    }
    Err(Error::Invalid)
}

} // verus!
