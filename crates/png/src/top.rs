//! The decoder's entry point, proven to compute `spec::decode`.
use crate::chunks::Header;
use crate::decode::*;
use crate::output::*;
use crate::passes::*;
use crate::spec::*;
use crate::work::Meter;
use vstd::prelude::*;

verus! {

/// Output pixel formats (`spec::Format`).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum PixelFormat {
    /// 8-bit RGBA, 4 bytes per pixel.
    Rgba8,
    /// The file's own format, deinterlaced: rows of `ceil(width * bits /
    /// 8)` bytes, 16-bit samples big-endian, sub-byte pixels packed from the
    /// most significant bit.
    Native,
}

pub open spec fn fview(f: PixelFormat) -> Format {
    match f {
        PixelFormat::Rgba8 => Format::Rgba8,
        PixelFormat::Native => Format::Native,
    }
}

/// Decodes a PNG file into `fmt`, using at most about `limit` bytes for
/// the decompressed data and for the output.
///
/// The result is the specification's: `Ok` exactly with the spec's header
/// and pixels; `Invalid` exactly when the spec rejects the file.
/// `TooLarge` and `OutOfMemory` are the only other results.
pub fn decode(b: &[u8], fmt: PixelFormat, limit: usize) -> (r: Result<(Header, Vec<u8>), Error>)
    ensures
        match r {
            Ok((h, px)) => crate::spec::decode(b@, fview(fmt)) == Some((h.view(), px@)),
            Err(Error::Invalid) => crate::spec::decode(b@, fview(fmt)) is None,
            Err(_) => true,
        },
{
    let mut tail = Tail::new();
    decode_tail(b, fmt, limit, &mut tail)
}

/// `decode`, also saying what the image data held beyond the image.
pub fn decode_tail(b: &[u8], fmt: PixelFormat, limit: usize, tail: &mut Tail) -> (r: Result<(Header, Vec<u8>), Error>)
    ensures
        match r {
            Ok((h, px)) => crate::spec::decode(b@, fview(fmt)) == Some((h.view(), px@)),
            Err(Error::Invalid) => crate::spec::decode(b@, fview(fmt)) is None,
            Err(_) => true,
        },
{
    decode_counted(b, fmt, limit, tail).0
}

/// The bound on `decode`'s work for an `n`-byte file that makes it allocate
/// `px` bytes for its output: linear in both.
pub open spec fn png_work(n: nat, px: nat) -> nat {
    parse_work(n) + 3096 * n + 12 * px + 2008
}

/// `decode_tail`, counting its steps and the bytes it allocates for the
/// output (`px`, at most twice `limit`): at most `png_work(b.len(), px)`
/// steps.
pub fn decode_counted(b: &[u8], fmt: PixelFormat, limit: usize, tail: &mut Tail) -> (r: (
    Result<(Header, Vec<u8>), Error>,
    Ghost<(nat, nat)>,
))
    ensures
        match r.0 {
            Ok((h, px)) => crate::spec::decode(b@, fview(fmt)) == Some((h.view(), px@)),
            Err(Error::Invalid) => crate::spec::decode(b@, fview(fmt)) is None,
            Err(_) => true,
        },
        r.1@.1 <= 2 * limit,
        r.1@.0 <= png_work(b@.len(), r.1@.1),
{
    let tracked mut m = Meter { n: 0 };
    let tracked mut a = Meter { n: 0 };
    let (png, mut buf) = match parse_counted(b, limit, tail, Tracked(&mut m)) {
        Ok(p) => p,
        Err(e) => return (Err(e), Ghost((m.n, 0))),
    };
    let ghost raw = buf@;
    let off = match reconstruct_counted(&png.hdr, buf.as_mut_slice(), Tracked(&mut m)) {
        Ok(x) => x,
        Err(()) => return (Err(Error::Invalid), Ghost((m.n, 0))),
    };
    let ghost m1 = m.n;
    proof {
        assert(m1 <= parse_work(b@.len()) + 3096 * b@.len() + 8);
    }
    let ghost imgs = imgs_of(png.hdr.view(), buf@, off@);
    proof {
        lemma_rgba8_raw(Png { raw, ..png.view() }, png.view(), imgs);
    }
    let hdr = png.hdr;
    let flat = png.hdr.interlace == 0;
    let px = match fmt {
        PixelFormat::Rgba8 => if flat && png.hdr.bit_depth == 8 {
            crate::fast::rgba8_flat(&png, buf, &off, limit, Tracked(&mut m), Tracked(&mut a))
        } else if flat && png.hdr.bit_depth == 16 {
            crate::fast::rgba8_flat16(&png, buf.as_slice(), &off, limit, Tracked(&mut m), Tracked(&mut a))
        } else if png.hdr.bit_depth >= 8 {
            crate::deint::rgba8_interlaced(png, buf.as_slice(), &off, limit, Tracked(&mut m), Tracked(&mut a))
        } else {
            to_rgba8(&png, buf.as_slice(), &off, limit, Tracked(&mut m), Tracked(&mut a))
        },
        PixelFormat::Native => if flat && crate::geom::pixel_bits_exec(&png.hdr) >= 8 {
            Ok(crate::fast::native_flat(&png.hdr, buf, &off))
        } else if !flat && crate::geom::pixel_bits_exec(&png.hdr) >= 8 {
            crate::deint::deinterlace(&png.hdr, buf.as_slice(), &off, limit, Tracked(&mut m), Tracked(&mut a))
        } else {
            to_native(&png.hdr, buf.as_slice(), &off, limit, Tracked(&mut m), Tracked(&mut a))
        },
    };
    proof {
        assert(m.n <= m1 + 12 * a.n + 2000);
    }
    let ghost cnt = (m.n, a.n);
    match px {
        Ok(v) => (Ok((hdr, v)), Ghost(cnt)),
        Err(e) => (Err(e), Ghost(cnt)),
    }
}

/// The RGBA output does not depend on the raw data, only on the images.
pub proof fn lemma_rgba8_raw(p1: Png, p2: Png, imgs: Seq<Seq<u8>>)
    requires
        p1.hdr == p2.hdr,
        p1.plte == p2.plte,
        p1.trns == p2.trns,
    ensures
        rgba8(p1, imgs) == rgba8(p2, imgs),
{
    assert(rgba8(p1, imgs) =~= rgba8(p2, imgs));
}

} // verus!
