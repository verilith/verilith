//! The decoder's entry point, proven to compute `spec::decode`.
use crate::chunks::Header;
use crate::decode::*;
use crate::output::*;
use crate::passes::*;
use crate::spec::*;
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
    let (png, mut buf) = match parse_exec(b, limit) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    let ghost raw = buf@;
    let off = match reconstruct(&png.hdr, buf.as_mut_slice()) {
        Ok(x) => x,
        Err(()) => return Err(Error::Invalid),
    };
    let ghost imgs = imgs_of(png.hdr.view(), buf@, off@);
    proof {
        lemma_rgba8_raw(Png { raw, ..png.view() }, png.view(), imgs);
    }
    let hdr = png.hdr;
    let flat = png.hdr.interlace == 0;
    let px = match fmt {
        PixelFormat::Rgba8 => if flat && png.hdr.bit_depth == 8 {
            crate::fast::rgba8_flat(&png, buf, &off, limit)
        } else if flat && png.hdr.bit_depth == 16 {
            crate::fast::rgba8_flat16(&png, buf.as_slice(), &off, limit)
        } else if png.hdr.bit_depth >= 8 {
            crate::deint::rgba8_interlaced(png, buf.as_slice(), &off, limit)
        } else {
            to_rgba8(&png, buf.as_slice(), &off, limit)
        },
        PixelFormat::Native => if flat && crate::geom::pixel_bits_exec(&png.hdr) >= 8 {
            Ok(crate::fast::native_flat(&png.hdr, buf, &off))
        } else if !flat && crate::geom::pixel_bits_exec(&png.hdr) >= 8 {
            crate::deint::deinterlace(&png.hdr, buf.as_slice(), &off, limit)
        } else {
            to_native(&png.hdr, buf.as_slice(), &off, limit)
        },
    };
    match px {
        Ok(v) => Ok((hdr, v)),
        Err(e) => Err(e),
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
