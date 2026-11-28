//! The unverified glue: imgproxy-style URLs, signature checking, choosing
//! a decoder, fetching sources, and the pipeline that calls the verified
//! functions. Plain safe Rust; the trust it needs is listed in TRUST.md.
//!
//! Every call into a verified function is guarded here by a run-time
//! check of that function's `requires` clause (Verus does not check the
//! callers that are not verified), marked "pre:" below.
use crate::fit::{plan_x, Mode};
pub use crate::spec_geom::{GKind, Geo, Gravity};
pub use crate::spec_url::{Filter, Format, Kind, Options};

/// `spec_url::geo`: the geometry options.
pub fn geo(o: &Options) -> Geo {
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

/// `geom::geo_ok`, checked at run time.
pub fn geo_ok(g: &Geo) -> bool {
    let off = |g: &Gravity| (-65535..=65535).contains(&g.x) && (-65535..=65535).contains(&g.y);
    g.w <= MAX_DIM
        && g.h <= MAX_DIM
        && (1..=80000).contains(&g.dpr)
        && g.crop_w <= 655_359_999
        && g.crop_h <= 655_359_999
        && off(&g.gravity)
        && g.crop_g.as_ref().map_or(true, off)
        && g.extend_g.as_ref().map_or(true, off)
        && g.pad.iter().all(|&v| v <= MAX_DIM)
}
pub use crate::url::{jpeg_shrink_x as jpeg_shrink, Fail, Source};
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

/// The largest width or height anything here handles (`spec::MAX_DIM`).
pub const MAX_DIM: u32 = 65535;

impl Fail {
    pub fn status(&self) -> u16 {
        match self {
            Fail::BadUrl(_) => 400,
            Fail::Forbidden => 403,
            Fail::NotFound | Fail::Expired => 404,
            Fail::Unsupported => 415,
            Fail::Unprocessable(_) => 422,
            Fail::BadGateway(_) => 502,
        }
    }
    pub fn message(&self) -> &'static str {
        match self {
            Fail::BadUrl(m) | Fail::Unprocessable(m) | Fail::BadGateway(m) => m,
            Fail::Forbidden => "Invalid signature",
            Fail::NotFound => "Source not found",
            Fail::Expired => "Expired URL",
            Fail::Unsupported => "Source image type not supported",
        }
    }
}

// ---------------------------------------------------------------------------
// URLs
// ---------------------------------------------------------------------------

/// Fixed-point (`KONE` = 16384) samples of `f` every 1/256 over `[0, a)`.
fn table(a: usize, f: impl Fn(f64) -> f64) -> Vec<i32> {
    (0..a * 256).map(|j| (f(j as f64 / 256.0) * 16384.0).round().clamp(-32768.0, 32768.0) as i32).collect()
}

fn sinc(x: f64) -> f64 {
    if x == 0.0 {
        1.0
    } else {
        let p = std::f64::consts::PI * x;
        p.sin() / p
    }
}

/// The kernel table for a filter (`None` for `Area`). The tables only
/// decide how the result looks: `lanczos::thumb_rgba` is proven to compute
/// `spec_lanczos::thumb` for every table.
pub fn kernel(f: Filter) -> Option<&'static [i32]> {
    use std::sync::OnceLock;
    static T: [OnceLock<Vec<i32>>; 5] = [OnceLock::new(), OnceLock::new(), OnceLock::new(), OnceLock::new(), OnceLock::new()];
    let (i, a, k): (usize, usize, fn(f64) -> f64) = match f {
        Filter::Lanczos3 => (0, 3, |x| sinc(x) * sinc(x / 3.0)),
        Filter::Lanczos2 => (1, 2, |x| sinc(x) * sinc(x / 2.0)),
        Filter::Cubic => (2, 2, |x| {
            if x < 1.0 {
                1.5 * x * x * x - 2.5 * x * x + 1.0
            } else {
                -0.5 * x * x * x + 2.5 * x * x - 4.0 * x + 2.0
            }
        }),
        Filter::Linear => (3, 1, |x| 1.0 - x),
        Filter::Nearest => (4, 1, |x| if x < 0.5 { 1.0 } else if x == 0.5 { 0.5 } else { 0.0 }),
        Filter::Area => return None,
    };
    Some(T[i].get_or_init(|| table(a, k)).as_slice())
}

impl Default for Options {
    fn default() -> Self {
        crate::url::defaults_x()
    }
}

impl Format {
    pub fn mime(self) -> &'static [u8] {
        self.kind().mime()
    }
    pub fn kind(self) -> Kind {
        match self {
            Format::Png => Kind::Png,
            Format::Jpeg => Kind::Jpeg,
        }
    }
}

impl Kind {
    pub fn mime(self) -> &'static [u8] {
        match self {
            Kind::Png => b"image/png",
            Kind::Jpeg => b"image/jpeg",
            Kind::Webp => b"image/webp",
            Kind::Gif => b"image/gif",
        }
    }
    pub fn ext(self) -> &'static [u8] {
        match self {
            Kind::Png => b"png",
            Kind::Jpeg => b"jpg",
            Kind::Webp => b"webp",
            Kind::Gif => b"gif",
        }
    }
    /// `spec_url::kind_bit`: its bit in `Options::skip`.
    pub fn bit(self) -> u32 {
        crate::url::kind_bit_x(self)
    }
}

/// The `Content-Disposition` value: `inline` (or `attachment` with
/// `return_attachment`), and a file name, as imgproxy gives it: the
/// `filename` option's, else the source's last path segment without its
/// extension, else `image`; then the result's extension. The name is made
/// safe for a header: control bytes are dropped, and `"`, `\`, `%` and
/// non-ASCII bytes are percent-encoded.
pub fn disposition(filename: Option<&[u8]>, source: &Source, attachment: bool, k: Option<Kind>) -> Vec<u8> {
    let from_source = |u: &[u8]| -> Vec<u8> {
        let u = u.split(|&c| c == b'?' || c == b'#').next().unwrap_or(&[]);
        let last = u.rsplit(|&c| c == b'/').next().unwrap_or(&[]);
        let stem = match last.iter().rposition(|&c| c == b'.') {
            Some(i) => &last[..i],
            None => last,
        };
        let mut d = Vec::new();
        verilith_text::percent::decode_to(stem, &mut d);
        d
    };
    let name = match (filename, source) {
        (Some(f), _) if !f.is_empty() => f.to_vec(),
        (_, Source::Local(p)) => from_source(p),
        (_, Source::Http(u)) => from_source(u.splitn(4, |&c| c == b'/').nth(3).unwrap_or(&[])),
        (_, Source::Upload) => Vec::new(),
    };
    let name = if name.is_empty() { b"image".to_vec() } else { name };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(if attachment { b"attachment" } else { b"inline" });
    v.extend_from_slice(b"; filename=\"");
    for &c in &name {
        match c {
            0..=0x1f | 0x7f => {}
            b'"' | b'\\' | b'%' | 0x80..=0xff => v.extend_from_slice(format!("%{c:02X}").as_bytes()),
            _ => v.push(c),
        }
    }
    if let Some(k) = k {
        v.push(b'.');
        v.extend_from_slice(k.ext());
    }
    v.push(b'"');
    v
}

/// Lays the watermark over the `w` by `h` result: scaled to `wm_scale` of
/// the result's width if asked, and down to fit inside it if larger
/// (keeping its shape, with the verified thumbnailer), then placed at
/// `wm_g` (offsets times `dpr`) or tiled (`wm_g`'s offsets, times `dpr`,
/// as the spacing), at `wm_op` opacity, by `geom::watermark_rgba`.
fn watermark(px: Vec<u8>, w: u32, h: u32, wm: &Rgba, o: &Options) -> Result<Vec<u8>, Fail> {
    let bad = Fail::Unprocessable("Watermark is invalid");
    // pre: thumb_rgba, wm_at_x and watermark_rgba (sizes in 1..=MAX_DIM,
    // whole pixels; offsets within 65535 and dpr at most 80000, as geo_ok
    // checks; opacity at most F1).
    if wm.w == 0 || wm.h == 0 || wm.w > MAX_DIM || wm.h > MAX_DIM || wm.px.len() != wm.w as usize * wm.h as usize * 4 {
        return Err(bad);
    }
    if !(1..=80000).contains(&o.dpr) || o.wm_g.x.unsigned_abs() > 65535 || o.wm_g.y.unsigned_abs() > 65535 || o.wm_op > 10000 {
        return Err(bad);
    }
    let (mut ww, mut wh) = (wm.w as u64, wm.h as u64);
    if o.wm_scale > 0 {
        let tw = ((w as u64 * o.wm_scale as u64 + 5000) / 10000).max(1);
        wh = ((wh * tw + ww / 2) / ww).max(1);
        ww = tw;
    }
    if ww > w as u64 || wh > h as u64 {
        // Down to fit, keeping the shape: the smaller of the two ratios.
        if ww * h as u64 > wh * w as u64 {
            wh = ((wh * w as u64 + ww / 2) / ww).max(1);
            ww = w as u64;
        } else {
            ww = ((ww * h as u64 + wh / 2) / wh).max(1);
            wh = h as u64;
        }
    }
    let (ww, wh) = (ww.clamp(1, MAX_DIM as u64) as u32, wh.clamp(1, MAX_DIM as u64) as u32);
    let img = if (ww, wh) == (wm.w, wm.h) {
        std::borrow::Cow::Borrowed(&wm.px)
    } else {
        let kt = kernel(Filter::Lanczos3).ok_or(bad.clone())?;
        std::borrow::Cow::Owned(crate::lanczos::thumb_rgba(kt, &wm.px, wm.w as usize, wm.h as usize, ww as usize, wh as usize))
    };
    let (ww, wh) = (ww.min(w), wh.min(h));
    let dmul = |v: i32| ((2 * v.max(0) as i64 * o.dpr as i64 + 10000) / 20000) as usize;
    let (x, y, pw, ph) = if o.wm_tile {
        (0, 0, (ww as usize + dmul(o.wm_g.x)).min(2 * MAX_DIM as usize), (wh as usize + dmul(o.wm_g.y)).min(2 * MAX_DIM as usize))
    } else {
        let (x, y) = crate::geom::wm_at_x(w, h, ww, wh, o.wm_g, o.dpr);
        (x as usize, y as usize, 1, 1)
    };
    Ok(crate::geom::watermark_rgba(&px, w as usize, h as usize, &img, ww as usize, wh as usize, x, y, o.wm_tile, pw, ph, o.wm_op))
}

/// libvips's attention point of `px` (`w` by `h`) for a `cw` by `ch`
/// crop: the first highest value of `attention::attention`'s map
/// (`smart::first_max_x`), mapped back to the image (`x_pos / hscale`,
/// truncated, as `smartcrop.c` does).
pub fn attention_point(px: &[u8], w: usize, h: usize, alpha: bool, cw: usize, ch: usize, exact_shrink: bool) -> (usize, usize) {
    let (m, sw, _sh, hs, vs) = crate::attention::attention(px, w, h, alpha, cw, ch, exact_shrink);
    let bits: Vec<u32> = m.iter().map(|v| v.to_bits()).collect();
    // pre: first_max_x (the map has a value for each of its 1 or more pixels).
    let best = crate::smart::first_max_x(&bits);
    (((best % sw) as f64 / hs) as usize, ((best / sw) as f64 / vs) as usize)
}

/// imgproxy's `SmartCrop` (`vips_smartcrop`, attention): where a `cw` by
/// `ch` crop of `px` (`w` by `h`) starts. Nothing to choose when the crop
/// is the whole image.
pub fn smart_crop(px: &[u8], w: usize, h: usize, alpha: bool, cw: usize, ch: usize) -> (usize, usize) {
    if cw >= w && ch >= h {
        return (0, 0);
    }
    let (ax, ay) = attention_point(px, w, h, alpha, cw, ch, false);
    // pre: centred_x (sizes and the point below 2^32; the crop inside).
    let c = |a: usize, s: usize, c: usize| crate::smart::centred_x(a.min(1 << 32) as u64, s as u64, c.min(s) as u64) as usize;
    (c(ax, w, cw), c(ay, h, ch))
}

/// Whether libvips would see an alpha band in the source: PNG says so
/// in its header (a colour type with alpha, or a `tRNS` chunk); JPEG has
/// none; for the other formats, whether any pixel is not opaque.
fn has_alpha(data: &[u8], px: &[u8]) -> bool {
    if data.starts_with(b"\x89PNG\r\n\x1a\n") {
        if data.len() > 25 && (data[25] == 4 || data[25] == 6) {
            return true;
        }
        let mut i = 8;
        while i + 8 <= data.len() {
            let n = u32::from_be_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]) as usize;
            match &data[i + 4..i + 8] {
                b"tRNS" => return true,
                b"IDAT" => return false,
                _ => {}
            }
            i = i.saturating_add(12).saturating_add(n);
        }
        false
    } else if data.starts_with(&[0xFF, 0xD8]) {
        false
    } else {
        px.chunks_exact(4).any(|p| p[3] != 255)
    }
}

/// imgproxy's `IMGPROXY_QUALITY` default.
pub const DEFAULT_QUALITY: u32 = 80;

/// A parsed request URL.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed<'a> {
    pub signature: &'a [u8],
    /// What the signature signs: the path from the `/` after it.
    pub signed: &'a [u8],
    pub opts: Options,
    pub source: Source,
    /// `filename`, decoded.
    pub filename: Option<Vec<u8>>,
}

/// Parses `/%signature/%options/plain/%url[@%ext]`,
/// `/%signature/%options/%base64_url[.%ext]` or
/// `/%signature/%options/upload[@%ext]`: `url::parse_x`, which is proven
/// to compute `spec_url::parse`.
pub fn parse(path: &[u8]) -> Result<Parsed<'_>, Fail> {
    let u = crate::url::parse_x(path)?;
    Ok(Parsed { signature: &path[1..u.sig_end], signed: &path[u.sig_end..], opts: u.opts, source: u.source, filename: u.filename })
}

// ---------------------------------------------------------------------------
// Signatures
// ---------------------------------------------------------------------------

/// The URL signing key and salt (imgproxy's `IMGPROXY_KEY` and
/// `IMGPROXY_SALT`, hex). With no key, any signature is accepted.
#[derive(Clone, Default)]
pub struct Keys {
    pub key: Vec<u8>,
    pub salt: Vec<u8>,
}

pub fn unhex(s: &str) -> Option<Vec<u8>> {
    let b = s.trim().as_bytes();
    if b.len() % 2 != 0 {
        return None;
    }
    let h = |c: u8| crate::url::hexv_x(c);
    b.chunks(2).map(|p| if h(p[0]) < 0 || h(p[1]) < 0 { None } else { Some((16 * h(p[0]) + h(p[1])) as u8) }).collect()
}

/// Whether `sig` is base64url(HMAC-SHA256(key, salt || signed)), compared
/// in constant time by verilith-sha2's verified `verify`.
pub fn check(keys: &Keys, sig: &[u8], signed: &[u8]) -> bool {
    if keys.key.is_empty() {
        return true;
    }
    let Ok(tag) = verilith_text::base64::URL_SAFE_NO_PAD.decode(sig.strip_suffix(b"=").unwrap_or(sig)) else {
        return false;
    };
    let mut m = verilith_sha2::hmac::HmacSha256::new(&keys.key);
    m.update(&keys.salt);
    m.update(signed);
    m.verify(&tag)
}

/// The signature of `path` (for tests and for clients).
pub fn sign(keys: &Keys, path: &[u8]) -> String {
    let mut m = verilith_sha2::hmac::HmacSha256::new(&keys.key);
    m.update(&keys.salt);
    m.update(path);
    verilith_text::base64::URL_SAFE_NO_PAD.encode(m.finalize())
}

// ---------------------------------------------------------------------------
// Decoding
// ---------------------------------------------------------------------------

/// An RGBA image.
pub struct Rgba {
    pub w: u32,
    pub h: u32,
    pub px: Vec<u8>,
}

fn be32(b: &[u8], i: usize) -> Option<u32> {
    Some(u32::from_be_bytes(b.get(i..i + 4)?.try_into().ok()?))
}

fn size_ok(w: u64, h: u64, max_px: u64) -> Result<(), Fail> {
    if w == 0 || h == 0 || w > MAX_DIM as u64 || h > MAX_DIM as u64 {
        return Err(Fail::Unprocessable("Source image size not supported"));
    }
    if w * h > max_px {
        return Err(Fail::Unprocessable("Source image resolution is too big"));
    }
    Ok(())
}

/// The width and height a file's header gives, if it is a JPEG, PNG, WebP
/// or GIF file whose header can be read.
pub fn dims(data: &[u8]) -> Option<(u32, u32)> {
    let k = crate::url::kind_x(data);
    if k == Some(Kind::Jpeg) {
        let hd = verilith_jpeg::decode::read_header(data).ok()?;
        Some((hd.w as u32, hd.h as u32))
    } else if k == Some(Kind::Png) {
        Some((be32(data, 16)?, be32(data, 20)?))
    } else if k == Some(Kind::Webp) {
        let f = verilith_webp::capi::get_features(data).ok()?;
        Some((f.width as u32, f.height as u32))
    } else if k == Some(Kind::Gif) {
        Some((u16::from_le_bytes([*data.get(6)?, *data.get(7)?]) as u32, u16::from_le_bytes([*data.get(8)?, *data.get(9)?]) as u32))
    } else {
        None
    }
}

/// Decodes a JPEG, PNG, WebP or GIF file to RGBA, refusing images with
/// more than `max_px` pixels before decoding them.
pub fn decode(data: &[u8], max_px: u64) -> Result<Rgba, Fail> {
    decode_shrunk(data, max_px, 1)
}

/// `decode`, with a JPEG decoded at `1 / shrink` of its size (`shrink` 1,
/// 2, 4 or 8; other formats ignore it).
pub fn decode_shrunk(data: &[u8], max_px: u64, shrink: u32) -> Result<Rgba, Fail> {
    let bad = Fail::Unprocessable("Source image is invalid");
    // The format, from the first bytes: `url::kind_x`, proven to compute
    // `spec_url::kind`.
    let k = crate::url::kind_x(data);
    if k == Some(Kind::Jpeg) {
        let hd = verilith_jpeg::decode::read_header(data).map_err(|_| bad.clone())?;
        size_ok(hd.w as u64, hd.h as u64, max_px)?;
        let pic = match shrink {
            // pre: decode_scaled (m is 1, 2 or 4)
            8 => verilith_jpeg::decode_scaled(data, 1),
            4 => verilith_jpeg::decode_scaled(data, 2),
            2 => verilith_jpeg::decode_scaled(data, 4),
            _ => verilith_jpeg::decode::decode(data),
        }
        .map_err(|_| bad.clone())?;
        let nc = pic.nc as usize;
        // pre: expand
        if (nc != 1 && nc != 3) || pic.px.len() != pic.w as usize * pic.h as usize * nc {
            return Err(Fail::Unsupported);
        }
        let px = crate::pixels::expand(&pic.px, nc).ok_or(Fail::Unprocessable("Out of memory"))?;
        Ok(Rgba { w: pic.w, h: pic.h, px })
    } else if k == Some(Kind::Png) {
        let (w, h) = (be32(data, 16).ok_or(bad.clone())?, be32(data, 20).ok_or(bad.clone())?);
        size_ok(w as u64, h as u64, max_px)?;
        let limit = (max_px as usize).saturating_mul(8).saturating_add(1 << 20);
        let (hd, px) = verilith_png::top::decode(data, verilith_png::top::PixelFormat::Rgba8, limit).map_err(|e| match e {
            verilith_png::decode::Error::TooLarge => Fail::Unprocessable("Source image resolution is too big"),
            _ => bad.clone(),
        })?;
        Ok(Rgba { w: hd.width, h: hd.height, px })
    } else if k == Some(Kind::Webp) {
        let f = verilith_webp::capi::get_features(data).map_err(|_| bad.clone())?;
        size_ok(f.width as u64, f.height as u64, max_px)?;
        let img = verilith_webp::capi::decode(data).map_err(|_| bad.clone())?;
        // pre: from_argb (a Vec's length times 4 fits in usize: it is a u32 vector)
        let px = crate::pixels::from_argb(&img.argb);
        Ok(Rgba { w: img.width as u32, h: img.height as u32, px })
    } else if k == Some(Kind::Gif) {
        let w = u16::from_le_bytes([data.get(6).copied().ok_or(bad.clone())?, data.get(7).copied().ok_or(bad.clone())?]);
        let h = u16::from_le_bytes([data.get(8).copied().ok_or(bad.clone())?, data.get(9).copied().ok_or(bad.clone())?]);
        size_ok(w as u64, h as u64, max_px)?;
        let g = verilith_gif::decode::decode(data, (max_px as usize).saturating_mul(2)).map_err(|_| bad.clone())?;
        let f = g.frames.first().ok_or(bad.clone())?;
        let table: &[u8] = f.lct.as_deref().or(g.gct.as_deref()).unwrap_or(&[]);
        let tr = f.gce.and_then(|c| c.transparent);
        if f.width == 0 || f.height == 0 || f.pixels.len() != f.width as usize * f.height as usize {
            return Err(bad);
        }
        // pre: from_indexed (a pixel count of at most 65535^2)
        let px = crate::pixels::from_indexed(&f.pixels, table, tr);
        Ok(Rgba { w: f.width as u32, h: f.height as u32, px })
    } else {
        Err(Fail::Unsupported)
    }
}

// ---------------------------------------------------------------------------
// The pipeline
// ---------------------------------------------------------------------------

/// Limits, as imgproxy's settings of the same names.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// `IMGPROXY_MAX_SRC_RESOLUTION`, in pixels.
    pub max_src_px: u64,
    /// The largest result, in pixels.
    pub max_out_px: u64,
    /// `IMGPROXY_MAX_SRC_FILE_SIZE`, in bytes.
    pub max_src_bytes: usize,
    /// zlib level for PNG output.
    pub level: u32,
    /// Seconds to wait for an origin (`IMGPROXY_DOWNLOAD_TIMEOUT`).
    pub timeout: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Limits { max_src_px: 50_000_000, max_out_px: 50_000_000, max_src_bytes: 64 << 20, level: 6, timeout: 5 }
    }
}

/// Decodes, resizes, crops, flattens and encodes: the image to send.
pub fn process(data: &[u8], o: &Options, lim: &Limits) -> Result<Vec<u8>, Fail> {
    process_with(data, o, lim, None)
}

/// `process`, with the watermark image (`IMGPROXY_WATERMARK_PATH`) that
/// the `watermark` option lays over the result.
pub fn process_with(data: &[u8], o: &Options, lim: &Limits, wm: Option<&Rgba>) -> Result<Vec<u8>, Fail> {
    let too_big = Fail::Unprocessable("Result image is too big");
    // The plan is made from the size the header gives, so that shrinking a
    // JPEG on load changes only how the pixels are computed, not the
    // result's size. The plan is on the image as rotated (odd quarter
    // turns swap the sides), as the URL's sizes are.
    // `auto_rotate`: the EXIF orientation turns the image upright first,
    // then `rotate` and `flip` apply.
    let (w0, h0) = dims(data).ok_or(Fail::Unsupported)?;
    let orient = if o.auto_rotate { crate::exif::orientation_x(data) } else { 1 };
    let (eq, efh, efv) = crate::exif::upright_x(orient);
    let turned = o.rotate != 0 || o.flip_h || o.flip_v;
    let odd = (eq + o.rotate) % 2 == 1;
    let (ow0, oh0) = if odd { (h0, w0) } else { (w0, h0) };
    let g = geo(o);
    // pre: geom_x (sizes at most MAX_DIM; geo_ok holds for whatever
    // url::parse_x returns, and is checked here for other callers).
    if w0 == 0 || h0 == 0 || w0 > MAX_DIM || h0 > MAX_DIM || !geo_ok(&g) || o.rotate > 3 {
        return Err(Fail::Unprocessable("Source image size not supported"));
    }
    let mut p = crate::geom::geom_x(ow0, oh0, g, lim.max_out_px).ok_or(too_big.clone())?;
    let full = (p.x0, p.y0, p.cw0, p.ch0) == (0, 0, ow0, oh0);
    let shrink = if full { jpeg_shrink(ow0, oh0, p.rw, p.rh) } else { 1 };
    let img = decode_shrunk(data, lim.max_src_px, shrink)?;
    // pre: turn_rgba, geom_x and the resizers (sizes in 1..=MAX_DIM, a
    // whole number of pixels).
    if img.w == 0 || img.h == 0 || img.w > MAX_DIM || img.h > MAX_DIM || img.px.len() != img.w as usize * img.h as usize * 4 {
        return Err(Fail::Unprocessable("Source image is invalid"));
    }
    let (iw, ih) = (img.w as usize, img.h as usize);
    // pre: turn_rgba (q at most 3: upright_x and the check above).
    let px = if orient != 1 { crate::geom::turn_rgba(&img.px, iw, ih, eq, efh, efv) } else { img.px };
    let (iw, ih) = if eq % 2 == 1 { (ih, iw) } else { (iw, ih) };
    let px = if turned { crate::geom::turn_rgba(&px, iw, ih, o.rotate, o.flip_h, o.flip_v) } else { px };
    let (sw, sh) = if o.rotate % 2 == 1 { (ih, iw) } else { (iw, ih) };
    // A GIF's first frame can be smaller than its screen: plan from the frame.
    if shrink == 1 && (sw as u32, sh as u32) != (ow0, oh0) {
        p = crate::geom::geom_x(sw as u32, sh as u32, g, lim.max_out_px).ok_or(too_big.clone())?;
    }
    // Smart gravity, as imgproxy runs it: the `crop` option's on the
    // source, the result's on the image as resized (below).
    let sm = |g: &Gravity| g.kind == GKind::Sm;
    let alpha = has_alpha(data, &px);
    let crop_sm = g.crop_g.as_ref().map_or(sm(&g.gravity), sm);
    if crop_sm && shrink == 1 {
        let (x, y) = smart_crop(&px, sw, sh, alpha, p.cw0 as usize, p.ch0 as usize);
        p.x0 = x as u32;
        p.y0 = y as u32;
    }
    // Shrunk on load (only when the crop is the whole image): the crop is
    // the whole of what was decoded.
    let (x0, y0, cw0, ch0) =
        if shrink == 1 { (p.x0 as usize, p.y0 as usize, p.cw0 as usize, p.ch0 as usize) } else { (0, 0, sw, sh) };
    // pre: crop_rgba (geom_x ensures the rectangle is inside).
    let px = if (x0, y0, cw0, ch0) == (0, 0, sw, sh) { px } else { crate::resize::crop_rgba(&px, sw, sh, x0, y0, cw0, ch0) };
    let (rw, rh) = (p.rw as usize, p.rh as usize);
    // pre: resize_rgba and thumb_rgba (all sizes in 1..=MAX_DIM, ensured
    // by geom_x; the products are below 2^34 on a 64-bit target; kernel's
    // tables are 256 to 768 entries of at most 32768 in size).
    let px = if (rw, rh) == (cw0, ch0) {
        px
    } else {
        match kernel(o.filter) {
            Some(kt) => crate::lanczos::thumb_rgba(kt, &px, cw0, ch0, rw, rh),
            None => crate::resize::resize_rgba(&px, cw0, ch0, rw, rh),
        }
    };
    if sm(&g.gravity) {
        let (x, y) = smart_crop(&px, rw, rh, alpha, p.cw as usize, p.ch as usize);
        p.cx = x as u32;
        p.cy = y as u32;
    }
    // pre: crop_rgba (geom_x ensures the rectangle is inside; smart_crop's
    // centred_x keeps it so).
    let px = if (p.cx, p.cy, p.cw, p.ch) == (0, 0, p.rw, p.rh) {
        px
    } else {
        crate::resize::crop_rgba(&px, rw, rh, p.cx as usize, p.cy as usize, p.cw as usize, p.ch as usize)
    };
    // imgproxy's `vips_apply_filters`, on the cropped image, before
    // `extend` and `padding`: premultiplied alpha (for blur and sharpen
    // only, as imgproxy does it), `blur`, `sharpen`, `pixelate`, then
    // back. On an opaque image premultiplying changes nothing.
    // pre: blur_rgba, pixelate_rgba (mask::gaussblur's
    // tables are 1 to 9999 entries, odd, each at most 127 or 20; divisors
    // 2 to 2^31; sizes in 1..=MAX_DIM).
    let (fw, fh) = (p.cw as usize, p.ch as usize);
    let sigma = |v: u32| v as f64 / 10000.0;
    let bad = || Fail::Unprocessable("Blur or sharpen sigma out of range");
    let blur = if o.blur > 0 { crate::mask::gaussblur(sigma(o.blur)).map_err(|_| bad())? } else { None };
    let pre = o.blur > 0 || o.sharpen > 0;
    let px = if pre { crate::filter::premul_rgba(&px) } else { px };
    let px = match &blur {
        Some((g, d)) => crate::filter::blur_rgba(g, *d, &px, fw, fh),
        None => px,
    };
    // `vips_sharpen`: on the lightness of Lab, as libvips does it.
    let px = if o.sharpen > 0 { crate::colour::sharpen_rgba(&px, fw, fh, sigma(o.sharpen)).ok_or_else(bad)? } else { px };
    let px = crate::filter::pixelate_rgba(px, fw, fh, o.pixelate as usize);
    let px = if pre { crate::filter::unpremul_rgba(&px) } else { px };
    // pre: embed_rgba (geom_x ensures the image is inside the canvas).
    // `extend` and `padding` fill with the background, or transparency.
    let (cw, ch) = (p.canvas_w, p.canvas_h);
    let px = if (cw, ch) == (p.cw, p.ch) {
        px
    } else {
        let fill = match o.background {
            Some([r, g, b]) => [r, g, b, 255],
            None => [0, 0, 0, 0],
        };
        crate::geom::embed_rgba(&px, p.cw as usize, p.ch as usize, cw as usize, ch as usize, p.ax as usize, p.ay as usize, fill)
    };
    // pre: flatten (a whole number of pixels). JPEG has no alpha: it is
    // flattened onto the background, white by default, as imgproxy does.
    let bg = match o.format {
        Format::Jpeg => Some(o.background.unwrap_or([255, 255, 255])),
        Format::Png => o.background,
    };
    let px = match bg {
        Some(bg) => crate::pixels::flatten(&px, bg),
        None => px,
    };
    // `watermark`, last, as imgproxy lays it.
    let px = match wm {
        Some(wm) if o.wm_op > 0 => watermark(px, cw, ch, wm, o)?,
        _ => px,
    };
    match o.format {
        // pre: encode_rgba (sizes at most MAX_DIM).
        Format::Png => {
            crate::pngenc::encode_rgba(&px, cw, ch, lim.level).ok_or(Fail::Unprocessable("Result image is too big"))
        }
        // encode_rgb checks its input itself. Chroma is subsampled below
        // quality 90, as libvips (imgproxy's encoder) does by default.
        Format::Jpeg => {
            let q = if o.quality == 0 { DEFAULT_QUALITY } else { o.quality };
            verilith_jpeg::encode::encode_rgb(&px, cw as usize, ch as usize, 4, q as u8, q < 90)
                .ok_or(Fail::Unprocessable("Result image is too big for JPEG"))
        }
    }
}

// ---------------------------------------------------------------------------
// Sources
// ---------------------------------------------------------------------------

/// Reads `local:///path` beneath `root`: the path is resolved by
/// verilith-server's verified `path::resolve_exec` (no `.`, `..` or empty
/// component survives), hidden files are refused, and the file is opened
/// with `openat2(RESOLVE_BENEATH)` (or one component at a time without
/// following symlinks).
pub fn read_local(root: &std::fs::File, path: &[u8], max: usize) -> Result<Vec<u8>, Fail> {
    let Some((comps, dir)) = verilith_server::path::resolve_exec(path) else { return Err(Fail::NotFound) };
    if dir || comps.is_empty() || comps.iter().any(|c| verilith_server::path::hidden(c)) {
        return Err(Fail::NotFound);
    }
    let mut rel = Vec::with_capacity(path.len());
    verilith_server::path::join_to(&comps, &mut rel);
    let f = verilith_server::sys::open_beneath(root, &rel).map_err(|_| Fail::NotFound)?;
    let m = f.metadata().map_err(|_| Fail::NotFound)?;
    if !m.is_file() {
        return Err(Fail::NotFound);
    }
    if m.len() > max as u64 {
        return Err(Fail::Unprocessable("Source image file is too big"));
    }
    let mut out = Vec::with_capacity(m.len() as usize);
    f.take(max as u64 + 1).read_to_end(&mut out).map_err(|_| Fail::NotFound)?;
    if out.len() > max {
        return Err(Fail::Unprocessable("Source image file is too big"));
    }
    Ok(out)
}

/// How `https://` sources are fetched: verilith-tls's verified TLS 1.3
/// client (with aws-lc's cryptography), configured with the trust anchors
/// from [`load_roots`]. Without the `tls` feature there is none, and
/// `https://` sources fail.
#[cfg(feature = "tls")]
pub type Tls = std::sync::Arc<verilith_tls::client_hs::ClientConfig>;
#[cfg(not(feature = "tls"))]
#[derive(Clone, Debug)]
pub enum Tls {}

/// The client configuration for `https://` sources, trusting `roots`
/// (DER certificates).
#[cfg(feature = "tls")]
pub fn tls_config(roots: Vec<Vec<u8>>) -> Tls {
    std::sync::Arc::new(verilith_tls_aws_lc::client::config(roots, &[b"http/1.1"]))
}

/// Where the system's trust anchors usually are (`SSL_CERT_FILE` wins).
pub const CA_BUNDLES: &[&str] = &[
    "/etc/ssl/certs/ca-certificates.crt",
    "/etc/pki/tls/certs/ca-bundle.crt",
    "/etc/ssl/ca-bundle.pem",
    "/etc/ssl/cert.pem",
];

/// The DER certificates in a PEM file.
pub fn pem_certs(text: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut b64 = Vec::new();
    let mut inside = false;
    for line in text.split(|&c| c == b'\n') {
        let l = line.trim_ascii();
        if l == b"-----BEGIN CERTIFICATE-----" {
            inside = true;
            b64.clear();
        } else if l == b"-----END CERTIFICATE-----" {
            if inside {
                if let Ok(d) = verilith_text::base64::STANDARD.decode(&b64) {
                    out.push(d);
                }
            }
            inside = false;
        } else if inside {
            b64.extend_from_slice(l);
        }
    }
    out
}

/// The trust anchors for `https://` sources: the certificates in `path`,
/// or else in `$SSL_CERT_FILE`, or else in the first of [`CA_BUNDLES`]
/// that exists. Fails if there are none.
pub fn load_roots(path: Option<&str>) -> std::io::Result<(String, Vec<Vec<u8>>)> {
    let env = std::env::var("SSL_CERT_FILE").ok().filter(|v| !v.is_empty());
    let p = match path.map(str::to_string).or(env) {
        Some(p) => p,
        None => CA_BUNDLES
            .iter()
            .find(|p| std::path::Path::new(p).exists())
            .map(|p| p.to_string())
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "no CA bundle found"))?,
    };
    let roots = pem_certs(&std::fs::read(&p)?);
    if roots.is_empty() {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{p}: no certificates")));
    }
    Ok((p, roots))
}

/// A source URL split up: whether it is `https`, the host, the port and
/// the request target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin {
    pub https: bool,
    pub host: String,
    pub port: u16,
    pub target: Vec<u8>,
}

/// Splits `http[s]://host[:port]/path`. An `https` host must be a DNS
/// name (the TLS client checks the certificate against names only).
pub fn split_http(url: &[u8]) -> Result<Origin, Fail> {
    let (https, rest) = match url.strip_prefix(b"https://") {
        Some(r) => (true, r),
        None => (false, url.strip_prefix(b"http://").ok_or(Fail::BadUrl("Invalid source URL"))?),
    };
    let end = rest.iter().position(|&c| c == b'/' || c == b'?' || c == b'#').unwrap_or(rest.len());
    let auth = &rest[..end];
    let mut target = rest[end..].to_vec();
    if let Some(h) = target.iter().position(|&c| c == b'#') {
        target.truncate(h);
    }
    if target.is_empty() || target[0] != b'/' {
        target.insert(0, b'/');
    }
    if auth.contains(&b'@') || target.iter().any(|&c| c <= b' ' || c >= 0x7f) {
        return Err(Fail::BadUrl("Invalid source URL"));
    }
    let (host, port) = match auth.iter().rposition(|&c| c == b':') {
        Some(i) if !auth.ends_with(b"]") => {
            let p = std::str::from_utf8(&auth[i + 1..]).ok().and_then(|p| p.parse().ok()).ok_or(Fail::BadUrl("Invalid port"))?;
            (&auth[..i], p)
        }
        _ => (auth, if https { 443 } else { 80 }),
    };
    let host = std::str::from_utf8(host).map_err(|_| Fail::BadUrl("Invalid host"))?;
    if host.is_empty() || !host.bytes().all(|c| c.is_ascii_alphanumeric() || b".-[]:".contains(&c)) {
        return Err(Fail::BadUrl("Invalid host"));
    }
    if https && (host.starts_with('[') || host.parse::<std::net::Ipv4Addr>().is_ok()) {
        return Err(Fail::BadUrl("https sources need a host name, not an IP address"));
    }
    Ok(Origin { https, host: host.to_string(), port, target })
}

/// Fetches an `http://` or `https://` URL with one HTTP/1.1 GET. The
/// response head and its body framing (Content-Length, chunked, or until
/// close) are parsed by verilith-http's verified parser; `https://` goes
/// through `tls`, which checks the origin's certificate chain and name.
pub fn fetch(url: &[u8], lim: &Limits, tls: Option<&Tls>) -> Result<Vec<u8>, Fail> {
    let o = split_http(url)?;
    if o.https && tls.is_none() {
        return Err(Fail::BadUrl("https sources are not enabled"));
    }
    let t = Duration::from_secs(lim.timeout.max(1));
    let addr = (o.host.trim_matches(|c| c == '[' || c == ']'), o.port)
        .to_socket_addrs()
        .ok()
        .and_then(|mut a| a.next())
        .ok_or(Fail::BadGateway("Cannot resolve origin"))?;
    let s = TcpStream::connect_timeout(&addr, t).map_err(|_| Fail::BadGateway("Cannot connect to origin"))?;
    let _ = s.set_read_timeout(Some(t));
    let _ = s.set_write_timeout(Some(t));
    let _ = s.set_nodelay(true);
    match tls {
        #[cfg(feature = "tls")]
        Some(cfg) if o.https => {
            let s = verilith_tls_aws_lc::client::TlsStream::connect(cfg.clone(), &o.host, s)
                .map_err(|_| Fail::BadGateway("TLS handshake with origin failed"))?;
            get(s, &o, lim)
        }
        _ => get(s, &o, lim),
    }
}

/// The GET itself, over a connected stream.
fn get<S: Read + Write>(mut s: S, o: &Origin, lim: &Limits) -> Result<Vec<u8>, Fail> {
    let mut req = Vec::with_capacity(o.target.len() + o.host.len() + 96);
    req.extend_from_slice(b"GET ");
    req.extend_from_slice(&o.target);
    req.extend_from_slice(b" HTTP/1.1\r\nHost: ");
    req.extend_from_slice(o.host.as_bytes());
    if o.port != if o.https { 443 } else { 80 } {
        req.extend_from_slice(format!(":{}", o.port).as_bytes());
    }
    req.extend_from_slice(b"\r\nUser-Agent: verilith-imgproxy\r\nAccept: image/*\r\nConnection: close\r\n\r\n");
    s.write_all(&req).map_err(|_| Fail::BadGateway("Cannot send to origin"))?;
    let _ = s.flush();
    let mut buf: Vec<u8> = Vec::with_capacity(64 << 10);
    let mut chunk = vec![0u8; 64 << 10];
    let mut headers = Vec::new();
    let max_head = 64 << 10;
    loop {
        let n = s.read(&mut chunk).map_err(|_| Fail::BadGateway("Origin read failed"))?;
        if n == 0 {
            return Err(Fail::BadGateway("Origin closed the connection"));
        }
        buf.extend_from_slice(&chunk[..n]);
        match verilith_http::api::parse_response(&buf, false, false, &mut headers) {
            Ok(verilith_http::api::Status::Complete(r)) => {
                if r.status() == 404 || r.status() == 410 {
                    return Err(Fail::NotFound);
                }
                if r.status() != 200 {
                    return Err(Fail::BadGateway("Origin answered with an error"));
                }
                let head = r.head_len;
                let body = r.body;
                let mut data = buf.split_off(head);
                return read_body(&mut s, &mut data, body, &mut chunk, lim.max_src_bytes);
            }
            Ok(verilith_http::api::Status::Partial) if buf.len() < max_head => continue,
            _ => return Err(Fail::BadGateway("Invalid response from origin")),
        }
    }
}

/// Reads the body. A read error ends it as a failure: over TLS, that
/// includes the connection closing without close_notify, which could be
/// an attacker cutting the body short (a body read until close is only
/// complete at a close_notify).
fn read_body<S: Read>(
    s: &mut S,
    data: &mut Vec<u8>,
    body: verilith_http::spec::Body,
    chunk: &mut [u8],
    max: usize,
) -> Result<Vec<u8>, Fail> {
    use verilith_http::spec::Body;
    let too_big = Fail::Unprocessable("Source image file is too big");
    match body {
        Body::Empty => Ok(Vec::new()),
        Body::Length(n) => {
            if n > max as u64 {
                return Err(too_big);
            }
            let n = n as usize;
            while data.len() < n {
                let k = s.read(chunk).map_err(|_| Fail::BadGateway("Origin read failed"))?;
                if k == 0 {
                    return Err(Fail::BadGateway("Origin response was cut short"));
                }
                data.extend_from_slice(&chunk[..k]);
            }
            data.truncate(n);
            Ok(std::mem::take(data))
        }
        Body::Close => {
            loop {
                if data.len() > max {
                    return Err(too_big);
                }
                let k = s.read(chunk).map_err(|_| Fail::BadGateway("Origin read failed"))?;
                if k == 0 {
                    return Ok(std::mem::take(data));
                }
                data.extend_from_slice(&chunk[..k]);
            }
        }
        Body::Chunked => {
            let mut dec = verilith_http::api::ChunkedDecoder::new();
            let mut out = Vec::new();
            loop {
                if !data.is_empty() {
                    match dec.decode(data) {
                        Ok(verilith_http::api::Chunked::More { out: n }) => {
                            out.extend_from_slice(&data[..n]);
                            data.clear();
                        }
                        Ok(verilith_http::api::Chunked::Done { out: n, .. }) => {
                            out.extend_from_slice(&data[..n]);
                            return Ok(out);
                        }
                        Err(_) => return Err(Fail::BadGateway("Invalid chunked body from origin")),
                    }
                }
                if out.len() > max {
                    return Err(too_big);
                }
                let k = s.read(chunk).map_err(|_| Fail::BadGateway("Origin read failed"))?;
                if k == 0 {
                    return Err(Fail::BadGateway("Origin response was cut short"));
                }
                data.extend_from_slice(&chunk[..k]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn more_urls() {
        let p = parse(b"/sig/bg:ff8000/q:90/f:jpg/upload").unwrap();
        assert_eq!((p.signature, p.signed), (&b"sig"[..], &b"/bg:ff8000/q:90/f:jpg/upload"[..]));
        assert_eq!((p.opts.background, p.opts.quality, p.opts.format), (Some([255, 128, 0]), 90, Format::Jpeg));
        assert_eq!(parse(b"/x/bg:1:2:3/upload@png").unwrap().opts.background, Some([1, 2, 3]));
        assert_eq!(parse(b"/x/upload@jpeg").unwrap().opts.format, Format::Jpeg);
        let enc = verilith_text::base64::URL_SAFE.encode(b"http://a.b/c.png");
        let path = format!("/x/rs:fill:10:20:1/{}.png", enc);
        let p = parse(path.as_bytes()).unwrap();
        assert_eq!(p.source, Source::Http(b"http://a.b/c.png".to_vec()));
        assert_eq!((p.opts.mode, p.opts.w, p.opts.h, p.opts.enlarge), (Mode::Fill, 10, 20, true));
        for bad in [
            &b"x/plain/local:///a"[..],
            b"/x",
            b"/x/w:10",
            b"/x/w:65536/plain/local:///a",
            b"/x/w:1a/plain/local:///a",
            b"/x/bg:zz0000/plain/local:///a",
            b"/x/bg:256:0:0/plain/local:///a",
            b"/x/q:101/plain/local:///a",
            b"/x/g:up/plain/local:///a",
            b"/x/g:fp:2:0/plain/local:///a",
            b"/x/rot:45/plain/local:///a",
            b"/x/dpr:0/plain/local:///a",
            b"/x/plain/ftp://a/b",
            b"/x/plain/local:///a@gif",
            b"/x/uploadx",
            b"/x/upload/more",
            b"/x/!!!",
        ] {
            assert!(parse(bad).is_err(), "{}", String::from_utf8_lossy(bad));
        }
    }

    #[test]
    fn resizing_algorithms() {
        assert_eq!(parse(b"/x/ra:cubic/plain/local:///a.png").unwrap().opts.filter, Filter::Cubic);
        assert_eq!(parse(b"/x/plain/local:///a.png").unwrap().opts.filter, Filter::Lanczos3);
        assert!(parse(b"/x/ra:bogus/plain/local:///a.png").is_err());
        for f in [Filter::Lanczos3, Filter::Lanczos2, Filter::Cubic, Filter::Linear, Filter::Nearest] {
            let kt = kernel(f).unwrap();
            // pre: thumb_rgba's kt_ok.
            assert!(kt.len() >= 256 && kt.len() <= 1024 && kt.len() % 256 == 0);
            assert!(kt.iter().all(|&v| (-32768..=32768).contains(&v)));
            assert_eq!(kt[0], 16384);
        }
        assert!(kernel(Filter::Area).is_none());
    }

    #[test]
    fn origins() {
        let o = split_http(b"https://img.example.com/a/b.jpg?x=1#f").unwrap();
        assert_eq!(o, Origin { https: true, host: "img.example.com".into(), port: 443, target: b"/a/b.jpg?x=1".to_vec() });
        let o = split_http(b"http://example.com:8080").unwrap();
        assert_eq!((o.https, o.port, o.target), (false, 8080, b"/".to_vec()));
        assert!(split_http(b"https://[::1]/a").is_err());
        assert!(split_http(b"https://10.0.0.1/a").is_err());
        assert!(split_http(b"https://u@example.com/a").is_err());
        assert_eq!(parse(b"/x/plain/https://example.com/a.png").unwrap().source, Source::Http(b"https://example.com/a.png".to_vec()));
    }

    #[test]
    fn urls() {
        let p = parse(b"/insecure/rs:fill:300:200/plain/http://example.com/a%20b.jpg@png").unwrap();
        assert_eq!(p.signature, b"insecure");
        assert_eq!(p.opts.mode, Mode::Fill);
        assert_eq!((p.opts.w, p.opts.h), (300, 200));
        assert_eq!(p.source, Source::Http(b"http://example.com/a b.jpg".to_vec()));
        let enc = verilith_text::base64::URL_SAFE_NO_PAD.encode(b"local:///cat.png");
        let u = format!("/x/w:10/{}/{}.png", &enc[..4], &enc[4..]);
        let p = parse(u.as_bytes()).unwrap();
        assert_eq!(p.source, Source::Local(b"/cat.png".to_vec()));
        assert_eq!(p.opts.w, 10);
        assert_eq!(parse(b"/x/w:10/plain/local:///a.jpg").unwrap().opts.format, Format::Png);
        assert_eq!(parse(b"/x/w:10/plain/local:///a.png@jpg").unwrap().opts.format, Format::Jpeg);
        assert_eq!(parse(b"/x/f:jpeg/q:55/plain/local:///a.png").unwrap().opts.quality, 55);
        assert_eq!(parse(b"/x/f:jpeg/plain/local:///a.png").unwrap().opts.format, Format::Jpeg);
        assert!(matches!(parse(b"/x/q:101/plain/local:///a.png"), Err(Fail::BadUrl(_))));
        assert!(matches!(parse(b"/x/w:10/plain/local:///a.jpg@avif"), Err(Fail::Unprocessable(_))));
        assert!(matches!(parse(b"/x/zz:1/plain/local:///a.jpg"), Err(Fail::BadUrl(_))));
        assert_eq!(parse(b"/x/s:5:6/upload").unwrap().source, Source::Upload);
    }

    #[test]
    fn signatures() {
        // imgproxy's documented example: key "secret", salt "hello".
        let keys = Keys { key: b"secret".to_vec(), salt: b"hello".to_vec() };
        let path = b"/rs:fill:300:400:0/g:sm/aHR0cDovL2V4YW1w/bGUuY29tL2ltYWdl/cy9jdXJpb3NpdHku/anBn.png";
        let sig = sign(&keys, path);
        assert_eq!(sig, "oKfUtW34Dvo2BGQehJFR4Nr0_rIjOtdtzJ3QFsUcXH8");
        assert!(check(&keys, sig.as_bytes(), path));
        assert!(!check(&keys, b"AAAA", path));
    }

    #[test]
    fn shrink_on_load() {
        assert_eq!(jpeg_shrink(4000, 3000, 300, 225), 8);
        assert_eq!(jpeg_shrink(1920, 1280, 300, 200), 4);
        assert_eq!(jpeg_shrink(1000, 1000, 400, 400), 2);
        assert_eq!(jpeg_shrink(1000, 1000, 600, 600), 1);
        assert_eq!(jpeg_shrink(1000, 100, 100, 50), 2);
    }

    #[test]
    fn http_urls() {
        let o = split_http(b"http://a.b:8080/x?y").unwrap();
        assert_eq!((o.host.as_str(), o.port, o.target), ("a.b", 8080, b"/x?y".to_vec()));
        let o = split_http(b"http://a.b").unwrap();
        assert_eq!((o.host.as_str(), o.port, o.target), ("a.b", 80, b"/".to_vec()));
        assert!(split_http(b"http://u@a.b/").is_err());
    }
}
