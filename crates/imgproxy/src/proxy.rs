//! The unverified glue: imgproxy-style URLs, signature checking, choosing
//! a decoder, fetching sources, and the pipeline that calls the verified
//! functions. Plain safe Rust; the trust it needs is listed in TRUST.md.
//!
//! Every call into a verified function is guarded here by a run-time
//! check of that function's `requires` clause (Verus does not check the
//! callers that are not verified), marked "pre:" below.
use crate::fit::{plan_x, Mode};
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

/// The largest width or height anything here handles (`spec::MAX_DIM`).
pub const MAX_DIM: u32 = 65535;

/// Why a request failed, with the status it is answered with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fail {
    /// 400: the URL is not one we understand.
    BadUrl(&'static str),
    /// 403: the signature is wrong.
    Forbidden,
    /// 404: no such source.
    NotFound,
    /// 415: the source is not JPEG, PNG, WebP or GIF.
    Unsupported,
    /// 422: the source does not decode, or is larger than the limits.
    Unprocessable(&'static str),
    /// 502: the origin failed.
    BadGateway(&'static str),
}

impl Fail {
    pub fn status(&self) -> u16 {
        match self {
            Fail::BadUrl(_) => 400,
            Fail::Forbidden => 403,
            Fail::NotFound => 404,
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
            Fail::Unsupported => "Source image type not supported",
        }
    }
}

// ---------------------------------------------------------------------------
// URLs
// ---------------------------------------------------------------------------

/// What to do to the image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Options {
    pub mode: Mode,
    pub w: u32,
    pub h: u32,
    pub enlarge: bool,
    pub background: Option<[u8; 3]>,
}

impl Default for Options {
    fn default() -> Self {
        Options { mode: Mode::Fit, w: 0, h: 0, enlarge: false, background: None }
    }
}

/// Where the image comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// `local:///path`, under the configured root.
    Local(Vec<u8>),
    /// `http://...` or `https://...`.
    Http(Vec<u8>),
    /// The request body (`POST .../upload`).
    Upload,
}

/// A parsed request URL.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed<'a> {
    pub signature: &'a [u8],
    /// What the signature signs: the path from the `/` after it.
    pub signed: &'a [u8],
    pub opts: Options,
    pub source: Source,
}

fn num(s: &[u8]) -> Result<u32, Fail> {
    if s.is_empty() {
        return Ok(0);
    }
    let mut v: u32 = 0;
    for &c in s {
        if !c.is_ascii_digit() {
            return Err(Fail::BadUrl("Invalid number"));
        }
        v = v.checked_mul(10).and_then(|v| v.checked_add((c - b'0') as u32)).ok_or(Fail::BadUrl("Number too large"))?;
    }
    if v > MAX_DIM {
        return Err(Fail::BadUrl("Size too large"));
    }
    Ok(v)
}

fn boolean(s: &[u8]) -> Result<bool, Fail> {
    match s {
        b"1" | b"t" | b"true" => Ok(true),
        b"0" | b"f" | b"false" | b"" => Ok(false),
        _ => Err(Fail::BadUrl("Invalid boolean")),
    }
}

fn mode(s: &[u8]) -> Result<Mode, Fail> {
    match s {
        b"fit" => Ok(Mode::Fit),
        b"fill" => Ok(Mode::Fill),
        b"force" => Ok(Mode::Force),
        _ => Err(Fail::BadUrl("Unsupported resizing type")),
    }
}

fn hexbyte(s: &[u8]) -> Option<u8> {
    let d = |c: u8| (c as char).to_digit(16);
    match s {
        [a, b] => Some((d(*a)? * 16 + d(*b)?) as u8),
        _ => None,
    }
}

fn background(args: &[&[u8]]) -> Result<Option<[u8; 3]>, Fail> {
    match args {
        [] | [b""] => Ok(None),
        [hex] if hex.len() == 6 => {
            match (hexbyte(&hex[0..2]), hexbyte(&hex[2..4]), hexbyte(&hex[4..6])) {
                (Some(r), Some(g), Some(b)) => Ok(Some([r, g, b])),
                _ => Err(Fail::BadUrl("Invalid background")),
            }
        }
        [r, g, b] => {
            let c = |s: &[u8]| -> Result<u8, Fail> {
                let v = num(s)?;
                if v > 255 || s.is_empty() { Err(Fail::BadUrl("Invalid background")) } else { Ok(v as u8) }
            };
            Ok(Some([c(r)?, c(g)?, c(b)?]))
        }
        _ => Err(Fail::BadUrl("Invalid background")),
    }
}

/// Applies one processing option (`name:arg:arg...`).
fn option(o: &mut Options, seg: &[u8]) -> Result<(), Fail> {
    let mut parts = seg.split(|&c| c == b':');
    let name = parts.next().unwrap_or(b"");
    let args: Vec<&[u8]> = parts.collect();
    let arg = |i: usize| args.get(i).copied().unwrap_or(b"");
    match name {
        b"resize" | b"rs" => {
            if !arg(0).is_empty() {
                o.mode = mode(arg(0))?;
            }
            o.w = num(arg(1))?;
            o.h = num(arg(2))?;
            o.enlarge = boolean(arg(3))?;
        }
        b"size" | b"s" => {
            o.w = num(arg(0))?;
            o.h = num(arg(1))?;
            o.enlarge = boolean(arg(2))?;
        }
        b"resizing_type" | b"rt" => o.mode = mode(arg(0))?,
        b"width" | b"w" => o.w = num(arg(0))?,
        b"height" | b"h" => o.h = num(arg(0))?,
        b"enlarge" | b"el" => o.enlarge = boolean(arg(0))?,
        b"background" | b"bg" => o.background = background(&args)?,
        // Accepted and ignored: they do not change a PNG.
        b"quality" | b"q" | b"strip_metadata" | b"sm" | b"cachebuster" | b"cb" => {}
        b"format" | b"f" | b"ext" => format(arg(0))?,
        // Only centred crops (`ce`, the default) are implemented.
        b"gravity" | b"g" => {
            if !matches!(arg(0), b"" | b"ce") {
                return Err(Fail::Unprocessable("Only centre gravity is supported"));
            }
        }
        _ => return Err(Fail::BadUrl("Unknown processing option")),
    }
    Ok(())
}

/// The output format: PNG only, for now (the encoder this crate verifies).
fn format(ext: &[u8]) -> Result<(), Fail> {
    match ext {
        b"" | b"png" | b"best" => Ok(()),
        _ => Err(Fail::Unprocessable("Only PNG output is supported")),
    }
}

fn percent_decode(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    verilith_text::percent::decode_to(s, &mut out);
    out
}

fn source(url: Vec<u8>) -> Result<Source, Fail> {
    if let Some(p) = url.strip_prefix(b"local://") {
        Ok(Source::Local(p.to_vec()))
    } else if url.starts_with(b"http://") || url.starts_with(b"https://") {
        Ok(Source::Http(url))
    } else {
        Err(Fail::BadUrl("Unsupported source URL scheme"))
    }
}

/// Parses `/%signature/%options/plain/%url[@%ext]`,
/// `/%signature/%options/%base64_url[.%ext]` or
/// `/%signature/%options/upload[@%ext]`.
pub fn parse(path: &[u8]) -> Result<Parsed<'_>, Fail> {
    let rest = path.strip_prefix(b"/").ok_or(Fail::BadUrl("Invalid path"))?;
    let slash = rest.iter().position(|&c| c == b'/').ok_or(Fail::BadUrl("Invalid path"))?;
    let signature = &rest[..slash];
    let signed = &rest[slash..];
    let mut opts = Options::default();
    let mut segs = signed[1..].split(|&c| c == b'/').peekable();
    while let Some(seg) = segs.peek() {
        if seg.contains(&b':') && !seg.starts_with(b"http") && !seg.starts_with(b"local") {
            option(&mut opts, seg)?;
            segs.next();
        } else {
            break;
        }
    }
    let first = segs.next().ok_or(Fail::BadUrl("Missing source URL"))?;
    let source = if first == b"plain" {
        let joined: Vec<&[u8]> = segs.collect();
        let mut url = joined.join(&b'/');
        if let Some(at) = url.iter().rposition(|&c| c == b'@') {
            format(&url[at + 1..])?;
            url.truncate(at);
        }
        source(percent_decode(&url))?
    } else if first.starts_with(b"upload") && segs.peek().is_none() {
        if let Some(ext) = first.strip_prefix(b"upload@") {
            format(ext)?;
        } else if first != b"upload" {
            return Err(Fail::BadUrl("Invalid upload path"));
        }
        Source::Upload
    } else {
        let mut enc: Vec<u8> = first.to_vec();
        for s in segs {
            enc.extend_from_slice(s);
        }
        if let Some(dot) = enc.iter().position(|&c| c == b'.') {
            format(&enc[dot + 1..])?;
            enc.truncate(dot);
        }
        let url = verilith_text::base64::URL_SAFE_NO_PAD
            .decode(enc.strip_suffix(b"=").unwrap_or(&enc))
            .or_else(|_| verilith_text::base64::URL_SAFE.decode(&enc))
            .map_err(|_| Fail::BadUrl("Invalid base64 source URL"))?;
        source(url)?
    };
    Ok(Parsed { signature, signed, opts, source })
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
    b.chunks(2).map(hexbyte).collect()
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

/// imgproxy's shrink-on-load factor for a JPEG (`calcJpegShink`): the
/// largest of 8, 4 and 2 that the scale down to `rw` by `rh` allows, or 1.
/// The decoder then gives the image at 1/8, 1/4 or 1/2 of its size,
/// straight from the coefficients (verilith-jpeg's `decode_scaled`).
pub fn jpeg_shrink(sw: u32, sh: u32, rw: u32, rh: u32) -> u32 {
    let s = (sw / rw.max(1)).min(sh / rh.max(1));
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

/// The width and height a file's header gives, if it is a JPEG, PNG, WebP
/// or GIF file whose header can be read.
pub fn dims(data: &[u8]) -> Option<(u32, u32)> {
    if data.starts_with(&[0xff, 0xd8, 0xff]) {
        let hd = verilith_jpeg::decode::read_header(data).ok()?;
        Some((hd.w as u32, hd.h as u32))
    } else if data.starts_with(&[0x89, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a]) {
        Some((be32(data, 16)?, be32(data, 20)?))
    } else if data.len() >= 12 && &data[0..4] == b"RIFF" && &data[8..12] == b"WEBP" {
        let f = verilith_webp::capi::get_features(data).ok()?;
        Some((f.width as u32, f.height as u32))
    } else if data.starts_with(b"GIF87a") || data.starts_with(b"GIF89a") {
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
    if data.starts_with(&[0xff, 0xd8, 0xff]) {
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
    } else if data.starts_with(&[0x89, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a]) {
        let (w, h) = (be32(data, 16).ok_or(bad.clone())?, be32(data, 20).ok_or(bad.clone())?);
        size_ok(w as u64, h as u64, max_px)?;
        let limit = (max_px as usize).saturating_mul(8).saturating_add(1 << 20);
        let (hd, px) = verilith_png::top::decode(data, verilith_png::top::PixelFormat::Rgba8, limit).map_err(|e| match e {
            verilith_png::decode::Error::TooLarge => Fail::Unprocessable("Source image resolution is too big"),
            _ => bad.clone(),
        })?;
        Ok(Rgba { w: hd.width, h: hd.height, px })
    } else if data.len() >= 12 && &data[0..4] == b"RIFF" && &data[8..12] == b"WEBP" {
        let f = verilith_webp::capi::get_features(data).map_err(|_| bad.clone())?;
        size_ok(f.width as u64, f.height as u64, max_px)?;
        let img = verilith_webp::capi::decode(data).map_err(|_| bad.clone())?;
        // pre: from_argb (a Vec's length times 4 fits in usize: it is a u32 vector)
        let px = crate::pixels::from_argb(&img.argb);
        Ok(Rgba { w: img.width as u32, h: img.height as u32, px })
    } else if data.starts_with(b"GIF87a") || data.starts_with(b"GIF89a") {
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

/// Decodes, resizes, crops, flattens and encodes: the PNG to send.
pub fn process(data: &[u8], o: &Options, lim: &Limits) -> Result<Vec<u8>, Fail> {
    // The plan is made from the size the header gives, so that shrinking a
    // JPEG on load changes only how the pixels are computed, not the
    // result's size.
    let (w0, h0) = dims(data).ok_or(Fail::Unsupported)?;
    // pre: plan_x (sizes at most MAX_DIM).
    if w0 == 0 || h0 == 0 || w0 > MAX_DIM || h0 > MAX_DIM || o.w > MAX_DIM || o.h > MAX_DIM {
        return Err(Fail::Unprocessable("Source image size not supported"));
    }
    let mut p = plan_x(w0, h0, o.w, o.h, o.mode, o.enlarge, lim.max_out_px)
        .ok_or(Fail::Unprocessable("Result image is too big"))?;
    let shrink = jpeg_shrink(w0, h0, p.rw, p.rh);
    let img = decode_shrunk(data, lim.max_src_px, shrink)?;
    // pre: resize_rgba and plan_x (the decoded image's sizes in 1..=MAX_DIM).
    if img.w == 0 || img.h == 0 || img.w > MAX_DIM || img.h > MAX_DIM {
        return Err(Fail::Unprocessable("Source image size not supported"));
    }
    // A GIF's first frame can be smaller than its screen: plan from the frame.
    if shrink == 1 && (img.w, img.h) != (w0, h0) {
        p = plan_x(img.w, img.h, o.w, o.h, o.mode, o.enlarge, lim.max_out_px)
            .ok_or(Fail::Unprocessable("Result image is too big"))?;
    }
    if img.px.len() != img.w as usize * img.h as usize * 4 {
        return Err(Fail::Unprocessable("Source image is invalid"));
    }
    let (sw, sh) = (img.w as usize, img.h as usize);
    let (rw, rh) = (p.rw as usize, p.rh as usize);
    // pre: resize_rgba (all sizes in 1..=MAX_DIM, ensured by plan_x; the
    // products are below 2^34 on a 64-bit target).
    let px = if (rw, rh) == (sw, sh) { img.px } else { crate::resize::resize_rgba(&img.px, sw, sh, rw, rh) };
    // pre: crop_rgba (plan_x ensures the rectangle is inside).
    let px = if (p.cx, p.cy, p.cw, p.ch) == (0, 0, p.rw, p.rh) {
        px
    } else {
        crate::resize::crop_rgba(&px, rw, rh, p.cx as usize, p.cy as usize, p.cw as usize, p.ch as usize)
    };
    // pre: flatten (a whole number of pixels).
    let px = match o.background {
        Some(bg) => crate::pixels::flatten(&px, bg),
        None => px,
    };
    // pre: encode_rgba (sizes at most MAX_DIM).
    crate::pngenc::encode_rgba(&px, p.cw, p.ch, lim.level).ok_or(Fail::Unprocessable("Result image is too big"))
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
        assert!(matches!(parse(b"/x/w:10/plain/local:///a.jpg@jpg"), Err(Fail::Unprocessable(_))));
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
