# verilith-imgproxy

An image proxy and thumbnailer that answers [imgproxy](https://imgproxy.net)'s
URLs, built from the Verilith crates: images are decoded by the verified
JPEG, PNG, WebP and GIF decoders, resized by code verified here, encoded as
PNG (verified here) or JPEG (verilith-jpeg's verified encoder), and served by [verilith-server](../server). Parsing
untrusted images is where image servers have had their worst bugs
(ImageTragick, the libwebp heap overflow CVE-2023-4863, libpng's and
libjpeg's long lists); here the decoders, the resizer and the encoder are
proven free of memory errors, overflows and panics, and proven to compute
their specifications.

**Status: pre-release.** PNG and JPEG output (no WebP encoder yet),
`local://`, `http://`, `https://` (with `--features tls`) and uploaded
sources. Resampling is Lanczos 3 by default, as in imgproxy.

## What is proven

`cargo verus focus` checks 615 functions with no errors.

| Property | Where it is stated |
|---|---|
| The resizer computes exactly `spec::resize`: each output pixel is the area-weighted average of the source pixels its cell covers, rows then columns, rounded to nearest, with 8 bits of fraction kept between the passes. No overflow, no out-of-bounds access, for every size up to 65535 by 65535 | `resize::resize_rgba` (with `resize::rows`, `resize::cols`) against `spec::resize` |
| The row pass's values stay below 255 × 256 and the column pass's below 256, so the narrowing casts are exact (the weights of each output cell add up to the source length: `lemma_osum`) | `lemma_hpx_bound`, `lemma_opx_bound` |
| The thumbnailer computes exactly `spec_lanczos::thumb` for every kernel table (Lanczos 3, Lanczos 2, cubic, linear, or any other of up to 4 units' support): a box shrink by half the ratio rounded down, as `vips_resize` does, then the kernel stretched over each output sample, edges repeated, weights normalized by their sum, rows then columns with 8 bits of fraction kept and each pass clamped. No overflow, no out-of-bounds access, for every size up to 65535 by 65535 | `lanczos::thumb_rgba` (with `lanczos::taps`, `krows`, `kcols`) against `spec_lanczos::thumb` |
| URLs: `url::parse_x` refuses a path exactly when `spec_url::parse` gives none, and otherwise returns its signature span, options and source. The specification states imgproxy's grammar (signature, `name:arg` options applied in order, `plain/` sources percent-decoded with verilith-text's verified decoder, base64url sources with its verified decoder, `upload`, the `@`/`.` extension) | `url::parse_x` against `spec_url::parse` |
| Choosing a decoder: `url::kind_x` names the format exactly as `spec_url::kind` does from the first bytes (JPEG, PNG, WebP, GIF), and `jpeg_shrink_x` computes imgproxy's shrink-on-load factor | `url::kind_x`, `url::jpeg_shrink_x` |
| Geometry: `geom::geom_x` computes `spec_geom::geom`, imgproxy's `crop` (pixels or fractions, at its own gravity), resize (times `dpr`), the `fill` crop at `gravity` (compass offsets or a focus point, as `calcPosition`), `extend` and `padding`, and proves every rectangle is inside the one it is cut from or placed on, and the canvas within 65535 on a side and the pixel limit | `geom::geom_x` against `spec_geom::geom` |
| Rotating and flipping return exactly `spec_geom::turn` (clockwise quarter turns, then mirror), and placing on a canvas exactly `spec_geom::embed` | `geom::turn_rgba`, `geom::embed_rgba` |
| EXIF orientation: `exif::orientation_x` reads exactly `spec_exif::orientation` from any bytes (JPEG's first `Exif` APP1 before the scan, WebP's `EXIF` chunk, PNG's `eXIf` before `IDAT`; the IFD0 entry 0x0112 of type SHORT, 1 to 8, else 1), in bounds and without overflow, with loops (no recursion depth an input controls); `upright_x` gives each orientation's turn | `exif::orientation_x`, `exif::upright_x` |
| `blur` and `sharpen` compute exactly `spec_filter::blur` (libvips's `vips_convsep` at integer precision: rows then columns, each rounded to 8 bits, edges repeated, with any table of up to 10001 non-negative weights and any divisor up to 2^31), and `sharpen`'s step on the lightness computes exactly `spec_filter::sharpen_l` (`vips_sharpen`: the LabS lightness blurred at 16 bits with libvips's rounding, then moved by its curve's table), for every size up to 65535 by 65535 | `filter::blur_rgba`, `filter::sharpen_l_x` |
| Premultiplied alpha computes exactly `spec_filter::premultiply` and `unpremultiply`: libvips's single-precision arithmetic and truncation, written as integers | `filter::premul_rgba`, `filter::unpremul_rgba` |
| `pixelate` computes exactly `spec_filter::pixelate`: imgproxy's mirror padding to whole blocks, `vips_shrink` (rows, then columns, with libvips's 8-bit fixed-point average), `vips_zoom` and the crop back | `filter::pixelate_rgba` |
| Watermarks: `geom::watermark_rgba` computes exactly `spec_geom::watermark` (Porter-Duff "over" with straight alpha at the given opacity, rounded to nearest, once at a gravity or tiled), and `wm_at_x` places it inside the image as `calcPosition` does | `geom::watermark_rgba`, `geom::wm_at_x` |
| Smart gravity's choice computes exactly `spec_smart`'s: the first point of libvips's attention map with the highest value (`vips_max`), and the crop centred on it inside the image (`smartcrop.c`) | `smart::first_max_x`, `smart::centred_x` |
| Cropping returns exactly `spec::crop` | `resize::crop_rgba` |
| **PNG round trip:** for every RGBA image, the file `encode_rgba` writes decodes, under verilith-png's specification of PNG decoding, to exactly that image and header. The proof goes through every layer of the specification: the signature, IHDR, the chunk walk with its CRCs (computed by verilith-checksum, verified), the zlib stream (verilith-zlib's compressor, proven to round-trip), and the five row filters, each row filtered with whichever filter libpng's heuristic picks | `pngenc::encode_rgba` against `verilith_png::spec::decode` |
| **JPEG output:** the file verilith-jpeg's `encode_rgb` writes decodes, under verilith-jpeg's specification, to the coefficients libjpeg-turbo computes for the image with its default settings (and is byte-identical to libjpeg-turbo's file in its differential tests) | verilith-jpeg's `encode::encode_rgb` (verified there) |
| The output size: `plan_x` computes `fit::plan` (imgproxy's `fit`, `fill` and `force`, with and without `enlarge`), and the result is never empty, never larger than 65535 on a side or than the pixel limit, and the crop is inside the resized image | `fit::plan_x` |
| Grey, RGB, ARGB and palette pixels are converted to RGBA byte for byte as specified; alpha is flattened onto a background colour as specified | `pixels::expand`, `from_argb`, `from_indexed`, `flatten` |
| JPEG shrink-on-load: the reduced-size image is exactly libjpeg-turbo's scaled decode, as verilith-jpeg's `spec_scaled` states it | verilith-jpeg's `scaled::decode_scaled` (verified there) |
| URL signatures are checked with HMAC-SHA256 in constant time | verilith-sha2's `HmacSha256::verify` (verified there) |
| `local://` paths never leave the root | verilith-server's `path::resolve_exec` (verified there), then `openat2(RESOLVE_BENEATH)` |

What is not proven: the glue in `src/proxy.rs` and `src/handler.rs` (the
order of the pipeline's steps, the HTTP client's sockets); see
[TRUST.md](TRUST.md). It calls each verified function only after checking
that function's precondition at run time.

## Usage

```sh
cargo build --release -p verilith-imgproxy            # add --features tls for HTTPS (both sides)
IMGPROXY_KEY=736563726574 IMGPROXY_SALT=68656C6C6F \
  ./target/release/verilith-imgproxy --http 8080 --local-root ./images
```

URLs are imgproxy's:

```
/%signature/rs:fit:300:200/plain/local:///cat.jpg@png
/%signature/rs:fill:128:128/plain/http://origin.example/a.webp
/%signature/w:640/%base64url_of_source_url.png
POST /%signature/s:300:300/upload           (the image is the request body)
GET /health
```

The signature is imgproxy's: base64url (no padding) of
HMAC-SHA256(key, salt ‖ path), the path starting at the `/` after the
signature. With no `IMGPROXY_KEY`, any signature is accepted, as in
imgproxy.

Processing options: `resize`/`rs` (`fit`, `fill`, `force`, width, height,
enlarge, extend), `size`/`s`, `resizing_type`/`rt`, `width`/`w`, `height`/`h`,
`enlarge`/`el`, `resizing_algorithm`/`ra` (`lanczos3`, the default,
`lanczos2`, `cubic`, `linear`, `nearest`, and `area` for the exact area
average), `background`/`bg` (flattens alpha, and fills `extend` and
`padding`), `gravity`/`g` (`ce`, `no`, `so`, `ea`, `we`, `noea`, `nowe`,
`soea`, `sowe` with offsets, `fp` with a focus point, `sm`), `crop`/`c` (width,
height, gravity), `extend`/`ex` (with gravity), `padding`/`pd`, `dpr`,
`rotate`/`rot` (multiples of 90), `flip`/`fl`, `auto_rotate`/`ar` (EXIF
orientation, on by default), `blur`/`bl`, `sharpen`/`sh`, `pixelate`/`pix`,
`watermark`/`wm` (opacity, position or `re` to tile, offsets, scale; the
image from `--watermark`, `IMGPROXY_WATERMARK_PATH` or
`IMGPROXY_WATERMARK_DATA`), `format`/`f` or the URL's extension (`png`, `jpg`/`jpeg`; PNG when
none is given), `quality`/`q` (JPEG, 1 to 100, default 80);
`expires`/`exp` (404 once past), `filename`/`fn` (plain or base64url)
and `return_attachment`/`att` (the `Content-Disposition` header),
`raw` and `skip_processing`/`skp` (`jpg`, `png`, `webp`, `gif`: the
source is sent as it is); `strip_metadata` and `cachebuster` are accepted
and ignored. Anything else is answered 400, as
imgproxy does. Settings: `IMGPROXY_KEY`, `IMGPROXY_SALT`, `IMGPROXY_BIND`,
`IMGPROXY_LOCAL_FILESYSTEM_ROOT`, `IMGPROXY_ALLOWED_SOURCES`,
`IMGPROXY_MAX_SRC_RESOLUTION` (default 50 megapixels, checked from the
headers before decoding), `IMGPROXY_MAX_SRC_FILE_SIZE`,
`IMGPROXY_DOWNLOAD_TIMEOUT`, `IMGPROXY_TTL`; flags in the binary's doc
comment.

Errors: 400 for a URL it cannot parse, 403 for a bad signature, 404 for a
missing source, 415 for a format it cannot decode, 422 for an image that
does not decode or is over the limits, 502 for an origin that fails.

## Departures from imgproxy

- PNG and JPEG output only: `@webp` and `@avif` are answered 422. With no
  extension the result is PNG, where imgproxy keeps the source's format.
- JPEG is written as libvips writes it by default: baseline, 4:2:0 chroma
  below quality 90 and 4:4:4 from 90, typical (not optimized) Huffman
  tables, alpha flattened onto the background or white. The quantization
  tables are libjpeg's for the quality; imgproxy's libvips uses the same
  ones.
- Resampling follows libvips's design (box pre-shrink, then a
  normalized kernel, 8-bit clamping between passes) but is not
  bit-identical to it: the kernel tables are 1/256-step samples in 14-bit
  fixed point, and `nearest` is a one-sample box (an average over each
  output pixel's cell when downscaling), not a pick of one pixel.
- Alpha is resampled straight, not premultiplied. The filters use
  premultiplied alpha as imgproxy does.
- Smart gravity runs libvips's attention map as imgproxy does (the
  `crop` option's on the source, the result's on the resized image),
  except that an image under 32 pixels on a side is used as it is,
  where libvips first enlarges its copy with bicubic interpolation.
  libvips premultiplies the map's copy when the image has an alpha
  band; PNG says so in its header, and for GIF and WebP an alpha band is
  taken to mean a pixel that is not opaque. Gravity offsets are whole
  pixels. `skip_processing` knows
  only the four formats decoded here.
- GIF: the first frame, at its own size.
- No redirects from an origin. `https://` sources need `--features tls`;
  they go through verilith-tls's verified TLS 1.3 client (TLS 1.2-only
  origins fail), trusting `--ca-bundle`, `$SSL_CERT_FILE` or the system's
  bundle, and their host must be a name, not an IP address.
- Requests are handled on the server's worker threads, so a slow origin
  holds a worker until the download timeout.

## Speed

`bench/run.sh` times a 300x300 `fit` thumbnail written as PNG, one thread,
against libvips 8.15 (imgproxy's engine) two ways: `vips_thumbnail_buffer`,
which is what imgproxy does and decodes JPEG and WebP at reduced size
("shrink on load"), and a full-size load and `vips_resize` (Lanczos 3).
Cloud x86-64 (Intel Xeon, 2.1 GHz), median of 15, in milliseconds
([results](bench/results-cloud-x86.tsv)):

| Source | verilith-imgproxy | libvips thumbnail | libvips full-size resize |
|---|---:|---:|---:|
| 4000x3000 JPEG | 128 | 27 | 79 |
| 1920x1280 JPEG | 35 | 15 | 28 |
| 1920x1280 WebP (lossy) | 48 | 25 | 58 |
| 1920x1280 PNG | 36 | 57 | 64 |
| 512x512 PNG | 17 | 16 | 16 |

The output is 20 to 30% smaller than libvips's (libvips writes RGB without
row filters by default; this writes RGBA with libpng's filter choice).

JPEG sources are now decoded at reduced size, as imgproxy does
(`calcJpegShink`: 1/8, 1/4 or 1/2, the largest the scale allows), by
verilith-jpeg's verified `decode_scaled`, which goes from the coefficients
straight to the small image with libjpeg's reduced inverse DCTs and gives
libjpeg-turbo's pixels. The table above is from before that change. On
the same kind of machine, with a noisier 4000x3000 photograph (more
entropy-coded data than the table's), the 300x300 thumbnail went from
166 ms to 57 ms, and a 1920x1280 one from 33 ms to 21 ms (baseline) and
57 ms to 34 ms (progressive). What is left of the 12-megapixel case is
nearly all entropy decoding, which libjpeg-turbo does in about half the
time.

## Tests

`cargo test -p verilith-imgproxy` reads the encoder's output back with
the `png` crate and with verilith-png at every level, compares the
area-average resizer with a direct floating-point computation of the area
average on random sizes and the Lanczos resampler with a floating-point
Lanczos 3 (`tests/lanczos.rs`: at most 2 levels apart), runs the pipeline on JPEG and PNG files the `image` crate writes,
and checks URL parsing and imgproxy's documented signature example.

The filters and smart gravity are checked against libvips itself:
`scripts/vips_ref.py` runs an installed libvips through ctypes as
imgproxy calls it, and `VERILITH_VIPS_REF=dir cargo test --test libvips
-- --ignored` compares. Against libvips 8.15.1 (built with Highway):

- `blur` and premultiplied alpha are byte-identical on 255 images, on
  both its vector and its C path (`VIPS_NOVECTOR=1`). The masks are built
  as `vips_gaussmat` and `vips_convi_intize` build them (`src/mask.rs`).
- `sharpen` differs in 6 of 347,000 bytes, by at most 2. The colour
  conversions it goes through follow current libvips's source
  (`src/colour.rs`), which computes two matrices and a gamma table in
  single precision where 8.15 uses double; the conversion back to sRGB is
  byte-identical to 8.15 when those are switched to double.
- Smart gravity picks the same point as `vips_smartcrop` on 120 of 120
  images of 32 to 400 pixels, with and without alpha (`src/attention.rs`).
- `pixelate`, and the shrink in smart gravity's reduction, round as
  libvips 8.17 and later do (a fixed-point average, `shrinkv.c`); 8.15
  divides exactly. The test runs smart gravity with 8.15's rounding for
  8.15, and leaves `pixelate` out there.
