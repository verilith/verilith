# verilith-imgproxy

An image proxy and thumbnailer that answers [imgproxy](https://imgproxy.net)'s
URLs, built from the Verilith crates: images are decoded by the verified
JPEG, PNG, WebP and GIF decoders, resized and encoded as PNG by code
verified here, and served by [verilith-server](../server). Parsing
untrusted images is where image servers have had their worst bugs
(ImageTragick, the libwebp heap overflow CVE-2023-4863, libpng's and
libjpeg's long lists); here the decoders, the resizer and the encoder are
proven free of memory errors, overflows and panics, and proven to compute
their specifications.

**Status: pre-release.** PNG output only (no verified JPEG or WebP encoder
yet), `local://`, `http://` and uploaded sources (no HTTPS client yet), and
an area-average (box) resampler rather than imgproxy's Lanczos.

## What is proven

`cargo verus focus` checks 154 functions with no errors.

| Property | Where it is stated |
|---|---|
| The resizer computes exactly `spec::resize`: each output pixel is the area-weighted average of the source pixels its cell covers, rows then columns, rounded to nearest, with 8 bits of fraction kept between the passes. No overflow, no out-of-bounds access, for every size up to 65535 by 65535 | `resize::resize_rgba` (with `resize::rows`, `resize::cols`) against `spec::resize` |
| The row pass's values stay below 255 × 256 and the column pass's below 256, so the narrowing casts are exact (the weights of each output cell add up to the source length: `lemma_osum`) | `lemma_hpx_bound`, `lemma_opx_bound` |
| Cropping returns exactly `spec::crop` | `resize::crop_rgba` |
| **PNG round trip:** for every RGBA image, the file `encode_rgba` writes decodes, under verilith-png's specification of PNG decoding, to exactly that image and header. The proof goes through every layer of the specification: the signature, IHDR, the chunk walk with its CRCs (computed by verilith-checksum, verified), the zlib stream (verilith-zlib's compressor, proven to round-trip), and the five row filters, each row filtered with whichever filter libpng's heuristic picks | `pngenc::encode_rgba` against `verilith_png::spec::decode` |
| The output size: `plan_x` computes `fit::plan` (imgproxy's `fit`, `fill` and `force`, with and without `enlarge`), and the result is never empty, never larger than 65535 on a side or than the pixel limit, and the crop is inside the resized image | `fit::plan_x` |
| Grey, RGB, ARGB and palette pixels are converted to RGBA byte for byte as specified; alpha is flattened onto a background colour as specified | `pixels::expand`, `from_argb`, `from_indexed`, `flatten` |
| URL signatures are checked with HMAC-SHA256 in constant time | verilith-sha2's `HmacSha256::verify` (verified there) |
| `local://` paths never leave the root | verilith-server's `path::resolve_exec` (verified there), then `openat2(RESOLVE_BENEATH)` |

What is not proven: the glue in `src/proxy.rs` and `src/handler.rs` (URL
parsing, choosing a decoder, the HTTP client's sockets); see
[TRUST.md](TRUST.md). It calls each verified function only after checking
that function's precondition at run time.

## Usage

```sh
cargo build --release -p verilith-imgproxy            # add --features tls for HTTPS
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
enlarge), `size`/`s`, `resizing_type`/`rt`, `width`/`w`, `height`/`h`,
`enlarge`/`el`, `background`/`bg` (flattens alpha), `gravity`/`g` (`ce`
only), `format`/`f` (`png` only); `quality`, `strip_metadata` and
`cachebuster` are accepted and ignored. Anything else is answered 400, as
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

- PNG output only: `@jpg`, `@webp` and `@avif` are answered 422.
- Box (area-average) resampling instead of Lanczos 3. It is exact for
  downscaling, has no ringing, and is softer than Lanczos.
- Alpha is resampled straight, not premultiplied.
- Centre gravity only; no smart crop, watermarks, blur, sharpening,
  rotation or EXIF orientation.
- GIF: the first frame, at its own size.
- No HTTPS sources, and no redirects from an origin.
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

Where the time goes, on the 4000x3000 JPEG: about 60 ms decoding at full
size, 30 ms expanding RGB to RGBA, 37 ms resizing, 11 ms encoding. The
large gap to `vips_thumbnail` is shrink-on-load: libjpeg decodes at 1/8
size from the DC coefficients and never builds the full image. A verified
reduced-size decode in verilith-jpeg is the next step for speed; it needs
a specification of its own, since a DC-only decode is not the full decode
averaged (the full decode clamps and rounds each pixel).

## Tests

`cargo test -p verilith-imgproxy` reads the encoder's output back with
the `png` crate and with verilith-png at every level, compares the resizer
with a direct floating-point computation of the area average on random
sizes, runs the pipeline on JPEG and PNG files the `image` crate writes,
and checks URL parsing and imgproxy's documented signature example.
