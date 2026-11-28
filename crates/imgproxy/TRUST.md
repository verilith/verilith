# What verilith-imgproxy trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, and the
specifications: this crate's `src/spec.rs`, `src/spec_lanczos.rs`, `src/spec_geom.rs`, `src/spec_exif.rs`, `src/spec_filter.rs`, `src/spec_smart.rs` and `src/spec_url.rs`, verilith-png's `spec.rs`, which
the encoder's round-trip theorem is stated with, and the decoders' own
specifications), and beyond what the crates it builds on trust
(verilith-server's [TRUST.md](../server/TRUST.md) for the event loop,
sockets and TLS):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/mask.rs` | libvips's blur masks, built in floating point as `vips_gaussmat` and `vips_convi_intize` build them | `filter`'s proofs hold for every table and divisor, so a wrong value changes how the image looks, never what the code may do; checked against libvips itself (`tests/libvips.rs`) and against hand-computed masks (`tests/filter.rs`) |
| `src/colour.rs` | libvips's colour conversions between 8-bit sRGB and LabS (and XYZ and Lab), and `vips_sharpen`'s curve and glue, in floating point as libvips computes them | The step on the lightness between the conversions is verified (`filter::sharpen_l_x`) for every table and image; checked against libvips itself (`tests/libvips.rs`) |
| `src/attention.rs` | libvips's attention map for smart gravity: premultiplying, `vips_resize`'s Lanczos 3 reduction to about 32 pixels, XYZ, Lab, the Laplacian, the skin vector, the blur | The choice made from the map is verified (`smart::first_max_x`, `smart::centred_x`) for every map; checked against libvips's own crops (`tests/libvips.rs`) |
| `src/proxy.rs` | The signature check's glue, calling the verified URL parser (`url::parse_x`) and format sniffer (`url::kind_x`), the pipeline that calls the verified functions (including the watermark's size, and where smart gravity crops), `local://`, `http://` and `https://` sources, reading the CA bundle (PEM), the kernel tables (`kernel`; the proofs hold for any table, so a wrong value changes how the image looks, never what the code may do) | Calls each verified function only when its `requires` holds: each call is preceded by a run-time check of it, marked `pre:` (Verus does not check unverified callers). Reads `local://` files only through verilith-server's verified `path::resolve_exec` and `join_to` and the kernel's `openat2(RESOLVE_BENEATH)` (`sys::open_beneath`). Refuses images over the pixel limit from their headers, before decoding. Safe Rust, no `unsafe`; its URL and signature handling is tested in `src/proxy.rs`'s tests (including imgproxy's documented signature example), the pipeline in `tests/pipeline.rs`, the geometry options in `tests/geometry.rs`, EXIF orientation and the response options in `tests/exif.rs`, the filters, watermarks and smart gravity in `tests/filter.rs`, `tests/watermark.rs` and `tests/smart.rs` |
| `src/handler.rs` | The HTTP routes, status codes and response fields | Application code: sends what `proxy.rs` returns, through verilith-server's verified response path |
| `src/bin/verilith-imgproxy.rs` | Flags and environment variables | Application code |
| verilith-sha2's `HmacSha256` | URL signatures | Verified (its README): `verify` returns exactly whether the tag is the HMAC of the key and data, in time that depends only on the lengths |
| verilith-http's `parse_response` and `ChunkedDecoder` | Fetching `http://` sources | Verified (its README): the response head and the body's framing are the specification's |
| `std::net` | DNS resolution and TCP for `http://` and `https://` sources | The standard library |
| verilith-tls's client and verilith-tls-aws-lc's `client::TlsStream` (`--features tls`) | `https://` sources: the TLS 1.3 handshake, certificate chain and host name checks, and the record layer | verilith-tls's handshake, record layer and verilith-x509's chain and name checks are verified (their READMEs); the cryptography is aws-lc's, trusted (verilith-tls-aws-lc's CRYPTO.md). The trust anchors are whatever the CA bundle holds. A connection that ends without close_notify is a read error, so a body read until close is never taken short |
| verilith-jpeg's `encode_rgb` | JPEG output | Verified (its README and TRUST.md): checks its own input; the file decodes, under its specification, to what libjpeg-turbo would code |
| verilith-webp's `capi::decode` and `get_features` | WebP decoding | Plain-Rust wrappers in verilith-webp over its verified decoders (that crate's trusted base; lossy VP8 is proven safe, not correct) |

What is not here at all, so not trusted either: encoders other than PNG and JPEG.
