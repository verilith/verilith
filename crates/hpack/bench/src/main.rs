//! HPACK encoders on the same header lists: verilith-hpack's verified
//! encoder, h2's (the Rust HTTP/2 stack under hyper), and nghttp2's
//! deflater (under curl, Apache, Node.js). Prints, per workload and
//! encoder, ns per header block and bytes per block.
//!
//! A workload is the header blocks of one connection, encoded in order by
//! one encoder made for it, so the dynamic table does what it does in
//! use; the time per block includes making the encoder, spread over the
//! connection's blocks. Every encoder's output is checked, by
//! verilith-hpack's decoder, to decode to the fields given.
use bytes::BytesMut;
use std::hint::black_box;
use std::time::Instant;
use verilith_hpack::{Decoder, Encoder, Feed, Header};

// ---------------------------------------------------------------------------
// Workloads
// ---------------------------------------------------------------------------

type Block = Vec<(Vec<u8>, Vec<u8>, bool)>;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn hex(&mut self, n: usize) -> String {
        (0..n).map(|_| b"0123456789abcdef"[self.below(16) as usize] as char).collect()
    }
}

fn f(n: &str, v: &str) -> (Vec<u8>, Vec<u8>, bool) {
    (n.as_bytes().to_vec(), v.as_bytes().to_vec(), false)
}

/// Responses of a static file server: the same head every time but for
/// the length, the ETag, and the date, which changes every 50 responses.
fn static_responses(n: usize) -> Vec<Block> {
    let mut r = Rng(1);
    let types = ["text/html; charset=utf-8", "text/css", "application/javascript", "image/png", "image/webp"];
    let mods = ["Tue, 24 Nov 2026 10:00:00 GMT", "Mon, 23 Nov 2026 08:30:00 GMT", "Fri, 20 Nov 2026 17:45:12 GMT"];
    (0..n)
        .map(|i| {
            let s = 10 + i / 50;
            vec![
                f(":status", "200"),
                f("content-type", types[r.below(5) as usize]),
                f("content-length", &r.below(200000).to_string()),
                f("date", &format!("Thu, 26 Nov 2026 06:{:02}:{:02} GMT", s / 60 % 60, s % 60)),
                f("server", "verilith"),
                f("etag", &format!("\"{}\"", r.hex(16))),
                f("last-modified", mods[r.below(3) as usize]),
                f("cache-control", "public, max-age=31536000, immutable"),
                f("accept-ranges", "bytes"),
                f("vary", "accept-encoding"),
                f("content-encoding", "br"),
                f("strict-transport-security", "max-age=63072000; includeSubDomains; preload"),
            ]
        })
        .collect()
}

/// Requests of a browser loading a page's assets: the same headers every
/// time but for the path, with a long cookie (sent as sensitive, as
/// browsers' HTTP/2 stacks do for short cookies) and the usual Chrome set.
fn browser_requests(n: usize) -> Vec<Block> {
    let mut r = Rng(2);
    let cookie = format!("session={}; _ga=GA1.2.{}.{}; prefs=dark", r.hex(64), r.below(1 << 30), r.below(1 << 30));
    (0..n)
        .map(|_| {
            let ext = ["js", "css", "png", "woff2"][r.below(4) as usize];
            vec![
                f(":method", "GET"),
                f(":scheme", "https"),
                f(":authority", "www.example.com"),
                f(":path", &format!("/static/{}/asset-{}.{ext}", r.hex(8), r.below(1000))),
                f("sec-ch-ua", "\"Chromium\";v=\"131\", \"Not_A Brand\";v=\"24\""),
                f("sec-ch-ua-mobile", "?0"),
                f("sec-ch-ua-platform", "\"macOS\""),
                f("user-agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"),
                f("accept", "*/*"),
                f("sec-fetch-site", "same-origin"),
                f("sec-fetch-mode", "no-cors"),
                f("sec-fetch-dest", "script"),
                f("referer", "https://www.example.com/"),
                f("accept-encoding", "gzip, deflate, br, zstd"),
                f("accept-language", "en-US,en;q=0.9"),
                (b"cookie".to_vec(), cookie.as_bytes().to_vec(), true),
            ]
        })
        .collect()
}

/// API responses: small JSON responses with a request ID that is
/// different every time.
fn api_responses(n: usize) -> Vec<Block> {
    let mut r = Rng(3);
    (0..n)
        .map(|_| {
            vec![
                f(":status", if r.below(10) == 0 { "404" } else { "200" }),
                f("content-type", "application/json"),
                f("content-length", &r.below(5000).to_string()),
                f("x-request-id", &r.hex(32)),
                f("cache-control", "no-store"),
                f("server", "verilith"),
            ]
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The encoders
// ---------------------------------------------------------------------------

trait Enc {
    fn encode(&mut self, block: usize, out: &mut Vec<u8>);
}

struct Vh<'a> {
    e: Encoder,
    blocks: &'a [Vec<Header<'a>>],
}
impl Enc for Vh<'_> {
    #[inline(never)]
    fn encode(&mut self, block: usize, out: &mut Vec<u8>) {
        assert!(self.e.encode(&self.blocks[block], out));
    }
}

/// h2's encoder takes `http` header names and values; they are made once,
/// outside the timing, and cloned (a reference count) per block.
struct H2<'a> {
    e: h2::hpack::Encoder,
    blocks: &'a [Vec<h2::hpack::Header<Option<http::HeaderName>>>],
    buf: BytesMut,
}
impl Enc for H2<'_> {
    #[inline(never)]
    fn encode(&mut self, block: usize, out: &mut Vec<u8>) {
        self.buf.clear();
        self.e.encode(self.blocks[block].iter().cloned(), &mut self.buf);
        out.extend_from_slice(&self.buf);
    }
}

#[repr(C)]
struct Nv {
    name: *const u8,
    value: *const u8,
    namelen: usize,
    valuelen: usize,
    flags: u8,
}

unsafe extern "C" {
    fn nghttp2_hd_deflate_new(d: *mut *mut u8, max: usize) -> i32;
    fn nghttp2_hd_deflate_del(d: *mut u8);
    fn nghttp2_hd_deflate_hd(d: *mut u8, buf: *mut u8, buflen: usize, nva: *const Nv, nvlen: usize) -> isize;
    fn nghttp2_hd_deflate_bound(d: *mut u8, nva: *const Nv, nvlen: usize) -> usize;
    fn nghttp2_hd_inflate_new(d: *mut *mut u8) -> i32;
    fn nghttp2_hd_inflate_del(d: *mut u8);
    fn nghttp2_hd_inflate_hd3(d: *mut u8, nv: *mut Nv, flags: *mut i32, inp: *const u8, len: usize, fin: i32) -> isize;
    fn nghttp2_hd_inflate_end_headers(d: *mut u8) -> i32;
}

/// Decodes every block an encoder writes with nghttp2's decoder, a second
/// decoder that shares no code with verilith-hpack, and checks the fields
/// and their "never indexed" flags.
fn check_nghttp2<E: Enc>(blocks: &[Block], mut e: E, name: &str) {
    let mut d = std::ptr::null_mut();
    assert_eq!(unsafe { nghttp2_hd_inflate_new(&mut d) }, 0);
    let mut out = Vec::new();
    for (b, want) in blocks.iter().enumerate() {
        out.clear();
        e.encode(b, &mut out);
        let mut got = Vec::new();
        let mut at = 0;
        loop {
            let mut nv = Nv { name: std::ptr::null(), value: std::ptr::null(), namelen: 0, valuelen: 0, flags: 0 };
            let mut fl = 0;
            let n = unsafe { nghttp2_hd_inflate_hd3(d, &mut nv, &mut fl, out.as_ptr().add(at), out.len() - at, 1) };
            assert!(n >= 0, "{name}: nghttp2 rejects block {b}");
            at += n as usize;
            if fl & 2 != 0 {
                let s = |p: *const u8, l: usize| unsafe { std::slice::from_raw_parts(p, l) }.to_vec();
                got.push((s(nv.name, nv.namelen), s(nv.value, nv.valuelen), nv.flags & 1 != 0));
            }
            if fl & 1 != 0 {
                break;
            }
        }
        unsafe { nghttp2_hd_inflate_end_headers(d) };
        assert_eq!(&got, want, "{name}: block {b}, decoded by nghttp2");
    }
    unsafe { nghttp2_hd_inflate_del(d) };
}

struct Ng<'a> {
    d: *mut u8,
    blocks: &'a [Vec<Nv>],
}
impl Ng<'_> {
    fn new(blocks: &[Vec<Nv>]) -> Ng<'_> {
        let mut d = std::ptr::null_mut();
        assert_eq!(unsafe { nghttp2_hd_deflate_new(&mut d, 4096) }, 0);
        Ng { d, blocks }
    }
}
impl Drop for Ng<'_> {
    fn drop(&mut self) {
        unsafe { nghttp2_hd_deflate_del(self.d) }
    }
}
impl Enc for Ng<'_> {
    #[inline(never)]
    fn encode(&mut self, block: usize, out: &mut Vec<u8>) {
        let nv = &self.blocks[block];
        let bound = unsafe { nghttp2_hd_deflate_bound(self.d, nv.as_ptr(), nv.len()) };
        out.reserve(bound);
        let at = out.len();
        let n = unsafe { nghttp2_hd_deflate_hd(self.d, out.as_mut_ptr().add(at), bound, nv.as_ptr(), nv.len()) };
        assert!(n >= 0);
        unsafe { out.set_len(at + n as usize) };
    }
}

// ---------------------------------------------------------------------------
// Timing
// ---------------------------------------------------------------------------

/// Encodes the connection's blocks with a fresh encoder from `mk`, `reps`
/// times; the best time per block, and the bytes per block.
fn time<E: Enc>(n: usize, reps: usize, mut mk: impl FnMut() -> E) -> (f64, f64) {
    let mut out = Vec::with_capacity(1 << 16);
    let mut best = f64::MAX;
    let mut bytes = 0;
    for rep in 0..reps + reps / 10 + 1 {
        let t = Instant::now();
        let mut e = mk();
        bytes = 0;
        for b in 0..n {
            out.clear();
            e.encode(b, &mut out);
            bytes += out.len();
            black_box(&out);
        }
        drop(e);
        let dt = t.elapsed().as_secs_f64();
        if rep > reps / 10 {
            best = best.min(dt / n as f64);
        }
    }
    (best * 1e9, bytes as f64 / n as f64)
}

/// Decodes every block an encoder writes with verilith-hpack's decoder and
/// checks the fields.
fn check<E: Enc>(blocks: &[Block], mut e: E, name: &str) {
    let mut d = Decoder::new().unwrap();
    let mut out = Vec::new();
    for (b, want) in blocks.iter().enumerate() {
        out.clear();
        e.encode(b, &mut out);
        let mut got = Vec::new();
        let mut inp: &[u8] = &out;
        loop {
            match d.feed(inp, true) {
                Feed::Field(k, never) => {
                    got.push((d.name().to_vec(), d.value().to_vec(), never));
                    inp = &inp[k..];
                }
                Feed::Final => break,
                Feed::More | Feed::Bad => panic!("{name}: block {b} does not decode"),
            }
        }
        d.end_block();
        let strip = |v: &Block| v.iter().map(|(n, v, _)| (n.clone(), v.clone())).collect::<Vec<_>>();
        assert_eq!(strip(&got), strip(want), "{name}: block {b}");
    }
}

fn main() {
    let only = std::env::var("BENCH_ONLY").ok();
    let run = |e: &str| only.as_deref().map_or(true, |o| o == e);
    let conns: [(&str, Vec<Block>); 5] = [
        ("static file responses x100", static_responses(100)),
        ("browser requests x100", browser_requests(100)),
        ("API responses x100", api_responses(100)),
        ("static file response x1 (new connection)", static_responses(1)),
        ("browser request x1 (new connection)", browser_requests(1)),
    ];
    let wl_only: Option<usize> = std::env::var("BENCH_WL").ok().map(|s| s.parse().unwrap());
    for (k, (wl, blocks)) in conns.iter().enumerate() {
        if wl_only.map_or(false, |w| w != k) {
            continue;
        }
        let n = blocks.len();
        let reps = std::env::var("BENCH_BLOCKS").map_or(200_000, |s| s.parse().unwrap()) / n;
        if run("vhpack") {
            let hs: Vec<Vec<Header>> = blocks
                .iter()
                .map(|b| b.iter().map(|(n, v, s)| Header { name: n, value: v, sensitive: *s }).collect())
                .collect();
            let mk = || Vh { e: Encoder::new().unwrap(), blocks: &hs };
            check(blocks, mk(), "vhpack");
            check_nghttp2(blocks, mk(), "vhpack");
            let (ns, bytes) = time(n, reps, mk);
            println!("{wl}\tvhpack\t{ns:.1}\t{bytes:.1}");
        }
        if run("h2") {
            let hs: Vec<Vec<h2::hpack::Header<Option<http::HeaderName>>>> = blocks
                .iter()
                .map(|b| {
                    b.iter()
                        .map(|(n, v, s)| {
                            let mut value = http::HeaderValue::from_bytes(v).unwrap();
                            value.set_sensitive(*s);
                            if n[0] == b':' {
                                pseudo(n, v)
                            } else {
                                h2::hpack::Header::Field {
                                    name: Some(http::HeaderName::from_bytes(n).unwrap()),
                                    value,
                                }
                            }
                        })
                        .collect()
                })
                .collect();
            let mk = || H2 { e: h2::hpack::Encoder::default(), blocks: &hs, buf: BytesMut::with_capacity(1 << 16) };
            check(blocks, mk(), "h2");
            let (ns, bytes) = time(n, reps, mk);
            println!("{wl}\th2\t{ns:.1}\t{bytes:.1}");
        }
        if run("nghttp2") {
            let nvs: Vec<Vec<Nv>> = blocks
                .iter()
                .map(|b| {
                    b.iter()
                        .map(|(n, v, s)| Nv {
                            name: n.as_ptr(),
                            value: v.as_ptr(),
                            namelen: n.len(),
                            valuelen: v.len(),
                            flags: *s as u8,
                        })
                        .collect()
                })
                .collect();
            check(blocks, Ng::new(&nvs), "nghttp2");
            let (ns, bytes) = time(n, reps, || Ng::new(&nvs));
            println!("{wl}\tnghttp2\t{ns:.1}\t{bytes:.1}");
        }
    }
}

/// h2's pseudo-header fields.
fn pseudo(n: &[u8], v: &[u8]) -> h2::hpack::Header<Option<http::HeaderName>> {
    use h2::hpack::{BytesStr, Header as H};
    let s = || BytesStr::try_from(bytes::Bytes::copy_from_slice(v)).unwrap();
    match n {
        b":method" => H::Method(http::Method::from_bytes(v).unwrap()),
        b":scheme" => H::Scheme(s()),
        b":authority" => H::Authority(s()),
        b":path" => H::Path(s()),
        b":status" => H::Status(http::StatusCode::from_bytes(v).unwrap()),
        _ => panic!("pseudo-header {n:?}"),
    }
}
