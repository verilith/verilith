//! vqpack against ls-qpack: compressed size, encoding time and decoding
//! time per field section, on browser requests and server responses, over
//! one connection each. Each library decodes what it encoded, and (as an
//! interoperability check, before timing) what the other one encoded.
//!
//! Each run records the connection once (field sections, encoder stream,
//! decoder stream), then times the encoder replaying it (the decoder stream
//! fed back at the same points, so the encoder makes the same choices) and
//! the decoder replaying it. `BENCH_ONLY=<substring>` limits the rows.
use std::hint::black_box;
use std::time::Instant;
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};

mod lsq {
    use std::os::raw::{c_int, c_uint, c_void};
    unsafe extern "C" {
        pub fn lsq_enc_new(max_cap: c_uint, cap: c_uint, blocked: c_uint, sdtc: *mut u8, sdtc_sz: *mut usize) -> *mut c_void;
        pub fn lsq_enc_free(e: *mut c_void);
        pub fn lsq_encode(
            e: *mut c_void, stream: u64, seqno: c_uint, buf: *const u8, offs: *const u32, n: usize,
            hb: *mut u8, hb_cap: usize, hb_sz: *mut usize, es: *mut u8, es_cap: usize, es_sz: *mut usize,
        ) -> c_int;
        pub fn lsq_enc_decoder_in(e: *mut c_void, b: *const u8, n: usize) -> c_int;
        pub fn lsq_dec_new(cap: c_uint, blocked: c_uint) -> *mut c_void;
        pub fn lsq_dec_free(d: *mut c_void);
        pub fn lsq_dec_enc_in(d: *mut c_void, b: *const u8, n: usize, out: *mut u8, out_sz: *mut usize) -> c_int;
        pub fn lsq_decode(
            d: *mut c_void, stream: u64, b: *const u8, n: usize, out: *mut u8, out_sz: *mut usize,
            count: *mut usize, bytes: *mut usize,
        ) -> c_int;
        pub fn lsq_dec_arena(d: *mut c_void, len: *mut usize) -> *const u8;
    }
}

type Hdrs = Vec<(Vec<u8>, Vec<u8>)>;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn hex(&mut self, n: usize) -> String {
        (0..n).map(|_| char::from_digit(self.below(16) as u32, 16).unwrap()).collect()
    }
}

fn h(n: &str, v: impl Into<String>) -> (Vec<u8>, Vec<u8>) {
    (n.as_bytes().to_vec(), v.into().into_bytes())
}

/// What a browser sends loading pages from one site: documents, then their
/// styles, scripts, images, fonts and API calls.
fn requests(n: usize) -> Vec<Hdrs> {
    let mut r = Rng(0x2545_F491_4F6C_DD1D);
    let session = r.hex(32);
    let ga = r.below(1 << 31);
    let mut out = Vec::new();
    for i in 0..n {
        let kind = if i % 25 == 0 { 0 } else { 1 + r.below(5) };
        let (path, accept, dest, mode, prio) = match kind {
            0 => (format!("/products/{}", r.below(500)), "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8", "document", "navigate", "u=0, i"),
            1 => (format!("/static/css/{}.{}.css", ["main", "vendor", "theme"][r.below(3) as usize], r.hex(8)), "text/css,*/*;q=0.1", "style", "no-cors", "u=0"),
            2 => (format!("/static/js/{}.{}.chunk.js", r.below(40), r.hex(8)), "*/*", "script", "no-cors", "u=1"),
            3 => (format!("/images/products/{}-{}w.webp", r.below(2000), [320, 640, 1280][r.below(3) as usize]), "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8", "image", "no-cors", "u=5, i"),
            4 => (format!("/fonts/inter-{}.woff2", ["regular", "bold", "italic"][r.below(3) as usize]), "*/*", "font", "cors", "u=3"),
            _ => (format!("/api/v2/recommendations?item={}&limit=12", r.below(500)), "application/json", "empty", "cors", "u=4"),
        };
        let mut v = vec![
            h(":method", "GET"),
            h(":scheme", "https"),
            h(":authority", "shop.example.com"),
            h(":path", path),
            h("sec-ch-ua", "\"Chromium\";v=\"131\", \"Not_A Brand\";v=\"24\", \"Google Chrome\";v=\"131\""),
            h("sec-ch-ua-mobile", "?0"),
            h("sec-ch-ua-platform", "\"Linux\""),
            h("user-agent", "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"),
            h("accept", accept),
            h("sec-fetch-site", if kind == 0 { "none" } else { "same-origin" }),
            h("sec-fetch-mode", mode),
            h("sec-fetch-dest", dest),
        ];
        if kind != 0 {
            v.push(h("referer", "https://shop.example.com/products/17"));
        }
        v.push(h("accept-encoding", "gzip, deflate, br, zstd"));
        v.push(h("accept-language", "en-US,en;q=0.9"));
        v.push(h("cookie", format!("_ga=GA1.2.{ga}.1700000000; session={session}; theme=dark; cart=3")));
        v.push(h("priority", prio));
        out.push(v);
    }
    out
}

/// What a server answers to those requests.
fn responses(n: usize) -> Vec<Hdrs> {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let mut out = Vec::new();
    for i in 0..n {
        let kind = if i % 25 == 0 { 0 } else { 1 + r.below(5) };
        let status = if kind != 0 && r.below(10) == 0 { "304" } else if r.below(50) == 0 { "404" } else { "200" };
        let (ctype, cache, enc) = match kind {
            0 => ("text/html; charset=utf-8", "private, no-cache", true),
            1 => ("text/css", "public, max-age=31536000, immutable", true),
            2 => ("application/javascript", "public, max-age=31536000, immutable", true),
            3 => ("image/webp", "public, max-age=86400", false),
            4 => ("font/woff2", "public, max-age=31536000, immutable", false),
            _ => ("application/json", "no-store", true),
        };
        let mut v = vec![
            h(":status", status),
            h("date", format!("Thu, 26 Nov 2026 10:{:02}:{:02} GMT", i / 600, (i / 10) % 60)),
            h("server", "verilith"),
            h("content-type", ctype),
            h("cache-control", cache),
        ];
        if status != "304" {
            v.push(h("content-length", format!("{}", 200 + r.below(200_000))));
        }
        if enc {
            v.push(h("content-encoding", "br"));
            v.push(h("vary", "accept-encoding"));
        }
        v.push(h("etag", format!("\"{}\"", r.hex(16))));
        if kind != 0 && kind != 5 {
            v.push(h("last-modified", "Mon, 23 Nov 2026 08:12:31 GMT"));
        }
        if kind == 5 {
            v.push(h("access-control-allow-origin", "*"));
        }
        v.push(h("strict-transport-security", "max-age=63072000; includeSubDomains; preload"));
        v.push(h("x-content-type-options", "nosniff"));
        if i == 0 {
            v.push(h("alt-svc", "h3=\":443\"; ma=86400"));
        }
        out.push(v);
    }
    out
}

/// One connection, recorded: per section, the section, the encoder stream
/// bytes it came with, and the decoder stream bytes sent back after it.
struct Rec {
    hb: Vec<Vec<u8>>,
    es: Vec<Vec<u8>>,
    ds: Vec<Vec<u8>>,
}

impl Rec {
    fn bytes(&self) -> usize {
        self.hb.iter().map(|x| x.len()).sum::<usize>() + self.es.iter().map(|x| x.len()).sum::<usize>()
    }
}

fn fields(h: &Hdrs) -> Fields {
    let mut f = Fields::new();
    for (n, v) in h {
        f.push(n, v, false);
    }
    f
}

fn same(f: &Fields, h: &Hdrs) -> bool {
    f.len() == h.len() && (0..f.len()).all(|i| {
        let (n, v, _) = f.get(i);
        n == &h[i].0[..] && v == &h[i].1[..]
    })
}

/// Our decoder on a recorded connection: checks every section, and
/// returns the decoder stream it wrote after each.
fn v_decode(rec: &Rec, secs: &[Hdrs], cap: u64, blocked: u64) -> Vec<Vec<u8>> {
    let mut d = Decoder::new(cap, blocked, 1 << 20).unwrap();
    let mut out = Fields::new();
    let mut ready = Vec::new();
    let mut ds = Vec::new();
    for (i, want) in secs.iter().enumerate() {
        assert!(d.feed_encoder(&rec.es[i], &mut ready));
        assert_eq!(d.decode(4 * i as u64, &rec.hb[i], &mut out), Res::Done, "section {i}");
        assert!(same(&out, want), "section {i}");
        let mut o = Vec::new();
        d.take_output(&mut o);
        ds.push(o);
    }
    ds
}

fn v_record(secs: &[Hdrs], cap: u64, blocked: u64) -> Rec {
    let mut e = Encoder::new(cap, blocked, cap).unwrap();
    let mut d = Decoder::new(cap, blocked, 1 << 20).unwrap();
    let mut rec = Rec { hb: vec![], es: vec![], ds: vec![] };
    let mut out = Fields::new();
    let mut ready = Vec::new();
    for (i, s) in secs.iter().enumerate() {
        let mut hb = Vec::new();
        let mut es = Vec::new();
        e.encode(4 * i as u64, &fields(s), &mut hb);
        e.take_output(&mut es);
        assert!(d.feed_encoder(&es, &mut ready));
        assert_eq!(d.decode(4 * i as u64, &hb, &mut out), Res::Done);
        assert!(same(&out, s));
        let mut ds = Vec::new();
        d.take_output(&mut ds);
        assert!(e.feed_decoder(&ds));
        rec.hb.push(hb);
        rec.es.push(es);
        rec.ds.push(ds);
    }
    rec
}

fn v_time_encode(secs: &[Fields], rec: &Rec, cap: u64, blocked: u64) -> f64 {
    let mut hb = Vec::with_capacity(4096);
    let mut es = Vec::with_capacity(4096);
    let t = Instant::now();
    let mut e = Encoder::new(cap, blocked, cap).unwrap();
    for (i, f) in secs.iter().enumerate() {
        hb.clear();
        es.clear();
        e.encode(4 * i as u64, f, &mut hb);
        e.take_output(&mut es);
        black_box((&hb, &es));
        e.feed_decoder(&rec.ds[i]);
    }
    t.elapsed().as_nanos() as f64 / secs.len() as f64
}

fn v_time_decode(rec: &Rec, cap: u64, blocked: u64) -> f64 {
    let mut out = Fields::new();
    let mut ready = Vec::new();
    let mut ds = Vec::with_capacity(64);
    let t = Instant::now();
    let mut d = Decoder::new(cap, blocked, 1 << 20).unwrap();
    for i in 0..rec.hb.len() {
        d.feed_encoder(&rec.es[i], &mut ready);
        let r = d.decode(4 * i as u64, &rec.hb[i], &mut out);
        black_box((r, &out));
        ds.clear();
        d.take_output(&mut ds);
    }
    t.elapsed().as_nanos() as f64 / rec.hb.len() as f64
}

/// The fields as ls-qpack takes them: one buffer, four offsets a field.
struct Flat {
    buf: Vec<u8>,
    offs: Vec<u32>,
}

fn flat(h: &Hdrs) -> Flat {
    let mut f = Flat { buf: vec![], offs: vec![] };
    for (n, v) in h {
        f.offs.push(f.buf.len() as u32);
        f.offs.push(n.len() as u32);
        f.buf.extend_from_slice(n);
        f.offs.push(f.buf.len() as u32);
        f.offs.push(v.len() as u32);
        f.buf.extend_from_slice(v);
    }
    f
}

fn concat(h: &Hdrs) -> Vec<u8> {
    h.iter().flat_map(|(n, v)| n.iter().chain(v.iter()).copied()).collect()
}

fn l_enc_new(cap: u64, blocked: u64) -> (*mut std::os::raw::c_void, Vec<u8>) {
    let mut sdtc = [0u8; 16];
    let mut sz = sdtc.len();
    let e = unsafe { lsq::lsq_enc_new(cap as u32, cap as u32, blocked as u32, sdtc.as_mut_ptr(), &mut sz) };
    assert!(!e.is_null());
    (e, sdtc[..if cap > 0 { sz } else { 0 }].to_vec())
}

/// Encodes into `hb` and `es`, which must be 64 KiB long; returns the
/// lengths written.
fn l_encode_raw(e: *mut std::os::raw::c_void, i: usize, f: &Flat, hb: &mut [u8], es: &mut [u8]) -> (usize, usize) {
    let (mut hs, mut ess) = (0, 0);
    let r = unsafe {
        lsq::lsq_encode(e, 4 * i as u64, 0, f.buf.as_ptr(), f.offs.as_ptr(), f.offs.len() / 4,
            hb.as_mut_ptr(), hb.len(), &mut hs, es.as_mut_ptr(), es.len(), &mut ess)
    };
    assert_eq!(r, 0);
    (hs, ess)
}

fn l_encode(e: *mut std::os::raw::c_void, i: usize, f: &Flat, hb: &mut Vec<u8>, es: &mut Vec<u8>) {
    let mut a = vec![0u8; 64 * 1024];
    let mut b = vec![0u8; 64 * 1024];
    let (hs, ess) = l_encode_raw(e, i, f, &mut a, &mut b);
    hb.clear();
    hb.extend_from_slice(&a[..hs]);
    es.extend_from_slice(&b[..ess]);
}

/// ls-qpack's decoder on a recorded connection; checks every section.
fn l_decode(rec: &Rec, secs: &[Hdrs], cap: u64, blocked: u64) -> Vec<Vec<u8>> {
    let d = unsafe { lsq::lsq_dec_new(cap as u32, blocked as u32) };
    let mut ds = Vec::new();
    for (i, want) in secs.iter().enumerate() {
        let mut o = [0u8; 32];
        let mut osz = 0;
        assert_eq!(unsafe { lsq::lsq_dec_enc_in(d, rec.es[i].as_ptr(), rec.es[i].len(), o.as_mut_ptr(), &mut osz) }, 0);
        let mut out = o[..osz].to_vec();
        let (mut asz, mut count, mut bytes) = (0, 0, 0);
        let r = unsafe { lsq::lsq_decode(d, 4 * i as u64, rec.hb[i].as_ptr(), rec.hb[i].len(), o.as_mut_ptr(), &mut asz, &mut count, &mut bytes) };
        assert_eq!(r, 0, "section {i}");
        assert_eq!(count, want.len(), "section {i}");
        let mut alen = 0;
        let a = unsafe { std::slice::from_raw_parts(lsq::lsq_dec_arena(d, &mut alen), alen) };
        assert_eq!(a, &concat(want)[..], "section {i}");
        out.extend_from_slice(&o[..asz]);
        ds.push(out);
    }
    unsafe { lsq::lsq_dec_free(d) };
    ds
}

fn l_record(secs: &[Hdrs], cap: u64, blocked: u64) -> Rec {
    let (e, sdtc) = l_enc_new(cap, blocked);
    let flats: Vec<Flat> = secs.iter().map(flat).collect();
    let mut rec = Rec { hb: vec![], es: vec![], ds: vec![] };
    let d = unsafe { lsq::lsq_dec_new(cap as u32, blocked as u32) };
    for (i, f) in flats.iter().enumerate() {
        let mut hb = Vec::new();
        let mut es = if i == 0 { sdtc.clone() } else { Vec::new() };
        l_encode(e, i, f, &mut hb, &mut es);
        let mut o = [0u8; 32];
        let mut osz = 0;
        assert_eq!(unsafe { lsq::lsq_dec_enc_in(d, es.as_ptr(), es.len(), o.as_mut_ptr(), &mut osz) }, 0);
        let mut ds = o[..osz].to_vec();
        let (mut asz, mut c, mut b) = (0, 0, 0);
        assert_eq!(unsafe { lsq::lsq_decode(d, 4 * i as u64, hb.as_ptr(), hb.len(), o.as_mut_ptr(), &mut asz, &mut c, &mut b) }, 0);
        ds.extend_from_slice(&o[..asz]);
        assert_eq!(unsafe { lsq::lsq_enc_decoder_in(e, ds.as_ptr(), ds.len()) }, 0);
        rec.hb.push(hb);
        rec.es.push(es);
        rec.ds.push(ds);
    }
    unsafe {
        lsq::lsq_dec_free(d);
        lsq::lsq_enc_free(e);
    }
    rec
}

fn l_time_encode(flats: &[Flat], rec: &Rec, cap: u64, blocked: u64) -> f64 {
    let mut hb = vec![0u8; 64 * 1024];
    let mut es = vec![0u8; 64 * 1024];
    let t = Instant::now();
    let (e, _) = l_enc_new(cap, blocked);
    for (i, f) in flats.iter().enumerate() {
        let n = l_encode_raw(e, i, f, &mut hb, &mut es);
        black_box((&hb, &es, n));
        unsafe { lsq::lsq_enc_decoder_in(e, rec.ds[i].as_ptr(), rec.ds[i].len()) };
    }
    unsafe { lsq::lsq_enc_free(e) };
    t.elapsed().as_nanos() as f64 / flats.len() as f64
}

fn l_time_decode(rec: &Rec, cap: u64, blocked: u64) -> f64 {
    let t = Instant::now();
    let d = unsafe { lsq::lsq_dec_new(cap as u32, blocked as u32) };
    let mut o = [0u8; 32];
    for i in 0..rec.hb.len() {
        let mut osz = 0;
        unsafe { lsq::lsq_dec_enc_in(d, rec.es[i].as_ptr(), rec.es[i].len(), o.as_mut_ptr(), &mut osz) };
        let (mut asz, mut c, mut b) = (0, 0, 0);
        let r = unsafe { lsq::lsq_decode(d, 4 * i as u64, rec.hb[i].as_ptr(), rec.hb[i].len(), o.as_mut_ptr(), &mut asz, &mut c, &mut b) };
        black_box((r, c, b));
    }
    unsafe { lsq::lsq_dec_free(d) };
    t.elapsed().as_nanos() as f64 / rec.hb.len() as f64
}

/// The best of `reps` runs.
fn best(reps: usize, mut f: impl FnMut() -> f64) -> f64 {
    (0..reps).map(|_| f()).fold(f64::INFINITY, f64::min)
}

fn main() {
    let only = std::env::var("BENCH_ONLY").ok();
    let n = 200;
    let reps: usize = std::env::var("BENCH_REPS").ok().and_then(|r| r.parse().ok()).unwrap_or(200);
    let loads = [("requests", requests(n)), ("responses", responses(n))];
    let settings = [(4096u64, 100u64), (0, 0)];
    println!("workload\ttable\tlibrary\tbytes/section\tencode ns/section\tdecode ns/section");
    for (name, secs) in &loads {
        let raw: usize = secs.iter().map(|s| s.iter().map(|(n, v)| n.len() + v.len()).sum::<usize>()).sum();
        for &(cap, blocked) in &settings {
            let vr = v_record(secs, cap, blocked);
            let lr = l_record(secs, cap, blocked);
            // Interoperability, both ways.
            v_decode(&lr, secs, cap, blocked);
            l_decode(&vr, secs, cap, blocked);
            let fs: Vec<Fields> = secs.iter().map(fields).collect();
            let flats: Vec<Flat> = secs.iter().map(flat).collect();
            let tab = if cap == 0 { "static only".to_string() } else { format!("{cap} B, {blocked} blocked") };
            for lib in ["vqpack", "ls-qpack"] {
                let row = format!("{name}\t{tab}\t{lib}");
                if only.as_deref().is_some_and(|o| !row.contains(o)) {
                    continue;
                }
                let (bytes, enc, dec) = if lib == "vqpack" {
                    (vr.bytes(), best(reps, || v_time_encode(&fs, &vr, cap, blocked)), best(reps, || v_time_decode(&vr, cap, blocked)))
                } else {
                    (lr.bytes(), best(reps, || l_time_encode(&flats, &lr, cap, blocked)), best(reps, || l_time_decode(&lr, cap, blocked)))
                };
                println!("{row}\t{:.1}\t{enc:.0}\t{dec:.0}", bytes as f64 / n as f64);
            }
            if only.is_none() {
                eprintln!("# {name}: {:.1} bytes/section uncompressed", raw as f64 / n as f64);
            }
        }
    }
}
