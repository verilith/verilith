//! verilith-h2's frame layer against h2 (the crate hyper uses) and nghttp2,
//! on the same frames, in the same process.
//!
//!   NGHTTP2_LIB=.../nghttp2-1.70.0/lib cargo run --release [-- ROUNDS]
//!   ... cargo run --release -- agree [CASES]
//!
//! What each column runs:
//! - vh2: `verilith_h2::parse` over the buffer, borrowing payloads.
//! - h2 fn: h2's own frame functions (`Head::parse` and each type's `load`,
//!   with h2's `unstable` feature), on the payload h2's codec would split
//!   off its read buffer. No HPACK.
//! - h2 codec: `h2::Codec`, h2's whole frame reader (length-delimited
//!   framing into a `BytesMut`, then the same functions), read from memory.
//!   Used where the frames carry no header blocks, since the codec would
//!   also HPACK-decode those.
//! - nghttp2: nghttp2_frame.c's decode functions with the frame checks of
//!   nghttp2_session.c's inbound state machine (ngwrap.c): a lower bound for
//!   nghttp2, whose session does more per frame.
use bytes::{Bytes, BytesMut};
use std::hint::black_box;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::Instant;
use verilith_h2::spec::*;
use verilith_h2::{encode_head, parse, serialize, Frame, Params, Parsed, Priority};

unsafe extern "C" {
    fn ng_parse_all(b: *const u8, n: usize, acc: *mut u64) -> std::ffi::c_long;
    fn ng_pack_heads(q: *const u32, k: usize, out: *mut u8);
}

const MAX: u32 = 16384;

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
}

static SETTINGS_RAW: [u8; 18] = [0, 3, 0, 0, 0, 100, 0, 4, 0, 0x10, 0, 0, 0, 6, 0, 0, 0x40, 0];
static FRAG: [u8; 40] = [0x82; 40];
static BIG: [u8; 16384] = [0x61; 16384];

fn put(out: &mut Vec<u8>, f: &Frame) {
    serialize(f, MAX, out).unwrap();
}

/// A client's control frames: no DATA, no header blocks.
fn control(n: usize) -> Vec<u8> {
    let mut r = Rng(1);
    let mut v = Vec::new();
    for i in 0..n {
        let stream = 1 + 2 * (i as u32 % 100);
        match r.below(20) {
            0..=7 => put(&mut v, &Frame::WindowUpdate { stream: if r.below(2) == 0 { 0 } else { stream }, increment: 1 + r.below(1 << 20) as u32 }),
            8 => put(&mut v, &Frame::Settings { ack: false, params: Params::new(&SETTINGS_RAW).unwrap() }),
            9 => put(&mut v, &Frame::Settings { ack: true, params: Params::new(&[]).unwrap() }),
            10..=12 => put(&mut v, &Frame::Ping { ack: r.below(2) == 0, opaque: r.next() }),
            13..=15 => put(&mut v, &Frame::RstStream { stream, code: CANCEL }),
            _ => put(&mut v, &Frame::Priority { stream, prio: Priority { exclusive: false, dependency: stream - 1 + 0, weight: 15 } }),
        }
    }
    v
}

/// HEADERS with a 40-byte block fragment; a quarter with PRIORITY, an
/// eighth PADDED.
fn headers(n: usize) -> Vec<u8> {
    let mut r = Rng(2);
    let mut v = Vec::new();
    for i in 0..n {
        let stream = 1 + 2 * i as u32;
        let priority = if r.below(4) == 0 { Some(Priority { exclusive: false, dependency: 0, weight: 255 }) } else { None };
        let pad = if r.below(8) == 0 { Some(8) } else { None };
        put(&mut v, &Frame::Headers { stream, end_stream: true, end_headers: true, pad, priority, fragment: &FRAG });
    }
    v
}

/// A connection's receive side with uploads: DATA of 64 B to 16 KiB among
/// the control frames.
fn stream_mix(n: usize) -> Vec<u8> {
    let mut r = Rng(3);
    let c = control(n);
    let mut v = Vec::new();
    let mut off = 0;
    while off < c.len() {
        let Parsed::Frame(_, k) = parse(&c[off..], MAX) else { unreachable!() };
        v.extend_from_slice(&c[off..off + k]);
        off += k;
        if r.below(2) == 0 {
            let len = [64, 512, 1024, 4096, 16384][r.below(5) as usize];
            put(&mut v, &Frame::Data { stream: 1 + 2 * r.below(100) as u32, end_stream: false, pad: None, data: &BIG[..len] });
        }
    }
    v
}

fn data16k(n: usize) -> Vec<u8> {
    let mut v = Vec::new();
    for i in 0..n {
        put(&mut v, &Frame::Data { stream: 1 + 2 * (i as u32 % 8), end_stream: false, pad: None, data: &BIG });
    }
    v
}

// ---------------------------------------------------------------------------
// The decoders
// ---------------------------------------------------------------------------

fn vh2_all(b: &[u8]) -> (usize, u64) {
    let mut off = 0;
    let mut n = 0;
    let mut acc = 0u64;
    while let Parsed::Frame(f, k) = parse(&b[off..], MAX) {
        acc = acc.wrapping_add(match f {
            Frame::Data { stream, data, .. } => stream as u64 + data.len() as u64 + data.as_ptr() as u64,
            Frame::Headers { stream, fragment, priority, .. } => {
                stream as u64 + fragment.as_ptr() as u64 + fragment.len() as u64 + priority.map_or(0, |p| p.dependency as u64)
            }
            Frame::Priority { stream, prio } => stream as u64 + prio.dependency as u64 + prio.weight as u64,
            Frame::RstStream { stream, code } => stream as u64 + code as u64,
            Frame::Settings { params, .. } => {
                let mut s = 0u64;
                for i in 0..params.len() {
                    s += params.get(i).value as u64;
                }
                s
            }
            Frame::Ping { opaque, .. } => opaque & 0xff,
            Frame::WindowUpdate { stream, increment } => stream as u64 + increment as u64,
            _ => 0,
        });
        off += k;
        n += 1;
    }
    (n, acc)
}

fn h2_fn_all(buf: &mut BytesMut) -> (usize, u64) {
    use h2::frame::{self as hf, Kind};
    let mut n = 0;
    let mut acc = 0u64;
    while buf.len() >= 9 {
        let len = ((buf[0] as usize) << 16) | ((buf[1] as usize) << 8) | buf[2] as usize;
        let fb = buf.split_to(9 + len);
        let head = hf::Head::parse(&fb);
        let p = &fb[9..];
        acc = acc.wrapping_add(match head.kind() {
            Kind::Headers => {
                // As h2's codec does: drop the frame header, then load.
                let mut fb = fb;
                bytes::Buf::advance(&mut fb, 9);
                let (h, frag) = hf::Headers::load(head, fb, 0).unwrap();
                u32::from(h.stream_id()) as u64 + frag.len() as u64 + frag.as_ptr() as u64
            }
            Kind::Priority => {
                let pr = hf::Priority::load(head, p).unwrap();
                black_box(&pr); 1
            }
            Kind::Reset => {
                let r = hf::Reset::load(head, p).unwrap();
                u32::from(r.reason()) as u64 + u32::from(r.stream_id()) as u64
            }
            Kind::Settings => {
                let s = hf::Settings::load(head, p).unwrap();
                s.initial_window_size().unwrap_or(0) as u64 + s.max_concurrent_streams().unwrap_or(0) as u64
            }
            Kind::Ping => {
                let pg = hf::Ping::load(head, p).unwrap();
                pg.payload()[7] as u64
            }
            Kind::WindowUpdate => {
                let w = hf::WindowUpdate::load(head, p).unwrap();
                w.size_increment() as u64 + u32::from(w.stream_id()) as u64
            }
            _ => unreachable!(),
        });
        n += 1;
    }
    (n, acc)
}

/// An in-memory socket for h2's codec: reads come from `data`.
struct Mem {
    data: Bytes,
}
impl tokio::io::AsyncRead for Mem {
    fn poll_read(mut self: Pin<&mut Self>, _: &mut Context<'_>, buf: &mut tokio::io::ReadBuf<'_>) -> Poll<std::io::Result<()>> {
        let k = buf.remaining().min(self.data.len());
        let d = self.data.split_to(k);
        buf.put_slice(&d);
        Poll::Ready(Ok(()))
    }
}
impl tokio::io::AsyncWrite for Mem {
    fn poll_write(self: Pin<&mut Self>, _: &mut Context<'_>, b: &[u8]) -> Poll<std::io::Result<usize>> {
        Poll::Ready(Ok(b.len()))
    }
    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Ready(Ok(()))
    }
    fn poll_shutdown(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

fn h2_codec_all(data: Bytes) -> (usize, Result<u64, String>) {
    use futures_core::Stream;
    let mut codec: h2::Codec<Mem, Bytes> = h2::Codec::new(Mem { data });
    let mut cx = Context::from_waker(Waker::noop());
    let mut n = 0;
    let mut acc = 0u64;
    loop {
        match Pin::new(&mut codec).poll_next(&mut cx) {
            Poll::Ready(Some(Ok(f))) => {
                n += 1;
                acc = acc.wrapping_add(match f {
                    h2::frame::Frame::Data(d) => d.payload().len() as u64 + u32::from(d.stream_id()) as u64,
                    h2::frame::Frame::WindowUpdate(w) => w.size_increment() as u64,
                    h2::frame::Frame::Ping(p) => p.payload()[7] as u64,
                    h2::frame::Frame::Reset(r) => u32::from(r.reason()) as u64,
                    h2::frame::Frame::Settings(s) => s.initial_window_size().unwrap_or(0) as u64,
                    h2::frame::Frame::Priority(p) => { black_box(&p); 1 }
                    _ => 1,
                });
            }
            Poll::Ready(Some(Err(e))) => return (n, Err(format!("{e:?}"))),
            Poll::Ready(None) | Poll::Pending => return (n, Ok(acc)),
        }
    }
}

fn ng_all(b: &[u8]) -> (usize, u64) {
    let mut acc = 0u64;
    let n = unsafe { ng_parse_all(b.as_ptr(), b.len(), &mut acc) };
    assert!(n >= 0, "nghttp2 rejected the corpus");
    (n as usize, acc)
}

// ---------------------------------------------------------------------------
// Timing
// ---------------------------------------------------------------------------

/// Best ns per frame over `rounds` rounds of `reps` passes.
fn time(rounds: usize, frames: usize, mut pass: impl FnMut() -> u64) -> f64 {
    let reps = (200_000 / frames).max(1);
    let mut best = f64::MAX;
    for _ in 0..rounds {
        let t = Instant::now();
        for _ in 0..reps {
            black_box(pass());
        }
        best = best.min(t.elapsed().as_nanos() as f64 / (reps * frames) as f64);
    }
    best
}

fn row(name: &str, bytes: usize, frames: usize, cols: &[(&str, Option<f64>)]) {
    let base = cols[0].1.unwrap();
    let mut s = format!("| {name} | {frames} | {:.1} |", bytes as f64 / frames as f64);
    for (_, c) in cols {
        match c {
            Some(ns) => {
                let gbs = bytes as f64 / frames as f64 / ns;
                s += &format!(" {ns:.2} ns ({gbs:.1} GB/s){} |", if *ns == base { String::new() } else { format!(", {:.2}x", ns / base) });
            }
            None => s += " n/a |",
        }
    }
    println!("{s}");
}

fn bench(rounds: usize) {
    println!("Best of {rounds} rounds; ns per frame (lower is better), and the slowdown against vh2.\n");
    println!("| case | frames | bytes/frame | vh2 | h2 fn | h2 codec | nghttp2 |");
    println!("|---|---:|---:|---:|---:|---:|---:|");
    for (name, b, with_fn, with_codec) in [
        ("parse control", control(4096), true, true),
        ("parse headers", headers(4096), true, false),
        ("parse stream mix", stream_mix(4096), false, true),
        ("parse data 16k", data16k(256), false, true),
    ] {
        let (frames, a) = vh2_all(&b);
        let (nf, _) = ng_all(&b);
        assert_eq!(nf, frames);
        if with_fn {
            assert_eq!(h2_fn_all(&mut BytesMut::from(&b[..])).0, frames);
        }
        let bytes = Bytes::from(b.clone());
        if with_codec {
            let (n, r) = h2_codec_all(bytes.clone());
            assert_eq!(n, frames, "{r:?}");
        }
        black_box(a);
        // Alternate the order across rounds by timing each in turn.
        let vh2 = time(rounds, frames, || vh2_all(&b).1);
        // h2's codec and functions consume a BytesMut; making it is a memcpy
        // of the corpus, timed separately and subtracted.
        let copy = time(rounds, frames, || BytesMut::from(&b[..]).len() as u64);
        let h2f = with_fn.then(|| (time(rounds, frames, || h2_fn_all(&mut BytesMut::from(&b[..])).1) - copy).max(0.0));
        let h2c = with_codec.then(|| time(rounds, frames, || h2_codec_all(bytes.clone()).1.unwrap()));
        let ng = time(rounds, frames, || ng_all(&b).1);
        row(name, b.len(), frames, &[("vh2", Some(vh2)), ("h2 fn", h2f), ("h2 codec", h2c), ("nghttp2", Some(ng))]);
    }

    // Writing: the 9-byte header alone (what a DATA writev needs), and
    // whole control frames.
    let mut r = Rng(9);
    let quads: Vec<u32> = (0..4096).flat_map(|i| [r.below(16385) as u32, 0, (r.below(2)) as u32, 1 + 2 * i]).collect();
    let k = quads.len() / 4;
    let mut out = vec![0u8; 9 * k];
    let vh2 = time(rounds, k, || {
        for i in 0..k {
            let h = encode_head(quads[4 * i], quads[4 * i + 1] as u8, quads[4 * i + 2] as u8, quads[4 * i + 3]).unwrap();
            out[9 * i..9 * i + 9].copy_from_slice(&h);
        }
        out[17] as u64
    });
    let mut hb = BytesMut::with_capacity(9 * k);
    let h2h = time(rounds, k, || {
        hb.clear();
        for i in 0..k {
            let head = h2::frame::Head::new(h2::frame::Kind::Data, quads[4 * i + 2] as u8, quads[4 * i + 3].into());
            head.encode(quads[4 * i] as usize, &mut hb);
        }
        hb[17] as u64
    });
    let ngh = time(rounds, k, || {
        unsafe { ng_pack_heads(quads.as_ptr(), k, out.as_mut_ptr()) };
        out[17] as u64
    });
    row("write frame head", 9 * k, k, &[("vh2", Some(vh2)), ("h2 fn", Some(h2h)), ("h2 codec", None), ("nghttp2", Some(ngh))]);

    let c = control(4096);
    let mut frames = Vec::new();
    let mut off = 0;
    while let Parsed::Frame(f, n) = parse(&c[off..], MAX) {
        frames.push(f);
        off += n;
    }
    let mut v = Vec::with_capacity(c.len());
    let vh2 = time(rounds, frames.len(), || {
        v.clear();
        for f in &frames {
            serialize(f, MAX, &mut v).unwrap();
        }
        v.len() as u64
    });
    assert_eq!(v, c);
    use h2::frame as hf;
    let hframes: Vec<hf::Frame> = frames
        .iter()
        .map(|f| match *f {
            Frame::WindowUpdate { stream, increment } => hf::WindowUpdate::new(stream.into(), increment).into(),
            Frame::Settings { ack: true, .. } => hf::Settings::ack().into(),
            Frame::Settings { ack: false, .. } => {
                let mut s = hf::Settings::default();
                s.set_max_concurrent_streams(Some(100));
                s.set_initial_window_size(Some(0x100000));
                s.set_max_header_list_size(Some(0x4000));
                s.into()
            }
            Frame::Ping { ack, opaque } => if ack { hf::Ping::pong(opaque.to_be_bytes()) } else { hf::Ping::new(opaque.to_be_bytes()) }.into(),
            Frame::RstStream { stream, code } => hf::Reset::new(stream.into(), code.into()).into(),
            Frame::Priority { stream, .. } => hf::Priority::load(hf::Head::new(hf::Kind::Priority, 0, stream.into()), &[0, 0, 0, (stream - 1) as u8, 15]).unwrap().into(),
            _ => unreachable!(),
        })
        .collect();
    let mut hb = BytesMut::with_capacity(c.len());
    let h2w = time(rounds, frames.len(), || {
        hb.clear();
        for f in &hframes {
            match f {
                hf::Frame::WindowUpdate(w) => w.encode(&mut hb),
                hf::Frame::Settings(s) => s.encode(&mut hb),
                hf::Frame::Ping(p) => p.encode(&mut hb),
                hf::Frame::Reset(r) => r.encode(&mut hb),
                hf::Frame::Priority(_) => {
                    // h2 has no Priority::encode; it never sends PRIORITY.
                    hf::Head::new(hf::Kind::Priority, 0, 1.into()).encode(5, &mut hb);
                    hb.extend_from_slice(&[0, 0, 0, 0, 15]);
                }
                _ => unreachable!(),
            }
        }
        hb.len() as u64
    });
    row("write control", c.len(), frames.len(), &[("vh2", Some(vh2)), ("h2 fn", Some(h2w)), ("h2 codec", None), ("nghttp2", None)]);

    // One type only, so the branch predictor is not the measurement.
    let wu: Vec<(u32, u32)> = (0..4096).map(|i| (1 + 2 * i, 1 + (i * 7919) % 65536)).collect();
    let vh2 = time(rounds, wu.len(), || {
        v.clear();
        for &(stream, increment) in &wu {
            serialize(&Frame::WindowUpdate { stream, increment }, MAX, &mut v).unwrap();
        }
        v.len() as u64
    });
    let h2w = time(rounds, wu.len(), || {
        hb.clear();
        for &(stream, increment) in &wu {
            hf::WindowUpdate::new(stream.into(), increment).encode(&mut hb);
        }
        hb.len() as u64
    });
    row("write window_update", 13 * wu.len(), wu.len(), &[("vh2", Some(vh2)), ("h2 fn", Some(h2w)), ("h2 codec", None), ("nghttp2", None)]);
}

// ---------------------------------------------------------------------------
// Agreement
// ---------------------------------------------------------------------------

/// Mutated single frames (no header blocks, no CONTINUATION, which h2's
/// codec only takes after a HEADERS) through vh2 and h2's codec and nghttp2:
/// do they accept and reject the same ones? Prints each kind of difference.
fn agree(cases: usize) {
    use std::collections::BTreeMap;
    let mut r = Rng(77);
    let seeds = [control(64), stream_mix(64), headers(64)];
    let mut diffs: BTreeMap<String, (usize, String)> = BTreeMap::new();
    let mut same = 0;
    for i in 0..cases {
        let s = &seeds[i % 3];
        // A frame from the corpus, then a few byte changes.
        let mut off = 0;
        let mut b = Vec::new();
        for _ in 0..=r.below(40) {
            let Parsed::Frame(_, k) = parse(&s[off..], MAX) else { break };
            b = s[off..off + k].to_vec();
            off += k;
            if off >= s.len() {
                off = 0;
            }
        }
        let b0 = b.clone();
        for _ in 0..1 + r.below(3) {
            let j = r.below(b.len().min(24) as u64) as usize;
            b[j] = match r.below(4) {
                0 => r.next() as u8,
                1 => b[j] ^ (1 << r.below(8)),
                2 => 0,
                _ => b[j].wrapping_add(1),
            };
        }
        if r.below(3) == 0 {
            b[3] = r.below(10) as u8;
        }
        if b[3] == CONTINUATION {
            continue;
        }
        let len = ((b[0] as usize) << 16) | ((b[1] as usize) << 8) | b[2] as usize;
        if len > MAX as usize {
            continue;
        }
        b.truncate(9 + len.min(b.len() - 9));
        if b.len() < 9 + len {
            b.resize(9 + len, 0);
        }
        let v = match parse(&b, MAX) {
            Parsed::Frame(..) => "ok".to_string(),
            Parsed::StreamError { code, .. } => format!("stream error {code}"),
            Parsed::ConnError(code) => format!("conn error {code}"),
            Parsed::Incomplete(_) => unreachable!(),
        };
        let (hn, hr) = if matches!(b[3], HEADERS | PUSH_PROMISE) {
            // h2's own HEADERS and PUSH_PROMISE functions, without HPACK.
            use h2::frame as hf;
            let head = hf::Head::parse(&b);
            let p = BytesMut::from(&b[9..]);
            let r = if b[3] == HEADERS { hf::Headers::load(head, p, 0).map(|_| ()) } else { hf::PushPromise::load(head, p, 0).map(|_| ()) };
            (1, r.map(|_| 0).map_err(|e| format!("{e:?}")))
        } else {
            h2_codec_all(Bytes::from(b.clone()))
        };
        let h = match hr {
            Ok(_) => if hn == 1 || b[3] > 9 { "ok".to_string() } else { "nothing".to_string() },
            Err(e) => e.split('(').next().unwrap_or("").to_string() + "(" + e.split('(').nth(1).unwrap_or("") + "(" + e.split('(').nth(2).unwrap_or(""),
        };
        let mut acc = 0;
        let ng = if unsafe { ng_parse_all(b.as_ptr(), b.len(), &mut acc) } == 1 { "ok" } else { "error" };
        let key = format!("type {} | vh2 {v} | h2 {h} | nghttp2 {ng}", b[3]);
        let agreed = (v == "ok") == (h == "ok") && (v == "ok") == (ng == "ok");
        if agreed {
            same += 1;
        } else {
            let e = diffs.entry(key).or_insert((0, format!("{:02x?} (from {:02x?})", &b[..b.len().min(24)], &b0[..b0.len().min(24)])));
            e.0 += 1;
        }
    }
    println!("{same} agreed; differences:");
    for (k, (n, ex)) in diffs {
        println!("  {n:6}  {k}\n          e.g. {ex}");
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.get(1).map(|s| s.as_str()) == Some("agree") {
        agree(a.get(2).and_then(|s| s.parse().ok()).unwrap_or(200_000));
    } else {
        bench(a.get(1).and_then(|s| s.parse().ok()).unwrap_or(15));
    }
}
