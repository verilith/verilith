//! HTTP/3 frame reading: verilith-h3's `Reader` against hyperium h3's
//! `Frame::decode`, on whole streams held in memory.
//!
//! The two do different amounts of work. h3's decoder parses one frame
//! header (and buffers the payload of a non-DATA frame); the stream-level
//! order checks live elsewhere in h3. `Reader` also enforces the per-stream
//! frame order of RFC 9114 section 4.1 and the control-stream rules, so
//! these rows are a lower bound on what h3 spends doing the same job.
use bytes::{Buf, Bytes};
use h3::proto::frame::{Frame, FrameError};
use std::hint::black_box;
use std::time::Instant;
use verilith_h3::{Event, Reader};

fn bench<F: FnMut() -> usize>(name: &str, what: &str, bytes: usize, mut f: F) {
    // `h3bench NAME` runs one implementation's rows, so that each can be
    // timed in its own process.
    if let Some(only) = std::env::args().nth(1) {
        if only != name { return; }
    }
    for _ in 0..200 { black_box(f()); }
    let mut best = f64::MAX;
    let iters = (2_000_000 / bytes.max(1)).clamp(50, 20000);
    for _ in 0..30 {
        let t = Instant::now();
        for _ in 0..iters { black_box(f()); }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    println!("{what}\t{name}\t{:.0}", best * 1e9);
}

fn var(v: u64) -> Vec<u8> {
    if v < 64 { vec![v as u8] }
    else if v < 16384 { vec![0x40 | (v >> 8) as u8, v as u8] }
    else if v < 1 << 30 { ((v as u32) | 0x8000_0000).to_be_bytes().to_vec() }
    else { (v | 0xc000_0000_0000_0000).to_be_bytes().to_vec() }
}

fn frame(t: u64, p: &[u8]) -> Vec<u8> {
    let mut v = var(t);
    v.extend(var(p.len() as u64));
    v.extend_from_slice(p);
    v
}

/// A request: HEADERS, then `n` DATA frames of `size` bytes.
fn request(n: usize, size: usize) -> Vec<u8> {
    let mut s = frame(1, &[0x11; 120]);
    for _ in 0..n { s.extend(frame(0, &vec![0x61; size])); }
    s
}

/// A control stream: the stream type, SETTINGS with grease, then GOAWAYs.
fn control(n: usize) -> Vec<u8> {
    let mut p = Vec::new();
    for (k, v) in [(0x1u64, 4096u64), (0x6, 16384), (0x7, 100), (0x8, 1), (0x33, 1), (0x1f * 3 + 0x21, 7)] {
        p.extend(var(k));
        p.extend(var(v));
    }
    let mut s = var(0);
    s.extend(frame(4, &p));
    for i in 0..n { s.extend(frame(7, &var(4000 - 4 * i as u64))); }
    s
}

fn ours(server: bool, uni: bool, s: &[u8]) -> usize {
    let fin = !uni;
    let mut r = if uni { Reader::new_uni(server, 1 << 16) } else { Reader::new_request(server, 1 << 16) };
    let mut input = s;
    let mut sum = 0;
    loop {
        let (e, used) = r.next(input, fin);
        match e {
            Event::Data(a, b) => sum += b - a,
            Event::Headers(_) | Event::Settings(_) | Event::Goaway(_) | Event::StreamType(_) => sum += 1,
            Event::End => return sum,
            Event::Need if input.len() == used && uni => return sum,
            Event::Need => {}
            e => panic!("{e:?}"),
        }
        input = &input[used..];
    }
}

fn theirs(s: &Bytes, skip: usize) -> usize {
    let mut b = s.clone();
    b.advance(skip);
    let mut sum = 0;
    while b.has_remaining() {
        match Frame::decode(&mut b) {
            Ok(Frame::Data(len)) => {
                // The payload follows the header: hand it out and step over it.
                let d = b.copy_to_bytes(len.0);
                sum += d.len();
            }
            Ok(f) => { black_box(&f); sum += 1; }
            Err(FrameError::UnknownFrame(_)) => {}
            Err(e) => panic!("{e:?}"),
        }
    }
    sum
}

fn main() {
    let rows: [(&str, Vec<u8>, bool, bool); 5] = [
        ("req-64k", request(64, 1024), true, false),
        ("req-1m", request(16, 65536), true, false),
        ("req-tiny", request(4096, 8), true, false),
        ("headers", frame(1, &[0x11; 300]), true, false),
        ("control", control(256), true, true),
    ];
    for (what, s, server, uni) in rows.iter() {
        let b = Bytes::copy_from_slice(s);
        let skip = if *uni { 1 } else { 0 };
        assert_eq!(ours(*server, *uni, s) - skip, theirs(&b, skip));
        bench("verilith", what, s.len(), || ours(*server, *uni, s));
        bench("h3", what, s.len(), || theirs(&b, skip));
    }
}
