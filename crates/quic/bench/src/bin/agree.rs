//! Differential test: verilith-quic, quinn-proto and quiche on the same
//! frames. Valid frames of every type, encoded by verilith-quic, must be
//! read the same by all three; then the payloads are mutated (bytes
//! changed, inserted, cut) and the first frame of each is read by all
//! three, and every disagreement on whether it is valid, or on what it
//! says, is counted by kind and the first of each kind printed.
use bytes::Bytes;
use std::collections::BTreeMap;
use verilith_quic::frame::{self, Ack, Frame};
use verilith_quic::varint;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn vi(&mut self) -> u64 {
        let bits = [6, 14, 30, 62][(self.next() % 4) as usize];
        self.next() >> (64 - bits)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A frame as text, the same for all three readers.
fn ours(b: &[u8]) -> Option<(String, usize)> {
    let (f, e) = frame::parse(b, 0)?;
    let s = match f {
        Frame::Padding(n) => format!("PADDING {n}"),
        Frame::Ping => "PING".into(),
        Frame::Ack(a) => {
            let mut s = format!("ACK {} {} [{}-{}]", a.largest, a.delay, a.largest - a.first, a.largest);
            let mut it = a.ranges();
            while let Some((lo, hi)) = it.next() {
                s += &format!("[{lo}-{hi}]");
            }
            if let Some((a, b, c)) = a.ecn {
                s += &format!(" ecn {a} {b} {c}");
            }
            s
        }
        Frame::ResetStream { id, err, final_size } => format!("RESET_STREAM {id} {err} {final_size}"),
        Frame::StopSending { id, err } => format!("STOP_SENDING {id} {err}"),
        Frame::Crypto { offset, data } => format!("CRYPTO {offset} {data:x?}"),
        Frame::NewToken(t) => format!("NEW_TOKEN {t:x?}"),
        Frame::Stream { id, offset, fin, data, .. } => format!("STREAM {id} {offset} {fin} {data:x?}"),
        Frame::MaxData(m) => format!("MAX_DATA {m}"),
        Frame::MaxStreamData { id, max } => format!("MAX_STREAM_DATA {id} {max}"),
        Frame::MaxStreams { bidi, max } => format!("MAX_STREAMS {bidi} {max}"),
        Frame::DataBlocked(m) => format!("DATA_BLOCKED {m}"),
        Frame::StreamDataBlocked { id, max } => format!("STREAM_DATA_BLOCKED {id} {max}"),
        Frame::StreamsBlocked { bidi, max } => format!("STREAMS_BLOCKED {bidi} {max}"),
        Frame::NewConnectionId { seq, retire, cid, token } => format!("NEW_CONNECTION_ID {seq} {retire} {cid:x?} {token:x?}"),
        Frame::RetireConnectionId(s) => format!("RETIRE_CONNECTION_ID {s}"),
        Frame::PathChallenge(d) => format!("PATH_CHALLENGE {d:x?}"),
        Frame::PathResponse(d) => format!("PATH_RESPONSE {d:x?}"),
        Frame::ConnectionClose { app, err, frame_type, reason } => {
            format!("CONNECTION_CLOSE {app} {err} {} {reason:x?}", if app { 0 } else { frame_type })
        }
        Frame::HandshakeDone => "HANDSHAKE_DONE".into(),
    };
    Some((s, e))
}

fn quinn(b: &[u8]) -> Option<String> {
    use quinn_proto::frame::{Close, Frame as Q, Iter};
    let f = Iter::new(Bytes::copy_from_slice(b)).ok()?.next()?.ok()?;
    let bytes = |x: &[u8]| format!("{x:x?}");
    Some(match f {
        Q::Padding => {
            // quinn-proto reads a run of zeros as one PADDING frame.
            let n = b.iter().take_while(|&&x| x == 0).count();
            format!("PADDING {n}")
        }
        Q::Ping => "PING".into(),
        Q::Ack(a) => {
            let mut rs: Vec<_> = a.iter().collect();
            rs.sort_by_key(|r| std::cmp::Reverse(*r.end()));
            let mut s = format!("ACK {} {} ", a.largest, a.delay);
            for r in rs {
                s += &format!("[{}-{}]", r.start(), r.end());
            }
            if let Some(e) = a.ecn {
                s += &format!(" ecn {} {} {}", e.ect0, e.ect1, e.ce);
            }
            s
        }
        Q::ResetStream(r) => format!("RESET_STREAM {} {} {}", u64::from(r.id), r.error_code.into_inner(), r.final_offset.into_inner()),
        Q::StopSending(s) => format!("STOP_SENDING {} {}", u64::from(s.id), s.error_code.into_inner()),
        Q::Crypto(c) => format!("CRYPTO {} {}", c.offset, bytes(&c.data)),
        Q::NewToken(t) => format!("NEW_TOKEN {}", bytes(&t.token)),
        Q::Stream(s) => format!("STREAM {} {} {} {}", u64::from(s.id), s.offset, s.fin, bytes(&s.data)),
        Q::MaxData(m) => format!("MAX_DATA {}", m.into_inner()),
        Q::MaxStreamData { id, offset } => format!("MAX_STREAM_DATA {} {offset}", u64::from(id)),
        Q::MaxStreams { dir, count } => format!("MAX_STREAMS {} {count}", dir == quinn_proto::Dir::Bi),
        Q::DataBlocked { offset } => format!("DATA_BLOCKED {offset}"),
        Q::StreamDataBlocked { id, offset } => format!("STREAM_DATA_BLOCKED {} {offset}", u64::from(id)),
        Q::StreamsBlocked { dir, limit } => format!("STREAMS_BLOCKED {} {limit}", dir == quinn_proto::Dir::Bi),
        Q::NewConnectionId(n) => format!("NEW_CONNECTION_ID {} {} {} {}", n.sequence, n.retire_prior_to, bytes(&n.id), bytes(&n.reset_token[..])),
        Q::RetireConnectionId { sequence } => format!("RETIRE_CONNECTION_ID {sequence}"),
        Q::PathChallenge(x) => format!("PATH_CHALLENGE {}", bytes(&x.to_be_bytes())),
        Q::PathResponse(x) => format!("PATH_RESPONSE {}", bytes(&x.to_be_bytes())),
        Q::Close(Close::Connection(c)) => format!(
            "CONNECTION_CLOSE false {} {} {}",
            u64::from(c.error_code),
            c.frame_type.map_or(0, |t| t.0),
            bytes(&c.reason)
        ),
        Q::Close(Close::Application(c)) => format!("CONNECTION_CLOSE true {} 0 {}", c.error_code.into_inner(), bytes(&c.reason)),
        Q::HandshakeDone => "HANDSHAKE_DONE".into(),
        other => format!("EXTENSION {:?}", other.ty()),
    })
}

fn quiche(b: &[u8]) -> Option<String> {
    use quiche::frame::Frame as Q;
    let mut o = octets::Octets::with_slice(b);
    let f = Q::from_bytes(&mut o, quiche::Type::Short).ok()?;
    let bytes = |x: &[u8]| format!("{x:x?}");
    Some(match f {
        Q::Padding { len } => format!("PADDING {len}"),
        Q::Ping { .. } => "PING".into(),
        Q::ACK { ack_delay, ranges, ecn_counts } => {
            let mut rs: Vec<_> = ranges.iter().collect();
            rs.sort_by_key(|r| std::cmp::Reverse(r.end));
            let largest = rs.first().map_or(0, |r| r.end - 1);
            let mut s = format!("ACK {largest} {ack_delay} ");
            for r in rs {
                s += &format!("[{}-{}]", r.start, r.end - 1);
            }
            if let Some(e) = ecn_counts {
                s += &format!(" ecn {} {} {}", e.ect0_count, e.ect1_count, e.ecn_ce_count);
            }
            s
        }
        Q::ResetStream { stream_id, error_code, final_size } => format!("RESET_STREAM {stream_id} {error_code} {final_size}"),
        Q::StopSending { stream_id, error_code } => format!("STOP_SENDING {stream_id} {error_code}"),
        Q::Crypto { data } => format!("CRYPTO {} {}", data.off(), bytes(&data)),
        Q::NewToken { token } => format!("NEW_TOKEN {}", bytes(&token)),
        Q::Stream { stream_id, data } => format!("STREAM {stream_id} {} {} {}", data.off(), data.fin(), bytes(&data)),
        Q::MaxData { max } => format!("MAX_DATA {max}"),
        Q::MaxStreamData { stream_id, max } => format!("MAX_STREAM_DATA {stream_id} {max}"),
        Q::MaxStreamsBidi { max } => format!("MAX_STREAMS true {max}"),
        Q::MaxStreamsUni { max } => format!("MAX_STREAMS false {max}"),
        Q::DataBlocked { limit } => format!("DATA_BLOCKED {limit}"),
        Q::StreamDataBlocked { stream_id, limit } => format!("STREAM_DATA_BLOCKED {stream_id} {limit}"),
        Q::StreamsBlockedBidi { limit } => format!("STREAMS_BLOCKED true {limit}"),
        Q::StreamsBlockedUni { limit } => format!("STREAMS_BLOCKED false {limit}"),
        Q::NewConnectionId { seq_num, retire_prior_to, conn_id, reset_token } => {
            format!("NEW_CONNECTION_ID {seq_num} {retire_prior_to} {} {}", bytes(&conn_id), bytes(&reset_token))
        }
        Q::RetireConnectionId { seq_num } => format!("RETIRE_CONNECTION_ID {seq_num}"),
        Q::PathChallenge { data } => format!("PATH_CHALLENGE {}", bytes(&data)),
        Q::PathResponse { data } => format!("PATH_RESPONSE {}", bytes(&data)),
        Q::ConnectionClose { error_code, frame_type, reason } => format!("CONNECTION_CLOSE false {error_code} {frame_type} {}", bytes(&reason)),
        Q::ApplicationClose { error_code, reason } => format!("CONNECTION_CLOSE true {error_code} 0 {}", bytes(&reason)),
        Q::HandshakeDone => "HANDSHAKE_DONE".into(),
        other => format!("EXTENSION {other:?}"),
    })
}

/// ACK frames as quinn-proto and quiche print them: all ranges, largest
/// first (ours prints the first range in its own brackets too).
fn ack_norm(s: &str) -> String {
    if s.starts_with("ACK ") { s.replacen("] [", "][", 1) } else { s.to_string() }
}

/// Why RFC 9000 makes `b`'s first frame an error, if it is one of the
/// cases the others accept at parse time.
fn rfc_reason(b: &[u8]) -> Option<&'static str> {
    let t = b[0];
    let rd = |p: usize| varint::read(b, p);
    if t >= 0x40 {
        return Some("frame type not in its shortest encoding, or an extension (12.4)");
    }
    if t > 0x1e {
        return Some("extension frame type not negotiated (12.4)");
    }
    match t {
        0x12 | 0x13 | 0x16 | 0x17 => match rd(1) {
            Some((m, _)) if m > 1 << 60 => Some("stream count above 2^60 (19.11, 19.14)"),
            _ => None,
        },
        0x07 => match rd(1) {
            Some((0, _)) => Some("empty NEW_TOKEN (19.7)"),
            _ => None,
        },
        0x18 => match rd(1).and_then(|(seq, p)| rd(p).map(|(r, _)| (seq, r))) {
            Some((seq, r)) if r > seq => Some("Retire Prior To above Sequence Number (19.15)"),
            _ => None,
        },
        _ => None,
    }
}

fn random_frame(r: &mut Rng, data: &[u8], ranges: &mut Vec<u8>) -> Vec<u8> {
    let d = |r: &mut Rng, n: u64| &data[..r.below(n + 1) as usize];
    let f = match r.below(20) {
        0 => Frame::Padding(1 + r.below(30) as usize),
        1 => Frame::Ping,
        2 => {
            let largest = r.vi();
            let first = r.below(largest.min(50) + 1);
            let mut smallest = largest - first;
            let mut count = 0;
            ranges.clear();
            while smallest >= 2 && count < r.below(6) {
                let gap = r.below((smallest - 2).min(30) + 1);
                let hi = smallest - gap - 2;
                let len = r.below(hi.min(30) + 1);
                varint::write(ranges, gap);
                varint::write(ranges, len);
                smallest = hi - len;
                count += 1;
            }
            let ecn = if r.below(2) == 0 { None } else { Some((r.vi(), r.vi(), r.vi())) };
            Frame::Ack(Ack { largest, delay: r.vi(), first, count, raw: ranges, ecn })
        }
        3 => Frame::ResetStream { id: r.vi(), err: r.vi(), final_size: r.vi() },
        4 => Frame::StopSending { id: r.vi(), err: r.vi() },
        5 => Frame::Crypto { offset: r.below(1 << 40), data: d(r, 40) },
        6 => Frame::NewToken(&data[..1 + r.below(30) as usize]),
        7 => {
            let offset = if r.below(2) == 0 { 0 } else { r.below(1 << 40) };
            Frame::Stream { id: r.vi(), offset, len: true, fin: r.below(2) == 0, data: d(r, 40) }
        }
        8 => Frame::MaxData(r.vi()),
        9 => Frame::MaxStreamData { id: r.vi(), max: r.vi() },
        10 => Frame::MaxStreams { bidi: r.below(2) == 0, max: r.below((1 << 60) + 1) },
        11 => Frame::DataBlocked(r.vi()),
        12 => Frame::StreamDataBlocked { id: r.vi(), max: r.vi() },
        13 => Frame::StreamsBlocked { bidi: r.below(2) == 0, max: r.below((1 << 60) + 1) },
        14 => {
            let seq = r.vi();
            Frame::NewConnectionId { seq, retire: r.below(seq.saturating_add(1)), cid: &data[..1 + r.below(20) as usize], token: &data[..16] }
        }
        15 => Frame::RetireConnectionId(r.vi()),
        16 => Frame::PathChallenge(&data[..8]),
        17 => Frame::PathResponse(&data[8..16]),
        18 => {
            let app = r.below(2) == 0;
            Frame::ConnectionClose { app, err: r.vi(), frame_type: if app { 0 } else { r.vi() }, reason: d(r, 20) }
        }
        _ => Frame::HandshakeDone,
    };
    let mut out = Vec::new();
    frame::encode(&f, &mut out);
    out
}

fn main() {
    let n: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(200_000);
    let mut r = Rng(0x1234_5678);
    let data: Vec<u8> = (0..256).map(|i| (i * 37 + 11) as u8).collect();
    let mut ranges = Vec::new();

    // Valid frames: all three must read them the same.
    let mut valid_bad = 0;
    for _ in 0..n {
        let mut b = random_frame(&mut r, &data, &mut ranges);
        b.push(0x01);
        let o = ours(&b).map(|(s, _)| ack_norm(&s));
        let q = quinn(&b);
        let c = quiche(&b);
        if o.is_none() || o != q || o != c {
            valid_bad += 1;
            if valid_bad <= 5 {
                println!("valid frame read differently: {b:x?}\n  verilith {o:?}\n  quinn    {q:?}\n  quiche   {c:?}");
            }
        }
    }
    println!("valid frames: {n}, read differently: {valid_bad}");

    // Mutated frames: count disagreements by kind.
    let mut kinds: BTreeMap<String, (u64, String)> = BTreeMap::new();
    let mut reasons: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut total = 0;
    for _ in 0..n {
        let mut b = random_frame(&mut r, &data, &mut ranges);
        match r.below(4) {
            0 => {
                let i = r.below(b.len() as u64) as usize;
                b[i] = r.next() as u8;
            }
            1 => {
                let i = r.below(b.len() as u64) as usize;
                b.truncate(i.max(1));
            }
            2 => {
                let i = r.below(b.len() as u64 + 1) as usize;
                b.insert(i, r.next() as u8);
            }
            _ => {
                let i = r.below(b.len() as u64) as usize;
                b[i] ^= 1 << r.below(8);
            }
        }
        b.push(0x01);
        let o = ours(&b).map(|(s, _)| ack_norm(&s));
        let q = quinn(&b);
        let c = quiche(&b);
        total += 1;
        let label = |x: &Option<String>| x.as_ref().map_or("reject".to_string(), |s| s.split(' ').next().unwrap().to_string());
        let why = if o.is_none() { rfc_reason(&b) } else { None };
        if o != q {
            if o.is_none() && q.is_some() && why.is_some() {
                *reasons.entry(why.unwrap()).or_insert(0) += 1;
            }
            let k = format!("verilith {} / quinn-proto {}{}", label(&o), label(&q), if why.is_some() { " (RFC error)" } else { "" });
            let e = kinds.entry(k).or_insert((0, format!("{b:x?}\n    verilith {o:?}\n    quinn    {q:?}")));
            e.0 += 1;
        }
        if o != c {
            if o.is_none() && c.is_some() && why.is_some() {
                *reasons.entry(why.unwrap()).or_insert(0) += 1;
            }
            let k = format!("verilith {} / quiche {}{}", label(&o), label(&c), if why.is_some() { " (RFC error)" } else { "" });
            let e = kinds.entry(k).or_insert((0, format!("{b:x?}\n    verilith {o:?}\n    quiche   {c:?}")));
            e.0 += 1;
        }
    }
    println!("mutated frames: {total}");
    let mut unexplained = 0;
    for (k, (count, ex)) in &kinds {
        if !k.ends_with("(RFC error)") {
            unexplained += count;
            println!("{count:>8}  {k}\n    e.g. {ex}");
        }
    }
    println!("disagreements where verilith-quic rejects what RFC 9000 makes an error:");
    for (r, count) in &reasons {
        println!("{count:>8}  {r}");
    }
    println!("other disagreements: {unexplained}");
    if valid_bad > 0 || unexplained > 0 {
        std::process::exit(1);
    }
}
