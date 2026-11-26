//! The inputs: built with verilith-quic's encoder, whose output the
//! round-trip proof shows is the RFC encoding, and parsed by all three.
use verilith_quic::frame::{self, Ack, Frame};
use verilith_quic::packet::{self, Header};
use verilith_quic::params::{self, TransportParameters};
use verilith_quic::varint;

fn ranges(n: u64, gap: u64, len: u64) -> Vec<u8> {
    let mut v = Vec::new();
    for _ in 0..n {
        varint::write(&mut v, gap);
        varint::write(&mut v, len);
    }
    v
}

fn enc(fs: &[Frame]) -> Vec<u8> {
    let mut out = Vec::new();
    for f in fs {
        frame::encode(f, &mut out);
    }
    out
}

/// Typical 1-RTT payloads.
pub fn frame_payloads() -> Vec<(&'static str, Vec<u8>)> {
    let data = vec![0xa5u8; 1100];
    let r1 = ranges(1, 3, 10);
    let r8 = ranges(8, 2, 20);
    let tok = [7u8; 16];
    let cid = [9u8; 8];
    let mut v = Vec::new();
    // A server sending a full packet of response body.
    v.push((
        "server-data",
        enc(&[
            Frame::Ack(Ack { largest: 1000, delay: 30, first: 2, count: 1, raw: &r1, ecn: None }),
            Frame::Stream { id: 0, offset: 123_456, len: true, fin: false, data: &data },
        ]),
    ));
    // A client acknowledging with gaps and giving credit.
    v.push((
        "client-acks",
        enc(&[
            Frame::Ack(Ack { largest: 100_000, delay: 25, first: 5, count: 8, raw: &r8, ecn: Some((1000, 0, 3)) }),
            Frame::MaxData(10_000_000),
            Frame::MaxStreamData { id: 0, max: 1_000_000 },
            Frame::MaxStreamData { id: 4, max: 1_000_000 },
            Frame::Ping,
        ]),
    ));
    // The end of a handshake: CRYPTO, ACK, new connection IDs, a token.
    v.push((
        "handshake",
        enc(&[
            Frame::Ack(Ack { largest: 3, delay: 0, first: 0, count: 0, raw: &[], ecn: None }),
            Frame::Crypto { offset: 0, data: &data[..300] },
            Frame::NewConnectionId { seq: 1, retire: 0, cid: &cid, token: &tok },
            Frame::NewConnectionId { seq: 2, retire: 0, cid: &cid, token: &tok },
            Frame::NewConnectionId { seq: 3, retire: 0, cid: &cid, token: &tok },
            Frame::NewToken(&data[..60]),
            Frame::HandshakeDone,
        ]),
    ));
    // Twenty small STREAM frames: HTTP/3 requests on new streams.
    let small: Vec<Frame> = (0..20)
        .map(|i| Frame::Stream { id: 4 * i, offset: 0, len: true, fin: true, data: &data[..40] })
        .collect();
    v.push(("small-streams", enc(&small)));
    // An Initial padded to 1200 bytes.
    let mut p = enc(&[Frame::Crypto { offset: 0, data: &data[..280] }]);
    let pad = 1200 - p.len();
    frame::encode(&Frame::Padding(pad), &mut p);
    v.push(("crypto+padding", p));
    v
}

/// A client Initial (1200 bytes, 8-byte connection IDs, no token) and a
/// 1-RTT packet.
pub fn header_packets() -> Vec<(&'static str, Vec<u8>, usize)> {
    let cid = [3u8; 8];
    let mut init = Vec::new();
    let body = 1200 - (1 + 4 + 1 + 8 + 1 + 8 + 1 + 2);
    packet::encode_header(
        &Header::Long { first: 0xc3, dcid: &cid, scid: &cid, token: &[], len: body as u64 },
        &mut init,
    );
    init.resize(1200, 0x11);
    let mut short = Vec::new();
    packet::encode_header(&Header::Short { first: 0x43, dcid: &cid }, &mut short);
    short.resize(1200, 0x22);
    vec![("initial", init, 8), ("1rtt", short, 8)]
}

/// A server's transport parameters.
pub fn server_params() -> Vec<u8> {
    let cid = [5u8; 8];
    let tok = [6u8; 16];
    let mut t = TransportParameters::new();
    t.original_dcid = Some(&cid);
    t.max_idle_timeout = Some(30_000);
    t.stateless_reset_token = Some(&tok);
    t.max_udp_payload_size = Some(1472);
    t.initial_max_data = Some(10_000_000);
    t.initial_max_stream_data_bidi_local = Some(1_000_000);
    t.initial_max_stream_data_bidi_remote = Some(1_000_000);
    t.initial_max_stream_data_uni = Some(1_000_000);
    t.initial_max_streams_bidi = Some(100);
    t.initial_max_streams_uni = Some(100);
    t.max_ack_delay = Some(25);
    t.active_connection_id_limit = Some(4);
    t.initial_scid = Some(&cid);
    let mut out = Vec::new();
    params::encode(&t, &mut out);
    out
}

/// 1000 varints of mixed lengths, as in frames.
pub fn varints() -> Vec<u8> {
    let mut out = Vec::new();
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    for i in 0..1000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let v = match i % 8 {
            0..=3 => x % 64,
            4 | 5 => x % 16384,
            6 => x % (1 << 30),
            _ => x % (1 << 62),
        };
        varint::write(&mut out, v);
    }
    out
}

/// Eight ACK ranges after the first.
pub fn ack_ranges8() -> (Vec<u8>, u64) {
    (ranges(8, 2, 20), 8)
}

/// The same ranges for quiche.
pub fn quiche_ranges8() -> quiche::ranges::RangeSet {
    let mut rs = quiche::ranges::RangeSet::default();
    let mut hi = 100_000u64;
    let mut lo = hi - 3;
    rs.insert(lo..hi + 1);
    for _ in 0..8 {
        hi = lo - 2 - 2;
        lo = hi - 20;
        rs.insert(lo..hi + 1);
    }
    rs
}
