//! The examples of RFC 9000 (Appendix A) and round trips of the encoders
//! through the parsers on random values.
use verilith_quic::frame::{self, Ack, Frame};
use verilith_quic::packet::{self, Header};
use verilith_quic::params::{self, TransportParameters};
use verilith_quic::varint;

#[test]
fn varint_examples() {
    // Appendix A.1.
    let cases: &[(&[u8], u64)] = &[
        (&[0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c], 151_288_809_941_952_652),
        (&[0x9d, 0x7f, 0x3e, 0x7d], 494_878_333),
        (&[0x7b, 0xbd], 15_293),
        (&[0x25], 37),
        (&[0x40, 0x25], 37),
    ];
    for (b, v) in cases {
        assert_eq!(varint::read(b, 0), Some((*v, b.len())));
    }
    assert_eq!(varint::read(&[0x40], 0), None);
    let mut out = Vec::new();
    varint::write(&mut out, 494_878_333);
    assert_eq!(out, [0x9d, 0x7f, 0x3e, 0x7d]);
}

#[test]
fn packet_number_examples() {
    // Appendix A.3: largest 0xa82f30ea, 16 bits 0x9b32.
    assert_eq!(packet::decode_pn(0xa82f30eb, 0x9b32, 2), 0xa82f9b32);
    // Appendix A.2: 0xac5c02 with 0xabe8b3 acknowledged needs 2 bytes;
    // 0xace8fe with 0xabe8b3 acknowledged needs 3.
    assert_eq!(packet::pn_len(0xac5c02, Some(0xabe8b3)), 2);
    assert_eq!(packet::pn_len(0xace8fe, Some(0xabe8b3)), 3);
}

/// A small deterministic generator (xorshift64*).
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
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

#[test]
fn varint_round_trip() {
    let mut r = Rng(1);
    for _ in 0..100_000 {
        let v = r.vi();
        let mut out = vec![0xaa];
        varint::write(&mut out, v);
        assert_eq!(out.len() - 1, varint::size(v));
        assert_eq!(varint::read(&out, 1), Some((v, out.len())));
    }
}

fn random_frame<'a>(r: &mut Rng, data: &'a [u8], ranges: &'a mut Vec<u8>) -> Frame<'a> {
    let d = |r: &mut Rng, n: usize| &data[..(r.below(n as u64 + 1) as usize).min(data.len())];
    match r.below(20) {
        0 => Frame::Padding(1 + r.below(50) as usize),
        1 => Frame::Ping,
        2 => {
            let largest = r.vi();
            let first = r.below(largest.min(1000) + 1);
            let mut smallest = largest - first;
            let mut count = 0;
            ranges.clear();
            while smallest >= 2 && count < r.below(10) {
                let gap = r.below((smallest - 2).min(100) + 1);
                let hi = smallest - gap - 2;
                let len = r.below(hi.min(100) + 1);
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
        5 => Frame::Crypto { offset: r.below(1 << 40), data: d(r, 300) },
        6 => Frame::NewToken(&data[..1 + r.below(100) as usize]),
        7 => {
            let offset = if r.below(2) == 0 { 0 } else { r.below(1 << 40) };
            Frame::Stream { id: r.vi(), offset, len: true, fin: r.below(2) == 0, data: d(r, 1200) }
        }
        8 => Frame::MaxData(r.vi()),
        9 => Frame::MaxStreamData { id: r.vi(), max: r.vi() },
        10 => Frame::MaxStreams { bidi: r.below(2) == 0, max: r.below((1 << 60) + 1) },
        11 => Frame::DataBlocked(r.vi()),
        12 => Frame::StreamDataBlocked { id: r.vi(), max: r.vi() },
        13 => Frame::StreamsBlocked { bidi: r.below(2) == 0, max: r.below((1 << 60) + 1) },
        14 => {
            let seq = r.vi();
            Frame::NewConnectionId {
                seq,
                retire: r.below(seq.saturating_add(1)),
                cid: &data[..1 + r.below(20) as usize],
                token: &data[..16],
            }
        }
        15 => Frame::RetireConnectionId(r.vi()),
        16 => Frame::PathChallenge(&data[..8]),
        17 => Frame::PathResponse(&data[8..16]),
        18 => {
            let app = r.below(2) == 0;
            Frame::ConnectionClose { app, err: r.vi(), frame_type: if app { 0 } else { r.vi() }, reason: d(r, 40) }
        }
        _ => Frame::HandshakeDone,
    }
}

fn same(a: &Frame, b: &Frame) -> bool {
    let mut x = Vec::new();
    let mut y = Vec::new();
    frame::encode(a, &mut x);
    frame::encode(b, &mut y);
    x == y
}

#[test]
fn frames_round_trip() {
    let mut r = Rng(7);
    let data = r.bytes(2000);
    let mut ranges = Vec::new();
    for _ in 0..50_000 {
        let f = random_frame(&mut r, &data, &mut ranges);
        let mut out = Vec::new();
        frame::encode(&f, &mut out);
        out.push(0x01); // a PING after it
        let (g, e) = frame::parse(&out, 0).expect("parses");
        assert_eq!(e, out.len() - 1);
        assert!(same(&f, &g));
        if let (Frame::Ack(a), Frame::Ack(b)) = (&f, &g) {
            let mut i = a.ranges();
            let mut j = b.ranges();
            loop {
                let (x, y) = (i.next(), j.next());
                assert_eq!(x, y);
                if x.is_none() {
                    break;
                }
            }
        }
    }
}

#[test]
fn frames_reject() {
    // Truncated frames, an unknown type, a two-byte type, ACK ranges below
    // packet 0, a stream past 2^62 - 1, an empty NEW_TOKEN.
    for b in [
        &[0x02, 0x05, 0x00, 0x01][..],
        &[0x1f][..],
        &[0x40, 0x01][..],
        &[0x02, 0x05, 0x00, 0x01, 0x03, 0x01, 0x00][..],
        &[0x02, 0x05, 0x00, 0x00, 0x06][..],
        &[0x0e, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x00][..],
        &[0x07, 0x00][..],
        &[0x18, 0x01, 0x02, 0x01, 0xaa][..],
    ] {
        assert!(frame::parse(b, 0).is_none(), "{b:x?}");
    }
}

#[test]
fn headers_round_trip() {
    let mut r = Rng(3);
    let data = r.bytes(400);
    for _ in 0..20_000 {
        let dcid = &data[..r.below(21) as usize];
        let scid = &data[30..30 + r.below(21) as usize];
        let ty = r.below(3) as u8;
        let token = if ty == 0 { &data[60..60 + r.below(100) as usize] } else { &data[..0] };
        let len = r.below(300);
        let first = 0xc0 | (ty << 4) | (r.next() as u8 & 0x0f);
        let h = Header::Long { first, dcid, scid, token, len };
        let mut out = Vec::new();
        packet::encode_header(&h, &mut out);
        let e = out.len();
        out.extend_from_slice(&data[..len as usize]);
        let (g, ge) = packet::parse_header(&out, 0, 8).expect("parses");
        assert_eq!(ge, e);
        assert_eq!(packet::packet_end(g, ge, &out), out.len());
        match g {
            Header::Long { first: f, dcid: d, scid: s, token: t, len: l } => {
                assert_eq!((f, d, s, t, l), (first, dcid, scid, token, len));
            }
            _ => panic!(),
        }
        let first = 0x40 | (r.next() as u8 & 0x3f);
        let h = Header::Short { first, dcid: &data[..8] };
        let mut out = Vec::new();
        packet::encode_header(&h, &mut out);
        out.extend_from_slice(&data[..20]);
        assert!(matches!(packet::parse_header(&out, 0, 8), Some((Header::Short { dcid, .. }, 9)) if dcid == &data[..8]));
    }
}

#[test]
fn transport_params_round_trip() {
    let mut r = Rng(5);
    let data = r.bytes(100);
    for _ in 0..20_000 {
        let mut t = TransportParameters::new();
        let pick = |r: &mut Rng| r.below(2) == 0;
        if pick(&mut r) { t.original_dcid = Some(&data[..r.below(21) as usize]); }
        if pick(&mut r) { t.max_idle_timeout = Some(r.vi()); }
        if pick(&mut r) { t.stateless_reset_token = Some(&data[..16]); }
        if pick(&mut r) { t.max_udp_payload_size = Some(1200 + r.below(70000)); }
        if pick(&mut r) { t.initial_max_data = Some(r.vi()); }
        if pick(&mut r) { t.initial_max_stream_data_bidi_local = Some(r.vi()); }
        if pick(&mut r) { t.initial_max_streams_bidi = Some(r.below(1 << 60)); }
        if pick(&mut r) { t.ack_delay_exponent = Some(r.below(21)); }
        if pick(&mut r) { t.max_ack_delay = Some(r.below(1 << 14)); }
        t.disable_active_migration = pick(&mut r);
        if pick(&mut r) {
            t.preferred_address = Some(params::PreferredAddress { v4: &data[..6], v6: &data[6..24], cid: &data[24..32], token: &data[40..56] });
        }
        if pick(&mut r) { t.active_connection_id_limit = Some(2 + r.below(100)); }
        if pick(&mut r) { t.initial_scid = Some(&data[50..50 + r.below(21) as usize]); }
        let mut out = Vec::new();
        params::encode(&t, &mut out);
        let g = params::parse(&out).expect("parses");
        let mut again = Vec::new();
        params::encode(&g, &mut again);
        assert_eq!(out, again);
    }
    // A duplicate, and a max_udp_payload_size below 1200.
    assert!(params::parse(&[0x01, 0x01, 0x05, 0x01, 0x01, 0x06]).is_none());
    assert!(params::parse(&[0x03, 0x02, 0x44, 0xaf]).is_none());
    // Unknown and reserved (31 * N + 27) parameters are ignored.
    assert!(params::parse(&[0x1b, 0x02, 0xaa, 0xbb, 0x01, 0x01, 0x05]).unwrap().max_idle_timeout == Some(5));
}
