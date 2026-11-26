//! verilith-quic against quinn-proto 0.11 and quiche 0.24: the time to
//! parse typical 1-RTT payloads, packet headers, transport parameters and
//! varints, and to encode frames. `quicbench ROW` runs only the rows named
//! ROW, so each can be timed in its own process.
mod payloads;
use bytes::{Bytes, BytesMut};
use payloads::*;
use std::hint::black_box;
use std::time::Instant;
use verilith_quic::frame::{self, Frame};

fn bench<F: FnMut() -> usize>(row: &str, imp: &str, bytes: usize, mut f: F) {
    if let Some(only) = std::env::args().nth(1) {
        if only != row {
            return;
        }
    }
    let mut check = 0;
    for _ in 0..2000 {
        check = black_box(f());
    }
    let mut best = f64::MAX;
    for _ in 0..25 {
        let iters = 20_000;
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    let gbs = if bytes > 0 { format!("{:.2}", bytes as f64 / best / 1e9) } else { "-".into() };
    println!("{row}\t{imp}\t{:.1}\t{gbs}\t{check}", best * 1e9);
}

/// Every frame of the payload, with what a receiver reads of it: the data
/// lengths and the ACK ranges.
fn ours(p: &[u8]) -> usize {
    let mut pos = 0;
    let mut acc = 0usize;
    while pos < p.len() {
        let (f, e) = frame::parse(p, pos).expect("valid");
        acc += match f {
            Frame::Stream { data, offset, .. } => data.len() + offset as usize,
            Frame::Crypto { data, .. } => data.len(),
            Frame::Ack(a) => {
                let mut s = a.largest as usize;
                let mut it = a.ranges();
                while let Some((lo, hi)) = it.next() {
                    s += (lo ^ hi) as usize;
                }
                s
            }
            Frame::MaxStreamData { max, .. } => max as usize,
            Frame::NewConnectionId { cid, .. } => cid.len(),
            _ => 1,
        };
        pos = e;
    }
    acc
}

fn quinn(p: &Bytes) -> usize {
    use quinn_proto::frame::{Frame as Q, Iter};
    let mut acc = 0usize;
    for f in Iter::new(p.clone()).unwrap() {
        acc += match f.expect("valid") {
            Q::Stream(s) => s.data.len() + s.offset as usize,
            Q::Crypto(c) => c.data.len(),
            Q::Ack(a) => {
                let mut s = a.largest as usize;
                for r in a.iter() {
                    s += (r.start() ^ r.end()) as usize;
                }
                s
            }
            Q::MaxStreamData { offset, .. } => offset as usize,
            Q::NewConnectionId(n) => n.id.len(),
            _ => 1,
        };
    }
    acc
}

fn quiche(p: &[u8]) -> usize {
    use quiche::frame::Frame as Q;
    let mut b = octets::Octets::with_slice(p);
    let mut acc = 0usize;
    while b.cap() > 0 {
        acc += match Q::from_bytes(&mut b, quiche::Type::Short).expect("valid") {
            Q::Stream { data, .. } => data.len() + data.off() as usize,
            Q::Crypto { data } => data.len(),
            Q::ACK { ranges, .. } => ranges.iter().map(|r| (r.start ^ r.end) as usize).sum(),
            Q::MaxStreamData { max, .. } => max as usize,
            Q::NewConnectionId { conn_id, .. } => conn_id.len(),
            _ => 1,
        };
    }
    acc
}

fn main() {
    println!("row\timpl\tns\tGB/s\tcheck");
    for (name, p) in frame_payloads() {
        let row = format!("frames/{name}");
        let qb = Bytes::from(p.clone());
        assert_eq!(ours(&p) > 0, quinn(&qb) > 0);
        bench(&row, "verilith", p.len(), || ours(&p));
        bench(&row, "quinn-proto", p.len(), || quinn(&qb));
        bench(&row, "quiche", p.len(), || quiche(&p));
    }

    for (name, pkt, cid_len) in header_packets() {
        let row = format!("header/{name}");
        bench(&row, "verilith", 0, || {
            let (h, e) = verilith_quic::packet::parse_header(&pkt, 0, cid_len).unwrap();
            verilith_quic::packet::packet_end(h, e, &pkt) + e
        });
        bench(&row, "quinn-proto", 0, || {
            let cp = quinn_proto::FixedLengthConnectionIdParser::new(cid_len);
            let (d, _) = quinn_proto::PartialDecode::new(BytesMut::from(&pkt[..]), &cp, &[1], false).unwrap();
            d.dst_cid().len() + d.len()
        });
        bench(&row, "quinn-proto (copy only)", 0, || BytesMut::from(&pkt[..]).len());
        let mut m = pkt.clone();
        bench(&row, "quiche", 0, || {
            let h = quiche::Header::from_slice(&mut m, cid_len).unwrap();
            h.dcid.len() + h.ty as usize
        });
    }

    let tp = server_params();
    bench("params/server", "verilith", tp.len(), || {
        let t = verilith_quic::params::parse(&tp).unwrap();
        t.initial_max_data.unwrap() as usize + t.original_dcid.unwrap().len()
    });
    bench("params/server", "quinn-proto", tp.len(), || {
        let t = quinn_proto::transport_parameters::TransportParameters::read(quinn_proto::Side::Client, &mut &tp[..]).unwrap();
        t.initial_max_data.into_inner() as usize + t.original_dst_cid.unwrap().len()
    });
    bench("params/server", "quiche", tp.len(), || {
        let t = quiche::TransportParams::decode(&tp, false, None).unwrap();
        t.initial_max_data as usize + t.original_destination_connection_id.unwrap().len()
    });

    let vs = varints();
    bench("varint/1000", "verilith", vs.len(), || {
        let mut p = 0;
        let mut s = 0u64;
        while p < vs.len() {
            let (v, e) = verilith_quic::varint::read(&vs, p).unwrap();
            s = s.wrapping_add(v);
            p = e;
        }
        s as usize
    });
    bench("varint/1000", "quinn-proto", vs.len(), || {
        use quinn_proto::coding::Codec;
        let mut b = &vs[..];
        let mut s = 0u64;
        while !b.is_empty() {
            s = s.wrapping_add(quinn_proto::VarInt::decode(&mut b).unwrap().into_inner());
        }
        s as usize
    });
    bench("varint/1000", "quiche", vs.len(), || {
        let mut b = octets::Octets::with_slice(&vs);
        let mut s = 0u64;
        while b.cap() > 0 {
            s = s.wrapping_add(b.get_varint().unwrap());
        }
        s as usize
    });

    // Encoding a STREAM frame of 1100 bytes, and an ACK of 8 ranges.
    let data = vec![0x5au8; 1100];
    let mut out = Vec::with_capacity(2048);
    bench("encode/stream", "verilith", 1100, || {
        out.clear();
        frame::encode(&Frame::Stream { id: 4, offset: 123_456, len: true, fin: false, data: &data }, &mut out);
        out.len()
    });
    let mut qout = vec![0u8; 2048];
    bench("encode/stream", "quiche", 1100, || {
        let f = quiche::frame::Frame::StreamHeader { stream_id: 4, offset: 123_456, length: 1100, fin: false };
        let mut b = octets::OctetsMut::with_slice(&mut qout);
        let n = f.to_bytes(&mut b).unwrap();
        b.put_bytes(&data).unwrap();
        n + data.len()
    });
    let mut bout: Vec<u8> = Vec::with_capacity(2048);
    bench("encode/stream", "quinn-proto", 1100, || {
        use bytes::BufMut;
        bout.clear();
        let m = quinn_proto::frame::StreamMeta { id: quinn_proto::StreamId::new(quinn_proto::Side::Client, quinn_proto::Dir::Bi, 1), offsets: 123_456..124_556, fin: false };
        m.encode(true, &mut bout);
        bout.put_slice(&data);
        bout.len()
    });
    let (ack_raw, count) = ack_ranges8();
    bench("encode/ack8", "verilith", 0, || {
        out.clear();
        let a = frame::Ack { largest: 100_000, delay: 25, first: 3, count, raw: &ack_raw, ecn: None };
        frame::encode(&Frame::Ack(a), &mut out);
        out.len()
    });
    let rs = quiche_ranges8();
    bench("encode/ack8", "quiche", 0, || {
        let f = quiche::frame::Frame::ACK { ack_delay: 25, ranges: rs.clone(), ecn_counts: None };
        let mut b = octets::OctetsMut::with_slice(&mut qout);
        f.to_bytes(&mut b).unwrap()
    });
}
