//! The encoder against the decoder: every section decodes back to the
//! fields encoded, with the encoder stream and the decoder stream delivered
//! late, in pieces, or not at all for a while.
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};

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

type Hdrs = Vec<(Vec<u8>, Vec<u8>, bool)>;

fn fields(h: &Hdrs) -> Fields {
    let mut f = Fields::new();
    for (n, v, never) in h {
        f.push(n, v, *never);
    }
    f
}

fn lines(f: &Fields) -> Hdrs {
    (0..f.len())
        .map(|i| {
            let (n, v, never) = f.get(i);
            (n.to_vec(), v.to_vec(), never)
        })
        .collect()
}

fn request(i: usize) -> Hdrs {
    let mut h: Hdrs = vec![
        (b":method".to_vec(), b"GET".to_vec(), false),
        (b":scheme".to_vec(), b"https".to_vec(), false),
        (b":authority".to_vec(), b"www.example.com".to_vec(), false),
        (b":path".to_vec(), format!("/assets/img/{i}.png").into_bytes(), false),
        (b"user-agent".to_vec(), b"Mozilla/5.0 (X11; Linux x86_64; rv:120.0) Gecko/20100101 Firefox/120.0".to_vec(), false),
        (b"accept".to_vec(), b"image/avif,image/webp,*/*".to_vec(), false),
        (b"accept-language".to_vec(), b"en-US,en;q=0.5".to_vec(), false),
        (b"accept-encoding".to_vec(), b"gzip, deflate, br".to_vec(), false),
        (b"referer".to_vec(), b"https://www.example.com/".to_vec(), false),
    ];
    h.push((b"cookie".to_vec(), b"session=8c6f5a2e1d3b4c9a".to_vec(), true));
    h
}

#[test]
fn requests_compress() {
    let mut e = Encoder::new(4096, 16, 4096).unwrap();
    let mut d = Decoder::new(4096, 16, 1 << 16).unwrap();
    let mut sizes = Vec::new();
    let mut out = Fields::new();
    let mut ready = Vec::new();
    for i in 0..20 {
        let h = request(i);
        let mut sec = Vec::new();
        e.encode(4 * i as u64, &fields(&h), &mut sec);
        let mut es = Vec::new();
        e.take_output(&mut es);
        assert!(d.feed_encoder(&es, &mut ready));
        assert_eq!(d.decode(4 * i as u64, &sec, &mut out), Res::Done);
        assert_eq!(lines(&out), h);
        let mut ds = Vec::new();
        d.take_output(&mut ds);
        assert!(e.feed_decoder(&ds));
        sizes.push(sec.len() + es.len());
    }
    // Once the table holds the request's fields, a request is a few bytes
    // plus the path and the (never indexed) cookie.
    eprintln!("sizes {sizes:?}");
    assert!(sizes[5] < sizes[0] / 3, "{sizes:?}");
}

fn vocab(r: &mut Rng) -> (Vec<u8>, Vec<u8>, bool) {
    const NAMES: [&[u8]; 8] = [b":path", b"content-type", b"x-custom", b"cache-control", b"x-trace-id", b":status", b"a", b"set-cookie"];
    const VALS: [&[u8]; 8] = [b"/", b"text/html; charset=utf-8", b"no-cache", b"200", b"", b"abcdefghijklmnopqrstuvwxyz0123456789", b"\x00\xff\x80binary", b"404"];
    let n = NAMES[r.below(8) as usize].to_vec();
    let v = if r.below(4) == 0 {
        (0..r.below(40)).map(|_| r.next() as u8).collect()
    } else {
        VALS[r.below(8) as usize].to_vec()
    };
    (n, v, r.below(10) == 0)
}

/// Random fields, random settings, and both streams delivered late and in
/// random pieces.
#[test]
fn random_round_trips() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    for round in 0..300 {
        let cap = [0u64, 64, 100, 220, 1000, 4096][r.below(6) as usize];
        let blocked = [0u64, 1, 2, 16][r.below(4) as usize];
        let mut e = Encoder::new(cap, blocked, cap).unwrap();
        let mut d = Decoder::new(cap, blocked, 1 << 20).unwrap();
        let mut es_pending: Vec<u8> = Vec::new();
        let mut ds_pending: Vec<u8> = Vec::new();
        // Sections not yet decoded: (stream, bytes, fields).
        let mut waiting: Vec<(u64, Vec<u8>, Hdrs)> = Vec::new();
        let mut out = Fields::new();
        let mut ready = Vec::new();
        for s in 0..40u64 {
            let h: Hdrs = (0..r.below(8)).map(|_| vocab(&mut r)).collect();
            let mut sec = Vec::new();
            e.encode(s, &fields(&h), &mut sec);
            e.take_output(&mut es_pending);
            waiting.push((s, sec, h));
            // Deliver some of the encoder stream.
            if r.below(3) != 0 && !es_pending.is_empty() {
                let k = r.below(es_pending.len() as u64 + 1) as usize;
                let piece: Vec<u8> = es_pending.drain(..k).collect();
                assert!(d.feed_encoder(&piece, &mut ready), "round {round}");
            }
            // Decode what can be decoded, in random order.
            let mut i = 0;
            while i < waiting.len() {
                if r.below(2) == 0 {
                    i += 1;
                    continue;
                }
                let (st, ref b, ref want) = waiting[i];
                match d.decode(st, b, &mut out) {
                    Res::Done => {
                        assert_eq!(&lines(&out), want, "round {round}");
                        waiting.remove(i);
                    },
                    Res::Blocked => i += 1,
                    res => panic!("round {round}: {res:?}"),
                }
            }
            d.take_output(&mut ds_pending);
            if r.below(2) == 0 && !ds_pending.is_empty() {
                let k = r.below(ds_pending.len() as u64 + 1) as usize;
                let piece: Vec<u8> = ds_pending.drain(..k).collect();
                assert!(e.feed_decoder(&piece), "round {round}");
            }
        }
        // Deliver everything; every section decodes.
        assert!(d.feed_encoder(&es_pending, &mut ready));
        for (st, b, want) in &waiting {
            assert_eq!(d.decode(*st, b, &mut out), Res::Done, "round {round}");
            assert_eq!(&lines(&out), want);
        }
        d.take_output(&mut ds_pending);
        assert!(e.feed_decoder(&ds_pending));
    }
}
