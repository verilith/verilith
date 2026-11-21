//! RFC 7541 Appendix C: the worked examples (C.2 to C.6), decoded whole,
//! byte by byte and in pieces of 3, checking the header lists, the
//! dynamic table and its size after each block. The encoded bytes are
//! the RFC's, as quoted in golang.org/x/net/http2/hpack's tests.
mod common;
use common::*;
use verilith_hpack::decoder::Decoder;

fn p(n: &str, v: &str) -> (Vec<u8>, Vec<u8>) {
    (n.as_bytes().to_vec(), v.as_bytes().to_vec())
}

struct Step {
    enc: &'static str,
    want: Vec<(Vec<u8>, Vec<u8>)>,
    table: Vec<(Vec<u8>, Vec<u8>)>,
    size: u64,
}

fn series(max: u32, steps: &[Step]) {
    for pieces in [vec![], vec![1], vec![3], vec![2, 5, 1]] {
        let mut d = Decoder::new().unwrap();
        // The examples assume the table size is already `max`.
        d.table.resize(max);
        for s in steps {
            let block = dehex(s.enc);
            let got = decode_block(&mut d, &block, &pieces).expect("decodes");
            let got: Vec<_> = got.into_iter().map(|(n, v, _)| (n, v)).collect();
            assert_eq!(got, s.want, "headers, pieces {:?}", pieces);
            assert_eq!(table(&d), s.table, "table, pieces {:?}", pieces);
            assert_eq!(d.table.size, s.size);
        }
    }
}

#[test]
fn c2() {
    let cases: [(&str, (Vec<u8>, Vec<u8>), bool, usize); 4] = [
        ("400a 6375 7374 6f6d 2d6b 6579 0d63 7573 746f 6d2d 6865 6164 6572", p("custom-key", "custom-header"), false, 1),
        ("040c 2f73 616d 706c 652f 7061 7468", p(":path", "/sample/path"), false, 0),
        ("1008 7061 7373 776f 7264 0673 6563 7265 74", p("password", "secret"), true, 0),
        ("82", p(":method", "GET"), false, 0),
    ];
    for (enc, want, never, tlen) in cases {
        let mut d = Decoder::new().unwrap();
        let got = decode_block(&mut d, &dehex(enc), &[]).unwrap();
        assert_eq!(got, vec![(want.0, want.1, never)]);
        assert_eq!(d.table.ents.len(), tlen);
    }
}

#[test]
fn c3_requests() {
    series(4096, &[
        Step { enc: "8286 8441 0f77 7777 2e65 7861 6d70 6c65 2e63 6f6d",
            want: vec![p(":method", "GET"), p(":scheme", "http"), p(":path", "/"), p(":authority", "www.example.com")],
            table: vec![p(":authority", "www.example.com")], size: 57 },
        Step { enc: "8286 84be 5808 6e6f 2d63 6163 6865",
            want: vec![p(":method", "GET"), p(":scheme", "http"), p(":path", "/"), p(":authority", "www.example.com"), p("cache-control", "no-cache")],
            table: vec![p("cache-control", "no-cache"), p(":authority", "www.example.com")], size: 110 },
        Step { enc: "8287 85bf 400a 6375 7374 6f6d 2d6b 6579 0c63 7573 746f 6d2d 7661 6c75 65",
            want: vec![p(":method", "GET"), p(":scheme", "https"), p(":path", "/index.html"), p(":authority", "www.example.com"), p("custom-key", "custom-value")],
            table: vec![p("custom-key", "custom-value"), p("cache-control", "no-cache"), p(":authority", "www.example.com")], size: 164 },
    ]);
}

#[test]
fn c4_requests_huffman() {
    series(4096, &[
        Step { enc: "8286 8441 8cf1 e3c2 e5f2 3a6b a0ab 90f4 ff",
            want: vec![p(":method", "GET"), p(":scheme", "http"), p(":path", "/"), p(":authority", "www.example.com")],
            table: vec![p(":authority", "www.example.com")], size: 57 },
        Step { enc: "8286 84be 5886 a8eb 1064 9cbf",
            want: vec![p(":method", "GET"), p(":scheme", "http"), p(":path", "/"), p(":authority", "www.example.com"), p("cache-control", "no-cache")],
            table: vec![p("cache-control", "no-cache"), p(":authority", "www.example.com")], size: 110 },
        Step { enc: "8287 85bf 4088 25a8 49e9 5ba9 7d7f 8925 a849 e95b b8e8 b4bf",
            want: vec![p(":method", "GET"), p(":scheme", "https"), p(":path", "/index.html"), p(":authority", "www.example.com"), p("custom-key", "custom-value")],
            table: vec![p("custom-key", "custom-value"), p("cache-control", "no-cache"), p(":authority", "www.example.com")], size: 164 },
    ]);
}

fn responses() -> (Vec<Vec<(Vec<u8>, Vec<u8>)>>, Vec<Vec<(Vec<u8>, Vec<u8>)>>) {
    let date1 = "Mon, 21 Oct 2013 20:13:21 GMT";
    let date2 = "Mon, 21 Oct 2013 20:13:22 GMT";
    let loc = "https://www.example.com";
    let cookie = "foo=ASDJKHQKBZXOQWEOPIUAXQWEOIU; max-age=3600; version=1";
    (
        vec![
            vec![p(":status", "302"), p("cache-control", "private"), p("date", date1), p("location", loc)],
            vec![p(":status", "307"), p("cache-control", "private"), p("date", date1), p("location", loc)],
            vec![p(":status", "200"), p("cache-control", "private"), p("date", date2), p("location", loc), p("content-encoding", "gzip"), p("set-cookie", cookie)],
        ],
        vec![
            vec![p("location", loc), p("date", date1), p("cache-control", "private"), p(":status", "302")],
            vec![p(":status", "307"), p("location", loc), p("date", date1), p("cache-control", "private")],
            vec![p("set-cookie", cookie), p("content-encoding", "gzip"), p("date", date2)],
        ],
    )
}

#[test]
fn c5_responses() {
    let (w, t) = responses();
    series(256, &[
        Step { enc: "4803 3330 3258 0770 7269 7661 7465 611d 4d6f 6e2c 2032 3120 4f63 7420 3230 3133 2032 303a 3133 3a32 3120 474d 546e 1768 7474 7073 3a2f 2f77 7777 2e65 7861 6d70 6c65 2e63 6f6d",
            want: w[0].clone(), table: t[0].clone(), size: 222 },
        Step { enc: "4803 3330 37c1 c0bf", want: w[1].clone(), table: t[1].clone(), size: 222 },
        Step { enc: "88c1 611d 4d6f 6e2c 2032 3120 4f63 7420 3230 3133 2032 303a 3133 3a32 3220 474d 54c0 5a04 677a 6970 7738 666f 6f3d 4153 444a 4b48 514b 425a 584f 5157 454f 5049 5541 5851 5745 4f49 553b 206d 6178 2d61 6765 3d33 3630 303b 2076 6572 7369 6f6e 3d31",
            want: w[2].clone(), table: t[2].clone(), size: 215 },
    ]);
}

#[test]
fn c6_responses_huffman() {
    let (w, t) = responses();
    series(256, &[
        Step { enc: "4882 6402 5885 aec3 771a 4b61 96d0 7abe 9410 54d4 44a8 2005 9504 0b81 66e0 82a6 2d1b ff6e 919d 29ad 1718 63c7 8f0b 97c8 e9ae 82ae 43d3",
            want: w[0].clone(), table: t[0].clone(), size: 222 },
        Step { enc: "4883 640e ffc1 c0bf", want: w[1].clone(), table: t[1].clone(), size: 222 },
        Step { enc: "88c1 6196 d07a be94 1054 d444 a820 0595 040b 8166 e084 a62d 1bff c05a 839b d9ab 77ad 94e7 821d d7f2 e6c7 b335 dfdf cd5b 3960 d5af 2708 7f36 72c1 ab27 0fb5 291f 9587 3160 65c0 03ed 4ee5 b106 3d50 07",
            want: w[2].clone(), table: t[2].clone(), size: 215 },
    ]);
}
