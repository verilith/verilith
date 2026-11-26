//! RFC 9204 Appendix B, decoded.
use verilith_qpack::{Decoder, Fields, Res};

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn lines(f: &Fields) -> Vec<(String, String)> {
    (0..f.len())
        .map(|i| {
            let (n, v, _) = f.get(i);
            (String::from_utf8(n.to_vec()).unwrap(), String::from_utf8(v.to_vec()).unwrap())
        })
        .collect()
}

fn out(d: &mut Decoder) -> Vec<u8> {
    let mut v = Vec::new();
    d.take_output(&mut v);
    v
}

#[test]
fn appendix_b() {
    let mut d = Decoder::new(220, 16, 1 << 16).unwrap();
    let mut f = Fields::new();
    let mut ready = Vec::new();

    // B.1 Literal Field Line with Name Reference.
    assert_eq!(d.decode(0, &hex("0000 510b 2f69 6e64 6578 2e68 746d 6c"), &mut f), Res::Done);
    assert_eq!(lines(&f), vec![(":path".into(), "/index.html".into())]);
    assert!(out(&mut d).is_empty());

    // B.2 Dynamic Table.
    let enc = hex("3fbd01 c00f 7777 772e 6578 616d 706c 652e 636f 6d c10c 2f73 616d 706c 652f 7061 7468");
    // In two pieces, split inside an instruction.
    assert!(d.feed_encoder(&enc[..9], &mut ready));
    assert!(d.feed_encoder(&enc[9..], &mut ready));
    assert_eq!(d.table.icount(), 2);
    assert_eq!(d.table.size, 106);
    assert_eq!(out(&mut d), hex("02"));
    assert_eq!(d.decode(4, &hex("0381 10 11"), &mut f), Res::Done);
    assert_eq!(lines(&f), vec![(":authority".into(), "www.example.com".into()), (":path".into(), "/sample/path".into())]);
    assert_eq!(out(&mut d), hex("84"));

    // B.3 Speculative Insert.
    assert!(d.feed_encoder(&hex("4a63 7573 746f 6d2d 6b65 790c 6375 7374 6f6d 2d76 616c 7565"), &mut ready));
    assert_eq!(d.table.size, 160);
    assert_eq!(out(&mut d), hex("01"));

    // B.4 Duplicate, Stream Cancellation: the section arrives first.
    let sec = hex("0500 80 c1 81");
    assert_eq!(d.decode(8, &sec, &mut f), Res::Blocked);
    assert_eq!(d.decode(8, &sec, &mut f), Res::Blocked);
    d.cancel(8);
    assert_eq!(out(&mut d), hex("48"));
    assert!(d.feed_encoder(&hex("02"), &mut ready));
    assert!(ready.is_empty());
    assert_eq!(d.table.size, 217);
    assert_eq!(out(&mut d), hex("01"));
    // Had it not been cancelled, it would decode now.
    assert_eq!(d.decode(8, &sec, &mut f), Res::Done);
    assert_eq!(
        lines(&f),
        vec![
            (":authority".into(), "www.example.com".into()),
            (":path".into(), "/".into()),
            ("custom-key".into(), "custom-value".into())
        ]
    );
    assert_eq!(out(&mut d), hex("88"));

    // B.5 Dynamic Table Insert, Eviction.
    assert!(d.feed_encoder(&hex("810d 6375 7374 6f6d 2d76 616c 7565 32"), &mut ready));
    assert_eq!(d.table.size, 215);
    assert_eq!(d.table.dropped, 1);
    assert_eq!(d.table.icount(), 5);
}

#[test]
fn blocked_then_unblocked() {
    let mut d = Decoder::new(220, 1, 1 << 16).unwrap();
    let mut f = Fields::new();
    let mut ready = Vec::new();
    let sec = hex("0381 10 11");
    assert_eq!(d.decode(4, &sec, &mut f), Res::Blocked);
    // A second blocked stream is one more than SETTINGS_QPACK_BLOCKED_STREAMS.
    assert_eq!(d.decode(8, &sec, &mut f), Res::Bad);
    let enc = hex("3fbd01 c00f 7777 772e 6578 616d 706c 652e 636f 6d c10c 2f73 616d 706c 652f 7061 7468");
    for b in &enc {
        assert!(d.feed_encoder(std::slice::from_ref(b), &mut ready));
    }
    assert_eq!(ready, vec![4]);
    assert_eq!(d.decode(4, &sec, &mut f), Res::Done);
    assert_eq!(f.len(), 2);
}

#[test]
fn errors() {
    let mut d = Decoder::new(220, 1, 1 << 16).unwrap();
    let mut ready = Vec::new();
    // Capacity above the maximum.
    assert!(!d.feed_encoder(&hex("3fbe01"), &mut ready));
    let mut d = Decoder::new(220, 1, 1 << 16).unwrap();
    // An entry larger than the capacity (0).
    assert!(!d.feed_encoder(&hex("c00f 7777 772e 6578 616d 706c 652e 636f 6d"), &mut ready));
    let mut d = Decoder::new(220, 1, 40).unwrap();
    let mut f = Fields::new();
    // Over the size limit: :path=/index.html is 5 + 11 + 32 = 48.
    assert_eq!(d.decode(0, &hex("0000 510b 2f69 6e64 6578 2e68 746d 6c"), &mut f), Res::TooBig);
    // Static index out of range.
    assert_eq!(d.decode(0, &hex("0000 ff24"), &mut f), Res::Bad);
    // A truncated section.
    assert_eq!(d.decode(0, &hex("0000 510b 2f69"), &mut f), Res::Bad);
}
