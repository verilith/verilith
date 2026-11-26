//! Negotiation and server name checks, on the real ClientHellos in
//! tests/data and on edits of them.
use verilith_tls::hello::ClientHello;
use verilith_tls::negotiate::{NegAlert, Outcome, negotiate, valid_host_name_x};

fn data(name: &str) -> Vec<u8> {
    std::fs::read(format!("{}/tests/data/{name}.bin", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

const SUITES: &[u16] = &[0x1301, 0x1302, 0x1303];
const GROUPS: &[u16] = &[0x11ec, 0x001d, 0x0017];
const SIGS: &[u16] = &[0x0804, 0x0403, 0x0807];

fn alpn(protos: &[&[u8]]) -> Vec<u8> {
    protos.iter().flat_map(|p| std::iter::once(p.len() as u8).chain(p.iter().copied())).collect()
}

fn neg(name: &str, suites: &[u16], groups: &[u16], sigs: &[u16], protos: &[&[u8]]) -> (Vec<u8>, Vec<u8>, Outcome) {
    let b = data(name);
    let h = ClientHello::parse(&b).unwrap();
    let a = alpn(protos);
    let r = negotiate(&b, &h, suites, groups, sigs, &a);
    (b, a, r)
}

#[test]
fn full_handshakes() {
    let (b, a, r) = neg("py-default-sni-alpn", SUITES, GROUPS, SIGS, &[b"h2", b"http/1.1"]);
    let Outcome::Accept(c) = r else { panic!("{r:?}") };
    assert_eq!((c.suite, c.group), (0x1301, 0x11ec));
    assert_eq!(c.share.len(), 1216, "X25519MLKEM768 client share");
    let (ours, theirs) = c.alpn.unwrap();
    assert_eq!((ours.of(&a), theirs.of(&b)), (&b"h2"[..], &b"h2"[..]));
    // The server's preference wins.
    let (b, a, r) = neg("py-default-sni-alpn", &[0x1303, 0x1301], &[0x001d, 0x11ec], SIGS, &[b"http/1.1", b"h2"]);
    let Outcome::Accept(c) = r else { panic!("{r:?}") };
    assert_eq!((c.suite, c.group, c.share.len()), (0x1303, 0x001d, 32));
    assert_eq!(c.alpn.unwrap().0.of(&a), b"http/1.1");
    assert_eq!(c.alpn.unwrap().1.of(&b), b"http/1.1");
    // No ALPN from the client: none chosen, whatever the server has.
    let (_, _, r) = neg("py-tls13-only", SUITES, GROUPS, SIGS, &[b"h2"]);
    let Outcome::Accept(c) = r else { panic!("{r:?}") };
    assert!(c.alpn.is_none());
}

#[test]
fn retry_and_failures() {
    // openssl s_client -groups P-256:P-384 sends a P-256 share only. A
    // share the server takes is used even if the server prefers another
    // group (no extra round trip); without one, a HelloRetryRequest.
    let (_, _, r) = neg("ossl-p256-p384", SUITES, &[0x0018, 0x0017], SIGS, &[]);
    assert!(matches!(r, Outcome::Accept(c) if c.group == 0x0017));
    let (_, _, r) = neg("ossl-p256-p384", SUITES, &[0x001d, 0x0018], SIGS, &[]);
    assert_eq!(r, Outcome::Retry { suite: 0x1301, group: 0x0018 });
    let (_, _, r) = neg("ossl-p256-p384", SUITES, &[0x001d], SIGS, &[]);
    assert_eq!(r, Outcome::Reject(NegAlert::HandshakeFailure));
    let (_, _, r) = neg("py-tls12-only", SUITES, GROUPS, SIGS, &[]);
    assert_eq!(r, Outcome::Reject(NegAlert::ProtocolVersion));
    let (_, _, r) = neg("py-default-sni-alpn", &[0x1304], GROUPS, SIGS, &[]);
    assert_eq!(r, Outcome::Reject(NegAlert::HandshakeFailure));
    let (_, _, r) = neg("py-default-sni-alpn", SUITES, GROUPS, &[0x0101], &[]);
    assert_eq!(r, Outcome::Reject(NegAlert::HandshakeFailure));
    let (_, _, r) = neg("ossl-alpn3", SUITES, GROUPS, SIGS, &[b"spdy/3"]);
    assert_eq!(r, Outcome::Reject(NegAlert::NoApplicationProtocol));
    let (b, a, r) = neg("ossl-alpn3", SUITES, GROUPS, SIGS, &[b"spdy/3", b"acme-tls/1"]);
    let Outcome::Accept(c) = r else { panic!("{r:?}") };
    assert_eq!((c.alpn.unwrap().0.of(&a), c.alpn.unwrap().1.of(&b)), (&b"acme-tls/1"[..], &b"acme-tls/1"[..]));
}

#[test]
fn compression_must_be_null() {
    let mut b = data("py-tls13-only");
    let h = ClientHello::parse(&b).unwrap();
    b[h.compression_methods.start] = 1;
    let h = ClientHello::parse(&b).unwrap();
    assert_eq!(negotiate(&b, &h, SUITES, GROUPS, SIGS, &[]), Outcome::Reject(NegAlert::IllegalParameter));
}

#[test]
fn host_names() {
    for ok in ["example.com", "a", "x-y.example", "_acme.example.org", "123.example", "EXAMPLE.com", &"a".repeat(63)] {
        assert!(valid_host_name_x(ok.as_bytes()), "{ok}");
    }
    let long = ["a".repeat(63), "b".repeat(63), "c".repeat(63), "d".repeat(61)].join(".");
    assert_eq!(long.len(), 253);
    assert!(valid_host_name_x(long.as_bytes()));
    for bad in [
        "", "example.com.", ".example", "a..b", "-a.example", "a-.example", "10.0.0.1", "1",
        "::1", "[::1]", "ex ample.com", "exa\0mple", "é.example", &"a".repeat(64), &(long.clone() + "e"),
    ] {
        assert!(!valid_host_name_x(bad.as_bytes()), "{bad:?}");
    }
}
