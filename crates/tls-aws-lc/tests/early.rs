//! 0-RTT data (RFC 8446 §4.2.10) with a rustls client, in memory:
//! accepted on a resumption, answered before the handshake is done,
//! and refused when replayed or when the ticket does not allow it.
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore};
use std::io::{Read, Write};
use std::sync::Arc;
use verilith_tls::server::Config;
use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

fn server_config(alpn: &[u8], max_early: u32) -> Arc<Config> {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let mut wire = vec![alpn.len() as u8];
    wire.extend_from_slice(alpn);
    let mut c = Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), wire, &vec![LEAF.to_vec()]).unwrap();
    c.set_tickets(2, 3600);
    c.set_early_data(max_early);
    Arc::new(c)
}

fn client_config(alpn: &[u8]) -> Arc<ClientConfig> {
    let mut roots = RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let mut c = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = vec![alpn.to_vec()];
    c.enable_early_data = true;
    Arc::new(c)
}

fn server(cfg: &Arc<Config>, keys: &Arc<TicketKeys>) -> ServerStream<AwsLc> {
    ServerStream::new(cfg.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())).with_tickets(keys.clone()))
}

fn client(cc: &Arc<ClientConfig>) -> ClientConnection {
    ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap()
}

fn client_out(c: &mut ClientConnection) -> Vec<u8> {
    let mut buf = Vec::new();
    while c.wants_write() {
        c.write_tls(&mut buf).unwrap();
    }
    buf
}

fn to_client(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>, got: &mut Vec<u8>) {
    let out = s.take_pending();
    let mut rd = &out[..];
    while !rd.is_empty() {
        c.read_tls(&mut rd).unwrap();
        c.process_new_packets().expect("client accepts what the server sends");
        let _ = c.reader().read_to_end(got);
    }
}

/// Runs the rest of the handshake and any data both ways.
fn pump(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>, got: &mut Vec<u8>) {
    for _ in 0..20 {
        let buf = client_out(c);
        s.read_tls(&buf);
        s.process().unwrap();
        let moved = !buf.is_empty() || !s.pending().is_empty();
        to_client(c, s, got);
        if !moved {
            return;
        }
    }
}

/// A full handshake, so that the client holds tickets.
fn first(cc: &Arc<ClientConfig>, sc: &Arc<Config>, keys: &Arc<TicketKeys>) {
    let mut c = client(cc);
    let mut s = server(sc, keys);
    pump(&mut c, &mut s, &mut Vec::new());
    assert!(!c.is_handshaking() && !s.is_handshaking());
    assert!(!s.conn().early_accepted());
}

#[test]
fn early_data_is_taken_and_answered_before_the_handshake_is_done() {
    let keys = Arc::new(TicketKeys::new(3600));
    let sc = server_config(b"http/1.1", 16384);
    let cc = client_config(b"http/1.1");
    first(&cc, &sc, &keys);
    let mut c = client(&cc);
    let req = b"GET / HTTP/1.1\r\nHost: x\r\n\r\n";
    let n = c.early_data().expect("the ticket allows 0-RTT data").write(req).unwrap();
    assert_eq!(n, req.len());
    let mut s = server(&sc, &keys);
    // The ClientHello and the 0-RTT data, in one flight.
    s.read_tls(&client_out(&mut c));
    s.process().unwrap();
    assert!(s.conn().early_accepted());
    assert!(s.in_early_data());
    assert_eq!(s.plaintext(), req);
    s.consume_plaintext(req.len());
    // 0.5-RTT: the answer goes with the server's flight.
    s.write(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi").unwrap();
    let mut got = Vec::new();
    to_client(&mut c, &mut s, &mut got);
    pump(&mut c, &mut s, &mut got);
    assert!(c.is_early_data_accepted());
    assert!(!s.is_handshaking() && !s.in_early_data());
    assert_eq!(got, b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi");
    // After the handshake, ordinary data both ways.
    c.writer().write_all(b"after").unwrap();
    pump(&mut c, &mut s, &mut Vec::new());
    assert_eq!(s.plaintext(), b"after");
}

#[test]
fn replayed_early_data_is_refused() {
    let keys = Arc::new(TicketKeys::new(3600));
    let sc = server_config(b"http/1.1", 16384);
    let cc = client_config(b"http/1.1");
    first(&cc, &sc, &keys);
    let mut c = client(&cc);
    c.early_data().unwrap().write_all(b"POST /pay HTTP/1.1\r\n\r\n").unwrap();
    let flight = client_out(&mut c);
    let mut s1 = server(&sc, &keys);
    s1.read_tls(&flight);
    s1.process().unwrap();
    assert!(s1.conn().early_accepted());
    // An attacker sends the same bytes again, to a second connection: the
    // handshake goes on (1-RTT) but the 0-RTT data is skipped.
    let mut s2 = server(&sc, &keys);
    s2.read_tls(&flight);
    s2.process().unwrap();
    assert!(!s2.conn().early_accepted());
    assert!(!s2.in_early_data());
    assert!(s2.plaintext().is_empty());
    assert!(!s2.pending().is_empty(), "the server still answers the ClientHello");
}

#[test]
fn no_early_data_unless_the_server_allows_it() {
    let keys = Arc::new(TicketKeys::new(3600));
    // Tickets from a server that takes no 0-RTT data say so: the client
    // sends none.
    let sc = server_config(b"http/1.1", 0);
    let cc = client_config(b"http/1.1");
    first(&cc, &sc, &keys);
    let mut c = client(&cc);
    assert!(c.early_data().is_none());
    let mut s = server(&sc, &keys);
    pump(&mut c, &mut s, &mut Vec::new());
    assert!(!s.is_handshaking() && !s.conn().early_accepted());
}

#[test]
fn early_data_turned_off_after_the_ticket_was_issued() {
    let keys = Arc::new(TicketKeys::new(3600));
    let cc = client_config(b"http/1.1");
    first(&cc, &server_config(b"http/1.1", 16384), &keys);
    let mut c = client(&cc);
    c.early_data().unwrap().write_all(b"GET / HTTP/1.1\r\n\r\n").unwrap();
    // Same ticket keys, but this server takes no 0-RTT data: it resumes
    // and skips the early records, and the client sends them again.
    let sc = server_config(b"http/1.1", 0);
    let mut s = server(&sc, &keys);
    let mut got = Vec::new();
    pump(&mut c, &mut s, &mut got);
    assert!(!s.is_handshaking() && !s.conn().early_accepted());
    assert!(!c.is_early_data_accepted());
    assert!(s.plaintext().is_empty());
}
