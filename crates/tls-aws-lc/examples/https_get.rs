//! `cargo run --example https_get -- https://host/path [roots.pem]`: a GET
//! over the verified client, printing the response head. Roots default to
//! the system bundle; `HTTPS_PROXY` (http://host:port) is followed with
//! CONNECT.
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::sync::Arc;
use verilith_tls_aws_lc::client::{config, TlsStream};

fn pem_certs(text: &str) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut b64 = String::new();
    let mut inside = false;
    for line in text.lines() {
        let l = line.trim();
        if l == "-----BEGIN CERTIFICATE-----" {
            inside = true;
            b64.clear();
        } else if l == "-----END CERTIFICATE-----" {
            inside = false;
            if let Some(d) = base64(&b64) {
                out.push(d);
            }
        } else if inside {
            b64.push_str(l);
        }
    }
    out
}

fn base64(s: &str) -> Option<Vec<u8>> {
    let val = |c: u8| match c {
        b'A'..=b'Z' => Some(c - b'A'),
        b'a'..=b'z' => Some(c - b'a' + 26),
        b'0'..=b'9' => Some(c - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    };
    let mut out = Vec::new();
    let (mut acc, mut bits) = (0u32, 0);
    for &c in s.as_bytes() {
        if c == b'=' {
            break;
        }
        acc = acc << 6 | val(c)? as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    Some(out)
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let url = args.get(1).expect("usage: https_get https://host/path [roots.pem]");
    let rest = url.strip_prefix("https://").expect("an https URL");
    let (hostport, path) = rest.split_once('/').map(|(h, p)| (h, format!("/{p}"))).unwrap_or((rest, "/".into()));
    let (host, port) = hostport.split_once(':').map(|(h, p)| (h, p.parse().unwrap())).unwrap_or((hostport, 443u16));
    let roots_file = args.get(2).cloned().unwrap_or("/etc/ssl/certs/ca-certificates.crt".into());
    let roots = pem_certs(&std::fs::read_to_string(&roots_file)?);
    eprintln!("{} trust anchors from {roots_file}", roots.len());

    let proxy = std::env::var("HTTPS_PROXY").or_else(|_| std::env::var("https_proxy")).ok();
    let tcp = match proxy {
        Some(p) => {
            let p = p.trim_start_matches("http://").trim_end_matches('/');
            let p = p.rsplit_once('@').map(|(_, h)| h).unwrap_or(p);
            let mut tcp = TcpStream::connect(p)?;
            write!(tcp, "CONNECT {host}:{port} HTTP/1.1\r\nHost: {host}:{port}\r\n\r\n")?;
            let mut r = BufReader::new(tcp.try_clone()?);
            let mut line = String::new();
            r.read_line(&mut line)?;
            assert!(line.contains(" 200"), "proxy: {line}");
            loop {
                line.clear();
                r.read_line(&mut line)?;
                if line == "\r\n" || line.is_empty() {
                    break;
                }
            }
            tcp
        }
        None => TcpStream::connect((host, port))?,
    };
    let mut t = TlsStream::connect(Arc::new(config(roots, &[b"http/1.1"])), host, tcp)?;
    eprintln!("connected: {} certificates, ALPN {:?}", t.peer_certificates().len(), t.alpn().map(String::from_utf8_lossy));
    write!(t, "GET {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nUser-Agent: verilith-tls-example\r\n\r\n")?;
    let mut body = Vec::new();
    let r = t.read_to_end(&mut body);
    let text = String::from_utf8_lossy(&body);
    println!("{}", text.split("\r\n\r\n").next().unwrap_or(""));
    eprintln!("{} bytes; end: {:?}", body.len(), r.err().map(|e| e.to_string()));
    Ok(())
}
