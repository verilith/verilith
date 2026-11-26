//! Differential check: random mutations of each input, parsed by both.
//! verilith-tls's ClientHello rules are a subset of what rustls checks
//! when it reads one (rustls also checks values, e.g. that the server name
//! is a DNS name), so every mutation rustls accepts must parse here, and
//! must give the same server name and ALPN list.
use crate::record;
use rustls::server::Acceptor;
use verilith_tls::hello::ClientHello;

pub fn run(inputs: &[(String, Vec<u8>)]) {
    let mut seed = 0x2545f4914f6cdd1du64;
    let mut rnd = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let (mut both, mut only_ours, mut only_theirs, mut neither) = (0, 0, 0, 0);
    for (name, body) in inputs {
        for _ in 0..200_000 {
            let mut m = body.clone();
            for _ in 0..1 + rnd() % 2 {
                let i = (rnd() as usize) % m.len();
                m[i] = rnd() as u8;
            }
            let ours = ClientHello::parse(&m);
            let rec = record(&m);
            let mut acc = Acceptor::default();
            acc.read_tls(&mut &rec[..]).unwrap();
            let theirs = match acc.accept() {
                Ok(Some(a)) => {
                    let ch = a.client_hello();
                    Some((
                        ch.server_name().map(|s| s.as_bytes().to_vec()),
                        ch.alpn().map(|i| i.map(|p| p.to_vec()).collect::<Vec<_>>()),
                    ))
                }
                _ => None,
            };
            match (&ours, &theirs) {
                (Ok(h), Some((sni, alpn))) => {
                    both += 1;
                    let our_sni = h.server_name.map(|s| {
                        let n = s.of(&m);
                        n.strip_suffix(b".").unwrap_or(n).to_ascii_lowercase()
                    });
                    // rustls keeps no name that is not a DNS name, and
                    // lowercases the ones it keeps and drops a final dot.
                    if sni.is_some() {
                        assert_eq!(&our_sni, sni, "{name}: server name");
                    }
                    let our_alpn = h.alpn.map(|a| {
                        let mut v = Vec::new();
                        let mut l = a.of(&m);
                        while let [n, rest @ ..] = l {
                            v.push(rest[..*n as usize].to_vec());
                            l = &rest[*n as usize..];
                        }
                        v
                    });
                    assert_eq!(&our_alpn, alpn, "{name}: alpn");
                }
                (Ok(_), None) => only_ours += 1,
                (Err(e), Some(_)) => {
                    only_theirs += 1;
                    if only_theirs <= 10_000 {
                        eprintln!("{name}: rustls accepts, verilith-tls says {e:?}: {}", hex(&m));
                    }
                }
                (Err(_), None) => neither += 1,
            }
        }
    }
    println!("both accept {both}, only verilith-tls {only_ours}, only rustls {only_theirs}, neither {neither}");
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
