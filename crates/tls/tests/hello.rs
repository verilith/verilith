//! ClientHello parsing on real ClientHellos (tests/data, from
//! tools/gen_hellos.py) and on hand-built ones for each rule of the spec.
use verilith_tls::hello::{Alert, ClientHello, Span};
use verilith_tls::record::{RecordHeader, handshake_message_x};

fn data(name: &str) -> Vec<u8> {
    std::fs::read(format!("{}/tests/data/{name}.bin", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

fn u16s(b: &[u8], s: Span) -> Vec<u16> {
    s.of(b).chunks(2).map(|c| u16::from_be_bytes([c[0], c[1]])).collect()
}

fn alpn(b: &[u8], s: Span) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    let mut l = s.of(b);
    while !l.is_empty() {
        let n = l[0] as usize;
        v.push(l[1..1 + n].to_vec());
        l = &l[1 + n..];
    }
    v
}

fn key_share_groups(b: &[u8], s: Span) -> Vec<u16> {
    let mut v = Vec::new();
    let mut l = s.of(b);
    while !l.is_empty() {
        v.push(u16::from_be_bytes([l[0], l[1]]));
        let n = u16::from_be_bytes([l[2], l[3]]) as usize;
        l = &l[4 + n..];
    }
    v
}

#[test]
fn real_hellos() {
    let cases: &[(&str, Option<&str>, &[&str], bool)] = &[
        ("py-default-sni-alpn", Some("example.com"), &["h2", "http/1.1"], true),
        ("py-no-sni", None, &["http/1.1"], true),
        ("py-tls12-only", Some("example.org"), &[], false),
        ("py-tls13-only", Some("a.example"), &[], true),
        ("ossl-alpn3", Some("pq.example"), &["h2", "http/1.1", "acme-tls/1"], true),
        ("ossl-p256-p384", Some("x.example"), &[], true),
    ];
    for &(name, sni, protos, tls13) in cases {
        let b = data(name);
        let h = ClientHello::parse(&b).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        assert_eq!(h.legacy_version, 0x0303, "{name}");
        assert_eq!(h.server_name.map(|s| s.of(&b).to_vec()), sni.map(|s| s.as_bytes().to_vec()), "{name}");
        let want: Vec<Vec<u8>> = protos.iter().map(|p| p.as_bytes().to_vec()).collect();
        assert_eq!(h.alpn.map(|s| alpn(&b, s)).unwrap_or_default(), want, "{name}");
        let versions = h.supported_versions.map(|s| u16s(&b, s)).unwrap_or_default();
        assert_eq!(versions.contains(&0x0304), tls13, "{name}");
        if tls13 {
            let groups = key_share_groups(&b, h.key_shares.unwrap());
            assert!(!groups.is_empty(), "{name}");
            assert!(h.supported_groups.is_some() && h.signature_algorithms.is_some(), "{name}");
        }
        assert_eq!(h.compression_methods.of(&b), &[0], "{name}");
        assert!(u16s(&b, h.cipher_suites).len() >= 1);
        // Every strict prefix is malformed, but for the one that stops
        // before the extensions (an old-style ClientHello without them);
        // so is one more byte.
        for n in 0..b.len() {
            let ok = n == h.compression_methods.end;
            assert_eq!(ClientHello::parse(&b[..n]).is_ok(), ok, "{name}: prefix {n}");
        }
        let mut longer = b.clone();
        longer.push(0);
        assert_eq!(ClientHello::parse(&longer).unwrap_err(), Alert::DecodeError);
    }
    let b = data("py-default-sni-alpn");
    let groups = key_share_groups(&b, ClientHello::parse(&b).unwrap().key_shares.unwrap());
    assert!(groups.contains(&0x11ec), "Python's OpenSSL offers X25519MLKEM768: {groups:x?}");
}

#[test]
fn record_and_handshake_headers() {
    let b = data("ossl-alpn3");
    let mut msg = vec![1u8, 0, (b.len() >> 8) as u8, b.len() as u8];
    msg.extend_from_slice(&b);
    let (t, sp) = handshake_message_x(&msg).unwrap();
    assert_eq!((t, sp.start, sp.end), (1, 4, msg.len()));
    assert!(handshake_message_x(&msg[..msg.len() - 1]).is_none());
    let mut rec = vec![22u8, 3, 1, (msg.len() >> 8) as u8, msg.len() as u8];
    rec.extend_from_slice(&msg);
    let h = RecordHeader::parse(&rec).unwrap();
    assert_eq!((h.content_type, h.legacy_version, h.length), (22, 0x0301, msg.len()));
    assert!(RecordHeader::parse(&rec[..4]).is_none());
}

// ---- Hand-built ClientHellos ----------------------------------------------

fn v8(b: &[u8]) -> Vec<u8> {
    let mut v = vec![b.len() as u8];
    v.extend_from_slice(b);
    v
}

fn v16(b: &[u8]) -> Vec<u8> {
    let mut v = (b.len() as u16).to_be_bytes().to_vec();
    v.extend_from_slice(b);
    v
}

fn ext(t: u16, data: &[u8]) -> Vec<u8> {
    let mut v = t.to_be_bytes().to_vec();
    v.extend(v16(data));
    v
}

fn hello(exts: &[Vec<u8>]) -> Vec<u8> {
    let mut b = vec![3, 3];
    b.extend([7u8; 32]);
    b.extend(v8(&[1; 32]));
    b.extend(v16(&[0x13, 0x01, 0x13, 0x02]));
    b.extend(v8(&[0]));
    b.extend(v16(&exts.concat()));
    b
}

fn sni(names: &[(u8, &[u8])]) -> Vec<u8> {
    let mut l = Vec::new();
    for (t, n) in names {
        l.push(*t);
        l.extend(v16(n));
    }
    ext(0, &v16(&l))
}

fn alpn_ext(protos: &[&[u8]]) -> Vec<u8> {
    let l: Vec<u8> = protos.iter().flat_map(|p| v8(p)).collect();
    ext(16, &v16(&l))
}

fn key_share(groups: &[u16]) -> Vec<u8> {
    let mut l = Vec::new();
    for g in groups {
        l.extend(g.to_be_bytes());
        l.extend(v16(&[0x42; 32]));
    }
    ext(51, &v16(&l))
}

fn psk(ids: usize, binders: usize) -> Vec<u8> {
    let mut i = Vec::new();
    for _ in 0..ids {
        i.extend(v16(b"ticket"));
        i.extend([0, 0, 0, 1]);
    }
    let mut b = Vec::new();
    for _ in 0..binders {
        b.extend(v8(&[9; 32]));
    }
    let mut d = v16(&i);
    d.extend(v16(&b));
    ext(41, &d)
}

fn parse(b: &[u8]) -> Result<ClientHello, Alert> {
    ClientHello::parse(b)
}

#[test]
fn outer_fields() {
    let b = hello(&[]);
    let h = parse(&b).unwrap();
    assert_eq!(h.session_id.of(&b), &[1; 32]);
    assert_eq!(u16s(&b, h.cipher_suites), vec![0x1301, 0x1302]);
    assert!(h.extensions.start == h.extensions.end);
    // No extensions vector at all: allowed for older clients.
    let mut b = vec![3, 3];
    b.extend([0u8; 32]);
    b.extend(v8(&[]));
    b.extend(v16(&[0, 0x2f]));
    b.extend(v8(&[0]));
    let h = parse(&b).unwrap();
    assert_eq!((h.extensions.start, h.extensions.end), (b.len(), b.len()));
    // A 33-byte session id, odd or empty cipher suites, no compression method.
    let bad = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut b = vec![3, 3];
        b.extend([0u8; 32]);
        f(&mut b);
        assert_eq!(parse(&b).unwrap_err(), Alert::DecodeError);
    };
    bad(&|b| {
        b.extend(v8(&[0; 33]));
        b.extend(v16(&[0, 0x2f]));
        b.extend(v8(&[0]));
    });
    bad(&|b| {
        b.extend(v8(&[]));
        b.extend(v16(&[0, 0x2f, 1]));
        b.extend(v8(&[0]));
    });
    bad(&|b| {
        b.extend(v8(&[]));
        b.extend(v16(&[]));
        b.extend(v8(&[0]));
    });
    bad(&|b| {
        b.extend(v8(&[]));
        b.extend(v16(&[0, 0x2f]));
        b.extend(v8(&[]));
    });
}

#[test]
fn extension_rules() {
    // Duplicates and pre_shared_key placement are illegal_parameter.
    assert_eq!(parse(&hello(&[ext(0xff01, &[0]), ext(0xff01, &[0])])).unwrap_err(), Alert::IllegalParameter);
    assert_eq!(parse(&hello(&[ext(43, &[2, 3, 4]), ext(43, &[2, 3, 4])])).unwrap_err(), Alert::IllegalParameter);
    assert_eq!(parse(&hello(&[psk(1, 1), ext(43, &[2, 3, 4])])).unwrap_err(), Alert::IllegalParameter);
    let b = hello(&[ext(43, &[2, 3, 4]), psk(2, 2)]);
    let h = parse(&b).unwrap();
    let (ids, binders) = h.pre_shared_key.unwrap();
    assert_eq!(ids.len(), 2 * (2 + 6 + 4));
    assert_eq!(binders.len(), 2 * 33);
    assert_eq!(binders.end, b.len());
    // Binder count must match; binders are at least 32 bytes.
    assert_eq!(parse(&hello(&[psk(2, 1)])).unwrap_err(), Alert::DecodeError);
    // A repeated extension is illegal_parameter even when its contents are
    // malformed: repeats are checked before contents.
    assert_eq!(parse(&hello(&[ext(43, &[3, 3, 4]), ext(43, &[3, 3, 4])])).unwrap_err(), Alert::IllegalParameter);
    // Unknown extensions are not interpreted.
    assert!(parse(&hello(&[ext(0x1234, &[1, 2, 3])])).is_ok());
    // early_data must be empty in a ClientHello.
    assert!(parse(&hello(&[ext(42, &[])])).unwrap().early_data);
    assert_eq!(parse(&hello(&[ext(42, &[0])])).unwrap_err(), Alert::DecodeError);
    // An extension running past the block.
    let mut b = hello(&[ext(0x1234, &[1, 2, 3])]);
    let n = b.len();
    b[n - 4] = 9;
    assert_eq!(parse(&b).unwrap_err(), Alert::DecodeError);
}

#[test]
fn server_name_rules() {
    let b = hello(&[sni(&[(0, b"example.com")])]);
    assert_eq!(parse(&b).unwrap().server_name.unwrap().of(&b), b"example.com");
    // Unknown name types are skipped.
    let b = hello(&[sni(&[(7, b"zz"), (0, b"a.b")])]);
    assert_eq!(parse(&b).unwrap().server_name.unwrap().of(&b), b"a.b");
    assert!(parse(&hello(&[sni(&[(7, b"zz")])])).unwrap().server_name.is_none());
    // Two host names, an empty one, an empty list.
    assert_eq!(parse(&hello(&[sni(&[(0, b"a"), (0, b"b")])])).unwrap_err(), Alert::DecodeError);
    assert_eq!(parse(&hello(&[sni(&[(0, b"")])])).unwrap_err(), Alert::DecodeError);
    assert_eq!(parse(&hello(&[sni(&[])])).unwrap_err(), Alert::DecodeError);
    // The list must be the whole extension.
    let mut e = sni(&[(0, b"a")]);
    e.push(0);
    let n = e.len() - 4;
    e[2..4].copy_from_slice(&(n as u16).to_be_bytes());
    assert_eq!(parse(&hello(&[e])).unwrap_err(), Alert::DecodeError);
}

#[test]
fn alpn_rules() {
    let b = hello(&[alpn_ext(&[b"h2", b"http/1.1"])]);
    let h = parse(&b).unwrap();
    assert_eq!(alpn(&b, h.alpn.unwrap()), vec![b"h2".to_vec(), b"http/1.1".to_vec()]);
    assert_eq!(parse(&hello(&[alpn_ext(&[b"h2", b""])])).unwrap_err(), Alert::DecodeError);
    assert_eq!(parse(&hello(&[alpn_ext(&[])])).unwrap_err(), Alert::DecodeError);
    // A name running past the list.
    assert_eq!(parse(&hello(&[ext(16, &v16(&[5, b'h', b'2']))])).unwrap_err(), Alert::DecodeError);
}

#[test]
fn key_share_rules() {
    let b = hello(&[key_share(&[0x11ec, 29, 23])]);
    assert_eq!(key_share_groups(&b, parse(&b).unwrap().key_shares.unwrap()), vec![0x11ec, 29, 23]);
    assert!(parse(&hello(&[key_share(&[])])).is_ok());
    assert_eq!(parse(&hello(&[key_share(&[29, 23, 29])])).unwrap_err(), Alert::IllegalParameter);
    assert_eq!(parse(&hello(&[key_share(&[0x11ec, 0x11ec])])).unwrap_err(), Alert::IllegalParameter);
    // An empty key_exchange.
    assert_eq!(parse(&hello(&[ext(51, &v16(&[0, 29, 0, 0]))])).unwrap_err(), Alert::DecodeError);
}

#[test]
fn many_extension_types() {
    // More than 16 types of 64 or more moves the duplicate check to its
    // bitmap; duplicates are still found, on either side of the move.
    let mut exts: Vec<Vec<u8>> = (0..40u16).map(|i| ext(0x1000 + 7 * i, &[])).collect();
    assert!(parse(&hello(&exts)).is_ok());
    exts.push(ext(0x1000 + 7 * 3, &[]));
    assert_eq!(parse(&hello(&exts)).unwrap_err(), Alert::IllegalParameter);
    exts.pop();
    exts.push(ext(0x1000 + 7 * 30, &[]));
    assert_eq!(parse(&hello(&exts)).unwrap_err(), Alert::IllegalParameter);
    let groups: Vec<u16> = (0..30u16).map(|i| 0x2000 + i).collect();
    assert!(parse(&hello(&[key_share(&groups)])).is_ok());
    let mut g = groups.clone();
    g.push(0x2000 + 20);
    assert_eq!(parse(&hello(&[key_share(&g)])).unwrap_err(), Alert::IllegalParameter);
}

/// A plain reference parser for the syntax, written separately from the
/// verified one, compared on mutations of the real ClientHellos.
fn reference_ok(b: &[u8]) -> bool {
    fn take<'a>(b: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
        if b.len() < n {
            return None;
        }
        let (x, y) = b.split_at(n);
        *b = y;
        Some(x)
    }
    fn vec<'a>(b: &mut &'a [u8], w: usize) -> Option<&'a [u8]> {
        let l = take(b, w)?;
        let n = l.iter().fold(0usize, |a, &x| a * 256 + x as usize);
        take(b, n)
    }
    fn go(mut b: &[u8]) -> Option<()> {
        take(&mut b, 34)?;
        if vec(&mut b, 1)?.len() > 32 {
            return None;
        }
        let cs = vec(&mut b, 2)?;
        if cs.len() < 2 || cs.len() % 2 == 1 {
            return None;
        }
        if vec(&mut b, 1)?.is_empty() {
            return None;
        }
        if b.is_empty() {
            return Some(());
        }
        let mut x = vec(&mut b, 2)?;
        if !b.is_empty() {
            return None;
        }
        let mut types = std::collections::HashSet::new();
        let mut last_psk = false;
        while !x.is_empty() {
            let t = take(&mut x, 2)?;
            let t = u16::from_be_bytes([t[0], t[1]]);
            let _ = vec(&mut x, 2)?;
            if last_psk || !types.insert(t) {
                return Some(()); // illegal, but syntactically fine
            }
            last_psk = t == 41;
        }
        Some(())
    }
    go(b).is_some()
}

#[test]
fn mutations_agree_with_reference() {
    let mut seed = 0x9e3779b97f4a7c15u64;
    let mut rnd = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for name in ["py-default-sni-alpn", "py-tls12-only", "ossl-alpn3", "ossl-p256-p384"] {
        let b = data(name);
        for _ in 0..20000 {
            let mut m = b.clone();
            for _ in 0..1 + rnd() % 3 {
                let i = (rnd() as usize) % m.len();
                m[i] = rnd() as u8;
            }
            let r = parse(&m);
            if !reference_ok(&m) {
                assert_eq!(r.unwrap_err(), Alert::DecodeError, "{name}");
            }
            if let Ok(h) = r {
                // Every span is inside the input.
                for s in [h.session_id, h.cipher_suites, h.compression_methods, h.extensions] {
                    assert!(s.start <= s.end && s.end <= m.len());
                }
            }
        }
    }
}
