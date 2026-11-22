//! Parses a URL, then applies a sequence of setters with arbitrary values,
//! reading every component after each one.
//!
//! The setters are proven to leave the record the Standard's setters leave
//! (`set.rs`), and that record's href need not be a fixed point of the
//! parser: setting the protocol of "https://h/C|/" to "file" gives
//! "file://h/C|/", which parses as "file://h/C:/". So this target checks
//! that the result reads back without a panic, not that it reparses to
//! itself.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_url::Url;

fuzz_target!(|data: &[u8]| {
    let mut parts = data.split(|&c| c == 0);
    let Some(first) = parts.next() else { return };
    let Some(mut u) = Url::parse(&String::from_utf8_lossy(first), None) else { return };
    for p in parts {
        let Some((&op, v)) = p.split_first() else { continue };
        let v = String::from_utf8_lossy(v);
        match op % 10 {
            0 => drop(u.set_href(&v)),
            1 => drop(u.set_protocol(&v)),
            2 => drop(u.set_username(&v)),
            3 => drop(u.set_password(&v)),
            4 => drop(u.set_host(&v)),
            5 => {
                // The host-only shortcut agrees with the setter.
                let mut h = Vec::new();
                let short = u.hostname_host(&v, &mut h);
                let ok = u.set_hostname(&v);
                match short {
                    None => {}
                    Some(None) => assert!(!ok),
                    Some(Some(_)) => assert!(ok && u.hostname().as_bytes() == h.as_slice()),
                }
            }
            6 => drop(u.set_port(&v)),
            7 => drop(u.set_pathname(&v)),
            8 => u.set_search(&v),
            _ => u.set_hash(&v),
        }
        for s in [u.href(), u.protocol(), u.username(), u.password(), u.host(), u.hostname(), u.pathname(), u.search(), u.hash()] {
            assert!(s.is_ascii());
        }
        let _ = (u.port(), u.origin(), Url::parse(u.href(), None));
    }
});
