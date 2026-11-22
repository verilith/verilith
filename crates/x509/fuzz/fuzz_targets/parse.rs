//! The verified parser, every accessor and iterator, and `try_parse`'s
//! agreement with it.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::fmt::Write;

fuzz_target!(|b: &[u8]| {
    let c = match verilith_x509::try_parse(b) {
        Ok(c) => c,
        Err(e) => {
            assert!(verilith_x509::parse(b).is_none());
            assert!(e.offset <= b.len());
            return;
        }
    };
    let mut s = String::new();
    for a in c.issuer().attributes().chain(c.subject().attributes()) {
        let _ = write!(s, "{}={:?}", verilith_x509::OidDisplay(a.oid), a.value_str());
    }
    let _ = (c.not_before().unix_timestamp(), c.not_after().unix_timestamp());
    for e in c.extensions() {
        let _ = write!(s, "{}", verilith_x509::OidDisplay(e.oid));
        assert_eq!(c.extension(e.oid).map(|x| x.value), Some(e.value));
    }
    let _ = (c.basic_constraints(), c.key_usage(), c.subject_key_id());
    let _ = write!(s, "{:?}", c.authority_key_id().map(|a| a.key_id));
    for l in [c.subject_alt_names(), c.issuer_alt_names()].into_iter().flatten() {
        for g in l {
            let _ = write!(s, "{g:?}");
        }
    }
    let _ = c.ext_key_usage().map(|i| i.count());
    let _ = c.certificate_policies().map(|i| i.count());
    if let Some(nc) = c.name_constraints() {
        let _ = write!(s, "{:?}", nc.permitted.is_some());
    }
});
