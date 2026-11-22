//! Accept/reject and field-by-field comparison with x509-parser, x509-cert,
//! rustls-webpki and OpenSSL over a directory of DER certificates
//! (`VX509_CORPUS`, see corpus/README.md).
use std::collections::BTreeMap;

fn corpus() -> Vec<(String, Vec<u8>)> {
    let Ok(dir) = std::env::var("VX509_CORPUS") else { return vec![] };
    let mut v: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| {
        let p = e.unwrap().path();
        (p.file_name().unwrap().to_string_lossy().into_owned(), std::fs::read(&p).unwrap())
    }).collect();
    v.sort();
    v
}

fn openssl_ok(b: &[u8]) -> bool {
    openssl::x509::X509::from_der(b).map(|c| c.to_der().map(|d| d == b).unwrap_or(false)).unwrap_or(false)
}

#[test]
fn accept_reject() {
    let certs = corpus();
    if certs.is_empty() { eprintln!("VX509_CORPUS not set; skipping"); return; }
    let mut table: BTreeMap<(bool, bool, bool, bool, bool), Vec<&str>> = BTreeMap::new();
    for (name, b) in &certs {
        let v = verilith_x509::cert::parse(b).is_some();
        let xp = matches!(x509_parser::parse_x509_certificate(b), Ok((r, _)) if r.is_empty());
        let xc = <x509_cert::Certificate as der::Decode>::from_der(b).is_ok();
        let wp = webpki::EndEntityCert::try_from(&rustls_pki_types::CertificateDer::from(&b[..])).is_ok();
        let os = openssl_ok(b);
        table.entry((v, os, xp, xc, wp)).or_default().push(name);
    }
    println!("vx509 openssl x509-parser x509-cert webpki : count  examples");
    for (k, names) in &table {
        println!("{:5} {:7} {:11} {:9} {:6} : {:6} {:?}", k.0, k.1, k.2, k.3, k.4, names.len(), &names[..names.len().min(4)]);
    }
}

/// Every field vx509 decodes, against x509-parser and OpenSSL, on every
/// certificate all three accept.
#[test]
fn fields_agree() {
    use x509_parser::prelude::*;
    let certs = corpus();
    if certs.is_empty() { return; }
    let mut compared = 0;
    let mut bad: Vec<String> = vec![];
    for (name, b) in &certs {
        let Some(v) = verilith_x509::parse(b) else { continue };
        let Ok((_, x)) = parse_x509_certificate(b) else { continue };
        let Ok(o) = openssl::x509::X509::from_der(b) else { continue };
        compared += 1;
        let mut d = |what: &str, ok: bool| if !ok { bad.push(format!("{name}: {what}")) };
        d("version", v.version() as u32 == x.version().0);
        d("serial", v.serial() == x.raw_serial());
        d("serial/openssl", o.serial_number().to_bn().unwrap().to_vec() == {
            let s = v.serial(); let s = if s.len() > 1 && s[0] == 0 { &s[1..] } else { s };
            if s == [0] { vec![] } else { s.to_vec() }
        } || v.serial()[0] >= 0x80);
        d("tbs", v.tbs_der == x.tbs_certificate.as_ref());
        d("sigalg", v.tbs.signature.oid == x.signature_algorithm.algorithm.as_bytes());
        d("issuer", x.issuer().as_raw().ends_with(v.issuer().raw) && x.issuer().as_raw().len() - v.issuer().raw.len() <= 4);
        d("issuer/openssl", o.issuer_name().to_der().unwrap().ends_with(v.issuer().raw));
        d("subject", x.subject().as_raw().ends_with(v.subject().raw));
        d("subject/openssl", o.subject_name().to_der().unwrap().ends_with(v.subject().raw));
        d("issuer attrs", v.issuer().attributes().count() == x.issuer().iter_attributes().count());
        d("subject attrs", v.subject().attributes().count() == x.subject().iter_attributes().count());
        d("not_before", v.not_before().unix_timestamp() == x.validity().not_before.timestamp());
        d("not_after", v.not_after().unix_timestamp() == x.validity().not_after.timestamp());
        d("spki", v.tbs.spki_der == x.public_key().raw);
        d("spki/openssl", o.public_key().map(|k| k.public_key_to_der().unwrap() == v.tbs.spki_der).unwrap_or(true));
        d("key", v.tbs.spki.key == &x.public_key().subject_public_key.data[..]);
        d("signature", v.signature == &x.signature_value.data[..]);
        d("signature/openssl", o.signature().as_slice() == v.signature);
        let ve: Vec<_> = v.extensions().map(|e| (e.oid.to_vec(), e.critical, e.value.to_vec())).collect();
        let xe: Vec<_> = x.extensions().iter().map(|e| (e.oid.as_bytes().to_vec(), e.critical, e.value.to_vec())).collect();
        d("extensions", ve == xe);
        if let Ok(bc) = x.basic_constraints() {
            let vb = v.basic_constraints();
            d("basic constraints", vb.map(|b| (b.ca, b.path_len)) == bc.map(|b| (b.value.ca, b.value.path_len_constraint.map(|p| p as u64))));
        }
        if let Ok(ku) = x.key_usage() {
            d("key usage", v.key_usage() == ku.map(|k| k.value.flags));
        }
        if let Ok(san) = x.subject_alternative_name() {
            let xs: Vec<String> = san.map(|s| s.value.general_names.iter().map(|g| match g {
                x509_parser::extensions::GeneralName::DNSName(d) => format!("dns:{d}"),
                x509_parser::extensions::GeneralName::RFC822Name(d) => format!("email:{d}"),
                x509_parser::extensions::GeneralName::URI(d) => format!("uri:{d}"),
                x509_parser::extensions::GeneralName::IPAddress(d) => format!("ip:{d:?}"),
                _ => "other".into(),
            }).collect()).unwrap_or_default();
            let vs: Vec<String> = v.subject_alt_names().into_iter().flatten().map(|g| match g {
                verilith_x509::GeneralName::Dns(d) => format!("dns:{}", String::from_utf8_lossy(d)),
                verilith_x509::GeneralName::Rfc822(d) => format!("email:{}", String::from_utf8_lossy(d)),
                verilith_x509::GeneralName::Uri(d) => format!("uri:{}", String::from_utf8_lossy(d)),
                verilith_x509::GeneralName::Ip(d) => format!("ip:{d:?}"),
                _ => "other".into(),
            }).collect();
            d("subject alt names", vs == xs);
            let od: Vec<String> = o.subject_alt_names().map(|s| s.iter().filter_map(|g| g.dnsname().map(|d| d.to_string())).collect()).unwrap_or_default();
            let vd: Vec<String> = v.dns_names().map(|d| String::from_utf8_lossy(d).into_owned()).collect();
            d("dns names/openssl", od == vd);
        }
        if let (Ok(Some(e)), Some(ve)) = (x.extended_key_usage(), v.ext_key_usage()) {
            let n = { let e = &e.value; e.any as usize + e.server_auth as usize + e.client_auth as usize + e.code_signing as usize + e.email_protection as usize + e.time_stamping as usize + e.ocsp_signing as usize + e.other.len() };
            d("eku count", ve.count() == n);
        }
    }
    println!("{compared} certificates compared, {} disagreements", bad.len());
    for b in bad.iter().take(30) { println!("  {b}"); }
    assert!(bad.is_empty());
}
