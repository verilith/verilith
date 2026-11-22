use std::hint::black_box;
use std::time::Instant;

// `x509bench ROW` runs only the row whose name is exactly ROW, so that each
// implementation can be timed in its own process. The mbedTLS rows are in
// mbedtls_bench.c, which links against one mbedTLS build at a time.
fn bench<F: FnMut() -> usize>(name: &str, cert: &str, mut f: F) {
    if let Some(only) = std::env::args().nth(1) {
        if only != name {
            return;
        }
    }
    for _ in 0..1000 {
        black_box(f());
    }
    let mut best = f64::MAX;
    for _ in 0..30 {
        let iters = 20000;
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    println!("{cert}\t{name}\t{:.0}", best * 1e9);
}

/// Touches every field vx509 exposes: names down to each attribute, both
/// times, the key, and every decoded extension down to each list entry.
fn vx509_visit(c: &verilith_x509::Certificate) -> usize {
    let mut n = c.serial().len() + c.tbs.spki.key.len();
    n += c.not_before().second as usize + c.not_after().second as usize;
    for r in c.issuer_rdns().chain(c.subject_rdns()) {
        n += r.attributes().map(|a| a.value.content.len()).sum::<usize>();
    }
    n += c.extensions().count();
    n += c.basic_constraints().map_or(0, |b| b.ca as usize);
    n += c.key_usage().unwrap_or(0) as usize;
    n += c.ext_key_usage().map_or(0, |i| i.count());
    n += c.subject_alt_names().map_or(0, |i| i.count());
    n += c.subject_key_id().map_or(0, |s| s.len());
    n += c.authority_key_id().map_or(0, |a| a.key_id.map_or(0, |k| k.len()));
    n += c.certificate_policies().map_or(0, |i| i.count());
    n
}

fn main() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/data");
    for cert in ["leaf", "root-rsa", "root-ecdsa"] {
        let b = std::fs::read(format!("{dir}/{cert}.der")).unwrap();
        let b = &b[..];

        bench("vx509 parse", cert, || verilith_x509::parse(b).unwrap().tbs.serial.len());
        bench("vx509 parse + visit every field", cert, || vx509_visit(&verilith_x509::parse(b).unwrap()));
        bench("x509-parser parse_x509_certificate", cert, || {
            let (_, c) = x509_parser::parse_x509_certificate(b).unwrap();
            c.tbs_certificate.serial.bits() as usize
        });
        bench("x509-cert Certificate::from_der", cert, || {
            use der::Decode;
            let c = x509_cert::Certificate::from_der(b).unwrap();
            c.tbs_certificate.serial_number.as_bytes().len()
        });
        bench("webpki EndEntityCert::try_from", cert, || {
            let d = rustls_pki_types::CertificateDer::from(b);
            webpki::EndEntityCert::try_from(&d).is_ok() as usize
        });
        bench("OpenSSL X509::from_der", cert, || openssl::x509::X509::from_der(b).unwrap().serial_number().to_bn().unwrap().num_bits() as usize);
    }
}
