//! X.509, vx509 side of the native comparison with Verdict
//! (runners/verdict-run): parse each certificate held in memory with
//! verilith_x509::parse, which checks the whole certificate, and drop it.
//!
//!   parse/NAME     NAME.der
//!   parse/roots    every root in roots/ (Mozilla's bundle, via certifi)
//!
//! `vx509-run read` is the native side of the comparison with mbedTLS
//! (suites/x509/x509.c read), cases read/NAME and read/roots: parse, then
//! read what a TLS client reads (serial, every issuer and subject
//! attribute, both validity times, key usage, the CA flag, the DNS
//! subjectAltNames and the extended key usages).
//! check = certificates * 1000003 + a sum over everything read, the same
//! sum the mbedTLS driver computes from `mbedtls_x509_crt`.
//!
//! Certificates the parser rejects are skipped and reported, so the check
//! (certificates parsed * 1000 + their total length) differs between the
//! two sides when one rejects what the other accepts.

fn parse(d: &[u8]) -> bool {
    std::hint::black_box(verilith_x509::parse(d)).is_some()
}

fn read(d: &[u8]) -> Option<u64> {
    let c = verilith_x509::parse(d)?;
    let mut s = c.serial().len() as u64;
    for a in c.issuer().attributes().chain(c.subject().attributes()) {
        s += a.value.content.len() as u64;
    }
    let (nb, na) = (c.not_before(), c.not_after());
    s += nb.year as u64 + nb.second as u64 + na.year as u64 + na.second as u64;
    s += c.key_usage().map_or(0, |k| k.count_ones() as u64);
    s += c.basic_constraints().map_or(0, |b| b.ca as u64);
    if let Some(names) = c.subject_alt_names() {
        s += names.filter(|n| matches!(n, verilith_x509::GeneralName::Dns(_))).count() as u64;
    }
    s += c.ext_key_usage().map_or(0, |i| i.count() as u64);
    Some(s)
}

fn read_case(r: &mut vbrun::Runner, name: String, certs: Vec<Vec<u8>>) {
    let total: u64 = certs.iter().map(|c| c.len() as u64).sum();
    r.case(name, total, move || {
        let (mut k, mut s) = (0u64, 0u64);
        for c in &certs {
            match read(std::hint::black_box(c)) {
                Some(x) => s += x,
                None => std::process::abort(),
            }
            k += 1;
        }
        k * 1000003 + s
    });
}

fn load(dir: &str, names: &[String]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for n in names {
        let d = std::fs::read(format!("{dir}/{n}")).unwrap();
        if parse(&d) {
            out.push(d);
        } else {
            eprintln!("skipping {n}: rejected");
        }
    }
    out
}

fn case(r: &mut vbrun::Runner, name: String, certs: Vec<Vec<u8>>) {
    let total: u64 = certs.iter().map(|c| c.len() as u64).sum();
    r.case(name, total, move || {
        let mut k = 0u64;
        for c in &certs {
            if !parse(std::hint::black_box(c)) {
                std::process::abort();
            }
            k += 1;
        }
        k * 1000 + total
    });
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "parse".into());
    let case = if mode == "read" { read_case } else { case };
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".der") else { continue };
        let certs = load(&dir, &[name.clone()]);
        if !certs.is_empty() {
            case(&mut r, format!("{mode}/{stem}"), certs);
        }
    }
    let rdir = format!("{dir}/roots");
    let roots = load(&rdir, &vbrun::list_dir(&rdir));
    case(&mut r, format!("{mode}/roots"), roots);
    r.main();
}
