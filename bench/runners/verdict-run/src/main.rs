//! X.509, Verdict side of the native comparison with vx509
//! (runners/vx509-run): parse each certificate held in memory with
//! verdict_parser::parse_x509_der, which checks the whole certificate, and drop it.
//!
//!   parse/NAME     NAME.der
//!   parse/roots    every root in roots/ (Mozilla's bundle, via certifi)
//!
//! Certificates the parser rejects are skipped and reported, so the check
//! (certificates parsed * 1000 + their total length) differs between the
//! two sides when one rejects what the other accepts.

fn parse(d: &[u8]) -> bool {
    std::hint::black_box(verdict_parser::parse_x509_der(d)).is_ok()
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
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".der") else { continue };
        let certs = load(&dir, &[name.clone()]);
        if !certs.is_empty() {
            case(&mut r, format!("parse/{stem}"), certs);
        }
    }
    let rdir = format!("{dir}/roots");
    let roots = load(&rdir, &vbrun::list_dir(&rdir));
    case(&mut r, "parse/roots".into(), roots);
    r.main();
}
