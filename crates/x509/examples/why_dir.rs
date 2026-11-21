fn main() {
    let dir = std::env::args().nth(1).unwrap();
    let mut v: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    for p in v {
        let b = std::fs::read(&p).unwrap();
        if let Err(e) = verilith_x509::try_parse(&b) {
            if openssl::x509::X509::from_der(&b).is_ok() { println!("{:?} {}", e.kind, p.file_name().unwrap().to_string_lossy()); }
        }
    }
}
