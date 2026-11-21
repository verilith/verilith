// Quick survey: vx509's verdict on mbedTLS's x509parse_crt test vectors.
fn main() {
    let data = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    let lines: Vec<&str> = data.lines().collect();
    let (mut agree, mut strict, mut lax) = (0, 0, 0);
    for (i, l) in lines.iter().enumerate() {
        let Some(rest) = l.strip_prefix("x509parse_crt:\"").or(l.strip_prefix("x509parse_crt_cb:\"")) else { continue };
        let (hex, tail) = rest.split_once('"').unwrap();
        let expect = tail.rsplit(':').next().unwrap().trim_end_matches(';');
        let b: Vec<u8> = (0..hex.len() / 2).map(|j| u8::from_str_radix(&hex[2 * j..2 * j + 2], 16).unwrap()).collect();
        // mbedTLS takes the first TLV and ignores what follows.
        let first = verilith_x509::der::read_tlv(&b).map(|(_, r)| &b[..b.len() - r.len()]).unwrap_or(&b);
        let ok = verilith_x509::parse(first).is_some();
        let mb_ok = expect == "0";
        let title = lines[i.saturating_sub(1)];
        let title = if title.starts_with("depends_on") { lines[i - 2] } else { title };
        match (ok, mb_ok) {
            (a, b) if a == b => agree += 1,
            (false, true) => { strict += 1; println!("STRICT  {title} | {:?}", verilith_x509::try_parse(first).err()); }
            _ => { lax += 1; println!("LAX     {title} | expected {expect}"); }
        }
    }
    println!("agree {agree}, vx509 rejects where mbedTLS accepts {strict}, vx509 accepts where mbedTLS rejects {lax}");
}
