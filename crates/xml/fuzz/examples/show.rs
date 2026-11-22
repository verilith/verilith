//! Both canonical forms of one file: show FILE
fn main() {
    let p = std::env::args().nth(1).unwrap();
    let d = std::fs::read(&p).unwrap();
    match verilith_xml::parse(&d) {
        Ok(doc) => println!("ours:  {}", String::from_utf8_lossy(&vxml_fuzz::ours(&doc))),
        Err(e) => println!("ours:  rejected: {e}"),
    }
    match vxml_fuzz::expat(&d) {
        Some(c) => println!("expat: {}", String::from_utf8_lossy(&c)),
        None => println!("expat: rejected: {}", vxml_fuzz::expat_reason(&d)),
    }
}
