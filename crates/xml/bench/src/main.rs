//! Parse speed of verilith-xml against the Rust XML parsers, on every
//! `.xml` (and `.svg`, `.plist`, `.rss`, `.fodt`) file in the directories
//! given.
//!
//!   cargo run --release -- DIR...
//!
//! Each parser visits every event or node. Best of many timed runs per
//! file, in MB/s. Against expat and libxml2, the C parsers verilith-xml
//! replaces, use vbench (`bench/run.sh --only xml` at the repository root),
//! which builds them from pinned sources with the same flags and pairs the
//! samples.
use std::time::Instant;

fn best<F: FnMut() -> u64>(bytes: usize, mut f: F) -> f64 {
    let mut iters = 1u64;
    loop {
        let t = Instant::now();
        for _ in 0..iters {
            std::hint::black_box(f());
        }
        if t.elapsed().as_millis() > 20 {
            break;
        }
        iters *= 2;
    }
    let mut b = f64::MAX;
    for _ in 0..15 {
        let t = Instant::now();
        for _ in 0..iters {
            std::hint::black_box(f());
        }
        b = b.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    bytes as f64 / b / 1e6
}

fn quick(data: &[u8]) -> u64 {
    let mut r = quick_xml::Reader::from_reader(data);
    r.config_mut().check_end_names = true;
    let mut buf = Vec::new();
    let mut n = 0u64;
    loop {
        match r.read_event_into(&mut buf) {
            Ok(quick_xml::events::Event::Eof) => break,
            Ok(quick_xml::events::Event::Start(e)) | Ok(quick_xml::events::Event::Empty(e)) => {
                for a in e.attributes() {
                    n += a.unwrap().value.len() as u64;
                }
                n += 1;
            }
            Ok(_) => n += 1,
            Err(_) => return u64::MAX,
        }
        buf.clear();
    }
    n
}

fn walk(e: verilith_xml::Element, n: &mut u64) {
    *n += 1;
    for a in e.attrs() {
        *n += a.value.len() as u64;
    }
    for c in e.children() {
        match c {
            verilith_xml::Child::Element(c) => walk(c, n),
            verilith_xml::Child::Text(t) | verilith_xml::Child::CData(t) => *n += t.len() as u64,
            _ => {}
        }
    }
}

fn xmlrs(data: &[u8]) -> u64 {
    let mut n = 0u64;
    for e in xml::reader::EventReader::new(data) {
        if e.is_err() {
            return u64::MAX;
        }
        n += 1;
    }
    n
}

fn main() {
    let mut files = Vec::new();
    for d in std::env::args().skip(1) {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            let ext = p.extension().and_then(|x| x.to_str()).unwrap_or("");
            if ["xml", "svg", "plist", "rss", "fodt"].contains(&ext) {
                files.push(p);
            }
        }
    }
    files.sort();
    println!("{:<20} {:>6} {:>9} {:>9} {:>9} {:>9} {:>9}", "file", "KB", "vxml chk", "vxml read", "roxmltree", "quick-xml", "xml-rs");
    let mut tape = verilith_xml::tape::Tape::new();
    for p in files {
        let data = std::fs::read(&p).unwrap();
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        let ok = verilith_xml::check(&data, &mut tape);
        let rox_ok = std::str::from_utf8(&data).ok().map_or(false, |s| {
            roxmltree::Document::parse_with_options(s, roxmltree::ParsingOptions { allow_dtd: true, ..Default::default() }).is_ok()
        });
        let ours = best(data.len(), || {
            verilith_xml::check(&data, &mut tape) as u64
        });
        let read = best(data.len(), || {
            let mut n = 0;
            if let Ok(d) = verilith_xml::parse(&data) {
                walk(d.root(), &mut n);
            }
            n
        });
        let rox = if let Ok(s) = std::str::from_utf8(&data) {
            best(data.len(), || {
                roxmltree::Document::parse_with_options(s, roxmltree::ParsingOptions { allow_dtd: true, ..Default::default() })
                    .map(|d| d.descendants().count() as u64)
                    .unwrap_or(0)
            })
        } else {
            0.0
        };
        let q = best(data.len(), || quick(&data));
        let x = best(data.len(), || xmlrs(&data));
        println!(
            "{:<20} {:>6} {:>9.0} {:>9.0} {:>9.0} {:>9.0} {:>9.0} {}",
            name,
            data.len() / 1024,
            ours,
            read,
            rox,
            q,
            x,
            if ok == rox_ok { String::new() } else { format!("(vxml {} roxmltree {})", ok, rox_ok) }
        );
    }
}
