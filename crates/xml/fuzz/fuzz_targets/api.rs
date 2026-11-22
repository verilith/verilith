//! Every reading of an accepted document: no panic, and reading twice
//! gives the same.
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(doc) = verilith_xml::parse(data) {
        let a = vxml_fuzz::ours(&doc);
        assert_eq!(a, vxml_fuzz::ours(&doc));
        let _ = doc.notations();
        let _ = doc.doctype_name();
        for e in doc.root().elements() {
            let _ = e.try_attributes();
            let _ = e.text();
        }
    }
});
