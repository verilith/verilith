//! verilith-xml against libexpat: the same verdict, and when both accept,
//! the same canonical form.
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Some(d) = vxml_fuzz::unexplained(data) {
        panic!("{d:?} on {:?}", String::from_utf8_lossy(data));
    }
});
