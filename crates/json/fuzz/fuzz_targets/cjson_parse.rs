//! Parses the input with vjson's C ABI and with upstream cJSON. vjson must
//! accept only what cJSON accepts (it is stricter: RFC 8259), and the two
//! trees must print the same and compare equal. The printed text must parse
//! back to an equal tree, and a duplicate must compare equal.
#![no_main]
#![allow(unsafe_op_in_unsafe_fn)]
use libfuzzer_sys::fuzz_target;
use std::ffi::CStr;
use std::os::raw::c_char;

#[path = "api.rs"]
mod api;
use api::{cJSON, Lib, UPSTREAM, VJSON};

unsafe fn text(lib: &Lib, item: *const cJSON, fmt: bool) -> Vec<u8> {
    let p = if fmt { (lib.print)(item) } else { (lib.print_unformatted)(item) };
    assert!(!p.is_null());
    let s = CStr::from_ptr(p).to_bytes().to_vec();
    (lib.free)(p as *mut _);
    s
}

fuzz_target!(|data: &[u8]| unsafe {
    let v = (VJSON.parse_with_length)(data.as_ptr() as *const c_char, data.len());
    let u = (UPSTREAM.parse_with_length)(data.as_ptr() as *const c_char, data.len());
    if !v.is_null() {
        if u.is_null() {
            // cJSON skips a BOM only when more than 4 bytes follow from
            // the start (`can_access_at_index(buffer, 4)`).
            assert!(data.starts_with(b"\xEF\xBB\xBF") && data.len() <= 4, "vjson accepted what cJSON rejects");
            (VJSON.delete)(v);
            return;
        }
        // Real JSON (as vjson checks it) is UTF-8 up to the parsed end.
        assert!(verilith_json::parse_prefix(data).is_ok());
        for fmt in [false, true] {
            let a = text(&VJSON, v, fmt);
            assert_eq!(String::from_utf8_lossy(&a), String::from_utf8_lossy(&text(&UPSTREAM, u, fmt)));
            let mut z = a.clone();
            z.push(0);
            let back = (VJSON.parse)(z.as_ptr() as *const c_char);
            let up_back = (UPSTREAM.parse)(z.as_ptr() as *const c_char);
            // The printed text can be JSON vjson rejects only where cJSON
            // prints a number it cannot read back the same (inf as null).
            if !back.is_null() {
                assert_eq!((VJSON.compare)(back, v, 1), (UPSTREAM.compare)(up_back, u, 1), "reparse");
            }
            (VJSON.delete)(back);
            (UPSTREAM.delete)(up_back);
        }
        let d = (VJSON.duplicate)(v, 1);
        let e = (UPSTREAM.duplicate)(u, 1);
        assert_eq!((VJSON.compare)(d, v, 1), (UPSTREAM.compare)(e, u, 1), "duplicate");
        (VJSON.delete)(d);
        (UPSTREAM.delete)(e);
    }
    (VJSON.delete)(v);
    (UPSTREAM.delete)(u);
});
