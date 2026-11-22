//! `ares_expand_name` (the C ABI adapter) at every offset of the input.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_char, c_long};
use verilith_dns::capi::vdns_expand_name;

extern "C" {
    fn ares_free_string(s: *mut std::os::raw::c_void);
}

fuzz_target!(|b: &[u8]| {
    for i in 0..b.len() {
        let mut s: *mut c_char = std::ptr::null_mut();
        let mut len: c_long = 0;
        let rc = unsafe { vdns_expand_name(b.as_ptr().add(i), b.as_ptr(), b.len() as i32, &mut s, &mut len) };
        if rc == 0 {
            assert!(!s.is_null() && len > 0 && (i + len as usize) <= b.len());
            unsafe {
                let _ = std::ffi::CStr::from_ptr(s).to_bytes().len();
                ares_free_string(s as *mut _);
            }
        } else {
            assert!(s.is_null());
        }
    }
});
