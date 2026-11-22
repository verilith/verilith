//! mbedTLS with the vx509 patch, under AddressSanitizer: parse, print every
//! field with mbedtls_x509_crt_info, free. mbedTLS must never accept a
//! certificate the verified parser rejects.
#![no_main]
use libfuzzer_sys::fuzz_target;
use std::os::raw::{c_char, c_int};

// Larger than mbedtls_x509_crt in any configuration.
#[repr(C, align(16))]
struct Crt([u8; 4096]);

unsafe extern "C" {
    fn mbedtls_x509_crt_init(crt: *mut Crt);
    fn mbedtls_x509_crt_free(crt: *mut Crt);
    fn mbedtls_x509_crt_parse_der(crt: *mut Crt, buf: *const u8, len: usize) -> c_int;
    fn mbedtls_x509_crt_parse_der_nocopy(crt: *mut Crt, buf: *const u8, len: usize) -> c_int;
    fn mbedtls_x509_crt_info(buf: *mut c_char, size: usize, prefix: *const c_char, crt: *const Crt) -> c_int;
}

fuzz_target!(|b: &[u8]| {
    // mbedTLS reads the first TLV and ignores what follows.
    let first = verilith_x509::der::read_tlv(b).map(|(_, r)| &b[..b.len() - r.len()]).unwrap_or(b);
    let verified = verilith_x509::parse(first).is_some();
    for copy in [true, false] {
        // An exact-size heap copy, so ASan sees any read past the end.
        let input = b.to_vec().into_boxed_slice();
        let mut crt = Box::new(Crt([0; 4096]));
        unsafe {
            mbedtls_x509_crt_init(&mut *crt);
            let r = if copy {
                mbedtls_x509_crt_parse_der(&mut *crt, input.as_ptr(), input.len())
            } else {
                mbedtls_x509_crt_parse_der_nocopy(&mut *crt, input.as_ptr(), input.len())
            };
            assert!(r != 0 || verified, "mbedTLS accepted what vx509 rejects");
            if r == 0 {
                let mut out = vec![0 as c_char; 8192];
                mbedtls_x509_crt_info(out.as_mut_ptr(), out.len(), c"".as_ptr(), &*crt);
            }
            mbedtls_x509_crt_free(&mut *crt);
        }
    }
});
