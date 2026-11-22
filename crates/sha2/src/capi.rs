//! OpenSSL's SHA-224 and SHA-256 C API (`openssl/sha.h`), as an unverified
//! adapter over the proven hashers. It turns C pointers into slices and
//! stores a hasher in the caller's `SHA256_CTX`; every digest comes from
//! [`Sha256::finalize`] or [`Sha224::finalize`].
//!
//! Symbols are exported as `vsha2_SHA256_Init` and so on, or under
//! OpenSSL's own names with the `openssl-abi` feature, so that the static
//! library can be linked in libcrypto's place for these functions.
//!
//! `SHA256_CTX` is caller-allocated, so its size is part of the ABI:
//! OpenSSL's is 112 bytes, aligned to 4, and callers keep it on the stack.
//! The hasher is stored in those 112 bytes (copied in and out, since it is
//! aligned to 8), so its fields are not OpenSSL's: code that reads `h`,
//! `Nl` or `num` directly gets other values.
use crate::hash::{Sha224, Sha256};
use core::ffi::{c_int, c_uchar, c_void};

/// OpenSSL's `SHA256_CTX`, as storage: the same size and alignment.
#[repr(C, align(4))]
pub struct SHA256_CTX {
    _opaque: [u8; 112],
}

const _: () = assert!(core::mem::size_of::<Sha256>() <= core::mem::size_of::<SHA256_CTX>());
const _: () = assert!(core::mem::size_of::<Sha224>() <= core::mem::size_of::<SHA256_CTX>());

macro_rules! export {
    ($vs:literal, $ossl:literal, fn $name:ident($($a:ident: $t:ty),* $(,)?) -> $r:ty $body:block) => {
        #[cfg_attr(feature = "openssl-abi", export_name = $ossl)]
        #[cfg_attr(not(feature = "openssl-abi"), export_name = $vs)]
        /// # Safety
        /// As the OpenSSL function of the same name: pointers must be valid
        /// for the sizes given with them, and a context must have been set
        /// up by the matching `_Init`.
        pub unsafe extern "C" fn $name($($a: $t),*) -> $r $body
    };
}

unsafe fn input<'a>(p: *const c_void, n: usize) -> &'a [u8] {
    if n == 0 || p.is_null() {
        &[]
    } else {
        // SAFETY: the caller gives `n` readable bytes at `p`.
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

unsafe fn load<T: Copy>(c: *const SHA256_CTX) -> T {
    // SAFETY: the context holds a `T` written by `store` (see `_Init`).
    core::ptr::read_unaligned(c as *const T)
}

unsafe fn store<T>(c: *mut SHA256_CTX, v: T) {
    // SAFETY: `T` fits in the context (the assertions above).
    core::ptr::write_unaligned(c as *mut T, v)
}

unsafe fn wipe(c: *mut SHA256_CTX) {
    // As OpenSSL's `_Final`, which cleanses the context.
    core::ptr::write_volatile(c, SHA256_CTX { _opaque: [0; 112] });
}

export!("vsha2_SHA256_Init", "SHA256_Init", fn sha256_init(c: *mut SHA256_CTX) -> c_int {
    if c.is_null() {
        return 0;
    }
    store(c, Sha256::new());
    1
});

export!("vsha2_SHA256_Update", "SHA256_Update", fn sha256_update(c: *mut SHA256_CTX, data: *const c_void, len: usize) -> c_int {
    if c.is_null() {
        return 0;
    }
    let mut h: Sha256 = load(c);
    if !h.plausible() {
        return 0;
    }
    h.update(input(data, len));
    store(c, h);
    1
});

export!("vsha2_SHA256_Final", "SHA256_Final", fn sha256_final(md: *mut c_uchar, c: *mut SHA256_CTX) -> c_int {
    if c.is_null() || md.is_null() {
        return 0;
    }
    let h: Sha256 = load(c);
    if !h.plausible() {
        return 0;
    }
    let d = h.finalize();
    // SAFETY: the caller gives 32 writable bytes at `md`.
    core::ptr::copy_nonoverlapping(d.as_ptr(), md, 32);
    wipe(c);
    1
});

export!("vsha2_SHA224_Init", "SHA224_Init", fn sha224_init(c: *mut SHA256_CTX) -> c_int {
    if c.is_null() {
        return 0;
    }
    store(c, Sha224::new());
    1
});

export!("vsha2_SHA224_Update", "SHA224_Update", fn sha224_update(c: *mut SHA256_CTX, data: *const c_void, len: usize) -> c_int {
    if c.is_null() {
        return 0;
    }
    let mut h: Sha224 = load(c);
    if !h.plausible() {
        return 0;
    }
    h.update(input(data, len));
    store(c, h);
    1
});

export!("vsha2_SHA224_Final", "SHA224_Final", fn sha224_final(md: *mut c_uchar, c: *mut SHA256_CTX) -> c_int {
    if c.is_null() || md.is_null() {
        return 0;
    }
    let h: Sha224 = load(c);
    if !h.plausible() {
        return 0;
    }
    let d = h.finalize();
    // SAFETY: the caller gives 28 writable bytes at `md`.
    core::ptr::copy_nonoverlapping(d.as_ptr(), md, 28);
    wipe(c);
    1
});

/// Where the one-shot functions write when `md` is NULL. OpenSSL does the
/// same, and documents that it is not thread safe.
static mut STATIC_MD: [u8; 32] = [0; 32];

export!("vsha2_SHA256", "SHA256", fn sha256_oneshot(d: *const c_uchar, n: usize, md: *mut c_uchar) -> *mut c_uchar {
    let out = if md.is_null() { core::ptr::addr_of_mut!(STATIC_MD) as *mut u8 } else { md };
    let r = crate::hash::sha256(input(d as *const c_void, n));
    // SAFETY: `out` has 32 writable bytes (the caller's, or the static).
    core::ptr::copy_nonoverlapping(r.as_ptr(), out, 32);
    out
});

export!("vsha2_SHA224", "SHA224", fn sha224_oneshot(d: *const c_uchar, n: usize, md: *mut c_uchar) -> *mut c_uchar {
    let out = if md.is_null() { core::ptr::addr_of_mut!(STATIC_MD) as *mut u8 } else { md };
    let r = crate::hash::sha224(input(d as *const c_void, n));
    // SAFETY: `out` has at least 28 writable bytes.
    core::ptr::copy_nonoverlapping(r.as_ptr(), out, 28);
    out
});
