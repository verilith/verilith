//! The C API against OpenSSL's own SHA-224 and SHA-256 (the system
//! libcrypto, `libcrypto.so.3` or `VSHA2_LIBCRYPTO`, loaded with dlopen).
use std::ffi::{c_char, c_int, c_void, CString};
use verilith_sha2::capi::*;

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type Init = unsafe extern "C" fn(*mut SHA256_CTX) -> c_int;
type Update = unsafe extern "C" fn(*mut SHA256_CTX, *const c_void, usize) -> c_int;
type Final = unsafe extern "C" fn(*mut u8, *mut SHA256_CTX) -> c_int;
type OneShot = unsafe extern "C" fn(*const u8, usize, *mut u8) -> *mut u8;

struct Api {
    init: Init,
    update: Update,
    fin: Final,
    oneshot: OneShot,
    len: usize,
}

unsafe fn libcrypto() -> Option<(Api, Api)> {
    let mut names: Vec<String> = std::env::var("VSHA2_LIBCRYPTO").into_iter().collect();
    names.extend(["libcrypto.so.3", "libcrypto.3.dylib", "/opt/homebrew/lib/libcrypto.3.dylib"].map(String::from));
    let h = names.iter().map(|n| dlopen(CString::new(n.as_str()).unwrap().as_ptr(), 2)).find(|h| !h.is_null())?;
    let sym = |n: &str| {
        let p = dlsym(h, CString::new(n).unwrap().as_ptr());
        assert!(!p.is_null(), "{n}");
        p
    };
    let api = |p: &str, len| Api {
        init: std::mem::transmute::<*mut c_void, Init>(sym(&format!("{p}_Init"))),
        update: std::mem::transmute::<*mut c_void, Update>(sym(&format!("{p}_Update"))),
        fin: std::mem::transmute::<*mut c_void, Final>(sym(&format!("{p}_Final"))),
        oneshot: std::mem::transmute::<*mut c_void, OneShot>(sym(p)),
        len,
    };
    Some((api("SHA256", 32), api("SHA224", 28)))
}

fn ours() -> (Api, Api) {
    (
        Api { init: sha256_init, update: sha256_update, fin: sha256_final, oneshot: sha256_oneshot, len: 32 },
        Api { init: sha224_init, update: sha224_update, fin: sha224_final, oneshot: sha224_oneshot, len: 28 },
    )
}

/// Hashes `data` in pieces of the given sizes, through `api`.
unsafe fn streamed(api: &Api, data: &[u8], pieces: &[usize]) -> Vec<u8> {
    let mut c = std::mem::MaybeUninit::<SHA256_CTX>::uninit();
    assert_eq!((api.init)(c.as_mut_ptr()), 1);
    let mut i = 0;
    for &k in pieces.iter().cycle() {
        if i >= data.len() {
            break;
        }
        let k = k.min(data.len() - i);
        assert_eq!((api.update)(c.as_mut_ptr(), data[i..].as_ptr() as *const c_void, k), 1);
        i += k;
    }
    let mut md = vec![0u8; api.len];
    assert_eq!((api.fin)(md.as_mut_ptr(), c.as_mut_ptr()), 1);
    md
}

unsafe fn oneshot(api: &Api, data: &[u8]) -> Vec<u8> {
    let mut md = vec![0u8; api.len];
    assert_eq!((api.oneshot)(data.as_ptr(), data.len(), md.as_mut_ptr()), md.as_mut_ptr());
    md
}

#[test]
fn against_libcrypto() {
    let Some((o256, o224)) = (unsafe { libcrypto() }) else {
        eprintln!("no libcrypto: skipped");
        return;
    };
    let (v256, v224) = ours();
    let mut x = 0x1234_5678_9abc_def1u64;
    let data: Vec<u8> = (0..20_000)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 24) as u8
        })
        .collect();
    let splits: [&[usize]; 6] = [&[1], &[63], &[64], &[65], &[7, 120, 1, 64], &[1000, 3]];
    for (o, v) in [(&o256, &v256), (&o224, &v224)] {
        for n in (0..600).chain([4095, 4096, 4097, 20_000]) {
            let d = &data[..n];
            let want = unsafe { oneshot(o, d) };
            assert_eq!(unsafe { oneshot(v, d) }, want, "one-shot len {n}");
            for s in splits {
                assert_eq!(unsafe { streamed(v, d, s) }, want, "len {n} pieces {s:?}");
            }
        }
    }
}

#[test]
fn c_api_edges() {
    unsafe {
        // A null pointer with length 0 is the empty message.
        let mut c = std::mem::MaybeUninit::<SHA256_CTX>::uninit();
        assert_eq!(sha256_init(c.as_mut_ptr()), 1);
        assert_eq!(sha256_update(c.as_mut_ptr(), std::ptr::null(), 0), 1);
        let mut md = [0u8; 32];
        assert_eq!(sha256_final(md.as_mut_ptr(), c.as_mut_ptr()), 1);
        assert_eq!(md, verilith_sha2::sha256(b""));
        // `_Final` wipes the context, as OpenSSL's does.
        let bytes = std::slice::from_raw_parts(c.as_ptr() as *const u8, std::mem::size_of::<SHA256_CTX>());
        assert!(bytes.iter().all(|&b| b == 0));
        // A context whose buffer count is out of range is refused.
        let mut bad = std::mem::MaybeUninit::<SHA256_CTX>::new(std::mem::transmute::<[u8; 112], SHA256_CTX>([0xff; 112]));
        assert_eq!(sha256_update(bad.as_mut_ptr(), b"x".as_ptr() as *const c_void, 1), 0);
        assert_eq!(sha256_final(md.as_mut_ptr(), bad.as_mut_ptr()), 0);
        // NULL md: the static buffer, as OpenSSL.
        let p = sha256_oneshot(b"abc".as_ptr(), 3, std::ptr::null_mut());
        assert_eq!(std::slice::from_raw_parts(p, 32), verilith_sha2::sha256(b"abc"));
    }
}
