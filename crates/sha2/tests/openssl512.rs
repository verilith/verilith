//! The SHA-384 and SHA-512 C API against OpenSSL's own (the system
//! libcrypto, `libcrypto.so.3` or `VSHA2_LIBCRYPTO`, loaded with dlopen).
use std::ffi::{c_char, c_int, c_void, CString};
use verilith_sha2::capi::*;

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type Init = unsafe extern "C" fn(*mut SHA512_CTX) -> c_int;
type Update = unsafe extern "C" fn(*mut SHA512_CTX, *const c_void, usize) -> c_int;
type Final = unsafe extern "C" fn(*mut u8, *mut SHA512_CTX) -> c_int;
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
    Some((api("SHA512", 64), api("SHA384", 48)))
}

unsafe fn streamed(api: &Api, data: &[u8], pieces: &[usize]) -> Vec<u8> {
    let mut c = std::mem::MaybeUninit::<SHA512_CTX>::uninit();
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
    let Some((o512, o384)) = (unsafe { libcrypto() }) else {
        eprintln!("no libcrypto: skipped");
        return;
    };
    let ours = (
        Api { init: sha512_init, update: sha512_update, fin: sha512_final, oneshot: sha512_oneshot, len: 64 },
        Api { init: sha384_init, update: sha384_update, fin: sha384_final, oneshot: sha384_oneshot, len: 48 },
    );
    let mut x = 0x1234_5678_9abc_def1u64;
    let data: Vec<u8> = (0..20_000)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 24) as u8
        })
        .collect();
    let splits: [&[usize]; 6] = [&[1], &[127], &[128], &[129], &[7, 250, 1, 128], &[1000, 3]];
    for (o, v) in [(&o512, &ours.0), (&o384, &ours.1)] {
        for n in (0..700).chain([8191, 8192, 8193, 20_000]) {
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
        let mut c = std::mem::MaybeUninit::<SHA512_CTX>::uninit();
        assert_eq!(sha512_init(c.as_mut_ptr()), 1);
        assert_eq!(sha512_update(c.as_mut_ptr(), std::ptr::null(), 0), 1);
        let mut md = [0u8; 64];
        assert_eq!(sha512_final(md.as_mut_ptr(), c.as_mut_ptr()), 1);
        assert_eq!(md, verilith_sha2::sha512(b""));
        let bytes = std::slice::from_raw_parts(c.as_ptr() as *const u8, std::mem::size_of::<SHA512_CTX>());
        assert!(bytes.iter().all(|&b| b == 0), "_Final wipes the context");
        let mut bad = std::mem::MaybeUninit::<SHA512_CTX>::new(std::mem::transmute::<[u8; 216], SHA512_CTX>([0xff; 216]));
        assert_eq!(sha512_update(bad.as_mut_ptr(), b"x".as_ptr() as *const c_void, 1), 0);
        let p = sha384_oneshot(b"abc".as_ptr(), 3, std::ptr::null_mut());
        assert_eq!(std::slice::from_raw_parts(p, 48), verilith_sha2::sha384(b"abc"));
        assert_eq!(std::mem::size_of::<SHA512_CTX>(), 216);
        assert_eq!(std::mem::align_of::<SHA512_CTX>(), 8);
    }
}
