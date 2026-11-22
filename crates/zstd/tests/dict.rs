//! Dictionaries, against the system's libzstd (loaded with `dlopen`):
//! dictionaries trained by libzstd's `ZDICT_trainFromBuffer` and raw-content
//! prefixes, frames compressed with them by libzstd, decoded by the proven
//! decoder and through every C entry point that takes a dictionary, and
//! compared with libzstd's own decoder, valid and corrupted.
#![allow(unsafe_op_in_unsafe_fn)]
use std::ffi::{c_char, c_int, c_uint, c_void, CString};
use verilith_zstd::capi::{self, DCtx, DDictH, InBuffer, OutBuffer};
use verilith_zstd::dict::{DictDecoder, DICT_LIMIT};
use verilith_zstd::frame::Error;

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type Train = unsafe extern "C" fn(*mut u8, usize, *const u8, *const usize, c_uint) -> usize;
type CompressDict = unsafe extern "C" fn(*mut c_void, *mut u8, usize, *const u8, usize, *const u8, usize, c_int) -> usize;
type Compress2 = unsafe extern "C" fn(*mut c_void, *mut u8, usize, *const u8, usize) -> usize;
type SetParam = unsafe extern "C" fn(*mut c_void, c_int, c_int) -> usize;
type RefPrefix = unsafe extern "C" fn(*mut c_void, *const u8, usize) -> usize;
type Reset = unsafe extern "C" fn(*mut c_void, c_int) -> usize;
type DecompressDict = unsafe extern "C" fn(*mut c_void, *mut u8, usize, *const u8, usize, *const u8, usize) -> usize;
type DecompressDCtx = unsafe extern "C" fn(*mut c_void, *mut u8, usize, *const u8, usize) -> usize;
type Bound = unsafe extern "C" fn(usize) -> usize;
type IsError = unsafe extern "C" fn(usize) -> c_uint;
type ErrorCode = unsafe extern "C" fn(usize) -> c_int;
type Create = unsafe extern "C" fn() -> *mut c_void;

struct Lib {
    train: Train,
    compress_dict: CompressDict,
    compress2: Compress2,
    set_param: SetParam,
    cref_prefix: RefPrefix,
    creset: Reset,
    decompress_dict: DecompressDict,
    dref_prefix: RefPrefix,
    decompress_dctx: DecompressDCtx,
    bound: Bound,
    is_error: IsError,
    error_code: ErrorCode,
    cctx: *mut c_void,
    dctx: *mut c_void,
}

fn lib() -> Option<Lib> {
    unsafe {
        let mut h = std::ptr::null_mut();
        let mut names: Vec<String> = std::env::var("VZSTD_LIBZSTD").into_iter().collect();
        names.extend(["libzstd.so.1", "libzstd.1.dylib", "/opt/homebrew/lib/libzstd.1.dylib", "/usr/local/lib/libzstd.1.dylib"].iter().map(|s| s.to_string()));
        for n in names {
            h = dlopen(CString::new(n).unwrap().as_ptr(), 2);
            if !h.is_null() {
                break;
            }
        }
        if h.is_null() {
            eprintln!("libzstd.so.1 not found: skipping");
            return None;
        }
        let sym = |n: &str| {
            let p = dlsym(h, CString::new(n).unwrap().as_ptr());
            assert!(!p.is_null(), "{n}");
            p
        };
        let cc: Create = std::mem::transmute(sym("ZSTD_createCCtx"));
        let dc: Create = std::mem::transmute(sym("ZSTD_createDCtx"));
        Some(Lib {
            train: std::mem::transmute(sym("ZDICT_trainFromBuffer")),
            compress_dict: std::mem::transmute(sym("ZSTD_compress_usingDict")),
            compress2: std::mem::transmute(sym("ZSTD_compress2")),
            set_param: std::mem::transmute(sym("ZSTD_CCtx_setParameter")),
            cref_prefix: std::mem::transmute(sym("ZSTD_CCtx_refPrefix")),
            creset: std::mem::transmute(sym("ZSTD_CCtx_reset")),
            decompress_dict: std::mem::transmute(sym("ZSTD_decompress_usingDict")),
            dref_prefix: std::mem::transmute(sym("ZSTD_DCtx_refPrefix")),
            decompress_dctx: std::mem::transmute(sym("ZSTD_decompressDCtx")),
            bound: std::mem::transmute(sym("ZSTD_compressBound")),
            is_error: std::mem::transmute(sym("ZSTD_isError")),
            error_code: std::mem::transmute(sym("ZSTD_getErrorCode")),
            cctx: cc(),
            dctx: dc(),
        })
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

/// A record-like message: the kind of small, similar inputs dictionaries
/// are for.
fn message(r: &mut Rng, words: &[Vec<u8>]) -> Vec<u8> {
    let mut v = Vec::new();
    v.extend_from_slice(b"{\"id\":");
    v.extend_from_slice(r.below(1_000_000).to_string().as_bytes());
    for _ in 0..1 + r.below(20) {
        let w = &words[(r.below(words.len() as u64) * r.below(words.len() as u64) / words.len() as u64) as usize];
        v.extend_from_slice(b",\"");
        v.extend_from_slice(w);
        v.extend_from_slice(b"\":\"");
        for _ in 0..r.below(12) {
            v.push(b'a' + r.below(26) as u8);
        }
        v.push(b'"');
    }
    v.push(b'}');
    v
}

fn words(r: &mut Rng) -> Vec<Vec<u8>> {
    (0..300).map(|_| (0..3 + r.below(9)).map(|_| b'a' + r.below(26) as u8).collect()).collect()
}

/// A dictionary trained by libzstd on `n` messages, at most `cap` bytes.
fn train(l: &Lib, r: &mut Rng, w: &[Vec<u8>], n: usize, cap: usize) -> Vec<u8> {
    let mut all = Vec::new();
    let mut sizes = Vec::new();
    for _ in 0..n {
        let m = message(r, w);
        sizes.push(m.len());
        all.extend_from_slice(&m);
    }
    let mut d = vec![0u8; cap];
    let k = unsafe { (l.train)(d.as_mut_ptr(), cap, all.as_ptr(), sizes.as_ptr(), n as c_uint) };
    assert_eq!(unsafe { (l.is_error)(k) }, 0, "training failed");
    d.truncate(k);
    d
}

impl Lib {
    fn compress(&self, src: &[u8], dict: &[u8], level: i32) -> Vec<u8> {
        unsafe {
            let mut dst = vec![0u8; (self.bound)(src.len())];
            let n = (self.compress_dict)(self.cctx, dst.as_mut_ptr(), dst.len(), src.as_ptr(), src.len(), dict.as_ptr(), dict.len(), level);
            assert_eq!((self.is_error)(n), 0);
            dst.truncate(n);
            dst
        }
    }

    /// With a raw-content prefix, a checksum and the given window log.
    fn compress_prefix(&self, src: &[u8], prefix: &[u8], level: i32, checksum: bool, wlog: i32) -> Vec<u8> {
        unsafe {
            (self.creset)(self.cctx, 3);
            (self.set_param)(self.cctx, 100, level);
            (self.set_param)(self.cctx, 201, checksum as c_int);
            if wlog != 0 {
                (self.set_param)(self.cctx, 101, wlog);
            }
            (self.cref_prefix)(self.cctx, prefix.as_ptr(), prefix.len());
            let mut dst = vec![0u8; (self.bound)(src.len())];
            let n = (self.compress2)(self.cctx, dst.as_mut_ptr(), dst.len(), src.as_ptr(), src.len());
            assert_eq!((self.is_error)(n), 0);
            dst.truncate(n);
            (self.creset)(self.cctx, 3);
            dst
        }
    }

    /// libzstd's decoder: the content, or its error code.
    fn decompress(&self, src: &[u8], dict: &[u8], cap: usize) -> Result<Vec<u8>, i32> {
        unsafe {
            let mut dst = vec![0u8; cap];
            let n = (self.decompress_dict)(self.dctx, dst.as_mut_ptr(), cap, src.as_ptr(), src.len(), dict.as_ptr(), dict.len());
            if (self.is_error)(n) != 0 {
                return Err((self.error_code)(n));
            }
            dst.truncate(n);
            Ok(dst)
        }
    }

    fn decompress_prefix(&self, src: &[u8], prefix: &[u8], cap: usize) -> Result<Vec<u8>, i32> {
        unsafe {
            (self.dref_prefix)(self.dctx, prefix.as_ptr(), prefix.len());
            let mut dst = vec![0u8; cap];
            let n = (self.decompress_dctx)(self.dctx, dst.as_mut_ptr(), cap, src.as_ptr(), src.len());
            if (self.is_error)(n) != 0 {
                return Err((self.error_code)(n));
            }
            dst.truncate(n);
            Ok(dst)
        }
    }
}

fn code(r: usize) -> Result<usize, i32> {
    unsafe {
        if capi::zstd_is_error(r) != 0 {
            Err(capi::zstd_get_error_code(r))
        } else {
            Ok(r)
        }
    }
}

/// Our `ZSTD_decompress_usingDict`.
fn ours(src: &[u8], dict: &[u8], cap: usize) -> Result<Vec<u8>, i32> {
    let mut dst = vec![0u8; cap];
    let n = code(unsafe {
        capi::zstd_decompress_using_dict(std::ptr::null_mut(), dst.as_mut_ptr() as *mut c_void, cap, src.as_ptr() as *const c_void, src.len(), dict.as_ptr() as *const c_void, dict.len())
    })?;
    dst.truncate(n);
    Ok(dst)
}

/// Our streaming decoder with `d`'s dictionary, fed in pieces chosen by
/// `r`. The content and the positions where a frame ended, or the error.
fn stream(d: *mut DCtx, src: &[u8], r: &mut Rng) -> Result<(Vec<u8>, Vec<usize>), i32> {
    let mut out = Vec::new();
    let mut ends = Vec::new();
    let mut buf = vec![0u8; 1 << 17];
    let mut pos = 0;
    let mut idle = 0;
    loop {
        let big = if r.below(4) == 0 { 1 << 17 } else { 300 };
        let n = (1 + r.below(big) as usize).min(src.len() - pos);
        let big = if r.below(4) == 0 { 1 << 17 } else { 300 };
        let osz = 1 + r.below(big) as usize;
        let mut i = InBuffer { src: src[pos..].as_ptr() as *const c_void, size: n, pos: 0 };
        let mut o = OutBuffer { dst: buf.as_mut_ptr() as *mut c_void, size: osz, pos: 0 };
        let ret = code(unsafe { capi::zstd_decompress_stream(d, &mut o, &mut i) })?;
        assert!(i.pos <= n && o.pos <= osz);
        out.extend_from_slice(&buf[..o.pos]);
        pos += i.pos;
        if ret == 0 {
            ends.push(pos);
            if pos == src.len() {
                return Ok((out, ends));
            }
        }
        if i.pos == 0 && o.pos == 0 {
            idle += 1;
            if idle > 3 {
                return Ok((out, ends));
            }
        } else {
            idle = 0;
        }
    }
}

const ERR_DICTIONARY_CORRUPTED: i32 = 30;
const ERR_DICTIONARY_WRONG: i32 = 32;

#[test]
fn trained_dictionaries() {
    let Some(l) = lib() else { return };
    let mut r = Rng(0x2545F4914F6CDD1D);
    let w = words(&mut r);
    let mut count = 0;
    for &cap in &[1024usize, 8192, 32768, 112_640] {
        let dict = train(&l, &mut r, &w, 2000, cap);
        let ddict = unsafe { capi::zstd_create_ddict(dict.as_ptr() as *const c_void, dict.len()) };
        assert!(!ddict.is_null());
        let dd = DictDecoder::load(&dict).expect("a trained dictionary loads");
        let mut dd = Some(dd);
        let dctx = unsafe { capi::zstd_create_dctx() };
        assert_eq!(code(unsafe { capi::zstd_dctx_load_dictionary(dctx, dict.as_ptr() as *const c_void, dict.len()) }), Ok(0));
        for round in 0..60 {
            // One message, several, or a long run of them.
            let n = [1, 1, 1, 3, 50, 2000][round % 6];
            let mut src = Vec::new();
            for _ in 0..n {
                src.extend_from_slice(&message(&mut r, &w));
            }
            let level = [-3, 1, 3, 6, 12, 19][r.below(6) as usize];
            let c = l.compress(&src, &dict, level);
            // The proven decoder.
            let (back, res) = dd.take().unwrap().decompress(&c, DICT_LIMIT);
            dd = Some(back);
            assert_eq!(res.as_deref().ok(), Some(&src[..]), "cap {cap} round {round}");
            // libzstd, and our C entry points.
            assert_eq!(l.decompress(&c, &dict, src.len()), Ok(src.clone()));
            assert_eq!(ours(&c, &dict, src.len()), Ok(src.clone()));
            let mut dst = vec![0u8; src.len()];
            let k = unsafe { capi::zstd_decompress_dctx(dctx, dst.as_mut_ptr() as *mut c_void, dst.len(), c.as_ptr() as *const c_void, c.len()) };
            assert_eq!(code(k), Ok(src.len()));
            assert_eq!(dst, src);
            let k = unsafe { capi::zstd_decompress_using_ddict(dctx, dst.as_mut_ptr() as *mut c_void, dst.len(), c.as_ptr() as *const c_void, c.len(), ddict) };
            assert_eq!(code(k), Ok(src.len()));
            assert_eq!(dst, src);
            // Streaming, with the loaded dictionary, frames one after another.
            let two = [c.clone(), c.clone()].concat();
            let (o, ends) = stream(dctx, &two, &mut r).expect("streaming");
            assert_eq!(o, [src.clone(), src.clone()].concat(), "cap {cap} round {round}");
            assert_eq!(ends, vec![c.len(), two.len()]);
            // Too little room.
            if !src.is_empty() {
                assert_eq!(ours(&c, &dict, src.len() - 1), Err(70));
            }
            count += 1;
        }
        unsafe {
            assert_eq!(capi::zstd_get_dict_id_from_ddict(ddict), capi::zstd_get_dict_id_from_dict(dict.as_ptr() as *const c_void, dict.len()));
            capi::zstd_free_ddict(ddict);
            capi::zstd_free_dctx(dctx);
        }
    }
    eprintln!("{count} frames with trained dictionaries");
}

#[test]
fn raw_prefixes() {
    let Some(l) = lib() else { return };
    let mut r = Rng(0x9E3779B97F4A7C15);
    for round in 0..80 {
        // A prefix, and input that repeats it in pieces, far back or near.
        let plen = [1usize, 100, 5000, 70_000, 300_000][round % 5];
        let prefix: Vec<u8> = (0..plen).map(|_| b'a' + r.below(if round % 2 == 0 { 26 } else { 256 }) as u8).collect();
        let n = [0usize, 10, 1000, 100_000][round / 5 % 4];
        let mut src = Vec::new();
        while src.len() < n {
            if r.below(3) > 0 {
                let a = r.below(plen as u64) as usize;
                let k = (4 + r.below(500) as usize).min(plen - a);
                src.extend_from_slice(&prefix[a..a + k]);
            } else {
                src.push(r.next() as u8);
            }
        }
        src.truncate(n);
        let wlog = if r.below(2) == 0 { 10 + r.below(10) as i32 } else { 0 };
        let c = l.compress_prefix(&src, &prefix, [1, 3, 19][r.below(3) as usize], r.below(2) == 0, wlog);
        let theirs = l.decompress_prefix(&c, &prefix, n + 10);
        assert_eq!(theirs, Ok(src.clone()), "round {round}");
        let (_, res) = DictDecoder::raw(&prefix).decompress(&c, DICT_LIMIT);
        assert_eq!(res.as_deref().ok(), Some(&src[..]), "round {round}");
        unsafe {
            let dctx = capi::zstd_create_dctx();
            // One shot: the prefix is used once.
            assert_eq!(code(capi::zstd_dctx_ref_prefix(dctx, prefix.as_ptr() as *const c_void, plen)), Ok(0));
            let mut dst = vec![0u8; n + 10];
            let k = capi::zstd_decompress_dctx(dctx, dst.as_mut_ptr() as *mut c_void, dst.len(), c.as_ptr() as *const c_void, c.len());
            assert_eq!(code(k), Ok(n), "round {round}");
            assert_eq!(&dst[..n], &src[..]);
            // Streaming.
            assert_eq!(code(capi::zstd_dctx_ref_prefix(dctx, prefix.as_ptr() as *const c_void, plen)), Ok(0));
            let (o, _) = stream(dctx, &c, &mut r).expect("streaming");
            assert_eq!(o, src, "round {round}");
            capi::zstd_free_dctx(dctx);
        }
    }
}

#[test]
fn the_wrong_dictionary() {
    let Some(l) = lib() else { return };
    let mut r = Rng(77);
    let w = words(&mut r);
    let a = train(&l, &mut r, &w, 1000, 8192);
    let b = train(&l, &mut r, &w, 1000, 8192);
    let src = message(&mut r, &w);
    let c = l.compress(&src, &a, 3);
    // The frame names `a`'s ID.
    assert_eq!(l.decompress(&c, &b, 1000), Err(ERR_DICTIONARY_WRONG));
    assert_eq!(ours(&c, &b, 1000), Err(ERR_DICTIONARY_WRONG));
    assert_eq!(ours(&c, &[], 1000), Err(ERR_DICTIONARY_WRONG));
    let raw: Vec<u8> = a[8..].to_vec();
    assert_eq!(ours(&c, &raw, 1000), l.decompress(&c, &raw, 1000));
    // Without a dictionary.
    let mut dst = vec![0u8; 1000];
    let k = unsafe { capi::zstd_decompress(dst.as_mut_ptr() as *mut c_void, 1000, c.as_ptr() as *const c_void, c.len()) };
    assert_eq!(code(k), Err(ERR_DICTIONARY_WRONG));
    // A frame that names no dictionary decodes with any.
    let plain = l.compress_prefix(&src, &[], 3, true, 0);
    assert_eq!(ours(&plain, &b, 1000), Ok(src.clone()));
}

/// Corrupted dictionaries: we load exactly those libzstd loads, and a frame
/// decodes the same with the damaged dictionary on both sides.
#[test]
fn corrupted_dictionaries_agree() {
    let Some(l) = lib() else { return };
    let mut r = Rng(0xC0FFEE);
    let w = words(&mut r);
    let good = train(&l, &mut r, &w, 1500, 16384);
    let (mut loaded, mut rejected) = (0, 0);
    for round in 0..3000 {
        let mut d = good.clone();
        // Most damage in the entropy tables and repeat offsets, near the front.
        for _ in 0..1 + r.below(3) {
            let i = if r.below(4) > 0 { 8 + r.below(400.min(d.len() as u64 - 8)) as usize } else { r.below(d.len() as u64) as usize };
            match r.below(3) {
                0 => d[i] ^= 1 << r.below(8),
                1 => d[i] = r.next() as u8,
                _ => d.truncate(i.max(9)),
            }
        }
        let src: Vec<u8> = (0..1 + r.below(5)).flat_map(|_| message(&mut r, &w)).collect();
        let c = l.compress(&src, &good, 3);
        let theirs = l.decompress(&c, &d, src.len() + 100);
        let mine = ours(&c, &d, src.len() + 100);
        let ok = DictDecoder::load(&d).is_some();
        if theirs == Err(ERR_DICTIONARY_CORRUPTED) {
            assert!(!ok, "round {round}: libzstd rejects a dictionary we load");
            assert_eq!(mine, Err(ERR_DICTIONARY_CORRUPTED));
            rejected += 1;
        } else {
            assert!(ok, "round {round}: libzstd loads a dictionary we reject ({theirs:?})");
            loaded += 1;
            // Both sides decode with the damaged dictionary.
            match (&theirs, &mine) {
                (Ok(a), Ok(b)) => assert_eq!(a, b, "round {round}"),
                (Err(_), Err(_)) => {},
                (Ok(_), Err(e)) => eprintln!("round {round}: libzstd decodes, we reject ({e})"),
                (Err(e), Ok(_)) => panic!("round {round}: we decode, libzstd rejects ({e})"),
            }
        }
    }
    eprintln!("dictionaries loaded {loaded}, rejected {rejected}");
    assert!(loaded > 100 && rejected > 100);
}

/// Corrupted frames with a dictionary: wherever we accept, libzstd accepts
/// with the same content.
#[test]
fn corrupted_frames_agree() {
    let Some(l) = lib() else { return };
    let mut r = Rng(0xBADC0DE);
    let w = words(&mut r);
    let dict = train(&l, &mut r, &w, 1500, 16384);
    let (mut both_ok, mut both_err, mut only_lib, mut only_us) = (0, 0, 0, 0);
    for round in 0..4000 {
        let src: Vec<u8> = (0..1 + r.below(30)).flat_map(|_| message(&mut r, &w)).collect();
        let mut c = l.compress(&src, &dict, [1, 3, 19][r.below(3) as usize]);
        for _ in 0..1 + r.below(3) {
            let i = r.below(c.len() as u64) as usize;
            match r.below(4) {
                0 => c[i] ^= 1 << r.below(8),
                1 => c[i] = r.next() as u8,
                2 => c.truncate(i),
                _ => c.insert(i, r.next() as u8),
            }
        }
        let cap = 4 * src.len() + 1000;
        let theirs = l.decompress(&c, &dict, cap);
        let mine = ours(&c, &dict, cap);
        match (&theirs, &mine) {
            (Ok(a), Ok(b)) => {
                assert_eq!(a, b, "round {round}");
                both_ok += 1;
            },
            (Err(_), Err(_)) => both_err += 1,
            (Ok(_), Err(_)) => only_lib += 1,
            (Err(e), Ok(_)) => {
                only_us += 1;
                eprintln!("round {round}: we accept, libzstd rejects ({e})");
            },
        }
    }
    eprintln!("both ok {both_ok}, both err {both_err}, only libzstd ok {only_lib}, only vzstd ok {only_us}");
    assert_eq!(only_us, 0);
}

#[test]
fn limits_and_errors() {
    let Some(l) = lib() else { return };
    let mut r = Rng(5);
    let w = words(&mut r);
    let dict = train(&l, &mut r, &w, 500, 4096);
    let src: Vec<u8> = (0..200).flat_map(|_| message(&mut r, &w)).collect();
    let c = l.compress(&src, &dict, 3);
    let dd = DictDecoder::load(&dict).unwrap();
    let (dd, res) = dd.decompress(&c, src.len());
    assert_eq!(res.ok(), Some(src.clone()));
    let (dd, res) = dd.decompress(&c, src.len() - 1);
    assert_eq!(res, Err(Error::TooLarge));
    // The decoder is unchanged by a failed call.
    let (_, res) = dd.decompress(&c, src.len());
    assert_eq!(res.ok(), Some(src.clone()));
    // A formatted dictionary of exactly 8 bytes, and an empty dictionary.
    assert!(DictDecoder::load(&dict[..8]).is_none());
    assert_eq!(ours(&c, &dict[..8], src.len()), Err(ERR_DICTIONARY_CORRUPTED));
    assert_eq!(l.decompress(&c, &dict[..8], src.len()), Err(ERR_DICTIONARY_CORRUPTED));
    let plain = l.compress_prefix(&src, &[], 3, false, 0);
    assert_eq!(ours(&plain, &[], src.len()), Ok(src.clone()));
    // Loading a dictionary mid-frame is refused.
    unsafe {
        let d = capi::zstd_create_dctx();
        assert_eq!(code(capi::zstd_dctx_load_dictionary(d, dict.as_ptr() as *const c_void, dict.len())), Ok(0));
        let mut buf = vec![0u8; 100];
        let mut i = InBuffer { src: c.as_ptr() as *const c_void, size: c.len() / 2, pos: 0 };
        let mut o = OutBuffer { dst: buf.as_mut_ptr() as *mut c_void, size: 100, pos: 0 };
        assert!(code(capi::zstd_decompress_stream(d, &mut o, &mut i)).is_ok());
        assert_eq!(code(capi::zstd_dctx_load_dictionary(d, dict.as_ptr() as *const c_void, dict.len())), Err(60));
        capi::zstd_dctx_reset(d, 1);
        assert_eq!(code(capi::zstd_dctx_load_dictionary(d, dict.as_ptr() as *const c_void, dict.len())), Ok(0));
        // A context with a reference to a DDict keeps its own copy.
        let h: *mut DDictH = capi::zstd_create_ddict(dict.as_ptr() as *const c_void, dict.len());
        assert_eq!(code(capi::zstd_dctx_ref_ddict(d, h)), Ok(0));
        capi::zstd_free_ddict(h);
        let mut dst = vec![0u8; src.len()];
        let k = capi::zstd_decompress_dctx(d, dst.as_mut_ptr() as *mut c_void, dst.len(), c.as_ptr() as *const c_void, c.len());
        assert_eq!(code(k), Ok(src.len()));
        assert_eq!(dst, src);
        capi::zstd_free_dctx(d);
    }
}
