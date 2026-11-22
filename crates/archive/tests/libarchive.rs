//! Differential tests against the system's libarchive, loaded at run time
//! with `dlopen` (nothing is built or linked from C), through the same C
//! API on both sides. Skipped, with a message, when libarchive is not
//! installed.
#![allow(unsafe_op_in_unsafe_fn)]
mod common;
use common::*;
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use verilith_archive::capi;

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
    fn setlocale(category: c_int, locale: *const c_char) -> *mut c_char;
}

/// libarchive converts names to the C library's locale and returns no name
/// at all when one does not fit, so give it a UTF-8 locale. (varchive
/// returns the bytes the archive holds.)
unsafe fn utf8_locale() {
    for (cat, name) in [(6, c"C.UTF-8"), (0, c"en_US.UTF-8"), (0, c"UTF-8")] {
        if !setlocale(cat, name.as_ptr()).is_null() {
            return;
        }
    }
}

type New = unsafe extern "C" fn() -> *mut c_void;
type A1 = unsafe extern "C" fn(*mut c_void) -> c_int;
type OpenMem = unsafe extern "C" fn(*mut c_void, *const c_void, usize) -> c_int;
type NextHeader = unsafe extern "C" fn(*mut c_void, *mut *mut c_void) -> c_int;
type EStr = unsafe extern "C" fn(*const c_void) -> *const c_char;
type EI64 = unsafe extern "C" fn(*const c_void) -> i64;
type EU32 = unsafe extern "C" fn(*const c_void) -> u32;
type ReadData = unsafe extern "C" fn(*mut c_void, *mut c_void, usize) -> isize;

/// The read API, from either library.
struct Api {
    new: New,
    support_filter_all: A1,
    support_format_all: A1,
    open_memory: OpenMem,
    next_header: NextHeader,
    pathname: EStr,
    symlink: EStr,
    hardlink: EStr,
    size: EI64,
    mtime: EI64,
    filetype: EU32,
    perm: EU32,
    read_data: ReadData,
    free: A1,
}

unsafe fn sym<T: Copy>(h: *mut c_void, name: &str) -> T {
    let p = dlsym(h, CString::new(name).unwrap().as_ptr());
    assert!(!p.is_null(), "{name}");
    std::mem::transmute_copy(&p)
}

unsafe fn libarchive() -> Option<Api> {
    let mut names: Vec<String> = std::env::var("VARCHIVE_LIBARCHIVE").into_iter().collect();
    names.extend(
        ["libarchive.so.13", "libarchive.13.dylib", "/opt/homebrew/opt/libarchive/lib/libarchive.13.dylib", "/usr/local/opt/libarchive/lib/libarchive.13.dylib"]
            .iter()
            .map(|s| s.to_string()),
    );
    let h = names.iter().map(|n| dlopen(CString::new(n.as_str()).unwrap().as_ptr(), 2)).find(|h| !h.is_null())?;
    Some(Api {
        new: sym(h, "archive_read_new"),
        support_filter_all: sym(h, "archive_read_support_filter_all"),
        support_format_all: sym(h, "archive_read_support_format_all"),
        open_memory: sym(h, "archive_read_open_memory"),
        next_header: sym(h, "archive_read_next_header"),
        pathname: sym(h, "archive_entry_pathname"),
        symlink: sym(h, "archive_entry_symlink"),
        hardlink: sym(h, "archive_entry_hardlink"),
        size: sym(h, "archive_entry_size"),
        mtime: sym(h, "archive_entry_mtime"),
        filetype: sym(h, "archive_entry_filetype"),
        perm: sym(h, "archive_entry_perm"),
        read_data: sym(h, "archive_read_data"),
        free: sym(h, "archive_read_free"),
    })
}

unsafe fn ours() -> Api {
    // The same functions, from this crate, behind the same pointer types.
    macro_rules! f {
        ($f:path) => {
            std::mem::transmute($f as *const c_void)
        };
    }
    Api {
        new: f!(capi::read_new),
        support_filter_all: f!(capi::support_filter_all),
        support_format_all: f!(capi::support_format_all),
        open_memory: f!(capi::read_open_memory),
        next_header: f!(capi::read_next_header),
        pathname: f!(capi::entry_pathname),
        symlink: f!(capi::entry_symlink),
        hardlink: f!(capi::entry_hardlink),
        size: f!(capi::entry_size),
        mtime: f!(capi::entry_mtime),
        filetype: f!(capi::entry_filetype),
        perm: f!(capi::entry_perm),
        read_data: f!(capi::read_data),
        free: f!(capi::read_free),
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Member {
    path: Vec<u8>,
    symlink: Option<Vec<u8>>,
    hardlink: Option<Vec<u8>>,
    size: i64,
    mtime: i64,
    filetype: u32,
    perm: u32,
    /// `None` if reading the data failed.
    data: Option<Vec<u8>>,
}

unsafe fn opt(p: *const c_char) -> Option<Vec<u8>> {
    (!p.is_null()).then(|| CStr::from_ptr(p).to_bytes().to_vec())
}

/// Everything the API says about an archive: `Err` with the members read
/// so far if opening or a header fails.
unsafe fn list(api: &Api, bytes: &[u8]) -> Result<Vec<Member>, Vec<Member>> {
    let a = (api.new)();
    (api.support_filter_all)(a);
    (api.support_format_all)(a);
    let mut out = Vec::new();
    if (api.open_memory)(a, bytes.as_ptr() as *const c_void, bytes.len()) != 0 {
        (api.free)(a);
        return Err(out);
    }
    let mut buf = vec![0u8; 1 << 16];
    loop {
        let mut e: *mut c_void = std::ptr::null_mut();
        let r = (api.next_header)(a, &mut e);
        if r == 1 {
            break;
        }
        // ARCHIVE_WARN (-20) is a usable header: libarchive warns when a
        // UTF-8 pax name does not fit the C locale, for one.
        if r != 0 && r != -20 {
            (api.free)(a);
            return Err(out);
        }
        let mut m = Member {
            path: opt((api.pathname)(e)).unwrap_or_default(),
            symlink: opt((api.symlink)(e)),
            hardlink: opt((api.hardlink)(e)),
            size: (api.size)(e),
            mtime: (api.mtime)(e),
            filetype: (api.filetype)(e),
            perm: (api.perm)(e),
            data: None,
        };
        let mut data = Vec::new();
        loop {
            let n = (api.read_data)(a, buf.as_mut_ptr() as *mut c_void, buf.len());
            if n < 0 {
                break;
            }
            if n == 0 {
                m.data = Some(data);
                break;
            }
            data.extend_from_slice(&buf[..n as usize]);
        }
        out.push(m);
    }
    (api.free)(a);
    Ok(out)
}

/// Every archive in tests/data reads the same through both libraries:
/// names, types, sizes, link targets, permissions and every byte of data.
#[test]
fn fixtures_agree() {
    unsafe {
        utf8_locale();
        let Some(la) = libarchive() else {
            eprintln!("libarchive not found: skipping");
            return;
        };
        let us = ours();
        let mut members = 0;
        for (name, bytes) in fixtures() {
            let mut a = list(&us, &bytes).unwrap_or_else(|_| panic!("{name}: varchive failed"));
            let mut b = list(&la, &bytes).unwrap_or_else(|_| panic!("{name}: libarchive failed"));
            assert_eq!(a.len(), b.len(), "{name}: member count");
            let zip = name.ends_with(".zip");
            for (x, y) in a.iter_mut().zip(b.iter_mut()) {
                if zip {
                    // libarchive converts MS-DOS times with the local time
                    // zone, or uses a Unix-time extra field; compare the
                    // rest.
                    x.mtime = 0;
                    y.mtime = 0;
                }
                assert!(x.data.is_some(), "{name}: {}: varchive could not read the data", String::from_utf8_lossy(&x.path));
                assert_eq!(x, y, "{name}");
                members += 1;
            }
        }
        assert!(members > 300);
        eprintln!("{members} members agree");
    }
}

/// Damaged archives: varchive never crashes, and whenever both libraries
/// return a member's data for the same name and size, it is the same data.
#[test]
fn mutations() {
    unsafe {
        utf8_locale();
        let la = libarchive();
        let us = ours();
        let mut rng = Rng(0x9e3779b97f4a7c15);
        let (mut both_ok, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
        for (name, bytes) in fixtures() {
            if bytes.len() > 400_000 {
                continue;
            }
            for _ in 0..150 {
                let mut m = bytes.clone();
                match rng.below(4) {
                    0 => m.truncate(rng.below(m.len())),
                    1 => {
                        for _ in 0..1 + rng.below(4) {
                            let i = rng.below(m.len());
                            m[i] ^= 1 << rng.below(8);
                        }
                    }
                    2 => {
                        // Aim at the structure: the first block and the tail.
                        let i = if rng.below(2) == 0 { rng.below(600.min(m.len())) } else { m.len() - 1 - rng.below(200.min(m.len())) };
                        m[i] = rng.next() as u8;
                    }
                    _ => {
                        let i = rng.below(m.len());
                        let j = (i + 1 + rng.below(64)).min(m.len());
                        m.drain(i..j);
                    }
                }
                let a = list(&us, &m);
                let Some(la) = &la else { continue };
                let b = list(la, &m);
                match (&a, &b) {
                    (Ok(_), Ok(_)) => both_ok += 1,
                    (Ok(_), Err(_)) => ours_only += 1,
                    (Err(_), Ok(_)) => theirs_only += 1,
                    (Err(_), Err(_)) => neither += 1,
                }
                let (a, b) = (a.unwrap_or_else(|v| v), b.unwrap_or_else(|v| v));
                for x in &a {
                    if let Some(y) = b.iter().find(|y| y.path == x.path && y.size == x.size && y.filetype == x.filetype) {
                        if let (Some(dx), Some(dy)) = (&x.data, &y.data) {
                            // libarchive hands out data before it has
                            // checked a zip member's CRC; varchive only
                            // returns data whose CRC matches. So compare
                            // only where the CRC cannot have been at stake.
                            if dx != dy {
                                assert!(name.contains("zip"), "{name}: data differs for {}", String::from_utf8_lossy(&x.path));
                            }
                        }
                    }
                }
            }
        }
        eprintln!("both accept {both_ok}, only varchive {ours_only}, only libarchive {theirs_only}, neither {neither}");
    }
}
