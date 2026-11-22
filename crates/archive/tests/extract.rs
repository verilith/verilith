//! Extraction onto a real file system, and Zstandard-compressed members.
#![cfg(unix)]
mod common;
use common::*;
use std::ffi::{c_char, c_int, c_void, CString};
use std::os::unix::ffi::OsStrExt;
use verilith_archive::{extract, Archive, Kind};

/// Every fixture extracts, and what lands on disk is what the archive
/// holds: each file's bytes, each link's target, each directory.
#[test]
fn fixtures_extract() {
    let base = std::env::temp_dir().join(format!("varchive-extract-{}", std::process::id()));
    let mut files = 0;
    for (name, bytes) in fixtures() {
        let root = base.join(&name);
        std::fs::create_dir_all(&root).unwrap();
        let a = Archive::open(&bytes).unwrap();
        let items = a.plan().unwrap_or_else(|r| panic!("{name}: refused {r:?}"));
        assert_eq!(extract::extract(&a, &root).unwrap(), items.len(), "{name}");
        for it in &items {
            let p = root.join(std::ffi::OsStr::from_bytes(&extract::join(&it.path)));
            let meta = std::fs::symlink_metadata(&p).unwrap_or_else(|e| panic!("{name}: {p:?}: {e}"));
            match it.kind {
                Kind::Dir => assert!(meta.is_dir()),
                Kind::File => {
                    assert!(meta.is_file());
                    assert_eq!(std::fs::read(&p).unwrap(), a.read(it.entry).unwrap(), "{name}: {p:?}");
                    files += 1;
                }
                Kind::Symlink => {
                    assert!(meta.file_type().is_symlink());
                    assert_eq!(std::fs::read_link(&p).unwrap().as_os_str().as_bytes(), extract::join(&it.target));
                    // Where it resolves (one fixture link dangles), it is
                    // to something under the root.
                    if let Ok(real) = std::fs::canonicalize(&p) {
                        assert!(real.starts_with(std::fs::canonicalize(&root).unwrap()));
                    }
                }
                Kind::Hardlink => {
                    let target = root.join(std::ffi::OsStr::from_bytes(&extract::join(&it.target)));
                    assert_eq!(std::fs::read(&p).unwrap(), std::fs::read(target).unwrap());
                }
                Kind::Other => unreachable!(),
            }
        }
    }
    assert!(files > 150);
    std::fs::remove_dir_all(&base).unwrap();
}

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

/// A zip member compressed with Zstandard (method 93), made with the
/// system's libzstd. Skipped when libzstd is not installed.
#[test]
fn zstd_member() {
    type Compress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize, c_int) -> usize;
    let data: Vec<u8> = (0..200_000u32).map(|i| (i % 251) as u8 ^ (i / 1000) as u8).collect();
    let packed = unsafe {
        let h = ["libzstd.so.1", "libzstd.1.dylib", "/opt/homebrew/lib/libzstd.1.dylib"]
            .iter()
            .map(|n| dlopen(CString::new(*n).unwrap().as_ptr(), 2))
            .find(|h| !h.is_null());
        let Some(h) = h else {
            eprintln!("libzstd not found: skipping");
            return;
        };
        let f: Compress = std::mem::transmute(dlsym(h, c"ZSTD_compress".as_ptr()));
        let mut out = vec![0u8; data.len() + 1024];
        let n = f(out.as_mut_ptr(), out.len(), data.as_ptr(), data.len(), 3);
        out.truncate(n);
        out
    };
    assert!(packed.len() < data.len() / 2);
    let m = ZipMember { method: 93, stored: packed, ..stored("z", &data) };
    let z = zip(&[m.clone()]);
    let a = Archive::open(&z).unwrap();
    assert_eq!(a.read(0).unwrap(), data);
    // One byte short, or a wrong CRC, is refused.
    let short = ZipMember { size: m.size - 1, ..m.clone() };
    assert!(Archive::open(&zip(&[short])).unwrap().read(0).is_err());
    let bad = ZipMember { crc: m.crc ^ 1, ..m };
    assert!(Archive::open(&zip(&[bad])).unwrap().read(0).is_err());
}
