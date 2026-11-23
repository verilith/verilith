//! libarchive's read API (`archive.h`, `archive_entry.h`), as an unverified
//! adapter over the proven readers.
//!
//! The subset here is what programs that list or unpack zip and tar files
//! call: `archive_read_new`, the `archive_read_support_*` switches,
//! `archive_read_open_memory` / `_open_filename`, `archive_read_next_header`,
//! the `archive_entry_*` getters, `archive_read_data` / `_data_block` /
//! `_data_skip`, `archive_read_extract`, and `archive_read_free`.
//!
//! Symbols are exported as `varchive_*`, or under libarchive's own names
//! with the `libarchive-abi` feature.
//!
//! Differences from libarchive that a caller can see are listed in
//! README.md ("Differences from libarchive"). The two that matter: a
//! member's data is checked (length and CRC-32) before any of it is handed
//! out, and `archive_read_extract` refuses every member of an archive that
//! the planner rejects.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::api::{Archive, Filter, OpenError};
use crate::plan::{Item, Rejected};
use crate::reader::Format;
use crate::spec::Kind;
use core::ffi::{c_char, c_int, c_void};
use std::ffi::{CStr, CString};

pub const ARCHIVE_EOF: c_int = 1;
pub const ARCHIVE_OK: c_int = 0;
pub const ARCHIVE_WARN: c_int = -20;
pub const ARCHIVE_FAILED: c_int = -25;
pub const ARCHIVE_FATAL: c_int = -30;

pub const ARCHIVE_FORMAT_TAR: c_int = 0x30000;
pub const ARCHIVE_FORMAT_ZIP: c_int = 0x50000;
pub const ARCHIVE_FILTER_NONE: c_int = 0;
pub const ARCHIVE_FILTER_GZIP: c_int = 1;
pub const ARCHIVE_FILTER_ZSTD: c_int = 14;

pub const AE_IFREG: u32 = 0o100000;
pub const AE_IFLNK: u32 = 0o120000;
pub const AE_IFDIR: u32 = 0o040000;

/// `struct archive_entry`.
pub struct CEntry {
    pathname: CString,
    symlink: Option<CString>,
    hardlink: Option<CString>,
    size: i64,
    filetype: u32,
    perm: u32,
    mtime: i64,
}

/// `struct archive`.
pub struct CArchive {
    /// After `archive_read_open_memory` this borrows the caller's buffer,
    /// which libarchive too requires to stay valid until the archive is
    /// closed.
    ar: Option<Archive<'static>>,
    /// The next member `archive_read_next_header` returns.
    next: usize,
    /// The member whose header was returned last.
    cur: Option<usize>,
    /// Its data, once read: in `own`, or (a stored member) in the archive.
    data: Option<(*const u8, usize)>,
    own: Vec<u8>,
    pos: usize,
    err: CString,
    errno: c_int,
    entry: CEntry,
    plan: Option<Result<Vec<Item>, Rejected>>,
}

/// A C string of `b` up to its first NUL.
fn cstring(b: &[u8]) -> CString {
    let end = b.iter().position(|&c| c == 0).unwrap_or(b.len());
    CString::new(&b[..end]).unwrap()
}

fn empty_entry() -> CEntry {
    CEntry { pathname: CString::default(), symlink: None, hardlink: None, size: 0, filetype: 0, perm: 0, mtime: 0 }
}

/// Days from 1970-01-01 to the given civil date.
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

/// An MS-DOS date and time (as `date << 16 | time`), read as UTC.
fn dos_to_unix(dt: i64) -> i64 {
    let (date, time) = (dt >> 16, dt & 0xffff);
    let (y, m, d) = (1980 + (date >> 9), ((date >> 5) & 15).max(1), (date & 31).max(1));
    days_from_civil(y, m, d) * 86400 + (time >> 11) * 3600 + ((time >> 5) & 63) * 60 + (time & 31) * 2
}

impl CArchive {
    fn fail(&mut self, code: c_int, errno: c_int, msg: &str) -> c_int {
        self.err = cstring(msg.as_bytes());
        self.errno = errno;
        code
    }

    fn open(&mut self, r: Result<Archive<'static>, OpenError>) -> c_int {
        match r {
            Ok(a) => {
                self.ar = Some(a);
                self.next = 0;
                self.cur = None;
                self.data = None;
                self.plan = None;
                ARCHIVE_OK
            }
            Err(OpenError::NotAnArchive) => self.fail(ARCHIVE_FATAL, 84, "Unrecognized archive format"),
            Err(OpenError::BadCompression) => self.fail(ARCHIVE_FATAL, 84, "Damaged gzip or zstd data"),
            Err(OpenError::TooLarge) => self.fail(ARCHIVE_FATAL, 12, "Archive is over the size limit"),
        }
    }

    fn load(&mut self) -> c_int {
        if self.data.is_some() {
            return ARCHIVE_OK;
        }
        let (Some(a), Some(i)) = (&self.ar, self.cur) else {
            return self.fail(ARCHIVE_FATAL, 22, "No current entry");
        };
        // As libarchive: links have no data (a zip symlink's data is its
        // target, which `archive_entry_symlink` returns).
        if matches!(a.entries()[i].kind, Kind::Symlink | Kind::Hardlink) {
            self.data = Some((core::ptr::NonNull::dangling().as_ptr(), 0));
            self.pos = 0;
            return ARCHIVE_OK;
        }
        match a.read_ref(i) {
            Ok(v) => {
                self.data = Some((v.as_ptr(), v.len()));
                self.own = match v {
                    std::borrow::Cow::Owned(v) => v,
                    std::borrow::Cow::Borrowed(_) => Vec::new(),
                };
                self.pos = 0;
                ARCHIVE_OK
            }
            Err(crate::read::Error::Unsupported) => {
                self.fail(ARCHIVE_FAILED, 84, "Unsupported compression method or encrypted entry")
            }
            Err(crate::read::Error::TooLarge) => self.fail(ARCHIVE_FAILED, 12, "Entry is over the size limit"),
            Err(crate::read::Error::BadData) => {
                self.fail(ARCHIVE_FAILED, 84, "Entry data does not match its declared size or CRC")
            }
        }
    }
}

macro_rules! capi {
    ($name:literal, $vname:literal, fn $f:ident($($arg:ident: $ty:ty),*) -> $ret:ty $body:block) => {
        /// # Safety
        /// As for the libarchive function of the same name.
        #[cfg_attr(feature = "libarchive-abi", unsafe(export_name = $name))]
        #[cfg_attr(not(feature = "libarchive-abi"), unsafe(export_name = $vname))]
        pub unsafe extern "C" fn $f($($arg: $ty),*) -> $ret $body
    };
}

capi!("archive_read_new", "varchive_read_new", fn read_new() -> *mut CArchive {
    Box::into_raw(Box::new(CArchive {
        ar: None,
        next: 0,
        cur: None,
        data: None,
        own: Vec::new(),
        pos: 0,
        err: CString::default(),
        errno: 0,
        entry: empty_entry(),
        plan: None,
    }))
});

// The format and filter switches: everything this library reads is always
// on, so these only report success.
capi!("archive_read_support_format_all", "varchive_read_support_format_all", fn support_format_all(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_format_zip", "varchive_read_support_format_zip", fn support_format_zip(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_format_tar", "varchive_read_support_format_tar", fn support_format_tar(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_format_gnutar", "varchive_read_support_format_gnutar", fn support_format_gnutar(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_filter_all", "varchive_read_support_filter_all", fn support_filter_all(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_filter_none", "varchive_read_support_filter_none", fn support_filter_none(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_filter_gzip", "varchive_read_support_filter_gzip", fn support_filter_gzip(_a: *mut CArchive) -> c_int { ARCHIVE_OK });
capi!("archive_read_support_filter_zstd", "varchive_read_support_filter_zstd", fn support_filter_zstd(_a: *mut CArchive) -> c_int { ARCHIVE_OK });

capi!("archive_read_open_memory", "varchive_read_open_memory", fn read_open_memory(a: *mut CArchive, buf: *const c_void, size: usize) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    if buf.is_null() && size != 0 {
        return a.fail(ARCHIVE_FATAL, 22, "Null buffer");
    }
    let input: &'static [u8] = if size == 0 { &[] } else { core::slice::from_raw_parts(buf as *const u8, size) };
    a.open(Archive::open(input))
});

capi!("archive_read_open_filename", "varchive_read_open_filename", fn read_open_filename(a: *mut CArchive, path: *const c_char, _block_size: usize) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    if path.is_null() {
        return a.fail(ARCHIVE_FATAL, 22, "Reading from standard input is not supported");
    }
    #[cfg(unix)]
    let p = {
        use std::os::unix::ffi::OsStrExt;
        std::path::PathBuf::from(std::ffi::OsStr::from_bytes(CStr::from_ptr(path).to_bytes()))
    };
    #[cfg(not(unix))]
    let p = std::path::PathBuf::from(CStr::from_ptr(path).to_string_lossy().into_owned());
    match std::fs::read(&p) {
        Ok(v) => a.open(Archive::open(&v).map(Archive::into_owned)),
        Err(e) => a.fail(ARCHIVE_FATAL, e.raw_os_error().unwrap_or(5), "Failed to open file"),
    }
});

capi!("archive_read_next_header", "varchive_read_next_header", fn read_next_header(a: *mut CArchive, entry: *mut *mut CEntry) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    let Some(ar) = &a.ar else { return a.fail(ARCHIVE_FATAL, 22, "Archive is not open") };
    a.data = None;
    a.pos = 0;
    if a.next >= ar.entries().len() {
        a.cur = None;
        return ARCHIVE_EOF;
    }
    let i = a.next;
    let e = &ar.entries()[i];
    let zip = ar.format() == Format::Zip;
    let mut symlink = None;
    let mut hardlink = None;
    let filetype = match e.kind {
        Kind::File => AE_IFREG,
        Kind::Dir => AE_IFDIR,
        Kind::Symlink => {
            // A zip symlink's target is its data.
            let t = if zip { ar.read(i).unwrap_or_default() } else { e.link.clone() };
            symlink = Some(cstring(&t));
            AE_IFLNK
        }
        Kind::Hardlink => {
            hardlink = Some(cstring(&e.link));
            // As libarchive: a tar hard link has no file type of its own.
            0
        }
        Kind::Other => 0,
    };
    a.entry = CEntry {
        pathname: cstring(&e.name),
        symlink,
        hardlink,
        size: if matches!(e.kind, Kind::Symlink | Kind::Hardlink) { 0 } else { e.size as i64 },
        filetype,
        perm: e.mode & 0o7777,
        mtime: if zip { dos_to_unix(e.mtime) } else { e.mtime },
    };
    a.cur = Some(i);
    a.next = i + 1;
    if !entry.is_null() {
        *entry = &mut a.entry;
    }
    ARCHIVE_OK
});

capi!("archive_entry_pathname", "varchive_entry_pathname", fn entry_pathname(e: *const CEntry) -> *const c_char {
    match e.as_ref() { Some(e) => e.pathname.as_ptr(), None => core::ptr::null() }
});
capi!("archive_entry_pathname_utf8", "varchive_entry_pathname_utf8", fn entry_pathname_utf8(e: *const CEntry) -> *const c_char {
    match e.as_ref() { Some(e) => e.pathname.as_ptr(), None => core::ptr::null() }
});
capi!("archive_entry_symlink", "varchive_entry_symlink", fn entry_symlink(e: *const CEntry) -> *const c_char {
    match e.as_ref().and_then(|e| e.symlink.as_ref()) { Some(s) => s.as_ptr(), None => core::ptr::null() }
});
capi!("archive_entry_hardlink", "varchive_entry_hardlink", fn entry_hardlink(e: *const CEntry) -> *const c_char {
    match e.as_ref().and_then(|e| e.hardlink.as_ref()) { Some(s) => s.as_ptr(), None => core::ptr::null() }
});
capi!("archive_entry_size", "varchive_entry_size", fn entry_size(e: *const CEntry) -> i64 {
    e.as_ref().map_or(0, |e| e.size)
});
capi!("archive_entry_size_is_set", "varchive_entry_size_is_set", fn entry_size_is_set(e: *const CEntry) -> c_int {
    e.as_ref().map_or(0, |_| 1)
});
capi!("archive_entry_filetype", "varchive_entry_filetype", fn entry_filetype(e: *const CEntry) -> u32 {
    e.as_ref().map_or(0, |e| e.filetype)
});
capi!("archive_entry_perm", "varchive_entry_perm", fn entry_perm(e: *const CEntry) -> u32 {
    e.as_ref().map_or(0, |e| e.perm)
});
capi!("archive_entry_mode", "varchive_entry_mode", fn entry_mode(e: *const CEntry) -> u32 {
    e.as_ref().map_or(0, |e| e.filetype | e.perm)
});
capi!("archive_entry_mtime", "varchive_entry_mtime", fn entry_mtime(e: *const CEntry) -> i64 {
    e.as_ref().map_or(0, |e| e.mtime)
});

capi!("archive_read_data", "varchive_read_data", fn read_data(a: *mut CArchive, buf: *mut c_void, size: usize) -> isize {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL as isize };
    let r = a.load();
    if r != ARCHIVE_OK {
        return r as isize;
    }
    let (d, len) = a.data.unwrap();
    let n = size.min(len - a.pos);
    if n > 0 {
        core::ptr::copy_nonoverlapping(d.add(a.pos), buf as *mut u8, n);
    }
    a.pos += n;
    n as isize
});

capi!("archive_read_data_block", "varchive_read_data_block", fn read_data_block(a: *mut CArchive, buf: *mut *const c_void, size: *mut usize, offset: *mut i64) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    let r = a.load();
    if r != ARCHIVE_OK {
        return r;
    }
    let (d, len) = a.data.unwrap();
    // The whole member is one block, then end of data.
    *offset = a.pos as i64;
    if a.pos >= len {
        *buf = core::ptr::null();
        *size = 0;
        return ARCHIVE_EOF;
    }
    *buf = d.add(a.pos) as *const c_void;
    *size = len - a.pos;
    a.pos = len;
    ARCHIVE_OK
});

capi!("archive_read_data_skip", "varchive_read_data_skip", fn read_data_skip(a: *mut CArchive) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    // As libarchive: the rest of the member is gone, so a later
    // `archive_read_data` returns 0 and `archive_read_data_block` EOF.
    a.data = Some((core::ptr::NonNull::dangling().as_ptr(), 0));
    a.own = Vec::new();
    a.pos = 0;
    ARCHIVE_OK
});

// Extracts the current member under the working directory, if the planner
// accepts the whole archive. `flags` are ignored: the policy of
// ARCHIVE_EXTRACT_SECURE_NODOTDOT, _SECURE_SYMLINKS and
// _SECURE_NOABSOLUTEPATHS is always on, and owners, times and ACLs are not
// restored.
#[cfg(unix)]
capi!("archive_read_extract", "varchive_read_extract", fn read_extract(a: *mut CArchive, _entry: *mut CEntry, _flags: c_int) -> c_int {
    let Some(a) = a.as_mut() else { return ARCHIVE_FATAL };
    let (Some(ar), Some(i)) = (&a.ar, a.cur) else { return a.fail(ARCHIVE_FATAL, 22, "No current entry") };
    if a.plan.is_none() {
        a.plan = Some(ar.plan());
    }
    let item = match a.plan.as_ref().unwrap() {
        Ok(items) => items.iter().find(|it| it.entry == i),
        Err(r) => {
            let msg = format!("Archive is not safe to extract: entry {} ({:?})", r.entry, r.why);
            return a.fail(ARCHIVE_FAILED, 1, &msg);
        }
    };
    let Some(item) = item else { return ARCHIVE_OK };
    match crate::extract::extract_item(ar, item, std::path::Path::new(".")) {
        Ok(()) => ARCHIVE_OK,
        Err(e) => {
            let msg = format!("{:?}", e);
            a.fail(ARCHIVE_FAILED, 5, &msg)
        }
    }
});

capi!("archive_format", "varchive_format", fn format(a: *mut CArchive) -> c_int {
    match a.as_ref().and_then(|a| a.ar.as_ref()) {
        Some(ar) => if ar.format() == Format::Zip { ARCHIVE_FORMAT_ZIP } else { ARCHIVE_FORMAT_TAR },
        None => 0,
    }
});
capi!("archive_format_name", "varchive_format_name", fn format_name(a: *mut CArchive) -> *const c_char {
    match a.as_ref().and_then(|a| a.ar.as_ref()) {
        Some(ar) => if ar.format() == Format::Zip { c"ZIP".as_ptr() } else { c"tar".as_ptr() },
        None => core::ptr::null(),
    }
});
capi!("archive_filter_code", "varchive_filter_code", fn filter_code(a: *mut CArchive, _n: c_int) -> c_int {
    match a.as_ref().and_then(|a| a.ar.as_ref()).map(|ar| ar.filter()) {
        Some(Filter::Gzip) => ARCHIVE_FILTER_GZIP,
        Some(Filter::Zstd) => ARCHIVE_FILTER_ZSTD,
        _ => ARCHIVE_FILTER_NONE,
    }
});
capi!("archive_file_count", "varchive_file_count", fn file_count(a: *mut CArchive) -> c_int {
    a.as_ref().map_or(0, |a| a.next as c_int)
});
capi!("archive_error_string", "varchive_error_string", fn error_string(a: *mut CArchive) -> *const c_char {
    match a.as_ref() { Some(a) if !a.err.as_bytes().is_empty() => a.err.as_ptr(), _ => core::ptr::null() }
});
capi!("archive_errno", "varchive_errno", fn errno(a: *mut CArchive) -> c_int {
    a.as_ref().map_or(0, |a| a.errno)
});
capi!("archive_read_close", "varchive_read_close", fn read_close(a: *mut CArchive) -> c_int {
    if let Some(a) = a.as_mut() {
        a.ar = None;
        a.data = None;
        a.cur = None;
    }
    ARCHIVE_OK
});
capi!("archive_read_free", "varchive_read_free", fn read_free(a: *mut CArchive) -> c_int {
    if !a.is_null() {
        drop(Box::from_raw(a));
    }
    ARCHIVE_OK
});
capi!("archive_read_finish", "varchive_read_finish", fn read_finish(a: *mut CArchive) -> c_int {
    if !a.is_null() {
        drop(Box::from_raw(a));
    }
    ARCHIVE_OK
});
