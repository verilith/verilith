//! The native C API (`include/vdns.h`), behind the `capi` feature.
//!
//! The Rust API with C types: a reusable message that the verified parser
//! fills, and questions and records read out of it as spans. Unlike the
//! c-ares shape (`cares.rs`), nothing is allocated per record and no
//! record is copied into a separate object.
//!
//! This layer is NOT verified. It is kept mechanical: pointer checks, a
//! call to the method of the same name on `Message`, and the copying of
//! the result into C structs. All wire-format handling is in verified code.
#![allow(non_camel_case_types)]
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::error::{ErrorKind, Part};
use crate::message::{Message, Section};
use crate::name::Name;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::ffi::{c_char, c_int};

pub const VDNS_E_ARGUMENT: c_int = -1;
pub const VDNS_E_NAME: c_int = -2;
pub const VDNS_E_SPACE: c_int = -3;

/// A parsed message. Opaque to C.
pub struct vdns_message(Message);

#[repr(C)]
pub struct vdns_question {
    /// The name in uncompressed wire form, root octet included.
    pub name: *const u8,
    pub name_len: usize,
    pub qtype: u16,
    pub qclass: u16,
}

#[repr(C)]
pub struct vdns_record {
    pub name: *const u8,
    pub name_len: usize,
    /// The RDATA with the names inside it uncompressed.
    pub rdata: *const u8,
    pub rdata_len: usize,
    pub ttl: u32,
    pub rtype: u16,
    pub rclass: u16,
}

#[repr(C)]
pub struct vdns_error {
    /// 0, or a positive `VDNS_E_*` code.
    pub code: c_int,
    /// `VDNS_PART_*`.
    pub part: c_int,
    /// The question or record at fault, within its section.
    pub index: usize,
    /// Offset of the byte that breaks the rule.
    pub offset: usize,
}

/// A new, empty message. Free it with `vdns_message_free`.
#[unsafe(no_mangle)]
pub extern "C" fn vdns_message_new() -> *mut vdns_message {
    Box::into_raw(Box::new(vdns_message(Message::new(0, 0))))
}

/// # Safety
/// `m` is null or came from `vdns_message_new` and was not freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_message_free(m: *mut vdns_message) {
    if !m.is_null() {
        drop(Box::from_raw(m));
    }
}

/// Parses a complete DNS message into `m`, replacing what it held.
/// Returns 0, or a `VDNS_E_*` code (and `m` is then empty).
///
/// # Safety
/// `m` is a live message no other thread is using, `wire` points to `len`
/// readable bytes, and `err` is null or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_parse(m: *mut vdns_message, wire: *const u8, len: usize, err: *mut vdns_error) -> c_int {
    if !err.is_null() {
        err.write(vdns_error { code: 0, part: 0, index: 0, offset: 0 });
    }
    if m.is_null() || (wire.is_null() && len != 0) {
        return VDNS_E_ARGUMENT;
    }
    let b: &[u8] = if len == 0 { &[] } else { core::slice::from_raw_parts(wire, len) };
    if (*m).0.parse_into(b) {
        return 0;
    }
    reject(b, err)
}

/// Why the verified parser rejected `b` (the unverified `error::try_parse`).
#[cold]
unsafe fn reject(b: &[u8], err: *mut vdns_error) -> c_int {
    let e = match crate::error::try_parse(b) {
        Err(e) => e,
        // Not reachable: `try_parse` rejects exactly what `parse` does.
        Ok(_) => return 2,
    };
    let code = match e.kind {
        ErrorKind::ShortHeader => 1,
        ErrorKind::Truncated => 2,
        ErrorKind::ReservedLabelType => 3,
        ErrorKind::PointerNotPrior => 4,
        ErrorKind::PointerToPointer => 5,
        ErrorKind::NameTooLong => 6,
        ErrorKind::BadRdata => 7,
        ErrorKind::TrailingBytes => 8,
    };
    let (part, index) = match e.part {
        Part::Header => (0, 0),
        Part::Question(i) => (1, i),
        Part::Answer(i) => (2, i),
        Part::Authority(i) => (3, i),
        Part::Additional(i) => (4, i),
        Part::End => (5, 0),
    };
    if !err.is_null() {
        err.write(vdns_error { code, part, index, offset: e.offset });
    }
    code
}

/// # Safety
/// For the functions below: `m` is null or a live message, and out
/// pointers are null or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_id(m: *const vdns_message) -> u16 {
    if m.is_null() {
        return 0;
    }
    (*m).0.id()
}

/// The 16 bits after the ID: QR, opcode, AA, TC, RD, RA, Z and RCODE.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_flags(m: *const vdns_message) -> u16 {
    if m.is_null() {
        return 0;
    }
    (*m).0.flags()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_question_count(m: *const vdns_message) -> usize {
    if m.is_null() {
        return 0;
    }
    (*m).0.question_count()
}

fn section(s: c_int) -> Option<Section> {
    match s {
        0 => Some(Section::Answer),
        1 => Some(Section::Authority),
        2 => Some(Section::Additional),
        _ => None,
    }
}

/// The number of records in a section (`VDNS_ANSWER`, `VDNS_AUTHORITY` or
/// `VDNS_ADDITIONAL`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_record_count(m: *const vdns_message, s: c_int) -> usize {
    match section(s) {
        Some(s) if !m.is_null() => (*m).0.record_count(s),
        _ => 0,
    }
}

/// The `i`th question. The name points into `m`: it is valid until `m` is
/// parsed into again or freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_get_question(m: *const vdns_message, i: usize, out: *mut vdns_question) -> bool {
    if m.is_null() {
        return false;
    }
    match (*m).0.question(i) {
        Some(q) => {
            if !out.is_null() {
                out.write(vdns_question { name: q.name.as_ptr(), name_len: q.name.len(), qtype: q.qtype, qclass: q.qclass });
            }
            true
        }
        None => false,
    }
}

/// The `i`th record of a section. The name and RDATA point into `m`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_get_record(m: *const vdns_message, s: c_int, i: usize, out: *mut vdns_record) -> bool {
    let Some(s) = section(s) else { return false };
    if m.is_null() {
        return false;
    }
    match (*m).0.record(s, i) {
        Some(r) => {
            if !out.is_null() {
                out.write(vdns_record {
                    name: r.name.as_ptr(),
                    name_len: r.name.len(),
                    rdata: r.rdata.as_ptr(),
                    rdata_len: r.rdata.len(),
                    ttl: r.ttl,
                    rtype: r.rtype,
                    rclass: r.rclass,
                });
            }
            true
        }
        None => false,
    }
}

/// Copies `text` and a NUL to `buf`, as much as fits in `cap` bytes.
unsafe fn put_text(text: &[u8], buf: *mut c_char, cap: usize) -> usize {
    if !buf.is_null() && cap > 0 {
        let n = text.len().min(cap - 1);
        core::ptr::copy_nonoverlapping(text.as_ptr(), buf as *mut u8, n);
        *(buf as *mut u8).add(n) = 0;
    }
    text.len()
}

/// Writes a wire-form name's presentation form (`www.example.com`, escaped
/// as c-ares does, the root name as the empty string) and a NUL to `buf`,
/// as much as fits in `cap` bytes. Returns the length of the whole text
/// (without the NUL), as `snprintf` does.
///
/// # Safety
/// `name` points to `name_len` readable bytes and `buf` to `cap` writable
/// ones.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_name_text(name: *const u8, name_len: usize, buf: *mut c_char, cap: usize) -> usize {
    if name.is_null() && name_len != 0 {
        return 0;
    }
    let wire: &[u8] = if name_len == 0 { &[] } else { core::slice::from_raw_parts(name, name_len) };
    // At most 4 bytes of text per byte of name.
    let mut text = Vec::with_capacity(4 * wire.len());
    Name::from_wire(wire).write_presentation(&mut text);
    put_text(&text, buf, cap)
}

/// Writes a query with one question to `out`: `name` is in presentation
/// format (`name_len` bytes, an optional trailing dot, `\.` and `\DDD`
/// escapes). Sets `*len` to the query's length and returns 0;
/// `VDNS_E_NAME` if the name is not valid; or `VDNS_E_SPACE` if `cap` is
/// too small, with the length needed in `*len`.
///
/// # Safety
/// `name` points to `name_len` readable bytes, `out` to `cap` writable
/// ones, and `len` is null or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_write_query(
    id: u16,
    flags: u16,
    name: *const c_char,
    name_len: usize,
    qtype: u16,
    qclass: u16,
    out: *mut u8,
    cap: usize,
    len: *mut usize,
) -> c_int {
    if (name.is_null() && name_len != 0) || (out.is_null() && cap != 0) {
        return VDNS_E_ARGUMENT;
    }
    let text: &[u8] = if name_len == 0 { &[] } else { core::slice::from_raw_parts(name as *const u8, name_len) };
    let Some((wire, _)) = crate::text::parse_text(text) else { return VDNS_E_NAME };
    let mut m = Message::new(id, flags);
    if m.add_question(&wire, qtype, qclass).is_err() {
        return VDNS_E_NAME;
    }
    let bytes = m.to_bytes();
    if !len.is_null() {
        *len = bytes.len();
    }
    if bytes.len() > cap {
        return VDNS_E_SPACE;
    }
    core::ptr::copy_nonoverlapping(bytes.as_ptr(), out, bytes.len());
    0
}
