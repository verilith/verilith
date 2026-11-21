//! The C API (unverified, thin wrappers): what compat/nghttp2's inflater
//! calls. Every decision is made by `Decoder::feed`, `change_settings` and
//! `end_block`; this file only moves pointers and lengths.
use crate::decoder::{Decoder, Feed};
use core::ffi::c_int;

pub const VHPACK_MORE: c_int = 0;
pub const VHPACK_FINAL: c_int = 1;
pub const VHPACK_FIELD: c_int = 2;
pub const VHPACK_BAD: c_int = -1;

/// A new decoder (initial state: 4096-byte table), or null.
#[no_mangle]
pub extern "C" fn vhpack_new() -> *mut Decoder {
    match Decoder::new() {
        Some(d) => Box::into_raw(Box::new(d)),
        None => core::ptr::null_mut(),
    }
}

/// # Safety
/// `d` is from `vhpack_new` (or null) and not used again.
#[no_mangle]
pub unsafe extern "C" fn vhpack_free(d: *mut Decoder) {
    if !d.is_null() {
        drop(Box::from_raw(d));
    }
}

/// A decoded field, as `vhpack_feed` reports it.
#[repr(C)]
pub struct VhpackField {
    /// Input bytes used, up to and including the field.
    pub consumed: usize,
    pub name: *const u8,
    pub namelen: usize,
    pub value: *const u8,
    pub valuelen: usize,
    /// `ids[0]` (`ids[1]`) is not 0 if the name (value) is a dynamic table
    /// entry's: one more than the number of entries inserted before it, so
    /// the same number always means the same entry.
    pub ids: [u64; 2],
    /// `n | v << 8`: if `n` (`v`) is from 1 to 61, the name (value) is that
    /// static table entry's, as the decoder's invariant proves.
    pub idx: u32,
    /// The field must never be indexed.
    pub never: c_int,
}

/// Decodes `inlen` bytes at `in_` up to the next field. Returns
/// `VHPACK_FIELD` with the field in `*f` (its name and value valid until
/// the next call), `VHPACK_MORE` or `VHPACK_FINAL` with all input used
/// (`f->consumed`), or `VHPACK_BAD`.
///
/// # Safety
/// `d` is a live decoder, `in_` points to `inlen` readable bytes (or
/// `inlen` is 0), and `f` is writable.
#[no_mangle]
pub unsafe extern "C" fn vhpack_feed(d: *mut Decoder, in_: *const u8, inlen: usize, fin: c_int, f: *mut VhpackField) -> c_int {
    let d = &mut *d;
    let f = &mut *f;
    let input: &[u8] = if inlen == 0 { &[] } else { core::slice::from_raw_parts(in_, inlen) };
    // feed takes less than 2^28 bytes at a time.
    const CHUNK: usize = 1 << 27;
    let mut off = 0;
    loop {
        let end = if input.len() - off > CHUNK { off + CHUNK } else { input.len() };
        let last = end == input.len();
        match d.feed(&input[off..end], last && fin != 0) {
            Feed::Field(n, nv) => {
                f.consumed = off + n;
                let (n, v) = (d.name(), d.value());
                f.name = n.as_ptr();
                f.namelen = n.len();
                f.value = v.as_ptr();
                f.valuelen = v.len();
                f.never = nv as c_int;
                let (nr, vr) = (d.name_ref, d.value_ref);
                let st = |r: usize| if r <= 61 { r as u32 } else { 0 };
                f.idx = st(nr) | (st(vr) << 8);
                // Dynamic entries by insertion number, plus one.
                let ins = d.table.ins;
                let id = |r: usize| if r > 61 { ins - (r - 62) as u64 } else { 0 };
                f.ids = [id(nr), id(vr)];
                return VHPACK_FIELD;
            }
            Feed::More if !last => off = end,
            Feed::More => {
                f.consumed = input.len();
                return VHPACK_MORE;
            }
            Feed::Final => {
                f.consumed = input.len();
                return VHPACK_FINAL;
            }
            Feed::Bad => return VHPACK_BAD,
        }
    }
}

/// SETTINGS_HEADER_TABLE_SIZE changed. Returns 0, or -1 if not at the
/// start of a header block.
///
/// # Safety
/// `d` is a live decoder.
#[no_mangle]
pub unsafe extern "C" fn vhpack_change_settings(d: *mut Decoder, n: u32) -> c_int {
    if (*d).change_settings(n) { 0 } else { -1 }
}

/// The header block ended.
///
/// # Safety
/// `d` is a live decoder.
#[no_mangle]
pub unsafe extern "C" fn vhpack_end_block(d: *mut Decoder) {
    (*d).end_block()
}

/// Entries in the dynamic table.
///
/// # Safety
/// `d` is a live decoder.
#[no_mangle]
pub unsafe extern "C" fn vhpack_table_len(d: *const Decoder) -> usize {
    (*d).table.ents.len()
}

/// The dynamic table's size (§4.1) and maximum size.
///
/// # Safety
/// `d` is a live decoder.
#[no_mangle]
pub unsafe extern "C" fn vhpack_table_size(d: *const Decoder) -> usize {
    (*d).table.size as usize
}

/// # Safety
/// `d` is a live decoder.
#[no_mangle]
pub unsafe extern "C" fn vhpack_table_max(d: *const Decoder) -> usize {
    (*d).table.max as usize
}

/// Dynamic table entry `i` (0 newest), valid until the table changes.
/// Returns 0, or -1 if there is no such entry.
///
/// # Safety
/// `d` is a live decoder and the out-pointers are writable.
#[no_mangle]
pub unsafe extern "C" fn vhpack_table_entry(
    d: *const Decoder,
    i: usize,
    name: *mut *const u8,
    namelen: *mut usize,
    value: *mut *const u8,
    valuelen: *mut usize,
) -> c_int {
    match (*d).table.ents.get(i) {
        Some(e) => {
            *name = e.name.as_ptr();
            *namelen = e.name.len();
            *value = e.value.as_ptr();
            *valuelen = e.value.len();
            0
        }
        None => -1,
    }
}
