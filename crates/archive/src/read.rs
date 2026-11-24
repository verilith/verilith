//! Reading a member's data: `read_entry` computes `spec::entry_data`.
use crate::spec::*;
use crate::zip::Entry;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The proofs cover archives below this size: 256 TiB on 64-bit targets,
/// and on 32-bit ones 2 GiB, above the largest slice there (`isize::MAX`
/// bytes). The same as verilith-zstd's `MAX_LIMIT`.
#[cfg(target_pointer_width = "64")]
pub const MAX_ARCHIVE: usize = 0x1_0000_0000_0000;

#[cfg(target_pointer_width = "32")]
pub const MAX_ARCHIVE: usize = 0x8000_0000;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Error {
    /// The member is encrypted or uses a compression method other than
    /// stored, DEFLATE and Zstandard.
    Unsupported,
    /// The member declares more data than the caller's limit.
    TooLarge,
    /// The data is not what the archive declares: it does not decompress,
    /// or not to the declared length, or not to the declared CRC-32.
    BadData,
}

fn zeros(n: usize) -> (v: Vec<u8>)
    ensures
        v@.len() == n,
{
    let mut v: Vec<u8> = Vec::new();
    v.resize(n, 0u8);
    v
}

/// **Reads a member's data.** `Ok` exactly with `entry_data`, which is
/// exactly `e.size` bytes long: nothing is ever returned (or allocated)
/// past the declared size, and a member whose data would be longer or
/// shorter than it declares is an error. At most `limit` bytes.
pub fn read_entry(b: &[u8], e: &Entry, limit: usize) -> (r: Result<Vec<u8>, Error>)
    requires
        e.data_off + e.csize <= b@.len(),
        b@.len() < MAX_ARCHIVE,
        limit <= MAX_ARCHIVE,
    ensures
        match r {
            Ok(v) => entry_data(b@, e.sv()) == Some(v@) && v@.len() == e.size && v@.len() <= limit,
            Err(Error::Unsupported) => entry_data(b@, e.sv()) is None && (e.encrypted || (e.method != 0 && e.method != 8
                && e.method != 93)),
            Err(Error::TooLarge) => e.size > limit,
            Err(Error::BadData) => entry_data(b@, e.sv()) is None,
        },
{
    if e.encrypted || (e.method != 0 && e.method != 8 && e.method != 93) {
        return Err(Error::Unsupported);
    }
    if e.size > limit as u64 {
        return Err(Error::TooLarge);
    }
    let size = e.size as usize;
    let c = slice_subrange(b, e.data_off, e.data_off + e.csize);
    let v = if e.method == 0 {
        if e.csize != size {
            return Err(Error::BadData);
        }
        let mut v: Vec<u8> = Vec::new();
        v.extend_from_slice(c);
        proof {
            assert(v@ =~= c@);
        }
        v
    } else if e.method == 8 {
        // One byte more than declared, so that output running past the
        // declared size is seen and refused.
        let mut out = zeros(size + 1);
        let mut dec = verilith_zlib::wrap::Decompressor::new();
        match dec.decompress_into(verilith_zlib::wrap::Format::Raw, c, out.as_mut_slice()) {
            Ok((used, n)) => {
                if used != e.csize || n != size {
                    return Err(Error::BadData);
                }
                let ghost full = out@;
                out.truncate(size);
                proof {
                    assert(out@ =~= full.subrange(0, n as int));
                }
                out
            },
            Err(_) => {
                return Err(Error::BadData);
            },
        }
    } else {
        match verilith_zstd::frame::decompress_exec(c, size) {
            Ok(v) => {
                if v.len() != size {
                    return Err(Error::BadData);
                }
                v
            },
            Err(_) => {
                return Err(Error::BadData);
            },
        }
    };
    proof {
        assert(e.sv().end() == e.data_off + e.csize);
        assert(unpack(e.method as int, c@) == Some(v@));
    }
    if e.has_crc && verilith_core::checksum::crc32(v.as_slice()) != e.crc {
        return Err(Error::BadData);
    }
    Ok(v)
}

/// **A stored member's data, in place.** When this answers true, the
/// member's data is exactly the `e.size` bytes of the archive from
/// `e.data_off` on (and they have the declared CRC-32), so a caller can hand
/// out that part of the archive without copying it. False says nothing: use
/// `read_entry`.
pub fn stored_in_place(b: &[u8], e: &Entry, limit: usize) -> (r: bool)
    requires
        e.data_off + e.csize <= b@.len(),
        b@.len() < MAX_ARCHIVE,
    ensures
        r ==> e.size <= limit && e.size == e.csize && entry_data(b@, e.sv()) == Some(
            b@.subrange(e.data_off as int, e.data_off + e.size),
        ),
{
    if e.encrypted || e.method != 0 || e.size > limit as u64 || e.csize as u64 != e.size {
        return false;
    }
    let c = slice_subrange(b, e.data_off, e.data_off + e.csize);
    proof {
        assert(e.sv().end() == e.data_off + e.csize);
        assert(unpack(e.method as int, c@) == Some(c@));
    }
    !e.has_crc || verilith_core::checksum::crc32(c) == e.crc
}

} // verus!

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Unsupported => "the member is encrypted or uses an unsupported compression method",
            Error::TooLarge => "the member is larger than the limit",
            Error::BadData => "the member's data does not match what the archive declares",
        })
    }
}

impl std::error::Error for Error {}
