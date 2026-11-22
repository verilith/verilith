//! The Rust API: an archive held in memory.
//!
//! This file is plain Rust that composes the verified pieces: it strips an
//! outer gzip or Zstandard layer (with vzlib and vzstd), calls
//! `reader::parse`, and passes the caller's requests to `read::read_entry`
//! and `plan::plan`. It is listed in TRUST.md.
use crate::plan::{Item, Rejected};
use crate::read::{read_entry, stored_in_place, Error};
use std::borrow::Cow;
use crate::reader::{parse, Format};
use crate::zip::Entry;

/// Most bytes any one decompression may produce unless the caller says
/// otherwise: 1 GiB.
pub const DEFAULT_LIMIT: usize = 1 << 30;

/// The proofs cover archives below this size (256 TiB).
const MAX_ARCHIVE: usize = 0x1_0000_0000_0000;

/// The compression around the whole archive.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Filter {
    None,
    Gzip,
    Zstd,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum OpenError {
    /// Neither a zip nor a tar archive.
    NotAnArchive,
    /// The outer gzip or Zstandard layer is corrupt.
    BadCompression,
    /// The archive, or what its outer layer decompresses to, is over the
    /// limit.
    TooLarge,
}

/// An open archive. It borrows the caller's bytes when they are not
/// compressed as a whole, and owns the decompressed bytes otherwise.
pub struct Archive<'a> {
    data: Cow<'a, [u8]>,
    format: Format,
    filter: Filter,
    entries: Vec<Entry>,
    limit: usize,
}

fn gunzip(input: &[u8], limit: usize) -> Result<Vec<u8>, OpenError> {
    let mut out: Vec<u8> = Vec::new();
    let mut rest = input;
    let mut dec = verilith_zlib::wrap::Decompressor::new();
    // A gzip file is one or more members; zero padding may follow.
    while rest.len() >= 2 && rest[0] == 0x1f && rest[1] == 0x8b {
        match dec.decompress_vec(verilith_zlib::wrap::Format::Gzip, rest, limit - out.len()) {
            Ok((v, used)) => {
                if out.is_empty() {
                    out = v;
                } else {
                    out.extend_from_slice(&v);
                }
                rest = &rest[used..];
            }
            Err(verilith_zlib::wrap::Error::InsufficientSpace) => return Err(OpenError::TooLarge),
            Err(_) => return Err(OpenError::BadCompression),
        }
    }
    Ok(out)
}

impl<'a> Archive<'a> {
    /// Opens the archive `input`, which may be wrapped in gzip or
    /// Zstandard (`.tar.gz`, `.tar.zst`).
    pub fn open(input: &'a [u8]) -> Result<Archive<'a>, OpenError> {
        Archive::open_with_limit(input, DEFAULT_LIMIT)
    }

    /// As `open`. `limit` bounds the size of the outer layer's output and
    /// of each member read.
    pub fn open_with_limit(input: &'a [u8], limit: usize) -> Result<Archive<'a>, OpenError> {
        let limit = limit.min(MAX_ARCHIVE - 1);
        if input.len() >= MAX_ARCHIVE {
            return Err(OpenError::TooLarge);
        }
        let (data, filter) = if input.len() >= 2 && input[0] == 0x1f && input[1] == 0x8b {
            (Cow::Owned(gunzip(input, limit)?), Filter::Gzip)
        } else if input.len() >= 4 && input[..4] == [0x28, 0xb5, 0x2f, 0xfd] {
            match verilith_zstd::frame::decompress_exec(input, limit) {
                Ok(v) => (Cow::Owned(v), Filter::Zstd),
                Err(verilith_zstd::frame::Error::TooLarge) => return Err(OpenError::TooLarge),
                Err(_) => return Err(OpenError::BadCompression),
            }
        } else {
            (Cow::Borrowed(input), Filter::None)
        };
        match parse(&data) {
            Some((format, entries)) => Ok(Archive { data, format, filter, entries, limit }),
            None => Err(OpenError::NotAnArchive),
        }
    }

    pub fn format(&self) -> Format {
        self.format
    }

    pub fn filter(&self) -> Filter {
        self.filter
    }

    /// The members, in archive order.
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// The archive's bytes, with any outer compression removed.
    pub fn bytes(&self) -> &[u8] {
        &self.data
    }

    /// Member `i`'s data: exactly its declared size, checked against its
    /// CRC-32 where the format has one.
    pub fn read(&self, i: usize) -> Result<Vec<u8>, Error> {
        read_entry(&self.data, &self.entries[i], self.limit)
    }

    /// As `read`, without copying a member that is stored uncompressed:
    /// its data is then a part of the archive itself (checked against its
    /// CRC-32 first, as always).
    pub fn read_ref(&self, i: usize) -> Result<Cow<'_, [u8]>, Error> {
        let e = &self.entries[i];
        if stored_in_place(&self.data, e, self.limit) {
            Ok(Cow::Borrowed(&self.data[e.data_off..e.data_off + e.size as usize]))
        } else {
            self.read(i).map(Cow::Owned)
        }
    }

    /// The archive as one that owns its bytes.
    pub fn into_owned(self) -> Archive<'static> {
        Archive { data: Cow::Owned(self.data.into_owned()), format: self.format, filter: self.filter, entries: self.entries, limit: self.limit }
    }

    /// The extraction plan, or why the archive is not safe to extract.
    pub fn plan(&self) -> Result<Vec<Item>, Rejected> {
        crate::plan::plan(&self.data, &self.entries)
    }
}
