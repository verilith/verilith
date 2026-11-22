//! Why a message was rejected.
//!
//! `parse` is verified and only says whether a message is well-formed. When
//! it is not, `try_parse` re-reads the message with the plain (unverified)
//! walk below to say where and why, following the same rules as
//! `spec::parse_message`. The walk only chooses the error to report: a
//! message is accepted, and its contents decided, by the verified parser
//! alone, so a mistake here can mislabel an error but never accept a
//! message or change one. `tests/errors.rs` checks the two agree on random
//! and mutated packets.
use alloc::vec::Vec;
use crate::message::Message;
use core::fmt;

/// What is wrong with a rejected message.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// Shorter than the 12-byte header.
    ShortHeader,
    /// The input ends inside a name, a fixed field or a record's RDATA.
    Truncated,
    /// A label type 0b01 or 0b10 (RFC 1035 §4.1.4 reserves them).
    ReservedLabelType,
    /// A compression pointer to an offset at or after the start of the
    /// current run of labels, so not a prior occurrence (RFC 1035 §4.1.4,
    /// RFC 9267 §2). This includes every pointer loop.
    PointerNotPrior,
    /// A compression pointer to another pointer (RFC 9267 §2).
    PointerToPointer,
    /// A name longer than 255 octets once decompressed (RFC 1035 §2.3.4,
    /// RFC 9267 §3).
    NameTooLong,
    /// RDATA of a type with names in it (NS, CNAME, SOA, PTR, MX, SIG, SRV,
    /// NAPTR) that does not decode as that type (RFC 9267 §5), or that is
    /// longer than 65535 octets once its names are decompressed.
    BadRdata,
    /// Bytes after the last record the counts describe (RFC 9267 §6).
    TrailingBytes,
}

/// Where in which part of the message a rejected message goes wrong.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Part {
    Header,
    /// The question with this index.
    Question(usize),
    /// The record with this index in the answer, authority or additional
    /// section.
    Answer(usize),
    Authority(usize),
    Additional(usize),
    /// After the last record.
    End,
}

/// A rejected message: what is wrong, where (byte offset), and in which
/// part.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Error {
    pub kind: ErrorKind,
    /// Offset of the byte that breaks the rule (for a name, the label or
    /// pointer at fault, which may be in an earlier part of the message).
    pub offset: usize,
    pub part: Part,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::ShortHeader => "message shorter than the 12-byte header",
            ErrorKind::Truncated => "message ends early",
            ErrorKind::ReservedLabelType => "reserved label type",
            ErrorKind::PointerNotPrior => "compression pointer does not point to a prior name",
            ErrorKind::PointerToPointer => "compression pointer points to another pointer",
            ErrorKind::NameTooLong => "name longer than 255 octets",
            ErrorKind::BadRdata => "RDATA does not decode as its type",
            ErrorKind::TrailingBytes => "bytes after the last record",
        };
        write!(f, "{what} at offset {} ({:?})", self.offset, self.part)
    }
}

impl core::error::Error for Error {}

/// Parses a message, saying why when it is rejected. Accepts exactly what
/// `parse` accepts.
pub fn try_parse(b: &[u8]) -> Result<Message, Error> {
    match crate::parse(b) {
        Some(m) => Ok(m),
        None => Err(diagnose(b)),
    }
}

impl TryFrom<&[u8]> for Message {
    type Error = Error;

    fn try_from(b: &[u8]) -> Result<Message, Error> {
        try_parse(b)
    }
}

fn be16(b: &[u8], p: usize) -> Option<usize> {
    Some(((*b.get(p)? as usize) << 8) | *b.get(p + 1)? as usize)
}

/// Reads the name at `pos` with the rules of `spec::parse_name`, returning
/// the offset where the message continues or what is wrong and where.
pub(crate) fn name_error(b: &[u8], pos: usize) -> Result<usize, (ErrorKind, usize)> {
    let (mut p, mut seg) = (pos, pos);
    let mut end = None;
    let mut wire = 1;
    loop {
        let c = *b.get(p).ok_or((ErrorKind::Truncated, p))?;
        if c == 0 {
            return Ok(end.unwrap_or(p + 1));
        } else if c >= 0xC0 {
            let lo = *b.get(p + 1).ok_or((ErrorKind::Truncated, p))?;
            let t = ((c as usize & 0x3F) << 8) | lo as usize;
            if t >= seg {
                return Err((ErrorKind::PointerNotPrior, p));
            }
            if b[t] >= 64 {
                return Err((ErrorKind::PointerToPointer, p));
            }
            end.get_or_insert(p + 2);
            p = t;
            seg = t;
        } else if c >= 64 {
            return Err((ErrorKind::ReservedLabelType, p));
        } else {
            if p + 1 + c as usize > b.len() {
                return Err((ErrorKind::Truncated, p));
            }
            wire += 1 + c as usize;
            if wire > 255 {
                return Err((ErrorKind::NameTooLong, p));
            }
            p += 1 + c as usize;
        }
    }
}

/// Why `parse` rejects `b`, following `spec::parse_message`.
pub(crate) fn diagnose(b: &[u8]) -> Error {
    let err = |kind, offset, part| Error { kind, offset, part };
    if b.len() < 12 {
        return err(ErrorKind::ShortHeader, b.len(), Part::Header);
    }
    let counts = [be16(b, 4).unwrap(), be16(b, 6).unwrap(), be16(b, 8).unwrap(), be16(b, 10).unwrap()];
    let mut p = 12;
    for (s, &n) in counts.iter().enumerate() {
        for i in 0..n {
            let part = match s {
                0 => Part::Question(i),
                1 => Part::Answer(i),
                2 => Part::Authority(i),
                _ => Part::Additional(i),
            };
            p = match name_error(b, p) {
                Ok(e) => e,
                Err((kind, at)) => return err(kind, at, part),
            };
            let fixed = if s == 0 { 4 } else { 10 };
            if b.len() - p < fixed {
                return err(ErrorKind::Truncated, b.len(), part);
            }
            if s > 0 {
                let rdlen = be16(b, p + 8).unwrap();
                if b.len() - (p + 10) < rdlen {
                    return err(ErrorKind::Truncated, b.len(), part);
                }
                let t = be16(b, p).unwrap() as u16;
                let mut c = Vec::new();
                if crate::parse::is_compressible(t)
                    && (!crate::rdata::canon_into(b, t, p + 10, p + 10 + rdlen, &mut c) || c.len() > 65535)
                {
                    return err(ErrorKind::BadRdata, p + 10, part);
                }
                p += rdlen;
            }
            p += fixed;
        }
    }
    // The walk found nothing wrong before the end, so what is left over is
    // the problem: `parse` accepts exactly the messages whose records end at
    // the last byte.
    err(ErrorKind::TrailingBytes, p, Part::End)
}
