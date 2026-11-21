//! Ergonomic, unverified helpers over the verified core: a borrowed view of
//! wire-form names and iterators. Presentation-format conversion delegates
//! to the verified `text` module.
//!
//! Nothing here touches untrusted input except through the verified parser.
//! Every function is panic-free on any input: they use checked slicing only.
use alloc::vec::Vec;
use alloc::string::String;
use crate::message::{BuildError, Message, QuestionRef, RecordRef, Section};
use core::fmt;

/// A domain name in uncompressed wire form, borrowed from a `Message`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Name<'a>(&'a [u8]);

impl<'a> Name<'a> {
    /// Wraps uncompressed wire-form bytes. Names obtained from a `Message`
    /// are always valid; other bytes are read leniently (iteration stops at
    /// the first malformed label).
    pub fn from_wire(wire: &'a [u8]) -> Self {
        Name(wire)
    }

    /// The uncompressed wire form, including the root octet.
    pub fn as_wire(&self) -> &'a [u8] {
        self.0
    }

    /// The labels, without the root label.
    pub fn labels(&self) -> Labels<'a> {
        Labels(self.0)
    }

    /// Whether this is the root name.
    pub fn is_root(&self) -> bool {
        self.0.first().is_none_or(|&c| c == 0)
    }

    /// Case-insensitive comparison (RFC 4343).
    pub fn eq_ignore_case(&self, other: &Name<'_>) -> bool {
        self.0.eq_ignore_ascii_case(other.0)
    }

    /// Appends the presentation form to `out`, escaped as c-ares does:
    /// labels joined by `.`, `"().;@$\` backslash-escaped, non-printable
    /// bytes as `\DDD`, and the root name as the empty string. For a
    /// well-formed name (every name from a `Message`) this is the verified
    /// `text::write_text`; other bytes are printed leniently, up to the first
    /// malformed label.
    pub fn write_presentation(&self, out: &mut Vec<u8>) {
        if !crate::text::write_text(self.0, out) {
            self.write_lenient(out);
        }
    }

    fn write_lenient(&self, out: &mut Vec<u8>) {
        for (i, label) in self.labels().enumerate() {
            if i > 0 {
                out.push(b'.');
            }
            for &c in label {
                if !(0x20..=0x7e).contains(&c) {
                    out.extend_from_slice(&[b'\\', b'0' + c / 100, b'0' + (c % 100) / 10, b'0' + c % 10]);
                } else {
                    if matches!(c, b'"' | b'.' | b';' | b'\\' | b'(' | b')' | b'@' | b'$') {
                        out.push(b'\\');
                    }
                    out.push(c);
                }
            }
        }
    }
}

impl fmt::Display for Name<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut v = Vec::with_capacity(self.0.len());
        self.write_presentation(&mut v);
        f.write_str(&String::from_utf8_lossy(&v))?;
        f.write_str(".")
    }
}

impl fmt::Debug for Name<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Name({self})")
    }
}

/// Iterator over a name's labels.
#[derive(Clone)]
pub struct Labels<'a>(&'a [u8]);

impl<'a> Iterator for Labels<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        let (&len, rest) = self.0.split_first()?;
        if len == 0 || len >= 64 {
            self.0 = &[];
            return None;
        }
        let label = rest.get(..len as usize)?;
        self.0 = &rest[len as usize..];
        Some(label)
    }
}

/// Converts a presentation-format name (`www.example.com`, with an optional
/// trailing dot and `\.`/`\DDD` escapes) to uncompressed wire form. This is
/// the verified `text::parse_text`.
pub fn encode_name(s: &str) -> Result<Vec<u8>, BuildError> {
    crate::text::parse_text(s.as_bytes()).map(|(v, _)| v).ok_or(BuildError::BadName)
}

impl<'a> QuestionRef<'a> {
    pub fn name(&self) -> Name<'a> {
        Name(self.name)
    }
}

impl<'a> RecordRef<'a> {
    pub fn name(&self) -> Name<'a> {
        Name(self.name)
    }
}

impl Message {
    /// The questions, in order.
    pub fn questions(&self) -> impl ExactSizeIterator<Item = QuestionRef<'_>> + '_ {
        Questions { m: self, i: 0, n: self.question_count() }
    }

    /// The records of section `s`, in order.
    pub fn records(&self, s: Section) -> impl ExactSizeIterator<Item = RecordRef<'_>> + '_ {
        Records { m: self, s, i: 0, n: self.record_count(s) }
    }

    pub fn answers(&self) -> impl ExactSizeIterator<Item = RecordRef<'_>> + '_ {
        self.records(Section::Answer)
    }

    pub fn authorities(&self) -> impl ExactSizeIterator<Item = RecordRef<'_>> + '_ {
        self.records(Section::Authority)
    }

    pub fn additionals(&self) -> impl ExactSizeIterator<Item = RecordRef<'_>> + '_ {
        self.records(Section::Additional)
    }

    /// Adds a question, with the name in presentation format.
    pub fn push_question(&mut self, name: &str, qtype: u16, qclass: u16) -> Result<(), BuildError> {
        self.add_question(&encode_name(name)?, qtype, qclass)
    }

    /// Adds a record, with the name in presentation format.
    pub fn push_record(
        &mut self,
        s: Section,
        name: &str,
        rtype: u16,
        rclass: u16,
        ttl: u32,
        rdata: &[u8],
    ) -> Result<(), BuildError> {
        self.add_record(s, &encode_name(name)?, rtype, rclass, ttl, rdata)
    }
}

struct Records<'a> {
    m: &'a Message,
    s: Section,
    i: usize,
    n: usize,
}

impl<'a> Iterator for Records<'a> {
    type Item = RecordRef<'a>;

    fn next(&mut self) -> Option<RecordRef<'a>> {
        if self.i >= self.n {
            return None;
        }
        self.i += 1;
        self.m.record(self.s, self.i - 1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n - self.i, Some(self.n - self.i))
    }
}

impl ExactSizeIterator for Records<'_> {}

struct Questions<'a> {
    m: &'a Message,
    i: usize,
    n: usize,
}

impl<'a> Iterator for Questions<'a> {
    type Item = QuestionRef<'a>;

    fn next(&mut self) -> Option<QuestionRef<'a>> {
        if self.i >= self.n {
            return None;
        }
        self.i += 1;
        self.m.question(self.i - 1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n - self.i, Some(self.n - self.i))
    }
}

impl ExactSizeIterator for Questions<'_> {}
