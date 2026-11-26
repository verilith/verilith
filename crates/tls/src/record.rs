//! Record and handshake message headers (§5.1, §4), proven to read exactly
//! `spec::record_header` and `spec::handshake_message`.
use crate::hello::Span;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// A record header (§5.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RecordHeader {
    pub content_type: u8,
    pub legacy_version: u16,
    /// The length of the fragment that follows.
    pub length: usize,
}

impl RecordHeader {
    pub open spec fn models(self, s: SpecRecordHeader) -> bool {
        self.content_type == s.content_type && self.legacy_version == s.legacy_version
            && self.length as nat == s.length
    }

    /// The header at the start of `b`, or `None` if `b` is shorter than
    /// one.
    #[inline(always)]
    pub fn parse(b: &[u8]) -> (r: Option<RecordHeader>)
        ensures
            r is None ==> record_header(b@) is None,
            r matches Some(h) ==> record_header(b@) matches Some(s) && h.models(s),
    {
        if b.len() < 5 {
            return None;
        }
        let v = (b[1] as u16) * 256 + b[2] as u16;
        let l = (b[3] as usize) * 256 + b[4] as usize;
        proof {
            assert(v == be16(b@, 1) as u16);
        }
        Some(RecordHeader { content_type: b[0], legacy_version: v, length: l })
    }
}

/// The handshake message at the start of `b` (§4): its type and the span
/// of its body, or `None` if `b` does not hold all of it yet.
#[inline(always)]
pub fn handshake_message_x(b: &[u8]) -> (r: Option<(u8, Span)>)
    ensures
        r is None ==> handshake_message(b@) is None,
        r matches Some((t, sp)) ==> handshake_message(b@) == Some((t, sp@)) && sp.start <= sp.end
            <= b@.len(),
{
    if b.len() < 4 {
        return None;
    }
    let l = ((b[1] as usize) * 256 + b[2] as usize) * 256 + b[3] as usize;
    if l > b.len() - 4 {
        return None;
    }
    Some((b[0], Span { start: 4, end: 4 + l }))
}

/// The length a handshake message's header announces, which a caller
/// buffering a message needs before the message is complete.
#[inline(always)]
pub fn handshake_length(b: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(l) ==> b@.len() >= 4 && l as nat == be24(b@, 1),
        r is None ==> b@.len() < 4,
{
    if b.len() < 4 {
        return None;
    }
    Some(((b[1] as usize) * 256 + b[2] as usize) * 256 + b[3] as usize)
}

} // verus!
