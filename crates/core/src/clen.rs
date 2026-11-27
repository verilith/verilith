//! A message body checked against its declared Content-Length, as HTTP/2
//! and HTTP/3 require of a request (RFC 9113 §8.1.1, RFC 9114 §4.1.2;
//! RFC 9110 §8.6): the DATA a stream carries must add up to exactly the
//! length its fields declare.
//!
//! [`BodyLen`] counts the body bytes received and remembers the length
//! declared. Its invariant is that, once a length is declared, the bytes
//! received never pass it: [`BodyLen::declare`] refuses a length below
//! what already arrived, or one that differs from an earlier declaration,
//! and [`BodyLen::add`] refuses bytes that would go past it. At the end of
//! the body, [`BodyLen::complete`] says whether the two are equal. Parsing
//! the field value is the caller's: verilith-http's
//! `framing::content_length_exec` is the verified parser.
use vstd::prelude::*;

verus! {

/// The body bytes a message has carried so far, and the Content-Length it
/// declared.
#[derive(Clone, Copy)]
pub struct BodyLen {
    declared: Option<u64>,
    got: u64,
}

impl BodyLen {
    /// The length declared, if any.
    pub closed spec fn declared(&self) -> Option<u64> {
        self.declared
    }

    /// Body bytes received.
    pub closed spec fn got(&self) -> nat {
        self.got as nat
    }

    /// The invariant: never more bytes than the length declared.
    pub open spec fn inv(&self) -> bool {
        self.declared() matches Some(d) ==> self.got() <= d as nat
    }

    /// The body is complete as declared: no length was declared, or
    /// exactly that many bytes arrived.
    pub open spec fn complete_s(&self) -> bool {
        self.declared() matches Some(d) ==> self.got() == d as nat
    }

    /// No length declared, no bytes received.
    pub fn new() -> (r: BodyLen)
        ensures
            r.inv(),
            r.declared() is None,
            r.got() == 0,
    {
        BodyLen { declared: None, got: 0 }
    }

    /// The fields declare a length of `n`: false (and nothing changes) if
    /// a different length was declared before, or more than `n` bytes
    /// already arrived.
    #[inline(always)]
    pub fn declare(&mut self, n: u64) -> (ok: bool)
        ensures
            ok == ((old(self).declared() is None || old(self).declared() == Some(n)) && old(self).got() <= n as nat),
            ok ==> final(self).declared() == Some(n),
            !ok ==> *final(self) == *old(self),
            final(self).got() == old(self).got(),
            old(self).inv() ==> final(self).inv(),
    {
        match self.declared {
            Some(d) => {
                if d != n {
                    return false;
                }
            },
            None => {},
        }
        if self.got > n {
            return false;
        }
        self.declared = Some(n);
        true
    }

    /// `n` more body bytes: false (and nothing changes) if they would go
    /// past the length declared, or past `u64::MAX`.
    #[inline(always)]
    pub fn add(&mut self, n: u64) -> (ok: bool)
        ensures
            ok == (old(self).got() + n <= u64::MAX as nat && (old(self).declared() matches Some(d)
                ==> old(self).got() + n <= d as nat)),
            ok ==> final(self).got() == old(self).got() + n,
            !ok ==> *final(self) == *old(self),
            final(self).declared() == old(self).declared(),
            old(self).inv() ==> final(self).inv(),
    {
        if n > u64::MAX - self.got {
            return false;
        }
        let g = self.got + n;
        match self.declared {
            Some(d) => {
                if g > d {
                    return false;
                }
            },
            None => {},
        }
        self.got = g;
        true
    }

    /// Whether the body is complete as declared ([`Self::complete_s`]).
    #[inline(always)]
    pub fn complete(&self) -> (r: bool)
        ensures
            r == self.complete_s(),
    {
        match self.declared {
            Some(d) => d == self.got,
            None => true,
        }
    }

    /// Body bytes received.
    #[inline(always)]
    pub fn received(&self) -> (r: u64)
        ensures
            r as nat == self.got(),
    {
        self.got
    }
}

} // verus!
