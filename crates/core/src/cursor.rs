//! A bounds-checked reader over a byte slice.
//!
//! A `Cursor` is a slice and a position in it. Every read either succeeds,
//! returning the bytes at the position and moving past them, or fails
//! because too few bytes are left, leaving the cursor where it was. The
//! spec view is the whole buffer (`data`), the position (`pos`) and the
//! bytes not yet read (`rest`).
use crate::bytes::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub struct Cursor<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    /// The whole buffer, including what has been read.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.buf@
    }

    /// How many bytes have been read.
    pub closed spec fn pos(&self) -> int {
        self.pos as int
    }

    /// The bytes not yet read.
    pub open spec fn rest(&self) -> Seq<u8> {
        self.data().subrange(self.pos(), self.data().len() as int)
    }

    pub closed spec fn wf(&self) -> bool {
        self.pos <= self.buf@.len()
    }

    /// `self` is `old` moved forward `n` bytes.
    pub open spec fn advanced(&self, old: &Cursor<'a>, n: int) -> bool {
        &&& self.wf()
        &&& self.data() == old.data()
        &&& self.pos() == old.pos() + n
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            0 <= self.pos() <= self.data().len(),
            self.rest().len() == self.data().len() - self.pos(),
    {
    }

    /// A cursor at the start of `buf`.
    #[inline(always)]
    pub fn new(buf: &'a [u8]) -> (r: Cursor<'a>)
        ensures
            r.wf(),
            r.data() == buf@,
            r.pos() == 0,
            r.rest() == buf@,
    {
        let r = Cursor { buf, pos: 0 };
        proof {
            assert(r.rest() =~= buf@);
        }
        r
    }

    /// A cursor at `pos` in `buf`, or `None` if `pos` is past the end.
    #[inline(always)]
    pub fn new_at(buf: &'a [u8], pos: usize) -> (r: Option<Cursor<'a>>)
        ensures
            r is Some <==> pos <= buf@.len(),
            r matches Some(c) ==> c.wf() && c.data() == buf@ && c.pos() == pos,
    {
        if pos <= buf.len() {
            Some(Cursor { buf, pos })
        } else {
            None
        }
    }

    /// The whole buffer.
    #[inline(always)]
    pub fn buffer(&self) -> (r: &'a [u8])
        ensures
            r@ == self.data(),
    {
        self.buf
    }

    #[inline(always)]
    pub fn position(&self) -> (r: usize)
        ensures
            r == self.pos(),
    {
        self.pos
    }

    #[inline(always)]
    pub fn remaining(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.rest().len(),
    {
        self.buf.len() - self.pos
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.rest().len() == 0),
    {
        self.pos == self.buf.len()
    }

    /// The next byte, without reading it.
    #[inline(always)]
    pub fn peek_u8(&self) -> (r: Option<u8>)
        requires
            self.wf(),
        ensures
            r is Some <==> self.rest().len() >= 1,
            r matches Some(x) ==> x == self.rest()[0],
    {
        if self.pos < self.buf.len() {
            Some(self.buf[self.pos])
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn read_u8(&mut self) -> (r: Option<u8>)
        requires
            old(self).wf(),
        ensures
            r is Some <==> old(self).rest().len() >= 1,
            r matches Some(x) ==> x == old(self).rest()[0] && final(self).advanced(old(self), 1),
            r is None ==> *final(self) == *old(self),
    {
        if self.pos < self.buf.len() {
            let x = self.buf[self.pos];
            self.pos = self.pos + 1;
            Some(x)
        } else {
            None
        }
    }

    /// A big-endian `u16`.
    #[inline(always)]
    pub fn read_u16_be(&mut self) -> (r: Option<u16>)
        requires
            old(self).wf(),
        ensures
            r is Some <==> old(self).rest().len() >= 2,
            r matches Some(x) ==> x as nat == be16(old(self).rest(), 0) && final(self).advanced(
                old(self),
                2,
            ),
            r matches Some(x) ==> parse_u16(old(self).data(), old(self).pos()) == Some(
                (x, final(self).pos()),
            ),
            r is None ==> *final(self) == *old(self),
    {
        if self.buf.len() - self.pos >= 2 {
            let p = self.pos;
            let x = (self.buf[p] as u16) * 256 + self.buf[p + 1] as u16;
            self.pos = p + 2;
            Some(x)
        } else {
            None
        }
    }

    /// A big-endian `u32`.
    #[inline(always)]
    pub fn read_u32_be(&mut self) -> (r: Option<u32>)
        requires
            old(self).wf(),
        ensures
            r is Some <==> old(self).rest().len() >= 4,
            r matches Some(x) ==> x as nat == be32(old(self).rest(), 0) && final(self).advanced(
                old(self),
                4,
            ),
            r matches Some(x) ==> parse_u32(old(self).data(), old(self).pos()) == Some(
                (x, final(self).pos()),
            ),
            r is None ==> *final(self) == *old(self),
    {
        if self.buf.len() - self.pos >= 4 {
            let p = self.pos;
            let x = (self.buf[p] as u32) * 0x100_0000 + (self.buf[p + 1] as u32) * 0x1_0000
                + (self.buf[p + 2] as u32) * 256 + self.buf[p + 3] as u32;
            self.pos = p + 4;
            Some(x)
        } else {
            None
        }
    }

    /// The next `n` bytes.
    #[inline(always)]
    pub fn take(&mut self, n: usize) -> (r: Option<&'a [u8]>)
        requires
            old(self).wf(),
        ensures
            r is Some <==> n <= old(self).rest().len(),
            r matches Some(s) ==> s@ == old(self).rest().subrange(0, n as int),
            r is Some ==> final(self).advanced(old(self), n as int),
            r is None ==> *final(self) == *old(self),
    {
        if n <= self.buf.len() - self.pos {
            let p = self.pos;
            let s = slice_subrange(self.buf, p, p + n);
            self.pos = p + n;
            proof {
                assert(s@ =~= old(self).rest().subrange(0, n as int));
            }
            Some(s)
        } else {
            None
        }
    }

    /// Moves past the next `n` bytes; false (and no move) if fewer are left.
    #[inline(always)]
    pub fn skip(&mut self, n: usize) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            r == (n <= old(self).rest().len()),
            r ==> final(self).advanced(old(self), n as int),
            !r ==> *final(self) == *old(self),
    {
        if n <= self.buf.len() - self.pos {
            self.pos = self.pos + n;
            true
        } else {
            false
        }
    }

    /// The bytes from `start` (which may be before the position) to the
    /// position, e.g. to recover a field's encoding after parsing it.
    #[inline(always)]
    pub fn slice_from(&self, start: usize) -> (r: Option<&'a [u8]>)
        requires
            self.wf(),
        ensures
            r is Some <==> start <= self.pos(),
            r matches Some(s) ==> s@ == self.data().subrange(start as int, self.pos()),
    {
        if start <= self.pos {
            Some(slice_subrange(self.buf, start, self.pos))
        } else {
            None
        }
    }

    /// A cursor over the next `n` bytes alone, and `self` moved past them:
    /// how a length-prefixed field (a DER TLV, a DNS RDATA) is parsed.
    #[inline(always)]
    pub fn split(&mut self, n: usize) -> (r: Option<Cursor<'a>>)
        requires
            old(self).wf(),
        ensures
            r is Some <==> n <= old(self).rest().len(),
            r matches Some(c) ==> c.wf() && c.pos() == 0 && c.data() == old(self).rest().subrange(
                0,
                n as int,
            ) && final(self).advanced(old(self), n as int),
            r is None ==> *final(self) == *old(self),
    {
        match self.take(n) {
            Some(s) => Some(Cursor::new(s)),
            None => None,
        }
    }
}

} // verus!
