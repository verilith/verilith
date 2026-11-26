//! The HTTP/1.1 output, verified: the byte queue a connection writes
//! from ([`Out`]), and the ledger of responses on it ([`Wire`],
//! [`Engine`]).
//!
//! [`Out`] holds owned bytes with shared bodies (static files, cached
//! responses) spliced in without a copy. Its ghost `wire` is every byte
//! queued, in order; `slices`, `slices_io` and `advance` are proven to hand
//! the event loop exactly the unwritten rest of it, in order, and to move
//! past exactly what was written.
//!
//! [`Engine`] joins the verified request core ([`crate::conn::Core`]) and
//! the output. Its invariant is the response-order theorem: the bytes
//! queued are the responses, back to back, one per request the core has
//! handed out and in that order (and at most one error response after the
//! last one, for a request the core rejected); each response head is one
//! `respond::theorem_head_parses` covers, framed by its true body length
//! (no body for HEAD, 1xx, 204 and 304); and a response that lists the
//! connection option `close` is the last one, while every close the
//! server decides itself is announced by `Connection: close` in the
//! response before it.
use vstd::prelude::*;
use std::sync::Arc;
use std::collections::VecDeque;
use std::marker::PhantomData;
use crate::conn::{Core, Ev, Phase};
use crate::respond::{self, Field, Framing, Prepared, SField};
#[cfg(verus_keep_ghost)]
use crate::respond::{fields_view, head, status_ok, reason_ok, fields_ok, framing_ok, conn_close};
use crate::persist::fields_close_exec;
#[cfg(verus_keep_ghost)]
use crate::persist::fields_close;
#[cfg(verus_keep_ghost)]
use crate::conn::first;
#[cfg(verus_keep_ghost)]
use verilith_http::parse::{hdr_ok, hdrs_ok, headers_view};
use verilith_http::framing::ci_eq_exec;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::ci_eq;
use vstd::slice::slice_subrange;

verus! {


/// A file descriptor, closed on drop (the Drop impl is sys's).
#[derive(Debug)]
pub struct Fd(pub i32);

/// A shared body, or a range of one.
pub struct Seg {
    pub a: Arc<[u8]>,
    pub off: usize,
    pub len: usize,
    /// A sealed file holding exactly `a`, to `sendfile` from (trusted:
    /// TRUST.md, a sealed memfd's contents cannot change).
    pub file: Option<Arc<Fd>>,
}

impl Seg {
    pub open spec fn wf(&self) -> bool {
        self.off + self.len <= (*self.a)@.len()
    }

    pub open spec fn view(&self) -> Seq<u8> {
        (*self.a)@.subrange(self.off as int, self.off + self.len)
    }

    fn bytes(&self) -> (r: &[u8])
        requires self.wf(),
        ensures r@ == self.view(),
    {
        let s: &[u8] = &self.a;
        let _n = s.len();
        vstd::slice::slice_subrange(s, self.off, self.off + self.len)
    }
}

/// What to write next: slices, or a range of a file.
pub enum Io<'a> {
    Slices(usize, PhantomData<&'a ()>),
    File { fd: i32, off: usize, len: usize },
}

/// The bytes still to write: `buf[p..at0] + seg0[off..] + buf[at0..at1] + seg1 + ... + buf[atk..]`.
pub open spec fn pend(buf: Seq<u8>, p: int, segs: Seq<(usize, Seg)>, off: int) -> Seq<u8>
    decreases segs.len(),
{
    if segs.len() == 0 {
        buf.subrange(p, buf.len() as int)
    } else {
        buf.subrange(p, segs[0].0 as int) + segs[0].1.view().subrange(off, segs[0].1.len as int)
            + pend(buf, segs[0].0 as int, segs.drop_first(), 0)
    }
}

/// The positions are in order and in bounds, each segment is well formed.
pub open spec fn segs_ok(n: int, p: int, segs: Seq<(usize, Seg)>, off: int) -> bool
    decreases segs.len(),
{
    if segs.len() == 0 {
        0 <= p <= n && off == 0
    } else {
        &&& 0 <= p <= segs[0].0
        &&& p < segs[0].0 ==> off == 0
        &&& 0 <= off <= segs[0].1.len
        &&& segs[0].1.wf()
        &&& segs_ok(n, segs[0].0 as int, segs.drop_first(), 0)
    }
}

proof fn lemma_skip(s: Seq<(usize, Seg)>, i: int)
    requires 0 <= i < s.len(),
    ensures s.skip(i)[0] == s[i], s.skip(i).drop_first() == s.skip(i + 1), s.skip(i).len() == s.len() - i,
{
    assert(s.skip(i).drop_first() =~= s.skip(i + 1));
}

proof fn lemma_pend_split(buf: Seq<u8>, p: int, segs: Seq<(usize, Seg)>, off: int, extra: Seq<u8>)
    requires segs_ok(buf.len() as int, p, segs, off),
    ensures pend(buf + extra, p, segs, off) == pend(buf, p, segs, off) + extra,
            segs_ok((buf + extra).len() as int, p, segs, off),
    decreases segs.len(),
{
    let b2 = buf + extra;
    if segs.len() == 0 {
        assert(b2.subrange(p, b2.len() as int) =~= buf.subrange(p, buf.len() as int) + extra);
    } else {
        lemma_pend_split(buf, segs[0].0 as int, segs.drop_first(), 0, extra);
        lemma_segs_le(buf.len() as int, segs[0].0 as int, segs.drop_first(), 0);
        assert(b2.subrange(p, segs[0].0 as int) =~= buf.subrange(p, segs[0].0 as int));
        assert(pend(b2, p, segs, off) =~= pend(buf, p, segs, off) + extra);
    }
}

proof fn lemma_segs_le(n: int, p: int, segs: Seq<(usize, Seg)>, off: int)
    requires segs_ok(n, p, segs, off),
    ensures p <= n,
    decreases segs.len(),
{
    if segs.len() > 0 {
        lemma_segs_le(n, segs[0].0 as int, segs.drop_first(), 0);
    }
}

/// Appending a segment at the end of the buffer.
proof fn lemma_push(buf: Seq<u8>, p: int, segs: Seq<(usize, Seg)>, off: int, s: Seg)
    requires segs_ok(buf.len() as int, p, segs, off), s.wf(), buf.len() <= usize::MAX,
    ensures
        segs_ok(buf.len() as int, p, segs.push((buf.len() as usize, s)), off),
        pend(buf, p, segs.push((buf.len() as usize, s)), off) == pend(buf, p, segs, off) + s.view(),
    decreases segs.len(),
{
    let t = (buf.len() as usize, s);
    if segs.len() == 0 {
        assert(segs.push(t).drop_first() =~= Seq::<(usize, Seg)>::empty());
        assert(buf.subrange(buf.len() as int, buf.len() as int) =~= Seq::<u8>::empty());
        assert(s.view().subrange(0, s.len as int) =~= s.view());
        assert(segs.push(t)[0] == t);
        assert(off == 0);
        let e = pend(buf, buf.len() as int, Seq::<(usize, Seg)>::empty(), 0);
        assert(e =~= Seq::<u8>::empty());
        assert(segs.push(t).drop_first() == Seq::<(usize, Seg)>::empty());
        assert(pend(buf, p, segs.push(t), off) == buf.subrange(p, buf.len() as int) + s.view().subrange(0, s.len as int) + e);
        assert(pend(buf, p, segs.push(t), off) =~= buf.subrange(p, buf.len() as int) + s.view());
        assert(t.0 as int == buf.len());
        assert(segs_ok(buf.len() as int, t.0 as int, segs.push(t).drop_first(), 0));
    } else {
        assert(segs.push(t).drop_first() =~= segs.drop_first().push(t));
        assert(segs.push(t)[0] == segs[0]);
        lemma_push(buf, segs[0].0 as int, segs.drop_first(), 0, s);
        let a = buf.subrange(p, segs[0].0 as int) + segs[0].1.view().subrange(off, segs[0].1.len as int);
        assert(pend(buf, p, segs.push(t), off) == a + pend(buf, segs[0].0 as int, segs.drop_first().push(t), 0));
        assert(pend(buf, p, segs, off) == a + pend(buf, segs[0].0 as int, segs.drop_first(), 0));
        assert(pend(buf, p, segs.push(t), off) =~= pend(buf, p, segs, off) + s.view());
        assert(segs_ok(buf.len() as int, segs[0].0 as int, segs.push(t).drop_first(), 0));
        lemma_segs_le(buf.len() as int, segs[0].0 as int, segs.drop_first(), 0);
    }
}

/// A connection's output: owned bytes, with shared bodies (static files,
/// cached responses) spliced in without a copy.
pub struct Out {
    pub buf: Vec<u8>,
    /// Shared bodies, each with the position in `buf` it follows.
    pub segs: VecDeque<(usize, Seg)>,
    /// Bytes of `buf` already written.
    pub pos: usize,
    /// Bytes of the front shared body already written.
    pub seg_off: usize,
    /// Bytes not yet written.
    pub queued: usize,
    /// Every byte queued since the connection began, and how many of them
    /// have been written.
    pub wire: Ghost<Seq<u8>>,
    pub sent: Ghost<nat>,
}

/// Bodies at least this long are sent from the shared buffer, not copied.
pub const SHARE_MIN: usize = 8 * 1024;

impl Out {
    /// The bytes not yet written, in order.
    pub open spec fn pending(&self) -> Seq<u8> {
        pend(self.buf@, self.pos as int, self.segs@, self.seg_off as int)
    }

    pub open spec fn inv(&self) -> bool {
        &&& segs_ok(self.buf@.len() as int, self.pos as int, self.segs@, self.seg_off as int)
        &&& self.queued == self.pending().len()
        &&& self.sent@ <= self.wire@.len()
        &&& self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) == self.pending()
    }

    pub fn new() -> (r: Out)
        ensures r.inv(), r.wire@.len() == 0,
    {
        let r = Out { buf: Vec::with_capacity(4096), segs: VecDeque::new(), pos: 0, seg_off: 0, queued: 0, wire: Ghost(Seq::empty()), sent: Ghost(0) };
        assert(r.pending() =~= Seq::<u8>::empty());
        r
    }

    /// An `Out` that has allocated nothing.
    pub fn empty() -> (r: Out)
        ensures r.inv(), r.wire@.len() == 0,
    {
        let r = Out { buf: Vec::new(), segs: VecDeque::new(), pos: 0, seg_off: 0, queued: 0, wire: Ghost(Seq::empty()), sent: Ghost(0) };
        assert(r.pending() =~= Seq::<u8>::empty());
        r
    }

    /// Forgets everything: a new connection.
    pub fn clear(&mut self)
        ensures final(self).inv(), final(self).wire@.len() == 0,
    {
        self.reset_bufs();
        self.wire = Ghost(Seq::empty());
        self.sent = Ghost(0);
        assert(self.buf@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(self.pending() =~= Seq::<u8>::empty());
        assert(self.wire@.subrange(0, 0) =~= Seq::<u8>::empty());
    }

    fn reset_bufs(&mut self)
        ensures final(self).buf@.len() == 0, final(self).segs@.len() == 0, final(self).pos == 0,
            final(self).seg_off == 0, final(self).queued == 0,
            final(self).wire == old(self).wire, final(self).sent == old(self).sent,
    {
        self.buf.clear();
        self.segs.clear();
        self.pos = 0;
        self.seg_off = 0;
        self.queued = 0;
    }

    /// Queues `b`.
    pub fn extend(&mut self, b: &[u8])
        requires old(self).inv(),
        ensures final(self).inv(), final(self).sent == old(self).sent,
            final(self).wire@ == old(self).wire@ + b@ || final(self).wire@ == old(self).wire@,
            old(self).queued + b@.len() <= usize::MAX ==> final(self).wire@ == old(self).wire@ + b@,
    {
        if b.len() > usize::MAX - self.queued {
            return;
        }
        let ghost b0 = self.buf@;
        let ghost w0 = self.wire@;
        proof { lemma_pend_split(b0, self.pos as int, self.segs@, self.seg_off as int, b@); }
        verilith_core::prims::extend(&mut self.buf, b);
        self.queued = self.queued + b.len();
        self.wire = Ghost(w0 + b@);
        proof {
            assert(self.buf@ =~= b0 + b@);
            assert(self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) =~= w0.subrange(self.sent@ as int, w0.len() as int) + b@);
        }
    }

    /// `buf` grew from `before` by bytes written into it directly.
    /// Trusted (TRUST.md): between the caller's reading `before` and this
    /// call, `buf` was only appended to.
    pub fn grew(&mut self, before: usize)
        requires
            before <= old(self).buf@.len(),
            old(self).inv_at(before as int),
        ensures
            final(self).inv(),
            final(self).sent == old(self).sent,
            final(self).wire@ == old(self).wire@ + old(self).buf@.subrange(before as int, old(self).buf@.len() as int)
                || final(self).wire@ == old(self).wire@,
            old(self).queued + (old(self).buf@.len() - before) <= usize::MAX ==>
                final(self).wire@ == old(self).wire@ + old(self).buf@.subrange(before as int, old(self).buf@.len() as int),
    {
        if self.buf.len() - before > usize::MAX - self.queued {
            // Cannot happen in practice (more bytes queued than memory):
            // drop the new bytes rather than lose count.
            self.buf.truncate(before);
            proof { assert(self.buf@ =~= old(self).buf@.subrange(0, before as int)); }
            return;
        }
        let ghost b0 = self.buf@.subrange(0, before as int);
        let ghost x = self.buf@.subrange(before as int, self.buf@.len() as int);
        let ghost w0 = self.wire@;
        proof {
            lemma_pend_split(b0, self.pos as int, self.segs@, self.seg_off as int, x);
            assert(b0 + x =~= self.buf@);
        }
        self.queued = self.queued + (self.buf.len() - before);
        self.wire = Ghost(w0 + x);
        proof {
            assert(self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) =~= w0.subrange(self.sent@ as int, w0.len() as int) + x);
        }
    }

    /// The invariant, of `buf[..n]`: what holds before bytes are written
    /// into `buf` directly.
    pub open spec fn inv_at(&self, n: int) -> bool {
        let b = self.buf@.subrange(0, n);
        let p = pend(b, self.pos as int, self.segs@, self.seg_off as int);
        &&& segs_ok(n, self.pos as int, self.segs@, self.seg_off as int)
        &&& self.queued == p.len()
        &&& self.sent@ <= self.wire@.len()
        &&& self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) == p
    }

    /// Queues `s`, shared.
    fn push_seg(&mut self, s: Seg)
        requires old(self).inv(), s.wf(),
        ensures final(self).inv(), final(self).sent == old(self).sent,
            final(self).wire@ == old(self).wire@ + s.view() || final(self).wire@ == old(self).wire@,
            old(self).queued + s.len <= usize::MAX ==> final(self).wire@ == old(self).wire@ + s.view(),
    {
        let ghost w0 = self.wire@;
        let ghost v = s.view();
        let _bl = self.buf.len();
        proof { lemma_push(self.buf@, self.pos as int, self.segs@, self.seg_off as int, s); }
        let n = s.len;
        if n > usize::MAX - self.queued {
            return;
        }
        self.segs.push_back((self.buf.len(), s));
        self.queued = self.queued + n;
        self.wire = Ghost(w0 + v);
        proof {
            assert(self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) =~= w0.subrange(self.sent@ as int, w0.len() as int) + v);
        }
    }
}


/// The bytes of slices, back to back.
pub open spec fn cat(s: Seq<&[u8]>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        cat(s.drop_last()) + s.last()@
    }
}

proof fn lemma_cat_put(s: Seq<&[u8]>, k: int, x: &[u8])
    requires 0 <= k < s.len(),
    ensures cat(s.update(k, x).take(k + 1)) == cat(s.take(k)) + x@,
            s.update(k, x).take(k) == s.take(k),
{
    assert(s.update(k, x).take(k + 1).drop_last() =~= s.take(k));
    assert(s.update(k, x).take(k) =~= s.take(k));
}

proof fn lemma_pend_unfold(buf: Seq<u8>, p: int, segs: Seq<(usize, Seg)>, i: int, off: int)
    requires 0 <= i < segs.len(),
    ensures pend(buf, p, segs.skip(i), off) == buf.subrange(p, segs[i].0 as int)
            + segs[i].1.view().subrange(off, segs[i].1.len as int) + pend(buf, segs[i].0 as int, segs.skip(i + 1), 0),
        segs_ok(buf.len() as int, p, segs.skip(i), off) ==> {
            &&& 0 <= p <= segs[i].0
            &&& (p < segs[i].0 ==> off == 0)
            &&& 0 <= off <= segs[i].1.len
            &&& segs[i].1.wf()
            &&& segs_ok(buf.len() as int, segs[i].0 as int, segs.skip(i + 1), 0)
        },
{
    lemma_skip(segs, i);
}

proof fn lemma_pend_len(buf: Seq<u8>, p: int, segs: Seq<(usize, Seg)>, off: int)
    requires segs_ok(buf.len() as int, p, segs, off),
    ensures segs.len() == 0 ==> pend(buf, p, segs, off) == buf.subrange(p, buf.len() as int),
{
}

impl Out {
    /// The bytes waiting to be written, as up to `out.len()` slices in
    /// order (for one `writev`). Returns how many slices were filled:
    /// together they are the start of what is pending, and all of it if
    /// fewer than `out.len()` were filled.
    pub fn slices<'a>(&'a self, out: &mut [&'a [u8]]) -> (k: usize)
        requires
            self.inv(),
        ensures
            k <= final(out)@.len() == old(out)@.len(),
            cat(final(out)@.take(k as int)).len() <= self.pending().len(),
            self.pending().subrange(0, cat(final(out)@.take(k as int)).len() as int) == cat(final(out)@.take(k as int)),
            k < final(out)@.len() ==> cat(final(out)@.take(k as int)) == self.pending(),
    {
        let ghost all = self.pending();
        let ghost b = self.buf@;
        let mut k: usize = 0;
        let mut p = self.pos;
        let mut off = self.seg_off;
        let mut i: usize = 0;
        let n = self.segs.len();
        proof {
            assert(self.segs@.skip(0) =~= self.segs@);
            assert(out@.take(0) =~= Seq::<&[u8]>::empty());
        }
        while i < n
            invariant
                self.inv(),
                all == self.pending(),
                b == self.buf@,
                n == self.segs@.len(),
                i <= n,
                k <= out@.len() == old(out)@.len(),
                segs_ok(b.len() as int, p as int, self.segs@.skip(i as int), off as int),
                cat(out@.take(k as int)) + pend(b, p as int, self.segs@.skip(i as int), off as int) == all,
            decreases n - i,
        {
            proof {
                lemma_pend_unfold(b, p as int, self.segs@, i as int, off as int);
                lemma_segs_le(b.len() as int, self.segs@[i as int].0 as int, self.segs@.skip(i + 1), 0);
            }
            let at = self.segs[i].0;
            let seg = &self.segs[i].1;
            if k == out.len() {
                return k;
            }
            if p < at {
                let x = vstd::slice::slice_subrange(self.buf.as_slice(), p, at);
                proof { lemma_cat_put(out@, k as int, x); }
                out[k] = x;
                k = k + 1;
                p = at;
                proof {
                    assert(b.subrange(at as int, at as int) =~= Seq::<u8>::empty());
                }
                if k == out.len() {
                    return k;
                }
            }
            if off < seg.len {
                let all_s = seg.bytes();
                let x = vstd::slice::slice_subrange(all_s, off, seg.len);
                proof { lemma_cat_put(out@, k as int, x); }
                out[k] = x;
                k = k + 1;
            }
            proof {
                assert(b.subrange(p as int, at as int) =~= Seq::<u8>::empty());
                assert(seg.view().subrange(seg.len as int, seg.len as int) =~= Seq::<u8>::empty());
            }
            off = 0;
            i = i + 1;
        }
        proof {
            assert(self.segs@.skip(n as int) =~= Seq::<(usize, Seg)>::empty());
        }
        if k < out.len() && p < self.buf.len() {
            let x = vstd::slice::slice_subrange(self.buf.as_slice(), p, self.buf.len());
            proof { lemma_cat_put(out@, k as int, x); }
            out[k] = x;
            k = k + 1;
        }
        proof {
            assert(b.subrange(b.len() as int, b.len() as int) =~= Seq::<u8>::empty());
        }
        k
    }
}

impl Out {
    /// Writes off up to `n` pending bytes from the front, within one piece.
    fn take(&mut self, n: usize) -> (t: usize)
        requires
            segs_ok(old(self).buf@.len() as int, old(self).pos as int, old(self).segs@, old(self).seg_off as int),
            0 < n <= old(self).pending().len(),
        ensures
            final(self).buf@ == old(self).buf@,
            final(self).wire == old(self).wire,
            final(self).sent == old(self).sent,
            final(self).queued == old(self).queued,
            segs_ok(final(self).buf@.len() as int, final(self).pos as int, final(self).segs@, final(self).seg_off as int),
            t <= n,
            final(self).pending() == old(self).pending().subrange(t as int, old(self).pending().len() as int),
            t > 0 || final(self).segs@.len() < old(self).segs@.len(),
            final(self).segs@.len() <= old(self).segs@.len(),
    {
        let ghost b = self.buf@;
        let ghost before = self.pending();
        proof { lemma_segs_le(b.len() as int, self.pos as int, self.segs@, self.seg_off as int); }
        if self.segs.len() == 0 {
            let ghost p0 = self.pos as int;
            proof { assert(before == b.subrange(p0, b.len() as int)); }
            let _bl = self.buf.len();
            self.pos = self.pos + n;
            proof { assert(self.pending() =~= before.subrange(n as int, before.len() as int)); }
            return n;
        }
        proof {
            assert(self.segs@.skip(0) =~= self.segs@);
            lemma_pend_unfold(b, self.pos as int, self.segs@, 0, self.seg_off as int);
            lemma_segs_le(b.len() as int, self.segs@[0].0 as int, self.segs@.skip(1), 0);
            assert(self.segs@.skip(1) =~= self.segs@.drop_first());
        }
        let at = self.segs[0].0;
        let len = self.segs[0].1.len;
        let ghost rest = pend(b, at as int, self.segs@.drop_first(), 0);
        let ghost sv = self.segs@[0].1.view();
        if self.pos < at {
            let t = if at - self.pos < n { at - self.pos } else { n };
            let ghost p0 = self.pos as int;
            self.pos = self.pos + t;
            proof {
                assert(sv.subrange(0, len as int) =~= sv);
                assert(before =~= b.subrange(p0, at as int) + sv + rest);
                assert(self.pending() =~= b.subrange(self.pos as int, at as int) + sv.subrange(0, len as int) + rest);
                assert(self.pending() =~= before.subrange(t as int, before.len() as int));
            }
            return t;
        }
        let t = if len - self.seg_off < n { len - self.seg_off } else { n };
        let ghost o = self.seg_off as int;
        self.seg_off = self.seg_off + t;
        proof {
            assert(b.subrange(at as int, at as int) =~= Seq::<u8>::empty());
            assert(before =~= sv.subrange(o, len as int) + rest);
            assert(self.pending() =~= sv.subrange(o + t, len as int) + rest);
            assert(self.pending() =~= before.subrange(t as int, before.len() as int));
        }
        if self.seg_off == len {
            let ghost d = self.segs@.drop_first();
            let _ = self.segs.pop_front();
            self.seg_off = 0;
            proof {
                assert(self.segs@ == d);
                assert(sv.subrange(len as int, len as int) =~= Seq::<u8>::empty());
                assert(self.pending() == rest);
            }
        }
        t
    }

    /// Drops the front segment if nothing of it, or of the bytes before it, is left.
    fn drop_done(&mut self) -> (r: bool)
        requires
            segs_ok(old(self).buf@.len() as int, old(self).pos as int, old(self).segs@, old(self).seg_off as int),
        ensures
            final(self).buf@ == old(self).buf@,
            final(self).wire == old(self).wire,
            final(self).sent == old(self).sent,
            final(self).queued == old(self).queued,
            segs_ok(final(self).buf@.len() as int, final(self).pos as int, final(self).segs@, final(self).seg_off as int),
            final(self).pending() == old(self).pending(),
            r ==> final(self).segs@.len() < old(self).segs@.len(),
            !r ==> final(self).segs@ == old(self).segs@,
    {
        if self.segs.len() == 0 {
            return false;
        }
        let ghost b = self.buf@;
        proof {
            assert(self.segs@.skip(0) =~= self.segs@);
            lemma_pend_unfold(b, self.pos as int, self.segs@, 0, self.seg_off as int);
            assert(self.segs@.skip(1) =~= self.segs@.drop_first());
            lemma_segs_le(b.len() as int, self.segs@[0].0 as int, self.segs@.skip(1), 0);
        }
        let at = self.segs[0].0;
        let l = self.segs[0].1.len;
        if self.seg_off >= l && self.pos >= at {
            proof {
                assert(segs_ok(b.len() as int, self.pos as int, self.segs@.skip(0), self.seg_off as int));
                let s0 = self.segs@[0];
                assert(b.subrange(self.pos as int, s0.0 as int) =~= Seq::<u8>::empty());
                assert(s0.1.view().subrange(self.seg_off as int, s0.1.len as int) =~= Seq::<u8>::empty());
            }
            let ghost d = self.segs@.drop_first();
            let _ = self.segs.pop_front();
            self.seg_off = 0;
            proof { assert(self.segs@ == d); }
            return true;
        }
        false
    }

    /// `n` bytes of what is pending were written (at most all of it).
    pub fn advance(&mut self, n: usize)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).wire@ == old(self).wire@,
            final(self).sent@ == old(self).sent@ + (if n <= old(self).queued { n } else { old(self).queued }),
    {
        let mut n = if n <= self.queued { n } else { self.queued };
        let ghost all = self.pending();
        let ghost n0 = n as int;
        let ghost w = self.wire@;
        let ghost s0 = self.sent@;
        self.queued = self.queued - n;
        self.sent = Ghost((self.sent@ + n0) as nat);
        let ghost b = self.buf@;
        while n > 0
            invariant
                b == self.buf@,
                w == self.wire@,
                self.sent@ == s0 + n0,
                0 <= n <= n0 <= all.len(),
                self.queued == all.len() - n0,
                segs_ok(b.len() as int, self.pos as int, self.segs@, self.seg_off as int),
                self.pending() == all.subrange(n0 - n, all.len() as int),
            decreases n + self.segs@.len(),
        {
            let t = self.take(n);
            n = n - t;
            proof { assert(self.pending() =~= all.subrange(n0 - n, all.len() as int)); }
        }
        // Drop finished zero-length leftovers.
        while self.drop_done()
            invariant
                b == self.buf@,
                w == self.wire@,
                self.sent@ == s0 + n0,
                n0 <= all.len(),
                self.queued == all.len() - n0,
                segs_ok(b.len() as int, self.pos as int, self.segs@, self.seg_off as int),
                self.pending() == all.subrange(n0, all.len() as int),
            decreases self.segs@.len(),
        {
        }
        proof {
            assert(w.subrange(s0 as int, w.len() as int) == all);
            assert(all.subrange(n0, all.len() as int) =~= w.subrange(s0 + n0, w.len() as int));
            assert(self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) =~= all.subrange(n0, all.len() as int));
        }
        if self.queued == 0 {
            self.reset_bufs();
            proof {
                assert(self.buf@.subrange(0, 0) =~= Seq::<u8>::empty());
                assert(self.pending() =~= Seq::<u8>::empty());
                assert(self.wire@.subrange(self.sent@ as int, self.wire@.len() as int) =~= Seq::<u8>::empty());
            }
        }
    }
}

pub open spec fn old_pos(p: usize, t: usize) -> int { p - t }

/// The file `fd` is the sealed copy of the shared body `a`, and its bytes
/// `[off, off + len)` are the next `len` bytes to write.
pub open spec fn file_next(o: &Out, fd: i32, off: usize, len: usize) -> bool {
    &&& len > 0
    &&& len <= o.pending().len()
    &&& exists|j: int| #![trigger o.segs@[j]] 0 <= j < o.segs@.len() && (o.segs@[j].1.file matches Some(f) && f.0 == fd
        && off + len <= (*o.segs@[j].1.a)@.len()
        && (*o.segs@[j].1.a)@.subrange(off as int, off + len) == o.pending().subrange(0, len as int))
}

impl Out {
    /// [`Out::slices`], stopping before a file-backed body: the event loop
    /// writes those with `sendfile`. `more` is set when slices stop at one
    /// (more bytes follow at once: MSG_MORE).
    pub fn slices_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> (r: Io<'a>)
        requires
            self.inv(),
        ensures
            final(out)@.len() == old(out)@.len(),
            r matches Io::Slices(k, _) ==> {
                &&& k <= final(out)@.len()
                &&& cat(final(out)@.take(k as int)).len() <= self.pending().len()
                &&& self.pending().subrange(0, cat(final(out)@.take(k as int)).len() as int) == cat(final(out)@.take(k as int))
            },
            r matches Io::File { fd, off, len } ==> file_next(self, fd, off, len),
    {
        *more = false;
        let ghost all = self.pending();
        let ghost b = self.buf@;
        let mut k: usize = 0;
        let mut p = self.pos;
        let mut off = self.seg_off;
        let mut i: usize = 0;
        let n = self.segs.len();
        proof {
            assert(self.segs@.skip(0) =~= self.segs@);
            assert(out@.take(0) =~= Seq::<&[u8]>::empty());
        }
        while i < n
            invariant
                self.inv(),
                all == self.pending(),
                b == self.buf@,
                n == self.segs@.len(),
                i <= n,
                k <= out@.len() == old(out)@.len(),
                segs_ok(b.len() as int, p as int, self.segs@.skip(i as int), off as int),
                cat(out@.take(k as int)) + pend(b, p as int, self.segs@.skip(i as int), off as int) == all,
            decreases n - i,
        {
            proof {
                lemma_pend_unfold(b, p as int, self.segs@, i as int, off as int);
                lemma_segs_le(b.len() as int, self.segs@[i as int].0 as int, self.segs@.skip(i + 1), 0);
            }
            let at = self.segs[i].0;
            let seg = &self.segs[i].1;
            if k == out.len() {
                return Io::Slices(k, PhantomData);
            }
            if p < at {
                let x = vstd::slice::slice_subrange(self.buf.as_slice(), p, at);
                proof { lemma_cat_put(out@, k as int, x); }
                out[k] = x;
                k = k + 1;
                p = at;
                proof {
                    assert(b.subrange(at as int, at as int) =~= Seq::<u8>::empty());
                }
                if k == out.len() {
                    return Io::Slices(k, PhantomData);
                }
            }
            if off < seg.len {
                match &seg.file {
                    Some(f) => {
                        if k == 0 {
                            let a: &[u8] = &seg.a;
                            let _al = a.len();
                            proof {
                                let sv = seg.view();
                                let rest = pend(b, at as int, self.segs@.skip(i + 1), 0);
                                assert(b.subrange(p as int, at as int) =~= Seq::<u8>::empty());
                                assert(cat(out@.take(0)) =~= Seq::<u8>::empty());
                                assert(all =~= sv.subrange(off as int, seg.len as int) + rest);
                                assert((*seg.a)@.subrange((seg.off + off) as int, seg.off + off + (seg.len - off))
                                    =~= all.subrange(0, (seg.len - off) as int));
                                assert(self.segs@[i as int].1.file == Some(*f));
                            }
                            return Io::File { fd: f.0, off: seg.off + off, len: seg.len - off };
                        }
                        *more = true;
                        return Io::Slices(k, PhantomData);
                    },
                    None => {},
                }
                let all_s = seg.bytes();
                let x = vstd::slice::slice_subrange(all_s, off, seg.len);
                proof { lemma_cat_put(out@, k as int, x); }
                out[k] = x;
                k = k + 1;
            }
            proof {
                assert(b.subrange(p as int, at as int) =~= Seq::<u8>::empty());
                assert(seg.view().subrange(seg.len as int, seg.len as int) =~= Seq::<u8>::empty());
            }
            off = 0;
            i = i + 1;
        }
        proof {
            assert(self.segs@.skip(n as int) =~= Seq::<(usize, Seg)>::empty());
        }
        if k < out.len() && p < self.buf.len() {
            let x = vstd::slice::slice_subrange(self.buf.as_slice(), p, self.buf.len());
            proof { lemma_cat_put(out@, k as int, x); }
            out[k] = x;
            k = k + 1;
        }
        proof {
            assert(b.subrange(b.len() as int, b.len() as int) =~= Seq::<u8>::empty());
        }
        Io::Slices(k, PhantomData)
    }
}


// ---------------------------------------------------------------------------
// Shared bodies
// ---------------------------------------------------------------------------

/// A body served many times (a static file): in memory, and on Linux, for
/// sizes where it is faster, also in a sealed memory file that HTTP/1.1
/// responses are sent from with `sendfile`. Sealed, so the bytes sent are
/// always the bytes the Content-Length counted, whatever happens to the
/// file it was read from. (Constructors: `h1.rs`.)
pub struct StaticBody {
    pub(crate) bytes: Arc<[u8]>,
    pub(crate) file: Option<Arc<Fd>>,
}

impl StaticBody {
    /// The body's bytes.
    pub closed spec fn view(&self) -> Seq<u8> {
        (*self.bytes)@
    }

    pub fn len(&self) -> (r: usize)
        ensures r == self.view().len(),
    {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.len() == 0
    }

    pub fn bytes(&self) -> &Arc<[u8]> {
        &self.bytes
    }
}

fn clone_file(f: &Option<Arc<Fd>>) -> (r: Option<Arc<Fd>>)
    ensures r == *f,
{
    match f {
        Some(a) => Some(a.clone()),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Responses
// ---------------------------------------------------------------------------

/// Why a response was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SendError {
    /// A response was already sent for this request.
    AlreadySent,
    /// The status is not a final status (200 to 999), the reason or a
    /// field name or value is not allowed (`respond::name_ok`, `value_ok`:
    /// CR, LF, NUL, a non-token name, or Content-Length/Transfer-Encoding,
    /// which the server writes), or a body range lies outside its body.
    Invalid,
}

/// A response body.
pub enum Body<'b> {
    /// Copied.
    Bytes(&'b [u8]),
    /// `a[off..off + len]`, written from `a` without a copy if long.
    Shared(&'b Arc<[u8]>, usize, usize),
    /// `body[off..off + len]`, with `sendfile` from its sealed file if it has one.
    Static(&'b StaticBody, usize, usize),
}

/// The body's bytes, if its range is inside it.
pub open spec fn body_view(b: Body) -> Option<Seq<u8>> {
    match b {
        Body::Bytes(x) => Some(x@),
        Body::Shared(a, off, len) => if off + len <= (**a)@.len() {
            Some((**a)@.subrange(off as int, off + len))
        } else {
            None
        },
        Body::Static(s, off, len) => if off + len <= s.view().len() {
            Some(s.view().subrange(off as int, off + len))
        } else {
            None
        },
    }
}

/// Responses without a body (RFC 9112 §6.3): 1xx, 204, 304.
pub open spec fn no_body_s(status: u16) -> bool {
    (100 <= status < 200) || status == 204 || status == 304
}

pub fn no_body(status: u16) -> (r: bool)
    ensures r == no_body_s(status),
{
    (100 <= status && status < 200) || status == 204 || status == 304
}

/// The server's own field lines (Server, Date, ...), without and with
/// `Connection: close`. The type invariant ties the two together.
pub struct Own {
    plain: Prepared,
    close: Prepared,
}

impl Own {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.close.fields() == self.plain.fields().push(conn_close())
    }

    pub closed spec fn fields(&self) -> Seq<SField> {
        self.plain.fields()
    }

    pub fn new(plain: Prepared) -> (r: Own)
        ensures r.fields() == plain.fields(),
    {
        let close = plain.with_close();
        Own { plain, close }
    }

    fn pick(&self, close: bool) -> (r: &Prepared)
        ensures r.fields() == if close { self.fields().push(conn_close()) } else { self.fields() },
    {
        proof { use_type_invariant(self); }
        if close { &self.close } else { &self.plain }
    }

    fn may_close(&self) -> (r: bool)
        ensures !r ==> !fields_close(self.fields()),
    {
        self.plain.may_close()
    }
}

/// One response, as queued.
pub ghost struct SResp {
    /// Interim responses before it (a `100 Continue`), or nothing.
    pub pre: Seq<u8>,
    pub status: u16,
    pub reason: Seq<u8>,
    pub fields: Seq<SField>,
    pub framing: Framing,
    pub body: Seq<u8>,
    /// The head says `Connection: close`.
    pub close: bool,
    /// It answers a HEAD request.
    pub head_req: bool,
    /// The handler asked to close after the head was written: the
    /// connection closes without the head saying so.
    pub late: bool,
}

/// `HTTP/1.1 100 Continue` and the empty line.
pub open spec fn cont_bytes() -> Seq<u8> {
    head(100, continue_reason(), Seq::empty(), Framing::Neither)
}

/// "Continue"
pub open spec fn continue_reason() -> Seq<u8> {
    seq![0x43u8, 0x6f, 0x6e, 0x74, 0x69, 0x6e, 0x75, 0x65]
}

pub open spec fn resp_bytes(r: SResp) -> Seq<u8> {
    r.pre + head(r.status, r.reason, r.fields, r.framing) + r.body
}

/// The responses' bytes, back to back.
pub open spec fn flat(rs: Seq<SResp>) -> Seq<u8>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::empty()
    } else {
        flat(rs.drop_last()) + resp_bytes(rs.last())
    }
}

/// What every queued response satisfies.
pub open spec fn resp_ok(r: SResp) -> bool {
    // The preconditions of respond::theorem_head_parses: the head parses
    // back to exactly this status, reason, field lines and framing.
    &&& status_ok(r.status)
    &&& reason_ok(r.reason)
    &&& fields_ok(r.fields)
    &&& framing_ok(r.framing)
    // A final response (a 1xx would read as interim and shift every later
    // response onto the wrong request).
    &&& r.status >= 200
    // Framing by the true body length.
    &&& no_body_s(r.status) ==> r.framing == Framing::Neither
    &&& !no_body_s(r.status) ==> (r.framing is Length)
    &&& (no_body_s(r.status) || r.head_req) ==> r.body.len() == 0
    &&& (!no_body_s(r.status) && !r.head_req) ==> r.framing == Framing::Length(r.body.len() as u64)
    // Connection: close.
    &&& r.close ==> r.fields.contains(conn_close())
    &&& fields_close(r.fields) ==> r.close
    &&& r.pre == Seq::<u8>::empty() || r.pre == cont_bytes()
}

/// Where a connection is in answering its current request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// No request is ready.
    Idle,
    /// A request is ready and not yet answered. `keep`: it persists
    /// (RFC 9112 §9.3); `head`: its method is HEAD.
    Open { keep: bool, head: bool },
    /// The ready request was answered; `close`: the head says so.
    Done { close: bool },
    /// No more responses.
    Shut,
}

/// A connection's output, with the ledger of the responses on it. Only
/// [`Wire::answer`] adds a response, and only for an open request.
pub struct Wire {
    out: Out,
    st: Slot,
    /// A `100 Continue` was sent for the current request.
    cont: bool,
    resps: Ghost<Seq<SResp>>,
    /// Interim bytes queued for the current request.
    cur: Ghost<Seq<u8>>,
    /// The last response is an error for a rejected request.
    bad: Ghost<bool>,
    /// Shut because the peer stopped sending.
    peer: Ghost<bool>,
    /// Shut because the fallback 500 could not be queued (more bytes
    /// queued than a usize counts); the open request is unanswered.
    failed: Ghost<bool>,
}

impl Wire {
    pub closed spec fn resps(&self) -> Seq<SResp> {
        self.resps@
    }

    pub closed spec fn slot(&self) -> Slot {
        self.st
    }

    pub closed spec fn bad(&self) -> bool {
        self.bad@
    }

    pub closed spec fn peer(&self) -> bool {
        self.peer@
    }

    pub closed spec fn failed(&self) -> bool {
        self.failed@
    }

    /// Every byte queued on the connection, in order.
    pub closed spec fn wire(&self) -> Seq<u8> {
        self.out.wire@
    }

    /// The bytes still to be written.
    pub closed spec fn unsent(&self) -> Seq<u8> {
        self.out.pending()
    }

    /// The sealed file `fd` holds, at `[off, off + len)`, the next `len` bytes to write.
    pub closed spec fn file_next(&self, fd: i32, off: usize, len: usize) -> bool {
        file_next(&self.out, fd, off, len)
    }

    pub closed spec fn interim(&self) -> Seq<u8> {
        self.cur@
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.out.inv()
        &&& self.out.wire@ == flat(self.resps@) + self.cur@
        &&& forall|i: int| 0 <= i < self.resps@.len() ==> resp_ok(#[trigger] self.resps@[i])
        // A response that says close is the last one.
        &&& forall|i: int| 0 <= i < self.resps@.len() - 1 ==> !(#[trigger] self.resps@[i]).close
        &&& forall|i: int| 0 <= i < self.resps@.len() - 1 ==> !(#[trigger] self.resps@[i]).late
        &&& (self.st is Idle || self.st is Open) ==> {
            &&& (self.resps@.len() > 0 ==> !self.resps@.last().close && !self.resps@.last().late)
            &&& self.cur@ == if self.cont { cont_bytes() } else { Seq::empty() }
            &&& !self.bad@
        }
        &&& self.st matches Slot::Done { close } ==> {
            &&& self.resps@.len() > 0
            &&& self.resps@.last().close == close
            &&& !self.resps@.last().late
            &&& self.cur@ == Seq::<u8>::empty()
            &&& !self.bad@
        }
        &&& self.st is Shut ==> self.cur@ == Seq::<u8>::empty() || self.failed@ || self.peer@
        &&& self.bad@ ==> self.st is Shut && self.resps@.len() > 0 && self.resps@.last().close
        &&& self.peer@ ==> self.st is Shut
        &&& self.failed@ ==> self.st is Shut
    }

    pub fn new() -> (r: Wire)
        ensures r.inv(), r.resps().len() == 0, r.slot() is Idle, r.wire().len() == 0,
    {
        let w = Wire { out: Out::new(), st: Slot::Idle, cont: false, resps: Ghost(Seq::empty()), cur: Ghost(Seq::empty()), bad: Ghost(false), peer: Ghost(false), failed: Ghost(false) };
        assert(flat(Seq::<SResp>::empty()) + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        assert(w.out.wire@ =~= flat(w.resps@) + w.cur@);
        w
    }

    /// A `Wire` that has allocated nothing: for a response that writes
    /// elsewhere (HTTP/2 and HTTP/3 replies).
    pub fn empty() -> (r: Wire)
        ensures r.inv(), r.resps().len() == 0, r.slot() is Idle,
    {
        let w = Wire { out: Out::empty(), st: Slot::Idle, cont: false, resps: Ghost(Seq::empty()), cur: Ghost(Seq::empty()), bad: Ghost(false), peer: Ghost(false), failed: Ghost(false) };
        assert(flat(Seq::<SResp>::empty()) + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        assert(w.out.wire@ =~= flat(w.resps@) + w.cur@);
        w
    }

    /// A new connection.
    pub fn clear(&mut self)
        ensures final(self).inv(), final(self).resps().len() == 0, final(self).slot() is Idle, final(self).wire().len() == 0,
    {
        self.out.clear();
        self.st = Slot::Idle;
        self.cont = false;
        self.resps = Ghost(Seq::empty());
        self.cur = Ghost(Seq::empty());
        self.bad = Ghost(false);
        self.peer = Ghost(false);
        self.failed = Ghost(false);
        assert(flat(Seq::<SResp>::empty()) + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        assert(self.out.wire@ =~= flat(self.resps@) + self.cur@);
    }

    /// The bytes waiting to be written, as up to `out.len()` slices in order.
    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> (k: usize)
        requires self.inv(),
        ensures
            k <= final(out)@.len() == old(out)@.len(),
            cat(final(out)@.take(k as int)).len() <= self.unsent().len(),
            self.unsent().subrange(0, cat(final(out)@.take(k as int)).len() as int) == cat(final(out)@.take(k as int)),
            k < final(out)@.len() ==> cat(final(out)@.take(k as int)) == self.unsent(),
    {
        self.out.slices(out)
    }

    /// [`Wire::pending`], stopping before a file-backed body.
    pub fn pending_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> (r: Io<'a>)
        requires self.inv(),
        ensures
            final(out)@.len() == old(out)@.len(),
            r matches Io::Slices(k, _) ==> {
                &&& k <= final(out)@.len()
                &&& self.unsent().subrange(0, cat(final(out)@.take(k as int)).len() as int) == cat(final(out)@.take(k as int))
            },
            r matches Io::File { fd, off, len } ==> self.file_next(fd, off, len),
    {
        self.out.slices_io(out, more)
    }

    pub fn pending_len(&self) -> (r: usize)
        requires self.inv(),
        ensures r == self.unsent().len(),
    {
        self.out.queued
    }

    /// `n` bytes of [`Wire::pending`] were written.
    pub fn wrote(&mut self, n: usize)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).resps() == old(self).resps(),
            final(self).slot() == old(self).slot(),
            final(self).wire() == old(self).wire(),
            final(self).bad() == old(self).bad(),
            final(self).peer() == old(self).peer(),
            final(self).interim() == old(self).interim(),
    {
        self.out.advance(n);
    }

    /// Answers the open request: the head, by the verified writer, with the
    /// server's fields `own`, then `pre`, then `fields`, framed by the
    /// body's length; then the body (none for HEAD, 1xx, 204, 304). The head
    /// says `Connection: close` if `close`, if the request does not persist,
    /// or if any of the fields list `close`.
    pub fn answer(&mut self, status: u16, reason: &[u8], own: &Own, pre: &Prepared, fields: &[Field], body: Body, close: bool) -> (r: Result<(), SendError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).bad() == old(self).bad(),
            final(self).peer() == old(self).peer(),
            r is Err ==> final(self).resps() == old(self).resps() && final(self).slot() == old(self).slot()
                && final(self).wire() == old(self).wire() && final(self).interim() == old(self).interim(),
            !(old(self).slot() is Open) ==> r == Err::<(), SendError>(SendError::AlreadySent),
            r is Ok ==> (old(self).slot() matches Slot::Open { keep, head } && {
                let x = final(self).resps().last();
                &&& final(self).resps() == old(self).resps().push(x)
                &&& final(self).slot() == Slot::Done { close: x.close }
                &&& x.status == status
                &&& x.head_req == head
                &&& (close || !keep) ==> x.close
                &&& !x.late
                &&& (body_view(body) matches Some(bv) && (if no_body_s(status) || head { x.body.len() == 0 } else { x.body == bv }))
            }),
    {
        let (keep, hd) = match self.st {
            Slot::Open { keep, head } => (keep, head),
            _ => { return Err(SendError::AlreadySent); },
        };
        if status < 200 || status > 999 {
            return Err(SendError::Invalid);
        }
        let n = match body {
            Body::Bytes(b) => b.len(),
            Body::Shared(a, off, len) => {
                let al = a.len();
                if off > al || len > al - off {
                    return Err(SendError::Invalid);
                }
                len
            },
            Body::Static(s, off, len) => {
                let al = s.bytes.len();
                if off > al || len > al - off {
                    return Err(SendError::Invalid);
                }
                len
            },
        };
        let nb = no_body(status);
        let framing = if nb { Framing::Neither } else { Framing::Length(n as u64) };
        let close = close || !keep || own.may_close() || pre.may_close() || fields_close_exec(fields);
        let o = own.pick(close);
        let ghost fs = o.fields() + pre.fields() + fields_view(fields@);
        proof {
            crate::persist::lemma_fields_close_concat(o.fields(), pre.fields());
            crate::persist::lemma_fields_close_concat(o.fields() + pre.fields(), fields_view(fields@));
            if close {
                assert(o.fields().last() == conn_close());
                assert(fs[o.fields().len() - 1] == conn_close());
                assert(fs.contains(conn_close()));
            } else {
                assert(!fields_close(fs));
            }
        }
        let ghost w0 = self.out.wire@;
        let ghost h = head(status, reason@, fs, framing);
        let body_n = if nb || hd { 0 } else { n };
        if !self.out.push_head(status, reason, o, pre, fields, framing, body_n) {
            return Err(SendError::Invalid);
        }
        let ghost w1 = self.out.wire@;
        let ghost bv = if nb || hd { Seq::<u8>::empty() } else { body_view(body).unwrap() };
        if !nb && !hd {
            self.out.push_body(body);
        } else {
            assert(self.out.wire@ =~= w1 + bv);
        }
        let ghost x = SResp {
            pre: self.cur@,
            status,
            reason: reason@,
            fields: fs,
            framing,
            body: bv,
            close,
            head_req: hd,
            late: false,
        };
        proof {
            assert(self.out.wire@ =~= w0 + h + bv);
            if close {
                assert(fs.contains(conn_close()));
            }
            let rs = self.resps@;
            assert forall|i: int| 0 <= i < rs.len() implies !(#[trigger] rs[i]).close && !rs[i].late by {
                if i == rs.len() - 1 {
                    assert(rs[i] == rs.last());
                }
            }
            lemma_record(self.resps@, x, self.cur@, w0, self.out.wire@);
        }
        self.resps = Ghost(self.resps@.push(x));
        self.cur = Ghost(Seq::empty());
        self.st = Slot::Done { close };
        Ok(())
    }
}

impl Out {
    /// Writes a response head with the verified writer, if it passes the
    /// checks and its head and `body_n` more bytes can be counted.
    fn push_head(&mut self, status: u16, reason: &[u8], a: &Prepared, b: &Prepared, c: &[Field], framing: Framing, body_n: usize) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).sent == old(self).sent,
            !r ==> final(self).wire == old(self).wire,
            r ==> {
                &&& status_ok(status)
                &&& reason_ok(reason@)
                &&& fields_ok(a.fields() + b.fields() + fields_view(c@))
                &&& framing_ok(framing)
                &&& final(self).wire@ == old(self).wire@ + head(status, reason@, a.fields() + b.fields() + fields_view(c@), framing)
                &&& final(self).queued + body_n <= usize::MAX
            },
    {
        let before = self.buf.len();
        if !respond::write_head_prepared(&mut self.buf, status, reason, a, b, c, framing) {
            return false;
        }
        let hl = self.buf.len() - before;
        if hl > usize::MAX - self.queued || body_n > usize::MAX - self.queued - hl {
            self.buf.truncate(before);
            proof {
                assert(self.buf@ =~= old(self).buf@);
            }
            return false;
        }
        let ghost h = head(status, reason@, a.fields() + b.fields() + fields_view(c@), framing);
        proof {
            assert(self.buf@.subrange(0, before as int) =~= old(self).buf@);
            assert(self.buf@.subrange(before as int, self.buf@.len() as int) =~= h);
        }
        self.grew(before);
        true
    }

    /// Queues a body whose range was checked.
    fn push_body(&mut self, body: Body)
        requires
            old(self).inv(),
            body_view(body) is Some,
            old(self).queued + body_view(body).unwrap().len() <= usize::MAX,
        ensures
            final(self).inv(),
            final(self).sent == old(self).sent,
            final(self).wire@ == old(self).wire@ + body_view(body).unwrap(),
    {
        match body {
            Body::Bytes(b) => {
                self.extend(b);
            },
            Body::Shared(a, off, len) => {
                if len < SHARE_MIN {
                    let x: &[u8] = a;
                    let _xl = x.len();
                    let y = slice_subrange(x, off, off + len);
                    self.extend(y);
                } else {
                    self.push_seg(Seg { a: a.clone(), off, len, file: None });
                }
            },
            Body::Static(s, off, len) => {
                let x: &[u8] = &s.bytes;
                let _xl = x.len();
                proof { assert(x@ == s.view()); }
                if s.file.is_some() {
                    self.push_seg(Seg { a: s.bytes.clone(), off, len, file: clone_file(&s.file) });
                } else if len < SHARE_MIN {
                    let y = slice_subrange(x, off, off + len);
                    self.extend(y);
                } else {
                    self.push_seg(Seg { a: s.bytes.clone(), off, len, file: None });
                }
            },
        }
    }
}

/// Adding a response keeps the ledger's facts.
proof fn lemma_record(rs: Seq<SResp>, x: SResp, cur: Seq<u8>, w0: Seq<u8>, w1: Seq<u8>)
    requires
        w0 == flat(rs) + cur,
        x.pre == cur,
        w1 == w0 + head(x.status, x.reason, x.fields, x.framing) + x.body,
        resp_ok(x),
        forall|i: int| 0 <= i < rs.len() ==> resp_ok(#[trigger] rs[i]),
        forall|i: int| 0 <= i < rs.len() ==> !(#[trigger] rs[i]).close && !rs[i].late,
    ensures
        w1 == flat(rs.push(x)),
        forall|i: int| 0 <= i < rs.push(x).len() ==> resp_ok(#[trigger] rs.push(x)[i]),
        forall|i: int| 0 <= i < rs.push(x).len() - 1 ==> !(#[trigger] rs.push(x)[i]).close,
        forall|i: int| 0 <= i < rs.push(x).len() - 1 ==> !(#[trigger] rs.push(x)[i]).late,
{
    let r2 = rs.push(x);
    assert(r2.drop_last() =~= rs);
    assert(w1 =~= flat(r2));
    assert forall|i: int| 0 <= i < r2.len() implies resp_ok(#[trigger] r2[i]) by {
        if i < rs.len() {
            assert(r2[i] == rs[i]);
        }
    }
    assert forall|i: int| 0 <= i < r2.len() - 1 implies !(#[trigger] r2[i]).close by {
        assert(r2[i] == rs[i]);
    }
    assert forall|i: int| 0 <= i < r2.len() - 1 implies !(#[trigger] r2[i]).late by {
        assert(r2[i] == rs[i]);
    }
}

// ---------------------------------------------------------------------------
// The ledger's other transitions
// ---------------------------------------------------------------------------

/// "Internal Server Error"
pub open spec fn ise_reason() -> Seq<u8> {
    seq![0x49u8, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x61, 0x6c, 0x20, 0x53, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20, 0x45, 0x72, 0x72, 0x6f, 0x72]
}

impl Wire {
    /// A request is ready.
    fn open(&mut self, keep: bool, head: bool)
        requires
            old(self).inv(),
            old(self).slot() is Idle,
        ensures
            final(self).inv(),
            final(self).slot() == (Slot::Open { keep, head }),
            final(self).resps() == old(self).resps(),
            final(self).bad() == old(self).bad(),
            final(self).peer() == old(self).peer(),
    {
        self.st = Slot::Open { keep, head };
    }

    /// Sends `100 Continue` for the request being read, once.
    fn send_continue(&mut self)
        requires
            old(self).inv(),
            old(self).slot() is Idle,
        ensures
            final(self).inv(),
            final(self).slot() is Idle,
            final(self).resps() == old(self).resps(),
            final(self).bad() == old(self).bad(),
            final(self).peer() == old(self).peer(),
    {
        if self.cont {
            return;
        }
        let ghost w0 = self.out.wire@;
        let reason: [u8; 8] = [0x43u8, 0x6f, 0x6e, 0x74, 0x69, 0x6e, 0x75, 0x65];
        assert(reason@ =~= continue_reason());
        let empty = Prepared::empty();
        let none: [Field; 0] = [];
        assert(fields_view(none@) =~= Seq::<SField>::empty());
        let e2 = Prepared::empty();
        if self.out.push_head(100, &reason, &empty, &e2, &none, Framing::Neither, 0) {
            proof {
                assert(empty.fields() + e2.fields() + fields_view(none@) =~= Seq::<SField>::empty());
                assert(self.out.wire@ =~= flat(self.resps@) + cont_bytes());
            }
            self.cont = true;
            self.cur = Ghost(cont_bytes());
        }
    }

    /// The handler returned. If it sent nothing, answers 500. Returns
    /// whether the connection closes now: the head said so, or the handler
    /// asked to close after sending it (`late`).
    fn finish(&mut self, own: &Own, late: bool) -> (res: Option<bool>)
        requires
            old(self).inv(),
            old(self).slot() is Open || old(self).slot() is Done,
        ensures
            final(self).inv(),
            final(self).bad() == old(self).bad(),
            final(self).peer() == old(self).peer(),
            res is None <==> final(self).failed(),
            match old(self).slot() {
                Slot::Done { close } => res matches Some(r) && (close ==> r),
                Slot::Open { keep, head: _ } => (res matches Some(r) ==> (!keep ==> r)),
                _ => true,
            },
            res matches Some(r) ==> {
                &&& final(self).resps().len() == old(self).resps().len() + (if old(self).slot() is Open { 1int } else { 0 })
                &&& final(self).resps().len() > 0
                &&& r ==> final(self).slot() is Shut && (final(self).resps().last().close || final(self).resps().last().late)
                &&& !r ==> final(self).slot() is Idle && !final(self).resps().last().close
                &&& (old(self).slot() matches Slot::Open { keep, head } ==> {
                    &&& final(self).resps().last().head_req == head
                    &&& !keep ==> final(self).resps().last().close
                })
                &&& (old(self).slot() is Done ==> final(self).resps().drop_last() == old(self).resps().drop_last())
            },
            final(self).failed() ==> final(self).slot() is Shut && final(self).resps() == old(self).resps() && old(self).slot() is Open,
            old(self).slot() is Open ==> final(self).resps().drop_last() == old(self).resps() || final(self).failed(),
    {
        if let Slot::Open { .. } = self.st {
            let reason: [u8; 21] = [0x49u8, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x61, 0x6c, 0x20, 0x53, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20, 0x45, 0x72, 0x72, 0x6f, 0x72];
            let empty = Prepared::empty();
            let none: [Field; 0] = [];
            if self.answer(500, &reason, own, &empty, &none, Body::Bytes(&reason), late).is_err() {
                // Only if more bytes were queued than a usize counts.
                self.st = Slot::Shut;
                self.failed = Ghost(true);
                return None;
            }
        }
        let close = match self.st {
            Slot::Done { close } => close,
            _ => { return None; },
        };
        let c = close || late;
        if late && !close {
            let ghost x = self.resps@.last();
            let ghost x2 = SResp { late: true, ..x };
            proof {
                let rs = self.resps@;
                let r2 = rs.update(rs.len() - 1, x2);
                assert(r2.drop_last() =~= rs.drop_last());
                assert(rs.drop_last().push(x) =~= rs);
                assert(flat(r2) =~= flat(rs));
                assert forall|i: int| 0 <= i < r2.len() - 1 implies !(#[trigger] r2[i]).close && !r2[i].late by {
                    assert(r2[i] == rs[i]);
                }
                assert forall|i: int| 0 <= i < r2.len() implies resp_ok(#[trigger] r2[i]) by {
                    if i < rs.len() - 1 { assert(r2[i] == rs[i]); }
                }
            }
            self.resps = Ghost(self.resps@.update(self.resps@.len() - 1, x2));
        }
        self.cont = false;
        self.st = if c { Slot::Shut } else { Slot::Idle };
        Some(c)
    }

    /// The request the core rejected is answered with `status` and the
    /// connection ends.
    fn error(&mut self, own: &Own, status: u16, reason: &[u8])
        requires
            old(self).inv(),
            old(self).slot() is Idle,
        ensures
            final(self).inv(),
            final(self).slot() is Shut,
            !final(self).peer(),
            final(self).failed() || (final(self).bad() && final(self).resps().drop_last() == old(self).resps() && final(self).resps().len() == old(self).resps().len() + 1),
            final(self).failed() ==> final(self).resps() == old(self).resps() && !final(self).bad(),
    {
        self.st = Slot::Open { keep: false, head: false };
        let empty = Prepared::empty();
        let none: [Field; 0] = [];
        match self.answer(status, reason, own, &empty, &none, Body::Bytes(reason), true) {
            Ok(()) => {
                self.st = Slot::Shut;
                self.bad = Ghost(true);
            },
            Err(_) => {
                self.st = Slot::Shut;
                self.failed = Ghost(true);
            },
        }
    }

    /// No more requests, without a response saying so: the peer closed.
    fn shut_peer(&mut self)
        requires
            old(self).inv(),
            old(self).slot() is Idle,
        ensures
            final(self).inv(),
            final(self).slot() is Shut,
            final(self).peer(),
            final(self).resps() == old(self).resps(),
            final(self).bad() == old(self).bad(),
            final(self).failed() == old(self).failed(),
    {
        self.st = Slot::Shut;
        self.peer = Ghost(true);
    }

    fn is_idle(&self) -> (r: bool)
        ensures r == self.slot() is Idle,
    {
        matches!(self.st, Slot::Idle)
    }

    fn is_shut(&self) -> (r: bool)
        ensures r == self.slot() is Shut,
    {
        matches!(self.st, Slot::Shut)
    }
}

// ---------------------------------------------------------------------------
// The engine: request core and output together
// ---------------------------------------------------------------------------

/// "expect"
pub open spec fn name_expect() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x70, 0x65, 0x63, 0x74]
}

/// "100-continue"
pub open spec fn val_continue() -> Seq<u8> {
    seq![0x31u8, 0x30, 0x30, 0x2d, 0x63, 0x6f, 0x6e, 0x74, 0x69, 0x6e, 0x75, 0x65]
}

/// Some field line of `hs` over `w` is `Expect: 100-continue` (any case).
pub open spec fn expects(w: Seq<u8>, hs: Seq<verilith_http::parse::Header>) -> bool
    decreases hs.len(),
{
    if hs.len() == 0 {
        false
    } else {
        let h = hs.last();
        expects(w, hs.drop_last()) || (ci_eq(w.subrange(h.name.start as int, h.name.end as int), name_expect())
            && ci_eq(w.subrange(h.value.start as int, h.value.end as int), val_continue()))
    }
}

/// One HTTP/1.1 connection's requests and responses. The invariant joins
/// the request core's and the output ledger's: see the module comment.
pub struct Engine {
    pub core: Core,
    pub wire: Wire,
}

impl Engine {
    /// The ready request's persistence (RFC 9112 §9.3).
    pub open spec fn ready_persists(&self) -> bool {
        crate::persist::persists(self.core.rest(), first(self.core.rest(), self.core.max()).unwrap().req)
    }

    /// How the request log and the response ledger line up: one response
    /// per request handed out, in order, plus at most one error response
    /// for a rejected request at the end.
    pub open spec fn rel(&self) -> bool {
        let n = self.core.log@.len();
        let rs = self.wire.resps();
        match self.wire.slot() {
            Slot::Idle => !(self.core.phase is Ready) && !(self.core.phase is Closed) && rs.len() == n,
            Slot::Open { keep, head } => self.core.phase is Ready && rs.len() == n && keep == self.ready_persists(),
            Slot::Done { close } => self.core.phase is Ready && rs.len() == n + 1 && (!self.ready_persists() ==> close),
            Slot::Shut => self.core.phase is Closed && rs.len() == n + (if self.wire.bad() { 1int } else { 0 }),
        }
    }

    /// Every close the server decides is announced by the response before it.
    pub open spec fn announced(&self) -> bool {
        (self.wire.slot() is Shut && !self.wire.peer() && !self.wire.failed()) ==> {
            let rs = self.wire.resps();
            rs.len() > 0 && (rs.last().close || rs.last().late)
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.core.inv()
        &&& self.wire.inv()
        &&& self.rel()
        &&& self.announced()
    }

    pub fn new(cap: usize, max_headers: usize, max_body: usize) -> (r: Engine)
        ensures r.inv(), r.core.rbuf@.len() == cap,
    {
        Engine { core: Core::new(cap, max_headers, max_body), wire: Wire::new() }
    }

    /// A new connection, keeping the buffers (at most `cap` bytes of read buffer).
    pub fn reset(&mut self, cap: usize)
        ensures final(self).inv(), final(self).core.max_headers == old(self).core.max_headers, final(self).core.max_body == old(self).core.max_body,
    {
        self.core.reset(cap);
        self.wire.clear();
    }

    /// Whether the ready request's method is HEAD.
    fn ready_head(&self) -> (r: bool)
        requires
            self.core.inv(),
    {
        let hd = match self.core.phase {
            Phase::Ready { hd, body: _ } => hd,
            _ => { return false; },
        };
        let (a, b) = (hd.method.start, hd.method.end);
        if a > b || b > self.core.end - self.core.start || b - a != 4 {
            return false;
        }
        let w = slice_subrange(self.core.rbuf.as_slice(), self.core.start, self.core.end);
        let m = slice_subrange(w, a, b);
        m[0] == 0x48 && m[1] == 0x45 && m[2] == 0x41 && m[3] == 0x44
    }

    /// Whether the request being read asks for `100 Continue`.
    fn expects_continue(&self) -> (r: bool)
        requires
            self.core.inv(),
            self.core.phase is Length || self.core.phase is Chunked,
        ensures
            r == expects(self.core.win(), self.core.headers@),
    {
        let w = slice_subrange(self.core.rbuf.as_slice(), self.core.start, self.core.end);
        let hs = self.core.headers.as_slice();
        let e = match self.core.phase {
            Phase::Length { hd, need: _ } => hd.head_len,
            Phase::Chunked { hd, out: _, dec: _ } => hd.head_len,
            _ => 0,
        };
        proof {
            assert(w@ == self.core.win());
            assert(hdrs_ok(hs@, w@.len() as int)) by {
                assert forall|j: int| 0 <= j < hs@.len() implies hdr_ok(#[trigger] hs@[j], w@.len() as int) by {
                    assert(hdr_ok(hs@[j], e as int));
                }
            }
        }
        let mut k: usize = 0;
        let mut acc = false;
        proof { assert(hs@.take(0) =~= Seq::<verilith_http::parse::Header>::empty()); }
        while k < hs.len()
            invariant
                k <= hs@.len(),
                w@ == self.core.win(),
                hdrs_ok(hs@, w@.len() as int),
                acc == expects(w@, hs@.take(k as int)),
            decreases hs@.len() - k,
        {
            let h = hs[k];
            proof {
                assert(hdr_ok(hs@[k as int], w@.len() as int));
                assert(hs@.take(k + 1).drop_last() =~= hs@.take(k as int));
                assert(hs@.take(k + 1).last() == h);
            }
            let name = slice_subrange(w, h.name.start, h.name.end);
            let value = slice_subrange(w, h.value.start, h.value.end);
            let ex: [u8; 6] = [0x65u8, 0x78, 0x70, 0x65, 0x63, 0x74];
            let co: [u8; 12] = [0x31u8, 0x30, 0x30, 0x2d, 0x63, 0x6f, 0x6e, 0x74, 0x69, 0x6e, 0x75, 0x65];
            assert(ex@ =~= name_expect());
            assert(co@ =~= val_continue());
            let this = ci_eq_exec(name, ex.as_slice()) && ci_eq_exec(value, co.as_slice());
            acc = acc || this;
            k += 1;
        }
        assert(hs@.take(hs@.len() as int) =~= hs@);
        acc
    }

    /// Moves the connection on: answers what the last handler left
    /// unanswered, then parses as far as the bytes allow. On `Ready` the
    /// ready request is open for exactly one [`Wire::answer`]; on `Bad` the
    /// error response is queued and the connection ends.
    #[verifier::rlimit(200)]
    pub fn step(&mut self, own: &Own) -> (r: Ev)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r == Ev::Ready <==> final(self).wire.slot() is Open,
            r == Ev::Ready ==> final(self).core.phase is Ready,
            final(self).core.stream@ == old(self).core.stream@,
    {
        if !self.wire.is_idle() && !self.wire.is_shut() {
            self.finish(own, false);
        }
        if self.wire.is_shut() {
            return Ev::Closed;
        }
        let r = self.core.step();
        match r {
            Ev::Ready => {
                let keep = self.core.ready_persists();
                let head = self.ready_head();
                self.wire.open(keep, head);
            },
            Ev::Need => {
                if matches!(self.core.phase, Phase::Length { .. } | Phase::Chunked { .. }) {
                    if self.expects_continue() {
                        self.wire.send_continue();
                    }
                }
            },
            Ev::Bad(status) => {
                let r413: [u8; 17] = [0x43u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x20, 0x54, 0x6f, 0x6f, 0x20, 0x4c, 0x61, 0x72, 0x67, 0x65];
                let r431: [u8; 31] = [0x52u8, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x20, 0x48, 0x65, 0x61, 0x64, 0x65, 0x72, 0x20, 0x46, 0x69, 0x65, 0x6c, 0x64, 0x73, 0x20, 0x54, 0x6f, 0x6f, 0x20, 0x4c, 0x61, 0x72, 0x67, 0x65];
                let r400: [u8; 11] = [0x42u8, 0x61, 0x64, 0x20, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74];
                if status == 413 {
                    self.wire.error(own, status, &r413);
                } else if status == 431 {
                    self.wire.error(own, status, &r431);
                } else {
                    self.wire.error(own, status, &r400);
                }
            },
            Ev::Closed => {
                self.wire.shut_peer();
            },
        }
        r
    }

    /// The handler returned (`late`: it asked to close after sending):
    /// answers 500 if it sent nothing, then moves past the request, to the
    /// next if the response persists, else to the end.
    #[verifier::rlimit(200)]
    pub fn finish(&mut self, own: &Own, late: bool)
        requires
            old(self).inv(),
            old(self).wire.slot() is Open || old(self).wire.slot() is Done,
        ensures
            final(self).inv(),
            final(self).wire.slot() is Idle || final(self).wire.slot() is Shut,
            final(self).core.stream@ == old(self).core.stream@,
    {
        let ghost p0 = self.ready_persists();
        let ghost n0 = self.core.log@.len();
        let ghost s0 = self.wire.slot();
        match self.wire.finish(own, late) {
            Some(c) => {
                assert(!c ==> p0);
                self.core.done(!c);
                assert(self.core.inv());
                assert(self.wire.inv());
                assert(self.core.log@.len() == n0 + 1);
                assert(self.wire.resps().len() == n0 + 1);
                assert(c ==> self.core.phase is Closed);
                assert(!c ==> self.core.phase is Head);
                assert(self.rel());
                assert(self.announced());
            },
            None => {
                self.core.close();
                assert(self.rel());
                assert(self.announced());
            },
        }
    }

    /// The peer closed its side: nothing more will arrive. (Between
    /// [`Engine::step`]s, where no request is open.)
    pub fn eof(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).wire.slot() is Idle || old(self).wire.slot() is Shut ==> final(self).core.phase is Closed,
    {
        if self.wire.is_idle() {
            self.core.close();
            self.wire.shut_peer();
        }
    }
}


impl Out {
    /// `body[off..off + n]`, queued without a copy (nothing if the range
    /// is not inside `body`).
    pub fn share_range(&mut self, body: Arc<[u8]>, off: usize, n: usize)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).sent == old(self).sent,
            final(self).wire@ == old(self).wire@ || (off + n <= (*body)@.len() && final(self).wire@ == old(self).wire@ + (*body)@.subrange(off as int, off + n)),
    {
        let l = body.len();
        if off > l || n > l - off {
            return;
        }
        self.push_seg(Seg { a: body, off, len: n, file: None });
    }

    /// `body`, queued without a copy.
    pub fn share(&mut self, body: Arc<[u8]>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).sent == old(self).sent,
    {
        let n = body.len();
        self.share_range(body, 0, n);
    }
}

} // verus!
