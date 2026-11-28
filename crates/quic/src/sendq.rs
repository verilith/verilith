//! What a sender of one stream (or CRYPTO at one level) still has to send,
//! resend and have acknowledged (RFC 9000 §2.2, §3.1, §13.3): the offsets
//! only; the bytes are kept by the caller.
//!
//! Proven, after any sequence of calls, of [`SendState`] and the set
//! `SendState::done` of offsets that need nothing more (acknowledged, or
//! given up by [`SendState::clear`]):
//!
//! - [`SendState::next`] returns only offsets written and not done: lost
//!   ones first, then new data within the flow control limit;
//! - [`SendState::base`] is exactly the first offset not done, so the
//!   bytes the caller may free ([`SendState::on_ack`]'s result) are all
//!   acknowledged, and nothing acknowledged is kept longer than that;
//! - [`SendState::on_lost`] queues again exactly the lost offsets that were
//!   sent and are not done;
//! - the FIN is sent only at the end of what was written, and resent if
//!   lost and not acknowledged.
//!
//! Every method checks its inputs, so a call with offsets that were never
//! sent changes nothing it should not.
use crate::ranges::RangeSet;
use vstd::prelude::*;

verus! {

/// Stream offsets are below 2^62 (§4.5).
pub const OFFSET_LIMIT: u64 = 0x4000_0000_0000_0000;

pub open spec fn span(a: int, b: int) -> ISet<int> {
    ISet::new(|x: int| a <= x < b)
}

/// One stream's (or CRYPTO level's) sending offsets.
pub struct SendState {
    /// The first offset not done.
    base: u64,
    /// The offset after the last one ever sent.
    unsent: u64,
    /// The offset after the last byte written.
    end: u64,
    /// The done offsets from `base` on.
    acked: RangeSet,
    /// Sent, declared lost, not done, and not sent again since.
    lost: RangeSet,
    fin: bool,
    fin_sent: bool,
    fin_acked: bool,
    done: Ghost<ISet<int>>,
}

impl SendState {
    pub closed spec fn spec_base(&self) -> u64 {
        self.base
    }

    pub closed spec fn unsent(&self) -> int {
        self.unsent as int
    }

    pub closed spec fn spec_end(&self) -> u64 {
        self.end
    }

    /// Offsets that need nothing more.
    pub closed spec fn done(&self) -> ISet<int> {
        self.done@
    }

    /// Offsets to send again.
    pub closed spec fn lost(&self) -> ISet<int> {
        self.lost.view()
    }

    pub closed spec fn spec_fin(&self) -> bool {
        self.fin
    }

    pub closed spec fn fin_sent(&self) -> bool {
        self.fin_sent
    }

    pub closed spec fn spec_fin_acked(&self) -> bool {
        self.fin_acked
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.base <= self.unsent <= self.end <= OFFSET_LIMIT
        &&& self.acked.wf()
        &&& self.lost.wf()
        &&& forall|x: int| #[trigger] self.done@.contains(x) ==> 0 <= x < self.unsent
        &&& forall|x: int| 0 <= x < self.base ==> #[trigger] self.done@.contains(x)
        &&& !self.done@.contains(self.base as int)
        &&& forall|x: int| #[trigger] self.acked.view().contains(x) == (self.done@.contains(x) && x >= self.base)
        &&& forall|x: int| #[trigger] self.lost.view().contains(x) ==> self.base <= x < self.unsent && !self.done@.contains(x)
        &&& self.fin_acked ==> self.fin
    }

    /// Nothing written yet.
    pub fn new() -> (r: SendState)
        ensures
            r.inv(),
            r.base() == 0 && r.unsent() == 0 && r.end() == 0,
            r.done() == ISet::<int>::empty(),
            r.lost() == ISet::<int>::empty(),
            !r.fin() && !r.fin_sent() && !r.fin_acked(),
    {
        SendState {
            base: 0,
            unsent: 0,
            end: 0,
            acked: RangeSet::new(),
            lost: RangeSet::new(),
            fin: false,
            fin_sent: false,
            fin_acked: false,
            done: Ghost(ISet::empty()),
        }
    }

    /// The first offset not done: bytes below it may be freed.
    #[verifier::when_used_as_spec(spec_base)]
    pub fn base(&self) -> (r: u64)
        ensures
            r == self.base(),
    {
        self.base
    }

    /// The offset after the last byte written.
    #[verifier::when_used_as_spec(spec_end)]
    pub fn end(&self) -> (r: u64)
        ensures
            r == self.end(),
    {
        self.end
    }

    /// Whether the stream ends after what was written.
    #[verifier::when_used_as_spec(spec_fin)]
    pub fn fin(&self) -> (r: bool)
        ensures
            r == self.fin(),
    {
        self.fin
    }

    /// Whether the FIN was acknowledged.
    #[verifier::when_used_as_spec(spec_fin_acked)]
    pub fn fin_acked(&self) -> (r: bool)
        ensures
            r == self.fin_acked(),
    {
        self.fin_acked
    }

    /// `n` more bytes were written. Refused (false) after the FIN, or past
    /// [`OFFSET_LIMIT`].
    pub fn write(&mut self, n: u64) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r == (!old(self).fin() && n <= OFFSET_LIMIT - old(self).end()),
            final(self).end() == if r { old(self).end() + n } else { old(self).end() as int },
            final(self).base() == old(self).base() && final(self).unsent() == old(self).unsent(),
            final(self).done() == old(self).done() && final(self).lost() == old(self).lost(),
            final(self).fin() == old(self).fin() && final(self).fin_sent() == old(self).fin_sent(),
            final(self).fin_acked() == old(self).fin_acked(),
    {
        if self.fin || n > OFFSET_LIMIT - self.end {
            return false;
        }
        self.end = self.end + n;
        true
    }

    /// The stream ends after what was written.
    pub fn set_fin(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).fin(),
            final(self).base() == old(self).base() && final(self).unsent() == old(self).unsent(),
            final(self).end() == old(self).end(),
            final(self).done() == old(self).done() && final(self).lost() == old(self).lost(),
            final(self).fin_sent() == old(self).fin_sent(),
            final(self).fin_acked() == old(self).fin_acked(),
    {
        self.fin = true;
    }

    /// Whether anything (data or the FIN) is waiting to be sent.
    pub fn has_pending(&self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == (self.lost() != ISet::<int>::empty() || self.unsent() < self.end() || (self.fin()
                && !self.fin_sent())),
    {
        !self.lost.is_empty() || self.unsent < self.end || (self.fin && !self.fin_sent)
    }

    /// Bytes written and never sent.
    pub fn new_pending(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.end() - self.unsent(),
    {
        self.end - self.unsent
    }

    /// Bytes written and not freed.
    pub fn unacked(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.end() - self.base(),
    {
        self.end - self.base
    }

    /// The next chunk to send, `(offset, len, fin)` with `len <= max`: lost
    /// data first, then new data up to `limit` (flow control's end offset),
    /// then a FIN on its own.
    pub fn next(&self, max: u64, limit: u64) -> (r: Option<(u64, u64, bool)>)
        requires
            self.inv(),
        ensures
            r matches Some((off, n, fin)) ==> n <= max && off + n <= self.end(),
            r matches Some((off, n, fin)) ==> forall|x: int| off <= x < off + n ==> !#[trigger] self.done().contains(x),
            r matches Some((off, n, fin)) ==> (fin ==> self.fin() && off + n == self.end()),
            r matches Some((off, n, fin)) ==> self.lost() != ISet::<int>::empty() ==> {
                &&& forall|x: int| off <= x < off + n ==> #[trigger] self.lost().contains(x)
                &&& forall|x: int| x < off ==> !#[trigger] self.lost().contains(x)
                &&& self.lost().contains(off as int)
            },
            r matches Some((off, n, fin)) ==> self.lost() == ISet::<int>::empty() ==> {
                &&& off == self.unsent() || (n == 0 && off == self.end())
                &&& off + n <= limit || n == 0
            },
            r is None ==> {
                &&& self.lost() == ISet::<int>::empty()
                &&& (self.unsent() >= self.end() || self.unsent() >= limit || max == 0)
                &&& !(self.fin() && !self.fin_sent() && self.unsent() == self.end())
            },
    {
        if let Some((a, b)) = self.lost.first() {
            let n = if b - a < max { b - a } else { max };
            let fin = self.fin && a + n == self.end && !self.fin_sent;
            proof {
                assert(self.lost.view().contains(b - 1));
                assert(self.lost.view().contains(a as int));
                assert forall|x: int| a <= x < a + n implies #[trigger] self.lost().contains(x) && !self.done().contains(x) by {
                    assert(self.lost.view().contains(x));
                }
                assert(self.lost() != ISet::<int>::empty());
                assert forall|x: int| a <= x < a + n implies !#[trigger] self.done().contains(x) by {
                    assert(self.lost.view().contains(x));
                }
            }
            return Some((a, n, fin));
        }
        let lim = if limit < self.end { limit } else { self.end };
        if self.unsent < lim && max > 0 {
            let n = if lim - self.unsent < max { lim - self.unsent } else { max };
            let fin = self.fin && self.unsent + n == self.end;
            proof {
                assert forall|x: int| self.unsent <= x < self.unsent + n implies !#[trigger] self.done().contains(x) by {}
            }
            return Some((self.unsent, n, fin));
        }
        if self.fin && !self.fin_sent && self.unsent == self.end {
            return Some((self.end, 0, true));
        }
        None
    }

    /// `[off, off + n)` (and the FIN if `fin`) went out in a packet. What
    /// is past the end written, and a FIN not at that end, is ignored.
    pub fn sent(&mut self, off: u64, n: u64, fin: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ({
                let e = if off >= old(self).end() { old(self).end() as int } else if n > old(self).end()
                    - off { old(self).end() as int } else { off + n };
                &&& final(self).unsent() == if e > old(self).unsent() { e } else { old(self).unsent() }
                &&& off < e ==> final(self).lost() == old(self).lost().difference(span(off as int, e))
                &&& off >= e ==> final(self).lost() == old(self).lost()
                &&& final(self).fin_sent() == (old(self).fin_sent() || (fin && old(self).fin() && e
                    == old(self).end()))
            }),
            final(self).base() == old(self).base() && final(self).end() == old(self).end(),
            final(self).done() == old(self).done(),
            final(self).fin() == old(self).fin() && final(self).fin_acked() == old(self).fin_acked(),
    {
        let e = if off >= self.end { self.end } else if n > self.end - off { self.end } else { off + n };
        if off < e {
            self.lost.remove(off, e);
        }
        if e > self.unsent {
            self.unsent = e;
        }
        if fin && self.fin && e == self.end {
            self.fin_sent = true;
        }
        proof {
            if off < e {
                assert(self.lost.view() =~= old(self).lost.view().difference(span(off as int, e as int)));
            }
        }
    }

    /// `[off, off + n)` (and the FIN if `fin`) was acknowledged. Returns
    /// how far [`SendState::base`] moved: the bytes the caller may free.
    /// Offsets never sent are ignored.
    pub fn on_ack(&mut self, off: u64, n: u64, fin: bool) -> (k: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ({
                let a = if off > old(self).base() { off as int } else { old(self).base() as int };
                let e = if off >= old(self).unsent() { old(self).unsent() as int } else if n > old(self).unsent()
                    - off { old(self).unsent() as int } else { off + n };
                final(self).done() == if a < e { old(self).done().union(span(a, e)) } else { old(self).done() }
            }),
            final(self).base() == old(self).base() + k,
            final(self).unsent() == old(self).unsent() && final(self).end() == old(self).end(),
            final(self).lost() == old(self).lost().difference(final(self).done()),
            final(self).fin() == old(self).fin() && final(self).fin_sent() == old(self).fin_sent(),
            final(self).fin_acked() == (old(self).fin_acked() || (fin && old(self).fin())),
    {
        if fin && self.fin {
            self.fin_acked = true;
        }
        let a = if off > self.base { off } else { self.base };
        let e = if off >= self.unsent { self.unsent } else if n > self.unsent - off { self.unsent } else { off + n };
        if a >= e {
            proof {
                assert(self.lost.view() =~= old(self).lost.view().difference(self.done@));
            }
            return 0;
        }
        let ghost d0 = self.done@;
        proof {
            self.done@ = d0.union(span(a as int, e as int));
        }
        self.acked.insert(a, e);
        self.lost.remove(a, e);
        proof {
            assert forall|x: int| #[trigger] self.acked.view().contains(x) == (self.done@.contains(x) && x >= self.base) by {}
            assert forall|x: int| #[trigger] self.lost.view().contains(x) == (old(self).lost.view().contains(x) && !self.done@.contains(x)) by {}
            assert(self.acked.view().contains(a as int));
        }
        let old_base = self.base;
        if let Some((s, t)) = self.acked.first() {
            if s == self.base {
                let ghost av = self.acked.view();
                self.acked.remove(s, t);
                self.base = t;
                proof {
                    assert forall|x: int| 0 <= x < self.base implies #[trigger] self.done@.contains(x) by {
                        if x >= old_base {
                            assert(av.contains(x));
                        }
                    }
                    assert(!av.contains(t as int));
                    assert(av.contains(t - 1));
                    assert(!self.done@.contains(self.base as int));
                    assert forall|x: int| #[trigger] self.acked.view().contains(x) == (self.done@.contains(x) && x >= self.base) by {
                        assert(av.contains(x) == (self.done@.contains(x) && x >= old_base));
                    }
                }
            } else {
                proof {
                    assert(self.acked.view().contains(s as int));
                    assert(!self.acked.view().contains(self.base as int));
                }
            }
        }
        proof {
            assert(self.lost.view() =~= old(self).lost.view().difference(self.done@));
        }
        self.base - old_base
    }

    /// `[off, off + n)` (and the FIN if `fin`) was lost: what of it was
    /// sent and is not done is queued to send again.
    pub fn on_lost(&mut self, off: u64, n: u64, fin: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ({
                let a = if off > old(self).base() { off as int } else { old(self).base() as int };
                let e = if off >= old(self).unsent() { old(self).unsent() as int } else if n > old(self).unsent()
                    - off { old(self).unsent() as int } else { off + n };
                final(self).lost() == if a < e {
                    old(self).lost().union(span(a, e).difference(old(self).done()))
                } else {
                    old(self).lost()
                }
            }),
            final(self).base() == old(self).base() && final(self).unsent() == old(self).unsent(),
            final(self).end() == old(self).end() && final(self).done() == old(self).done(),
            final(self).fin() == old(self).fin(),
            final(self).fin_sent() == (old(self).fin_sent() && !(fin && !old(self).fin_acked())),
            final(self).fin_acked() == old(self).fin_acked(),
    {
        if fin && !self.fin_acked {
            self.fin_sent = false;
        }
        let a = if off > self.base { off } else { self.base };
        let e = if off >= self.unsent { self.unsent } else if n > self.unsent - off { self.unsent } else { off + n };
        if a < e {
            self.lost.insert_except(a, e, &self.acked);
            proof {
                assert(self.lost.view() =~= old(self).lost.view().union(span(a as int, e as int).difference(self.done@)));
            }
        }
    }

    /// Everything written, and the FIN, is done.
    pub fn all_acked(&self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == ((forall|x: int| 0 <= x < self.end() ==> #[trigger] self.done().contains(x)) && (!self.fin()
                || self.fin_acked())),
    {
        proof {
            if self.base < self.end {
                assert(!self.done().contains(self.base as int));
            } else {
                assert forall|x: int| 0 <= x < self.end() implies #[trigger] self.done().contains(x) by {}
            }
        }
        self.base == self.end && (!self.fin || self.fin_acked)
    }

    /// Gives up on everything written (a reset stream).
    pub fn clear(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).base() == old(self).end() && final(self).unsent() == old(self).end(),
            final(self).end() == old(self).end(),
            final(self).done() == span(0, old(self).end() as int),
            final(self).lost() == ISet::<int>::empty(),
            final(self).fin() == old(self).fin() && final(self).fin_sent() == old(self).fin_sent(),
            final(self).fin_acked() == old(self).fin_acked(),
    {
        self.base = self.end;
        self.unsent = self.end;
        self.acked.clear();
        self.lost.clear();
        proof {
            self.done@ = span(0, self.end as int);
        }
    }
}

} // verus!
