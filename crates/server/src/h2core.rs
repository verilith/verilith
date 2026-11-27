//! The HTTP/2 connection core, verified: every decision `h2.rs` makes about
//! a frame (RFC 9113), sans I/O and without HPACK or handlers.
//!
//! `h2.rs` parses each frame with verilith-h2's verified parser and hands it
//! to [`Core::on_frame`]. The core keeps the connection's state (the stream
//! table, the peer's SETTINGS, both connection windows, the header block
//! being received, the flood budget, and whether the connection is
//! closing), writes every control frame the RFC asks for in reply
//! (SETTINGS and PING acknowledgements, WINDOW_UPDATE, RST_STREAM, GOAWAY)
//! with verilith-h2's verified serializer, and tells `h2.rs` what is left to
//! do: feed a header block fragment to the HPACK decoder, append request
//! body bytes, or run the handler.
//!
//! What is proven (the invariant [`Core::wf`] and the `ensures` below):
//!
//! - **The stream table.** Streams are kept in ID order; every ID is odd
//!   and at most the highest opened, which never goes down. A stream is
//!   opened only by HEADERS, only on a new odd ID (`streams::verdict`), and
//!   never while the peer is going away. At most `max_streams` are open at
//!   once (SETTINGS_MAX_CONCURRENT_STREAMS, §5.1.2): HEADERS past that is
//!   refused with RST_STREAM(REFUSED_STREAM) once its block is decoded,
//!   CONTINUATION frames included.
//! - **Frames in a header block.** Between HEADERS without END_HEADERS and
//!   the CONTINUATION that ends it, any other frame is a connection error
//!   (§6.10), and the block is decoded even for a refused or reset stream,
//!   so the HPACK tables never diverge (§4.3).
//! - **SETTINGS.** Every SETTINGS frame is acknowledged once it is applied
//!   (§6.5.3); SETTINGS_INITIAL_WINDOW_SIZE shifts every open stream's send
//!   window by the change (§6.9.2), and a window pushed past 2^31 − 1 is a
//!   FLOW_CONTROL_ERROR; SETTINGS_MAX_FRAME_SIZE stays in [2^14, 2^24 − 1].
//! - **RST_STREAM** is sent only for a stream that is not idle (§5.1).
//! - **GOAWAY** names the highest stream opened, so every request the
//!   server has handled is at or below it (§6.8); it is sent at most once,
//!   and after it the core does nothing. A peer's GOAWAY(NO_ERROR) drains:
//!   no new streams, the open ones finish, then GOAWAY and close.
//! - **Content-Length** (§8.1.1). Each live stream counts its DATA bytes
//!   against the Content-Length its fields declared (verilith-core's
//!   `BodyLen`, whose invariant is that they never pass it). A request is
//!   complete (`Step::Dispatch`, or `Step::Data` with END_STREAM) only if
//!   a declared length equals its DATA ([`Core::body_ok`]); otherwise it
//!   is malformed, and the stream is reset with PROTOCOL_ERROR.
//! - **Responses** ([`Core::send_headers`], [`Core::send_data`],
//!   [`Core::sent`]). A stream's response starts at most once: its header
//!   block goes out as `h2wire::header_frames` (HEADERS then CONTINUATION,
//!   which the peer reads back as exactly that block: `h2wire.rs`). Its
//!   body then goes out in DATA frames of at most `h2wire::CHUNK` bytes,
//!   each within both send windows, each starting where the last ended,
//!   with END_STREAM on the one that reaches the body's end (or on HEADERS
//!   for an empty body), and nothing after it: the stream closes. Only
//!   then does the response count as sent in full, for the budget below.
//! - **Flood budget.** Frames that carry no request bytes cost a unit of
//!   budget: PING, SETTINGS (and each parameter), WINDOW_UPDATE, PRIORITY,
//!   RST_STREAM (rapid reset), GOAWAY, unknown frames, empty DATA,
//!   HEADERS and CONTINUATION, refused streams, frames on closed streams,
//!   and every stream we reset. The budget is [`BASE_CREDIT`] plus
//!   `control_per_request` per response sent in full. While the
//!   connection is open, units spent never exceed it; the frame that would
//!   pass it closes the connection with ENHANCE_YOUR_CALM. A frame that
//!   costs nothing carries at least one byte of a header block or body, or
//!   completes a request ([`Core::on_frame`]'s `ensures`).
use vstd::prelude::*;

use verilith_h2::{Frame, Params};
#[cfg(verus_keep_ghost)]
use verilith_h2::spec;
use crate::flow::{take_data, RecvWindow, SendWindow, MAX_WINDOW};
use verilith_core::clen::BodyLen;
use crate::streams::{classify, Kind, St, Verdict};
use crate::h2wire::{write_headers, data_head, CHUNK};
#[cfg(verus_keep_ghost)]
use crate::h2wire::{header_frames, ser_all};
#[cfg(verus_keep_ghost)]
use crate::streams::{idle, verdict};

verus! {

// Error codes (§7).
pub const NO_ERROR: u32 = 0x0;
pub const PROTOCOL_ERROR: u32 = 0x1;
pub const INTERNAL_ERROR: u32 = 0x2;
pub const FLOW_CONTROL_ERROR: u32 = 0x3;
pub const STREAM_CLOSED: u32 = 0x5;
pub const REFUSED_STREAM: u32 = 0x7;
pub const COMPRESSION_ERROR: u32 = 0x9;
pub const ENHANCE_YOUR_CALM: u32 = 0xb;

// Settings (§6.5.2).
pub const S_HEADER_TABLE_SIZE: u16 = 0x1;
pub const S_ENABLE_PUSH: u16 = 0x2;
pub const S_MAX_CONCURRENT_STREAMS: u16 = 0x3;
pub const S_INITIAL_WINDOW_SIZE: u16 = 0x4;
pub const S_MAX_FRAME_SIZE: u16 = 0x5;

/// The largest stream identifier (§5.1.1).
pub const MAX_ID: u32 = 0x7fff_ffff;

/// Budget units a connection has before its first response.
pub const BASE_CREDIT: u64 = 1000;

/// Closed streams' buffers kept for the next ones.
const POOL: usize = 64;

/// Limits on one HTTP/2 connection.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct Limits2 {
    pub max_streams: u32,
    /// The receive window advertised for each stream, and for the
    /// connection.
    pub window: u32,
    /// Largest header block (all its fragments, and decoded fields).
    pub max_header_block: usize,
    /// Largest request body buffered for a handler.
    pub max_body: usize,
    /// Budget units each response sent in full adds: how many frames
    /// that carry no request (PING, SETTINGS, RST_STREAM, empty frames, ...)
    /// a peer may send per request before the connection is closed with
    /// ENHANCE_YOUR_CALM. The flood defences of DESIGN.md.
    pub control_per_request: u32,
}

/// What `h2.rs` keeps per stream: buffers, reused across streams.
pub trait Store: Sized {
    /// Empty buffers.
    fn fresh() -> Self;
    /// Empties the buffers of a closed stream, keeping their memory.
    fn recycle(&mut self);
}

/// A stream that is open or half-closed (remote).
pub struct Live<V> {
    pub st: St,
    /// What we may still send on the stream.
    pub send: SendWindow,
    /// What the peer may still send on the stream.
    pub recv: RecvWindow,
    /// Request body bytes received, and the Content-Length the request
    /// declared (§8.1.1).
    pub len: BodyLen,
    /// Our response on the stream.
    pub resp: Resp,
    pub v: V,
}

/// Where our response on a stream is.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Resp {
    /// Nothing sent yet.
    Waiting,
    /// HEADERS sent; `off` of the body's `len` bytes sent in DATA (all of
    /// them: waiting for [`Core::sent`]).
    Body { len: usize, off: usize },
}

/// What [`Core::send_data`] asks `h2.rs` to send: `head`, then the
/// body's bytes `off..off + n`.
pub struct DataOut {
    pub head: [u8; 9],
    pub off: usize,
    pub n: usize,
    pub end: bool,
}

/// `a` is how `b` begins.
pub open spec fn extends(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() <= b.len() && b.take(a.len() as int) == a
}

pub proof fn lemma_extends_refl(a: Seq<u8>)
    ensures extends(a, a),
{
    assert(a.take(a.len() as int) =~= a);
}

pub proof fn lemma_extends_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires extends(a, b), extends(b, c),
    ensures extends(a, c),
{
    assert(c.take(a.len() as int) =~= c.take(b.len() as int).take(a.len() as int));
}

/// A stream that has been opened: live, or closed (`None`).
pub struct Slot<V> {
    pub id: u32,
    pub live: Option<Live<V>>,
}

/// What happens to the fields of a header block being received.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// A request's fields, kept on the stream.
    Request,
    /// Trailers: decoded and dropped; the request is complete at the end.
    Trailers,
    /// A stream refused: decoded and dropped, then RST_STREAM(REFUSED_STREAM).
    Refused,
    /// A stream closed meanwhile: decoded and dropped.
    Dropped,
}

/// A header block being received (HEADERS, then CONTINUATION).
#[derive(Clone, Copy)]
pub struct Block {
    pub stream: u32,
    /// The stream's slot, for `Request` and `Trailers`.
    pub at: usize,
    pub end_stream: bool,
    /// Fragment bytes so far.
    pub len: usize,
    pub mode: Mode,
}

/// What `h2.rs` does next with a frame, after [`Core::on_frame`].
pub enum Step<'a> {
    /// Nothing (the core did all there was, or the connection is closing).
    None,
    /// A SETTINGS frame was applied and acknowledged: apply its
    /// SETTINGS_HEADER_TABLE_SIZE values to the HPACK encoder, in order.
    Settings,
    /// Feed this fragment to the HPACK decoder; keep the fields on the
    /// stream in slot `keep`, if any. Then, at `end_headers`, call
    /// [`Core::end_block`].
    Fragment { frag: &'a [u8], end_headers: bool, keep: Option<usize> },
    /// Append `data` to the body of the stream in slot `at`; if `end`, the
    /// request is complete: run the handler.
    Data { at: usize, data: &'a [u8], end: bool },
    /// The request on the stream in slot `at` is complete: run the handler.
    Dispatch { at: usize },
}

/// 1 for a live slot.
pub open spec fn is_live<V>(s: Slot<V>) -> nat {
    if s.live is Some { 1 } else { 0 }
}

/// How many slots are live.
pub open spec fn nlive_of<V>(s: Seq<Slot<V>>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { nlive_of(s.drop_last()) + is_live(s.last()) }
}

proof fn lemma_nlive_update<V>(s: Seq<Slot<V>>, i: int, x: Slot<V>)
    requires 0 <= i < s.len(),
    ensures nlive_of(s.update(i, x)) + is_live(s[i]) == nlive_of(s) + is_live(x),
    decreases s.len(),
{
    if i == s.len() - 1 {
        assert(s.update(i, x).drop_last() =~= s.drop_last());
    } else {
        lemma_nlive_update(s.drop_last(), i, x);
        assert(s.update(i, x).drop_last() =~= s.drop_last().update(i, x));
    }
}

proof fn lemma_nlive_push<V>(s: Seq<Slot<V>>, x: Slot<V>)
    ensures nlive_of(s.push(x)) == nlive_of(s) + is_live(x),
{
    assert(s.push(x).drop_last() =~= s);
}

proof fn lemma_nlive_le<V>(s: Seq<Slot<V>>)
    ensures nlive_of(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_nlive_le(s.drop_last());
    }
}

proof fn lemma_nlive_same<V>(a: Seq<Slot<V>>, b: Seq<Slot<V>>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> (a[i].live is Some <==> b[i].live is Some),
    ensures nlive_of(a) == nlive_of(b),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_nlive_same(a.drop_last(), b.drop_last());
    }
}

/// Slot IDs strictly increase.
pub open spec fn sorted<V>(s: Seq<Slot<V>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].id < s[j].id
}

/// Strictly increasing odd IDs: the `i`th is at least `2i + 1`.
proof fn lemma_ids_spread<V>(s: Seq<Slot<V>>, i: int)
    requires
        sorted(s),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k].id % 2 == 1,
        0 <= i < s.len(),
    ensures s[i].id >= 2 * i + 1,
    decreases i,
{
    if i > 0 {
        lemma_ids_spread(s, i - 1);
        assert(s[i - 1].id < s[i].id);
        assert(s[i].id % 2 == 1);
    }
}

pub struct Core<V> {
    /// Every stream opened and not yet compacted away, in ID order.
    slots: Vec<Slot<V>>,
    /// Scratch for compacting `slots`; always empty between calls.
    spare: Vec<Slot<V>>,
    /// Buffers of closed streams.
    pool: Vec<V>,
    nlive: usize,
    /// The highest stream ID opened (or refused).
    last: u32,
    /// The peer's SETTINGS_MAX_FRAME_SIZE.
    max_frame: u32,
    /// The peer's SETTINGS_INITIAL_WINDOW_SIZE.
    initial_window: u32,
    /// What we may still send on the connection.
    conn_send: SendWindow,
    /// What the peer may still send on the connection.
    conn_recv: RecvWindow,
    block: Option<Block>,
    /// Budget units spent, and the budget.
    control: u64,
    credit: u64,
    /// The peer sent GOAWAY(NO_ERROR): finishing the open streams.
    draining: bool,
    goaway_sent: bool,
    closing: bool,
    limits: Limits2,
}

/// A slot's own facts: an odd ID at most `last`, windows within bounds.
pub open spec fn slot_ok<V>(x: Slot<V>, last: u32) -> bool {
    &&& x.id % 2 == 1
    &&& x.id <= last
    &&& x.live matches Some(l) ==> l.send.inv() && l.recv.inv() && l.len.inv()
        && (l.resp matches Resp::Body { len, off } ==> off <= len)
}

/// The same IDs, live in the same places.
pub open spec fn same_shape<V>(a: Seq<Slot<V>>, b: Seq<Slot<V>>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].id == b[i].id && (a[i].live is Some <==> b[i].live is Some)
}

/// IDs strictly decrease.
pub open spec fn desc<V>(s: Seq<Slot<V>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].id > s[j].id
}

/// Frames that cost no budget: each carries a header block or body byte,
/// or ends a request.
pub open spec fn free<'a>(f: Frame<'a>, r: Step<'a>) -> bool {
    match r {
        Step::Fragment { frag, .. } => frag@.len() > 0,
        Step::Data { .. } => f matches Frame::Data { data, pad, end_stream, .. } && (data@.len() > 0 || pad is Some || end_stream),
        Step::Dispatch { .. } => true,
        _ => false,
    }
}

impl<V: Store> Core<V> {
    /// The invariant.
    pub closed spec fn wf(&self) -> bool {
        let s = self.slots@;
        &&& sorted(s)
        &&& forall|i: int| 0 <= i < s.len() ==> slot_ok(#[trigger] s[i], self.last)
        &&& self.nlive == nlive_of(s)
        &&& self.nlive <= self.limits.max_streams
        &&& self.spare@.len() == 0
        &&& self.pool@.len() <= POOL
        &&& self.last <= MAX_ID
        &&& self.conn_send.inv()
        &&& self.conn_recv.inv()
        &&& self.initial_window <= MAX_WINDOW
        &&& self.limits.window <= MAX_WINDOW
        &&& 16384 <= self.max_frame <= 16777215
        &&& (self.block matches Some(b) ==> self.block_ok(b))
        &&& !self.closing ==> self.control <= self.credit
        &&& self.goaway_sent ==> self.closing
    }

    pub closed spec fn block_ok(&self, b: Block) -> bool {
        let s = self.slots@;
        &&& b.stream % 2 == 1
        &&& b.stream <= self.last
        &&& b.len <= self.limits.max_header_block
        &&& (b.mode == Mode::Request || b.mode == Mode::Trailers) ==> {
            &&& b.at < s.len()
            &&& s[b.at as int].id == b.stream
            &&& (s[b.at as int].live matches Some(l) && l.st == St::Open)
        }
        &&& b.mode == Mode::Trailers ==> b.end_stream
    }

    /// Everything but the stream table is as in `o`.
    closed spec fn same_conn(&self, o: &Self) -> bool {
        &&& self.nlive == o.nlive
        &&& self.last == o.last
        &&& self.max_frame == o.max_frame
        &&& self.initial_window == o.initial_window
        &&& self.conn_send == o.conn_send
        &&& self.conn_recv == o.conn_recv
        &&& self.block == o.block
        &&& self.control == o.control
        &&& self.credit == o.credit
        &&& self.draining == o.draining
        &&& self.goaway_sent == o.goaway_sent
        &&& self.closing == o.closing
        &&& self.limits == o.limits
    }

    /// Whether the connection is closing: nothing more is to be read.
    pub closed spec fn is_closing(&self) -> bool {
        self.closing
    }

    /// Whether the peer is going away (GOAWAY with NO_ERROR).
    pub closed spec fn is_draining(&self) -> bool {
        self.draining
    }

    /// The highest stream ID opened.
    pub closed spec fn last_id(&self) -> u32 {
        self.last
    }

    /// Budget units spent.
    pub closed spec fn spent(&self) -> u64 {
        self.control
    }

    /// The budget.
    pub closed spec fn budget(&self) -> u64 {
        self.credit
    }

    /// Open streams.
    pub closed spec fn open_streams(&self) -> nat {
        self.nlive as nat
    }

    pub closed spec fn max_streams(&self) -> u32 {
        self.limits.max_streams
    }

    pub closed spec fn in_block(&self) -> bool {
        self.block is Some
    }

    /// The body count of the live stream in slot `at`: the DATA bytes it
    /// carried and the Content-Length it declared.
    pub closed spec fn body_len(&self, at: usize) -> Option<BodyLen> {
        if at < self.slots@.len() {
            match self.slots@[at as int].live {
                Some(l) => Some(l.len),
                None => None,
            }
        } else {
            None
        }
    }

    /// A request complete as RFC 9113 §8.1.1 asks: its stream is live, and
    /// a Content-Length it declared is the length of its DATA.
    pub open spec fn body_ok(&self, at: usize) -> bool {
        self.body_len(at) matches Some(b) && b.inv() && b.complete_s()
    }

    /// The theorems that hold in every state: while the connection is
    /// open, the budget spent is within the budget; at most `max_streams`
    /// streams are open; every stream kept is odd and at most the highest
    /// opened.
    pub proof fn lemma_wf(&self)
        requires self.wf(),
        ensures
            !self.is_closing() ==> self.spent() <= self.budget(),
            self.open_streams() <= self.max_streams() as nat,
            self.last_id() <= MAX_ID,
    {
    }

    /// The nlive count is the same for any table of the same shape.
    proof fn lemma_shape(s: Seq<Slot<V>>)
        ensures forall|t: Seq<Slot<V>>| same_shape(t, s) ==> #[trigger] nlive_of(t) == nlive_of(s),
    {
        assert forall|t: Seq<Slot<V>>| same_shape(t, s) implies #[trigger] nlive_of(t) == nlive_of(s) by {
            assert forall|i: int| 0 <= i < t.len() implies (t[i].live is Some <==> s[i].live is Some) by {
                assert(t[i].id == s[i].id);
            }
            lemma_nlive_same(t, s);
        }
    }

    /// A new connection; writes our SETTINGS (no push, `max_streams`, the
    /// stream window) and a WINDOW_UPDATE that opens the connection window
    /// to `window`.
    pub fn new(limits: Limits2, out: &mut Vec<u8>) -> (r: Core<V>)
        ensures r.wf(), !r.is_closing(), r.last_id() == 0, r.open_streams() == 0,
    {
        let window = if limits.window as i64 > MAX_WINDOW { MAX_WINDOW as u32 } else { limits.window };
        let limits = Limits2 { window, ..limits };
        let params = [
            verilith_h2::Setting { id: S_MAX_CONCURRENT_STREAMS, value: limits.max_streams },
            verilith_h2::Setting { id: S_INITIAL_WINDOW_SIZE, value: window },
            verilith_h2::Setting { id: S_ENABLE_PUSH, value: 0 },
        ];
        let _ = verilith_h2::serialize_settings(&params, 16384, out);
        if window > 65535 {
            let _ = verilith_h2::serialize(&Frame::WindowUpdate { stream: 0, increment: window - 65535 }, 16384, out);
        }
        let r = Core {
            slots: Vec::new(),
            spare: Vec::new(),
            pool: Vec::new(),
            nlive: 0,
            last: 0,
            max_frame: 16384,
            initial_window: 65535,
            conn_send: SendWindow::new(65535),
            conn_recv: RecvWindow::new(window),
            block: None,
            control: 0,
            credit: BASE_CREDIT,
            draining: false,
            goaway_sent: false,
            closing: false,
            limits,
        };
        proof {
            assert(r.slots@ =~= Seq::<Slot<V>>::empty());
        }
        r
    }

    pub fn closing(&self) -> (r: bool)
        ensures r == self.is_closing(),
    {
        self.closing
    }

    /// The peer closed its side: stop.
    pub fn eof(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).is_closing(),
    {
        self.closing = true;
    }

    /// The peer's SETTINGS_MAX_FRAME_SIZE.
    pub fn max_frame(&self) -> (r: u32)
        requires self.wf(),
        ensures 16384 <= r <= 16777215,
    {
        self.max_frame
    }

    /// Open streams.
    pub fn open(&self) -> (r: usize)
        requires self.wf(),
        ensures r == self.open_streams(),
    {
        self.nlive
    }

    /// What may be sent on the connection now.
    pub fn conn_avail(&self) -> usize
        requires self.wf(),
    {
        self.conn_send.avail()
    }

    /// The slot of `id`, if one is kept (live or closed).
    fn find(&self, id: u32) -> (r: Option<usize>)
        requires self.wf(),
        ensures
            r matches Some(i) ==> i < self.slots@.len() && self.slots@[i as int].id == id,
            r is None ==> forall|i: int| 0 <= i < self.slots@.len() ==> self.slots@[i].id != id,
    {
        let n = self.slots.len();
        if n == 0 {
            return None;
        }
        // The newest stream is the likeliest.
        let top = self.slots[n - 1].id;
        if top == id {
            return Some(n - 1);
        }
        if top < id {
            return None;
        }
        let mut lo: usize = 0;
        let mut hi: usize = n - 1;
        while lo < hi
            invariant
                self.wf(),
                n == self.slots@.len(),
                lo <= hi < n,
                self.slots@[n - 1].id > id,
                forall|i: int| 0 <= i < lo ==> self.slots@[i].id < id,
                forall|i: int| hi <= i < n ==> self.slots@[i].id > id,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let m = self.slots[mid].id;
            if m == id {
                return Some(mid);
            }
            if m < id {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        None
    }

    /// The stream's slot and state, if it is live.
    fn lookup(&self, id: u32) -> (r: (Option<usize>, Option<St>))
        requires self.wf(),
        ensures
            r.1 is Some <==> r.0 is Some,
            r.0 matches Some(i) ==> i < self.slots@.len() && self.slots@[i as int].id == id
                && (self.slots@[i as int].live matches Some(l) && r.1 == Some(l.st)),
            r.0 is None ==> forall|i: int| 0 <= i < self.slots@.len() && self.slots@[i].id == id
                ==> self.slots@[i].live is None,
    {
        match self.find(id) {
            None => (None, None),
            Some(i) => match &self.slots[i].live {
                Some(l) => (Some(i), Some(l.st)),
                None => {
                    proof {
                        assert forall|j: int| 0 <= j < self.slots@.len() && self.slots@[j].id == id
                            implies self.slots@[j].live is None by {
                            if j != i as int {
                                assert(self.slots@[j].id != self.slots@[i as int].id);
                            }
                        }
                    }
                    (None, None)
                },
            },
        }
    }

    /// The ID of the stream in slot `at` (0 if there is none).
    pub fn id(&self, at: usize) -> (r: u32)
        requires self.wf(),
        ensures r == self.id_of(at),
    {
        if at < self.slots.len() { self.slots[at].id } else { 0 }
    }

    /// The live stream `id`'s slot; `hint` is checked first.
    pub fn locate(&self, id: u32, hint: usize) -> (r: Option<usize>)
        requires self.wf(),
    {
        if hint < self.slots.len() && self.slots[hint].id == id && self.slots[hint].live.is_some() {
            return Some(hint);
        }
        self.lookup(id).0
    }

    /// The buffers of the live stream in slot `at`.
    pub fn val(&mut self, at: usize) -> (r: Option<&mut V>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).is_closing() == old(self).is_closing(),
            final(self).is_draining() == old(self).is_draining(),
            final(self).last_id() == old(self).last_id(),
            final(self).spent() == old(self).spent(),
            final(self).budget() == old(self).budget(),
            final(self).open_streams() == old(self).open_streams(),
            final(self).in_block() == old(self).in_block(),
    {
        if at >= self.slots.len() {
            return None;
        }
        proof {
            Self::lemma_shape(self.slots@);
        }
        match self.slots[at].live.as_mut() {
            Some(l) => Some(&mut l.v),
            None => None,
        }
    }

    /// Spends `n` budget units; past the budget, GOAWAY(ENHANCE_YOUR_CALM).
    /// Whether the connection is still open.
    fn charge(&mut self, n: u64, out: &mut Vec<u8>) -> (ok: bool)
        requires old(self).wf(), n >= 1,
        ensures
            final(self).wf(),
            ok == !final(self).closing,
            final(self).control > old(self).control || final(self).closing,
            final(self).control >= old(self).control,
            ok ==> final(out)@ == old(out)@,
            old(self).closing ==> final(out)@ == old(out)@,
            old(self).closing ==> final(self).closing,
            final(self).slots@ == old(self).slots@,
            final(self).last == old(self).last,
            final(self).block == old(self).block,
            final(self).nlive == old(self).nlive,
            final(self).draining == old(self).draining,
            final(self).initial_window == old(self).initial_window,
            final(self).max_frame == old(self).max_frame,
            final(self).limits == old(self).limits,
            final(self).credit == old(self).credit,
    {
        if self.closing {
            return false;
        }
        if n > self.credit - self.control {
            self.control = self.credit;
            self.goaway(ENHANCE_YOUR_CALM, out);
            return false;
        }
        self.control = self.control + n;
        true
    }

    /// GOAWAY with `code`, naming the highest stream opened, unless one was
    /// sent already; then closing.
    fn goaway(&mut self, code: u32, out: &mut Vec<u8>)
        requires old(self).wf() || (old(self).wf_open() && old(self).control <= old(self).credit),
        ensures
            final(self).wf(),
            final(self).closing,
            final(self).slots@ == old(self).slots@,
            final(self).last == old(self).last,
            final(self).block == old(self).block,
            final(self).nlive == old(self).nlive,
            final(self).control == old(self).control,
            final(self).credit == old(self).credit,
            final(self).draining == old(self).draining,
            final(self).initial_window == old(self).initial_window,
            final(self).max_frame == old(self).max_frame,
            final(self).limits == old(self).limits,
            old(self).goaway_sent ==> final(out)@ == old(out)@,
            extends(old(out)@, final(out)@),
    {
        if !self.goaway_sent {
            let e: [u8; 0] = [];
            let ghost o = out@;
            let r = verilith_h2::serialize(&Frame::GoAway { last_stream: self.last, code, debug: &e }, 16384, out);
            proof {
                let f = spec::Frame::GoAway { last_stream: self.last, code, debug: e@ };
                assert(spec::payload_of(f).len() == 8);
                assert(r is Ok);
                assert(out@.take(o.len() as int) =~= o);
            }
            self.goaway_sent = true;
        } else {
            proof {
                lemma_extends_refl(out@);
            }
        }
        self.closing = true;
    }

    /// `wf` with the budget and closing parts left out.
    closed spec fn wf_open(&self) -> bool {
        let s = self.slots@;
        &&& sorted(s)
        &&& forall|i: int| 0 <= i < s.len() ==> slot_ok(#[trigger] s[i], self.last)
        &&& self.nlive == nlive_of(s)
        &&& self.nlive <= self.limits.max_streams
        &&& self.spare@.len() == 0
        &&& self.pool@.len() <= POOL
        &&& self.last <= MAX_ID
        &&& self.conn_send.inv()
        &&& self.conn_recv.inv()
        &&& self.initial_window <= MAX_WINDOW
        &&& self.limits.window <= MAX_WINDOW
        &&& 16384 <= self.max_frame <= 16777215
        &&& (self.block matches Some(b) ==> self.block_ok(b))
    }

    /// Closes the stream in slot `at`, if it is live; its buffers go to
    /// the pool. Draining with no stream left: GOAWAY and close.
    fn close(&mut self, at: usize, out: &mut Vec<u8>)
        requires old(self).wf(), at < old(self).slots@.len(),
        ensures
            final(self).wf(),
            final(self).slots@.len() == old(self).slots@.len(),
            forall|i: int| 0 <= i < old(self).slots@.len() ==> #[trigger] final(self).slots@[i].id == old(self).slots@[i].id,
            forall|i: int| 0 <= i < old(self).slots@.len() && i != at ==> #[trigger] final(self).slots@[i] == old(self).slots@[i],
            final(self).slots@[at as int].live is None,
            final(self).nlive <= old(self).nlive,
            final(self).last == old(self).last,
            final(self).control == old(self).control,
            final(self).credit == old(self).credit,
            final(self).draining == old(self).draining,
            final(self).initial_window == old(self).initial_window,
            final(self).max_frame == old(self).max_frame,
            final(self).limits == old(self).limits,
            final(self).block is Some == old(self).block is Some,
            old(self).closing ==> final(self).closing,
            extends(old(out)@, final(out)@),
    {
        let ghost s0 = self.slots@;
        let ghost o = out@;
        proof {
            lemma_extends_refl(o);
        }
        let gone = self.slots[at].live.take();
        match gone {
            Some(l) => {
                proof {
                    lemma_nlive_update(s0, at as int, self.slots@[at as int]);
                    assert(self.slots@ =~= s0.update(at as int, self.slots@[at as int]));
                    assert(self.slots@[at as int].id == s0[at as int].id);
                    assert(sorted(self.slots@));
                    assert(forall|i: int| 0 <= i < self.slots@.len() ==> slot_ok(#[trigger] self.slots@[i], self.last));
                }
                self.nlive = self.nlive - 1;
                let mut v = l.v;
                v.recycle();
                if self.pool.len() < POOL {
                    self.pool.push(v);
                }
                match self.block {
                    Some(b) => {
                        let on_slot = match b.mode {
                            Mode::Request | Mode::Trailers => true,
                            _ => false,
                        };
                        if b.at == at && on_slot {
                            self.block = Some(Block { mode: Mode::Dropped, ..b });
                        }
                    },
                    None => {},
                }
                if self.draining && self.nlive == 0 {
                    self.goaway(NO_ERROR, out);
                }
            },
            None => {
                proof {
                    assert(self.slots@ =~= s0);
                }
            },
        }
    }

    /// Drops the closed slots, keeping the order; no allocation once both
    /// vectors have grown.
    fn compact(&mut self)
        requires old(self).wf(), old(self).block is None,
        ensures
            final(self).wf(),
            final(self).same_conn(old(self)),
            final(self).slots@.len() == old(self).nlive,
    {
        let ghost n = self.nlive as nat;
        let ghost last = self.last;
        let mut a: Vec<Slot<V>> = Vec::new();
        let mut b: Vec<Slot<V>> = Vec::new();
        std::mem::swap(&mut a, &mut self.slots);
        std::mem::swap(&mut b, &mut self.spare);
        proof {
            assert(b@ =~= Seq::<Slot<V>>::empty());
        }
        while a.len() > 0
            invariant
                sorted(a@),
                desc(b@),
                forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> a@[i].id < b@[j].id,
                forall|i: int| 0 <= i < a@.len() ==> slot_ok(#[trigger] a@[i], last),
                forall|i: int| 0 <= i < b@.len() ==> slot_ok(#[trigger] b@[i], last),
                nlive_of(a@) + nlive_of(b@) == n,
            decreases a@.len(),
        {
            let ghost a0 = a@;
            let x = a.pop().unwrap();
            proof {
                assert(a@ =~= a0.drop_last());
                lemma_nlive_push(b@, x);
            }
            b.push(x);
        }
        proof {
            assert(a@ =~= Seq::<Slot<V>>::empty());
        }
        while b.len() > 0
            invariant
                sorted(a@),
                desc(b@),
                forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> a@[i].id < b@[j].id,
                forall|i: int| 0 <= i < a@.len() ==> slot_ok(#[trigger] a@[i], last),
                forall|i: int| 0 <= i < b@.len() ==> slot_ok(#[trigger] b@[i], last),
                forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).live is Some,
                nlive_of(a@) + nlive_of(b@) == n,
                nlive_of(a@) == a@.len(),
            decreases b@.len(),
        {
            let ghost b0 = b@;
            let x = b.pop().unwrap();
            proof {
                assert(b@ =~= b0.drop_last());
            }
            if x.live.is_some() {
                proof {
                    lemma_nlive_push(a@, x);
                }
                a.push(x);
            }
        }
        proof {
            assert(b@ =~= Seq::<Slot<V>>::empty());
        }
        std::mem::swap(&mut a, &mut self.slots);
        std::mem::swap(&mut b, &mut self.spare);
    }

    /// Opens stream `id` (a new odd ID) in a new slot.
    fn open_stream(&mut self, id: u32) -> (at: usize)
        requires
            old(self).wf(),
            !old(self).closing,
            !old(self).draining,
            old(self).block is None,
            id % 2 == 1,
            id > old(self).last,
            id <= MAX_ID,
            old(self).nlive < old(self).limits.max_streams,
        ensures
            final(self).wf(),
            final(self).last == id,
            final(self).nlive == old(self).nlive + 1,
            at < final(self).slots@.len(),
            final(self).slots@[at as int].id == id,
            final(self).slots@[at as int].live matches Some(l) && l.st == St::Open,
            final(self).control == old(self).control,
            final(self).credit == old(self).credit,
            !final(self).closing,
            final(self).goaway_sent == old(self).goaway_sent,
            final(self).draining == old(self).draining,
            final(self).block is None,
            final(self).limits == old(self).limits,
    {
        proof {
            lemma_nlive_le(self.slots@);
        }
        let dead = self.slots.len() - self.nlive;
        if self.nlive == 0 {
            // All closed (the usual case between bursts): nothing to move.
            self.slots.clear();
            proof {
                assert(self.slots@ =~= Seq::<Slot<V>>::empty());
            }
        } else if dead >= 32 && dead - 32 >= self.nlive {
            self.compact();
        }
        let v = match self.pool.pop() {
            Some(v) => v,
            None => V::fresh(),
        };
        let l = Live { st: St::Open, send: SendWindow::new(self.initial_window), recv: RecvWindow::new(self.limits.window), len: BodyLen::new(), resp: Resp::Waiting, v };
        let ghost s0 = self.slots@;
        proof {
            if s0.len() > 0 {
                lemma_ids_spread(s0, s0.len() - 1);
            }
        }
        self.last = id;
        self.slots.push(Slot { id, live: Some(l) });
        proof {
            lemma_nlive_push(s0, self.slots@.last());
            assert(self.slots@.drop_last() =~= s0);
        }
        self.nlive = self.nlive + 1;
        self.slots.len() - 1
    }

    /// RST_STREAM(`code`) for stream `id`, which is not idle, closing it;
    /// a unit of budget.
    fn rst(&mut self, id: u32, code: u32, out: &mut Vec<u8>)
        requires old(self).wf(), id % 2 == 1, id <= old(self).last,
        ensures
            final(self).wf(),
            final(self).last == old(self).last,
            final(self).nlive <= old(self).nlive,
            final(self).draining == old(self).draining,
            final(self).control > old(self).control || final(self).closing,
            final(self).block is Some == old(self).block is Some,
            old(self).closing ==> final(self).closing,
    {
        if !self.charge(1, out) {
            return;
        }
        let _ = verilith_h2::serialize(&Frame::RstStream { stream: id, code }, self.max_frame, out);
        match self.lookup(id).0 {
            Some(at) => self.close(at, out),
            None => {},
        }
    }

    /// A connection error.
    pub fn conn_error(&mut self, code: u32, out: &mut Vec<u8>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).is_closing(), final(self).last_id() == old(self).last_id(),
    {
        self.goaway(code, out);
    }

    /// A stream error the frame parser found (§5.4.2): RST_STREAM, or
    /// GOAWAY when the stream is idle or a header block is open.
    pub fn stream_error(&mut self, stream: u32, code: u32, out: &mut Vec<u8>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).last_id() == old(self).last_id(),
            final(self).spent() > old(self).spent() || final(self).is_closing(),
            final(self).open_streams() <= old(self).open_streams(),
    {
        if self.closing {
            return;
        }
        if self.block.is_some() {
            self.goaway(PROTOCOL_ERROR, out);
        } else if stream % 2 == 0 || stream > self.last {
            self.goaway(code, out);
        } else {
            self.rst(stream, code, out);
        }
    }

    /// Sets the live stream in slot `at` half-closed (remote).
    fn half_close(&mut self, at: usize)
        requires old(self).wf(), at < old(self).slots@.len(), old(self).slots@[at as int].live is Some,
            old(self).block is None,
        ensures final(self).wf(), final(self).same_conn(old(self)),
            same_shape(final(self).slots@, old(self).slots@),
            final(self).body_len(at) == old(self).body_len(at),
    {
        proof {
            Self::lemma_shape(self.slots@);
        }
        match self.slots[at].live.as_mut() {
            Some(l) => l.st = St::HalfClosed,
            None => {},
        }
    }

    /// A unit of budget, then `v`'s error, for a frame that names a
    /// stream and is not applied.
    fn act<'a>(&mut self, stream: u32, v: Verdict, out: &mut Vec<u8>) -> (r: Step<'a>)
        requires
            old(self).wf(),
            v is Stream ==> stream % 2 == 1 && stream <= old(self).last,
        ensures
            final(self).wf(),
            r is None,
            final(self).last == old(self).last,
            final(self).nlive <= old(self).nlive,
            final(self).draining == old(self).draining,
            final(self).control > old(self).control || final(self).closing,
    {
        match v {
            Verdict::Conn(c) => self.goaway(c, out),
            Verdict::Stream(c) => self.rst(stream, c, out),
            _ => {
                let _ = self.charge(1, out);
            },
        }
        Step::None
    }

    /// The fragment of the open header block.
    fn fragment<'a>(&mut self, frag: &'a [u8], end_headers: bool, out: &mut Vec<u8>) -> (r: Step<'a>)
        requires old(self).wf(), old(self).block is Some,
        ensures
            final(self).wf(),
            final(self).last == old(self).last,
            final(self).nlive == old(self).nlive,
            final(self).draining == old(self).draining,
            r is None || r is Fragment,
            r matches Step::Fragment { frag: g, end_headers: e, .. } ==> g == frag && e == end_headers,
            free(Frame::Continuation { stream: 1, end_headers, fragment: frag }, r)
                || final(self).control > old(self).control || final(self).closing,
            final(self).block is Some || final(self).closing,
    {
        let b = match self.block {
            Some(b) => b,
            None => {
                self.goaway(INTERNAL_ERROR, out);
                return Step::None;
            },
        };
        if self.closing {
            return Step::None;
        }
        if frag.len() > self.limits.max_header_block - b.len {
            self.goaway(ENHANCE_YOUR_CALM, out);
            return Step::None;
        }
        if frag.len() == 0 && !self.charge(1, out) {
            return Step::None;
        }
        self.block = Some(Block { len: b.len + frag.len(), ..b });
        let keep = match b.mode {
            Mode::Request => Some(b.at),
            _ => None,
        };
        Step::Fragment { frag, end_headers, keep }
    }

    /// The Content-Length `n` that the request on the live stream in slot
    /// `at` declares: false if the stream's body already rules it out.
    fn declare_len(&mut self, at: usize, n: u64) -> (ok: bool)
        requires old(self).wf(), at < old(self).slots@.len(),
        ensures final(self).wf(), final(self).same_conn(old(self)),
            same_shape(final(self).slots@, old(self).slots@),
            final(self).body_len(at) matches Some(b) ==> (ok ==> b.declared() == Some(n)),
            !ok ==> final(self).body_len(at) == old(self).body_len(at),
    {
        proof {
            Self::lemma_shape(self.slots@);
        }
        match self.slots[at].live.as_mut() {
            Some(l) => {
                l.len.declare(n)
            },
            None => false,
        }
    }

    /// Whether the stream in slot `at` is live and its body is complete
    /// as declared ([`Self::body_ok`]).
    fn len_complete(&self, at: usize) -> (r: bool)
        requires self.wf(),
        ensures r == self.body_ok(at),
    {
        if at >= self.slots.len() {
            return false;
        }
        match &self.slots[at].live {
            Some(l) => {
                proof {
                    assert(slot_ok(self.slots@[at as int], self.last));
                }
                l.len.complete()
            },
            None => false,
        }
    }

    /// The header block ended (its last fragment decoded): `fields_ok` if
    /// its fields are a valid request (§8.3), and `cl` the Content-Length
    /// they declare, parsed (§8.1.1).
    pub fn end_block<'a>(&mut self, fields_ok: bool, cl: Option<u64>, out: &mut Vec<u8>) -> (r: Step<'a>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            !final(self).in_block() || final(self).is_closing(),
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
            r is None || r is Dispatch,
            r matches Step::Dispatch { at } ==> final(self).body_ok(at),
    {
        if self.closing {
            return Step::None;
        }
        let b = match self.block {
            Some(b) => b,
            None => return Step::None,
        };
        self.block = None;
        match b.mode {
            Mode::Request => {
                let declared = match cl {
                    Some(n) => self.declare_len(b.at, n),
                    None => true,
                };
                if !fields_ok || !declared {
                    self.rst(b.stream, PROTOCOL_ERROR, out);
                    Step::None
                } else if b.end_stream {
                    // No DATA follows: a Content-Length must be 0.
                    if !self.len_complete(b.at) {
                        self.rst(b.stream, PROTOCOL_ERROR, out);
                        return Step::None;
                    }
                    self.half_close(b.at);
                    Step::Dispatch { at: b.at }
                } else {
                    Step::None
                }
            },
            Mode::Trailers => {
                // The body ends here: its DATA must add up to the
                // Content-Length (§8.1.1).
                if !self.len_complete(b.at) {
                    self.rst(b.stream, PROTOCOL_ERROR, out);
                    return Step::None;
                }
                self.half_close(b.at);
                Step::Dispatch { at: b.at }
            },
            Mode::Refused => {
                self.rst(b.stream, REFUSED_STREAM, out);
                Step::None
            },
            Mode::Dropped => Step::None,
        }
    }

    /// SETTINGS_INITIAL_WINDOW_SIZE changed by `delta`: every live
    /// stream's send window shifts (§6.9.2). False if one would leave
    /// ±(2^31 − 1).
    fn shift_all(&mut self, delta: i64) -> (ok: bool)
        requires old(self).wf(), -MAX_WINDOW <= delta <= MAX_WINDOW,
        ensures final(self).wf(), final(self).same_conn(old(self)),
            same_shape(final(self).slots@, old(self).slots@),
    {
        let n = self.slots.len();
        let mut i: usize = 0;
        let ghost s0 = self.slots@;
        proof {
            Self::lemma_shape(s0);
        }
        while i < n
            invariant
                self.wf(),
                self.same_conn(old(self)),
                same_shape(self.slots@, s0),
                s0 == old(self).slots@,
                n == s0.len(),
                -MAX_WINDOW <= delta <= MAX_WINDOW,
            decreases n - i,
        {
            proof {
                Self::lemma_shape(self.slots@);
            }
            match self.slots[i].live.as_mut() {
                Some(l) => {
                    if !l.send.shift(delta) {
                        return false;
                    }
                },
                None => {},
            }
            i = i + 1;
        }
        true
    }

    /// WINDOW_UPDATE of `inc` for the live stream in slot `at`.
    fn grant_stream(&mut self, at: usize, inc: u32) -> (ok: bool)
        requires old(self).wf(), at < old(self).slots@.len(),
        ensures final(self).wf(), final(self).same_conn(old(self)),
            same_shape(final(self).slots@, old(self).slots@),
    {
        proof {
            Self::lemma_shape(self.slots@);
        }
        match self.slots[at].live.as_mut() {
            Some(l) => l.send.grant(inc),
            None => true,
        }
    }

    /// Flow control, the body limit and the Content-Length (§8.1.1) for
    /// `n` flow-controlled bytes, `len` of them body, on the open stream
    /// in slot `at`; `end` if the body ends with them: the stream
    /// WINDOW_UPDATE due, or the stream error.
    fn stream_data(&mut self, at: usize, n: u32, len: usize, end: bool) -> (r: Result<Option<u32>, u32>)
        requires old(self).wf(), at < old(self).slots@.len(), old(self).slots@[at as int].live is Some,
            old(self).block is None,
        ensures final(self).wf(), final(self).same_conn(old(self)),
            same_shape(final(self).slots@, old(self).slots@),
            r is Ok ==> (final(self).body_len(at) matches Some(b) && old(self).body_len(at) matches Some(b0)
                && b.got() == b0.got() + len && b.declared() == b0.declared() && (end ==> b.complete_s())),
    {
        proof {
            Self::lemma_shape(self.slots@);
        }
        let max_body = self.limits.max_body;
        match self.slots[at].live.as_mut() {
            Some(l) => {
                let u = match l.recv.receive(n) {
                    Err(()) => return Err(FLOW_CONTROL_ERROR),
                    Ok(u) => u,
                };
                if len > max_body || l.len.received() > (max_body - len) as u64 {
                    return Err(REFUSED_STREAM);
                }
                // More DATA than the Content-Length, or (at the end) less,
                // makes the request malformed (§8.1.1).
                if !l.len.add(len as u64) {
                    return Err(PROTOCOL_ERROR);
                }
                if end {
                    if !l.len.complete() {
                        return Err(PROTOCOL_ERROR);
                    }
                    l.st = St::HalfClosed;
                }
                Ok(u)
            },
            None => Err(STREAM_CLOSED),
        }
    }

    /// Applies a frame (any but in a header block, CONTINUATION of it).
    pub fn on_frame<'a>(&mut self, f: &Frame<'a>, out: &mut Vec<u8>) -> (r: Step<'a>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).last_id() >= old(self).last_id(),
            // The flood theorem's per-frame half.
            free(*f, r) || final(self).spent() > old(self).spent() || final(self).is_closing(),
            // Only HEADERS opens a stream, and only one: the highest so far.
            final(self).open_streams() <= old(self).open_streams() + 1,
            final(self).open_streams() == old(self).open_streams() + 1 ==> (*f matches Frame::Headers { stream, .. }
                && stream > old(self).last_id() && final(self).last_id() == stream && !old(self).is_draining()),
            // SETTINGS is acknowledged; PING is answered.
            (*f matches Frame::Settings { ack: false, .. }) && !final(self).is_closing() ==> final(out)@ == old(out)@
                + spec::serialize(spec::Frame::Settings { ack: true, params: Seq::empty() }),
            *f matches Frame::Ping { ack: false, opaque } ==> (!final(self).is_closing() ==> final(out)@ == old(out)@
                + spec::serialize(spec::Frame::Ping { ack: true, opaque })),
            r is Data ==> *f is Data,
            // A request's DATA: counted on its live stream, and at the end
            // of the body equal to any Content-Length declared (§8.1.1).
            r matches Step::Data { at, data, end } ==> (final(self).body_len(at) matches Some(b) && b.inv()
                && (old(self).body_len(at) matches Some(b0) && b.got() == b0.got() + data@.len())
                && (end ==> b.complete_s())),
            old(self).is_closing() ==> final(self).is_closing() && r is None,
    {
        if self.closing {
            return Step::None;
        }
        // Inside a header block only its CONTINUATION may come (§6.10).
        match self.block {
            Some(b) => {
                match *f {
                    Frame::Continuation { stream, end_headers, fragment } => {
                        if stream == b.stream {
                            return self.fragment(fragment, end_headers, out);
                        }
                    },
                    _ => {},
                }
                self.goaway(PROTOCOL_ERROR, out);
                return Step::None;
            },
            None => {},
        }
        match *f {
            Frame::Settings { ack, params } => {
                let n = params.len();
                let cost: u64 = if n >= 1_000_000 { 1_000_000 } else { n as u64 + 1 };
                if !self.charge(cost, out) {
                    return Step::None;
                }
                if ack {
                    return Step::None;
                }
                let ghost out0 = out@;
                let ghost c0 = self.control;
                let mut i: usize = 0;
                while i < n
                    invariant
                        self.wf(),
                        !self.closing,
                        self.last == old(self).last,
                        self.nlive == old(self).nlive,
                        self.control == c0,
                        c0 > old(self).control,
                        out@ == out0,
                        n == params@.len(),
                    decreases n - i,
                {
                    let p = params.get(i);
                    if p.id == S_INITIAL_WINDOW_SIZE {
                        if p.value as i64 > MAX_WINDOW {
                            self.goaway(FLOW_CONTROL_ERROR, out);
                            return Step::None;
                        }
                        let delta = p.value as i64 - self.initial_window as i64;
                        self.initial_window = p.value;
                        if !self.shift_all(delta) {
                            self.goaway(FLOW_CONTROL_ERROR, out);
                            return Step::None;
                        }
                    } else if p.id == S_MAX_FRAME_SIZE {
                        if p.value < 16384 || p.value > 16777215 {
                            self.goaway(PROTOCOL_ERROR, out);
                            return Step::None;
                        }
                        self.max_frame = p.value;
                    }
                    i = i + 1;
                }
                let e: [u8; 0] = [];
                match Params::new(&e) {
                    Ok(p) => {
                        p.lemma_valid();
                        proof {
                            assert(e@ =~= Seq::<u8>::empty());
                            assert(p@ =~= Seq::<verilith_h2::Setting>::empty());
                        }
                        let _ = verilith_h2::serialize(&Frame::Settings { ack: true, params: p }, self.max_frame, out);
                    },
                    Err(_) => {},
                }
                Step::Settings
            },
            Frame::Ping { ack, opaque } => {
                if !self.charge(1, out) {
                    return Step::None;
                }
                if !ack {
                    let _ = verilith_h2::serialize(&Frame::Ping { ack: true, opaque }, self.max_frame, out);
                }
                Step::None
            },
            Frame::WindowUpdate { stream, increment } => {
                if !self.charge(1, out) {
                    return Step::None;
                }
                if stream == 0 {
                    if !self.conn_send.grant(increment) {
                        self.goaway(FLOW_CONTROL_ERROR, out);
                    }
                    return Step::None;
                }
                let (at, known) = self.lookup(stream);
                match classify(stream, self.last, known, Kind::WindowUpdate) {
                    Verdict::Accept => {
                        match at {
                            Some(at) => {
                                if !self.grant_stream(at, increment) {
                                    self.rst(stream, FLOW_CONTROL_ERROR, out);
                                }
                            },
                            None => {},
                        }
                        Step::None
                    },
                    Verdict::Conn(c) => {
                        self.goaway(c, out);
                        Step::None
                    },
                    _ => Step::None,
                }
            },
            Frame::Priority { stream, prio } => {
                if !self.charge(1, out) {
                    return Step::None;
                }
                if prio.dependency == stream {
                    // §5.3.1; RST_STREAM is not sent on an idle stream.
                    if stream % 2 == 0 || stream > self.last {
                        self.goaway(PROTOCOL_ERROR, out);
                    } else {
                        self.rst(stream, PROTOCOL_ERROR, out);
                    }
                }
                Step::None
            },
            Frame::RstStream { stream, .. } => {
                // Every reset costs a unit: the rapid reset attack
                // (CVE-2023-44487) is a reset after each request.
                if !self.charge(1, out) {
                    return Step::None;
                }
                let (at, known) = self.lookup(stream);
                match classify(stream, self.last, known, Kind::RstStream) {
                    Verdict::Accept => {
                        match at {
                            Some(at) => self.close(at, out),
                            None => {},
                        }
                        Step::None
                    },
                    Verdict::Conn(c) => {
                        self.goaway(c, out);
                        Step::None
                    },
                    _ => Step::None,
                }
            },
            Frame::GoAway { code, .. } => {
                if !self.charge(1, out) {
                    return Step::None;
                }
                if code == NO_ERROR {
                    // Finish the open streams, open no more.
                    self.draining = true;
                    if self.nlive == 0 {
                        self.goaway(NO_ERROR, out);
                    }
                } else {
                    // The peer reports an error: nothing to answer.
                    self.goaway_sent = true;
                    self.closing = true;
                }
                Step::None
            },
            Frame::PushPromise { .. } => {
                // §8.4: a client cannot push.
                self.goaway(PROTOCOL_ERROR, out);
                Step::None
            },
            Frame::Continuation { .. } => {
                // §6.10: not after a block's end.
                self.goaway(PROTOCOL_ERROR, out);
                Step::None
            },
            Frame::Unknown { .. } => {
                let _ = self.charge(1, out);
                Step::None
            },
            Frame::Headers { stream, end_stream, end_headers, priority, fragment, .. } => {
                let (at, known) = self.lookup(stream);
                let v = classify(stream, self.last, known, Kind::Headers { end_stream });
                let self_dep = match priority {
                    Some(p) => p.dependency == stream,
                    None => false,
                };
                match v {
                    Verdict::Open => {
                        // A stream cannot depend on itself (§5.3.1); its
                        // block cannot be skipped, so this ends the
                        // connection.
                        if self_dep || stream > MAX_ID {
                            self.goaway(PROTOCOL_ERROR, out);
                            return Step::None;
                        }
                        if self.draining || self.nlive >= self.limits.max_streams as usize {
                            self.last = stream;
                            self.block = Some(Block { stream, at: 0, end_stream, len: 0, mode: Mode::Refused });
                            if !self.charge(1, out) {
                                return Step::None;
                            }
                        } else {
                            let at = self.open_stream(stream);
                            self.block = Some(Block { stream, at, end_stream, len: 0, mode: Mode::Request });
                        }
                        self.fragment(fragment, end_headers, out)
                    },
                    Verdict::Trailers => {
                        if self_dep {
                            self.goaway(PROTOCOL_ERROR, out);
                            return Step::None;
                        }
                        match at {
                            Some(at) => {
                                self.block = Some(Block { stream, at, end_stream: true, len: 0, mode: Mode::Trailers });
                                self.fragment(fragment, end_headers, out)
                            },
                            None => {
                                self.goaway(INTERNAL_ERROR, out);
                                Step::None
                            },
                        }
                    },
                    v => self.act(stream, v, out),
                }
            },
            Frame::Data { stream, end_stream, pad, data } => {
                if data.len() > MAX_WINDOW as usize {
                    self.goaway(FLOW_CONTROL_ERROR, out);
                    return Step::None;
                }
                let flow: u32 = data.len() as u32 + match pad {
                    Some(p) => p as u32 + 1,
                    None => 0,
                };
                match self.conn_recv.receive(flow) {
                    Err(()) => {
                        self.goaway(FLOW_CONTROL_ERROR, out);
                        return Step::None;
                    },
                    Ok(Some(inc)) => {
                        let _ = verilith_h2::serialize(&Frame::WindowUpdate { stream: 0, increment: inc }, self.max_frame, out);
                    },
                    Ok(None) => {},
                }
                if flow == 0 && !end_stream {
                    if !self.charge(1, out) {
                        return Step::None;
                    }
                }
                let (at, known) = self.lookup(stream);
                match classify(stream, self.last, known, Kind::Data) {
                    Verdict::Accept => {},
                    v => return self.act(stream, v, out),
                }
                let at = match at {
                    Some(at) => at,
                    None => {
                        self.goaway(INTERNAL_ERROR, out);
                        return Step::None;
                    },
                };
                match self.stream_data(at, flow, data.len(), end_stream) {
                    Err(code) => {
                        self.rst(stream, code, out);
                        Step::None
                    },
                    Ok(update) => {
                        if !end_stream {
                            match update {
                                Some(inc) => {
                                    let _ = verilith_h2::serialize(&Frame::WindowUpdate { stream, increment: inc }, self.max_frame, out);
                                },
                                None => {},
                            }
                        }
                        Step::Data { at, data, end: end_stream }
                    },
                }
            },
        }
    }

    /// The response on the stream in slot `at` was sent in full: the
    /// stream closes, and the budget grows by `control_per_request`.
    fn finish(&mut self, at: usize, out: &mut Vec<u8>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            at < old(self).slots@.len() ==> final(self).slots@.len() == old(self).slots@.len()
                && final(self).slots@[at as int].live is None
                && final(self).slots@[at as int].id == old(self).slots@[at as int].id,
            extends(old(out)@, final(out)@),
            old(self).is_closing() ==> final(self).is_closing(),
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
            final(self).in_block() == old(self).in_block() || final(self).is_closing(),
    {
        if at >= self.slots.len() {
            proof {
                lemma_extends_refl(out@);
            }
            return;
        }
        let k = self.limits.control_per_request as u64;
        if self.slots[at].live.is_some() {
            self.credit = if self.credit > u64::MAX - k { u64::MAX } else { self.credit + k };
        }
        self.close(at, out);
    }

    /// The ID of the stream in slot `at` (0 if there is none).
    pub closed spec fn id_of(&self, at: usize) -> u32 {
        if at < self.slots@.len() { self.slots@[at as int].id } else { 0 }
    }

    /// Our response on the live stream in slot `at`; None if the slot
    /// holds no live stream.
    pub closed spec fn resp_of(&self, at: usize) -> Option<Resp> {
        if at < self.slots@.len() {
            match self.slots@[at as int].live {
                Some(l) => Some(l.resp),
                None => None,
            }
        } else {
            None
        }
    }

    /// Whether the live stream in slot `at` has its response's HEADERS
    /// sent; None if the slot holds no live stream.
    pub fn started(&self, at: usize) -> (r: Option<bool>)
        requires self.wf(),
        ensures
            r == match self.resp_of(at) {
                Some(Resp::Waiting) => Some(false),
                Some(_) => Some(true),
                None => None::<bool>,
            },
    {
        if at >= self.slots.len() {
            return None;
        }
        match &self.slots[at].live {
            Some(l) => match l.resp {
                Resp::Waiting => Some(false),
                Resp::Body { .. } => Some(true),
            },
            None => None,
        }
    }

    /// Starts the response on the live stream in slot `at`, if it has
    /// none yet: appends the HEADERS and CONTINUATION frames of `block`
    /// ([`header_frames`], END_STREAM if `body_len` is 0), and then
    /// expects `body_len` bytes of body. An empty body completes the
    /// response: the stream closes and the budget grows.
    pub fn send_headers(&mut self, at: usize, block: &[u8], body_len: usize, out: &mut Vec<u8>) -> (r: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r == (old(self).resp_of(at) == Some(Resp::Waiting)),
            !r ==> final(out)@ == old(out)@ && final(self).resp_of(at) == old(self).resp_of(at),
            r ==> extends(
                old(out)@ + ser_all(header_frames(old(self).id_of(at), block@, body_len == 0, CHUNK as nat)),
                final(out)@,
            ),
            r && body_len > 0 ==> final(self).resp_of(at) == Some(Resp::Body { len: body_len, off: 0 }),
            r && body_len == 0 ==> final(self).resp_of(at) is None,
            final(self).id_of(at) == old(self).id_of(at),
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
            old(self).is_closing() ==> final(self).is_closing(),
            final(self).in_block() == old(self).in_block() || final(self).is_closing(),
    {
        if at >= self.slots.len() {
            return false;
        }
        proof {
            Self::lemma_shape(self.slots@);
        }
        let id = self.slots[at].id;
        let max = self.max_frame;
        match self.slots[at].live.as_mut() {
            Some(l) => {
                match l.resp {
                    Resp::Body { .. } => return false,
                    Resp::Waiting => {},
                }
                if body_len > 0 {
                    l.resp = Resp::Body { len: body_len, off: 0 };
                }
            },
            None => return false,
        }
        proof {
            assert(self.slots@[at as int].id == id);
        }
        let ghost o = out@;
        write_headers(id, block, body_len == 0, max, out);
        if body_len == 0 {
            let ghost o1 = out@;
            self.finish(at, out);
            proof {
                assert(out@.take(o1.len() as int).take(o1.len() as int) =~= out@.take(o1.len() as int));
            }
        } else {
            proof {
                assert(out@.take(out@.len() as int) =~= out@);
            }
        }
        true
    }

    /// The next DATA frame of the response on the live stream in slot
    /// `at`, as much as the windows allow now, at most [`CHUNK`] bytes:
    /// `head`, for `h2.rs` to send followed by the body's bytes
    /// `off..off + n`. Frames follow one another through the body (each
    /// `off` is where the last ended), and END_STREAM is set on the one
    /// that reaches its end; once its bytes are written, [`Core::sent`]
    /// completes the response. None if the stream has no response under
    /// way, its body is all sent, or a window is spent.
    pub fn send_data(&mut self, at: usize, out: &mut Vec<u8>) -> (r: Option<DataOut>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id_of(at) == old(self).id_of(at),
            r is None ==> final(out)@ == old(out)@ && final(self).resp_of(at) == old(self).resp_of(at),
            r matches Some(d) ==> {
                &&& old(self).resp_of(at) matches Some(Resp::Body { len, off })
                &&& d.off == off
                &&& 0 < d.n <= CHUNK
                &&& d.off + d.n <= len
                &&& d.end == (d.off + d.n == len)
                &&& d.head@ == spec::enc_head(d.n as u32, spec::DATA, if d.end { 1u8 } else { 0u8 }, old(self).id_of(at))
                &&& 1 <= old(self).id_of(at) <= spec::MAX_31
                &&& final(self).resp_of(at) == Some(Resp::Body { len, off: (off + d.n) as usize })
            },
            final(out)@ == old(out)@,
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
            old(self).is_closing() ==> final(self).is_closing(),
            final(self).in_block() == old(self).in_block() || final(self).is_closing(),
    {
        if at >= self.slots.len() {
            return None;
        }
        proof {
            Self::lemma_shape(self.slots@);
        }
        let id = self.slots[at].id;
        let d = match self.slots[at].live.as_mut() {
            Some(l) => match l.resp {
                Resp::Body { len, off } => {
                    if off == len {
                        return None;
                    }
                    let n = take_data(&mut self.conn_send, &mut l.send, len - off, CHUNK);
                    if n == 0 {
                        return None;
                    }
                    let end = n == len - off;
                    l.resp = Resp::Body { len, off: off + n };
                    DataOut { head: data_head(id, n, end), off, n, end }
                },
                Resp::Waiting => return None,
            },
            None => return None,
        };
        Some(d)
    }

    /// The response on the live stream in slot `at` is sent in full (its
    /// last DATA frame is written): the stream closes, and the budget grows
    /// by `control_per_request`. Nothing for a stream whose response is
    /// not all framed.
    pub fn sent(&mut self, at: usize, out: &mut Vec<u8>) -> (r: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r == (old(self).resp_of(at) matches Some(Resp::Body { len, off }) && off == len),
            r ==> final(self).resp_of(at) is None && extends(old(out)@, final(out)@),
            !r ==> final(out)@ == old(out)@ && final(self).resp_of(at) == old(self).resp_of(at),
            final(self).id_of(at) == old(self).id_of(at),
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
            old(self).is_closing() ==> final(self).is_closing(),
            final(self).in_block() == old(self).in_block() || final(self).is_closing(),
    {
        if at >= self.slots.len() {
            return false;
        }
        let done = match &self.slots[at].live {
            Some(l) => match l.resp {
                Resp::Body { len, off } => off == len,
                Resp::Waiting => false,
            },
            None => false,
        };
        if done {
            self.finish(at, out);
        }
        done
    }

    /// RST_STREAM(`code`) for the live stream in slot `at` (a response
    /// that could not be sent).
    pub fn reset(&mut self, at: usize, code: u32, out: &mut Vec<u8>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).last_id() == old(self).last_id(),
            final(self).open_streams() <= old(self).open_streams(),
    {
        if at >= self.slots.len() || self.slots[at].live.is_none() {
            return;
        }
        let id = self.slots[at].id;
        self.rst(id, code, out);
    }
}

} // verus!

impl Default for Limits2 {
    fn default() -> Self {
        Limits2 { max_streams: 256, window: 1 << 20, max_header_block: 64 * 1024, max_body: 1 << 20, control_per_request: 100 }
    }
}
