//! Streams: their IDs and limits (§2.1, §4.6), and the sending and
//! receiving state machines (§3.1, §3.2) with their final sizes (§4.5) and
//! flow control (§4.1).
//!
//! The theorems are the types' invariants and the transition relations
//! `send_step` and `recv_step`, which are Figures 2 and 3 of RFC 9000:
//! every method moves a stream only along an arrow of its figure; a
//! stream's final size never changes once known, and no data is
//! accepted past it; a sender never sends past either flow control limit
//! and its RESET_STREAM carries exactly the bytes it sent; the peer never
//! opens more streams than were allowed.
use crate::flow::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Stream IDs (§2.1, §4.6)
// ---------------------------------------------------------------------------

/// Stream `id` was opened by the client (§2.1: its least significant bit
/// is 0).
pub open spec fn client_initiated(id: u64) -> bool {
    id % 2 == 0
}

/// Stream `id` is unidirectional (bit 0x02).
pub open spec fn unidirectional(id: u64) -> bool {
    (id % 4) / 2 == 1
}

/// The stream's index among those of its type: the `n`-th stream opened
/// of a type is `4 * n` plus its type bits.
pub open spec fn index(id: u64) -> nat {
    (id / 4) as nat
}

/// How a frame about stream `id` uses it: carrying the peer's data
/// (STREAM, RESET_STREAM, STREAM_DATA_BLOCKED), or controlling our data
/// (MAX_STREAM_DATA, STOP_SENDING).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Use {
    /// The peer sends on the stream.
    PeerSends,
    /// The peer receives on the stream.
    PeerReceives,
}

/// Streams opened and allowed, of one type.
#[derive(Clone, Copy)]
pub struct Count {
    /// How many have been opened.
    pub opened: u64,
    /// How many may be opened (MAX_STREAMS, initial_max_streams_*).
    pub max: u64,
}

impl Count {
    /// Never more opened than allowed, at most `2^60` (§4.6).
    pub open spec fn inv(self) -> bool {
        self.opened <= self.max <= MAX_STREAMS_LIMIT
    }
}

/// The streams of a connection, opened and allowed in each direction.
pub struct StreamIds {
    /// Whether this endpoint is the server.
    pub server: bool,
    /// Our bidirectional streams, against the peer's limit.
    pub local_bidi: Count,
    /// Our unidirectional streams, against the peer's limit.
    pub local_uni: Count,
    /// The peer's bidirectional streams, against our limit.
    pub remote_bidi: Count,
    /// The peer's unidirectional streams, against our limit.
    pub remote_uni: Count,
}

/// What a frame about a stream means for it (`StreamIds::on_frame`).
pub open spec fn frame_ok(ids: StreamIds, id: u64, u: Use) -> Result<(), u64> {
    let local = client_initiated(id) != ids.server;
    let uni = unidirectional(id);
    let c = if local {
        if uni { ids.local_uni } else { ids.local_bidi }
    } else if uni {
        ids.remote_uni
    } else {
        ids.remote_bidi
    };
    if local && uni && u == Use::PeerSends {
        // §19.8, §19.4, §19.13: a STREAM, RESET_STREAM or
        // STREAM_DATA_BLOCKED frame for a send-only stream.
        Err(STREAM_STATE_ERROR)
    } else if !local && uni && u == Use::PeerReceives {
        // §19.10, §19.5: MAX_STREAM_DATA or STOP_SENDING for a
        // receive-only stream.
        Err(STREAM_STATE_ERROR)
    } else if local && index(id) >= c.opened {
        // §19.8 and others: a frame for a locally initiated stream that
        // has not yet been created.
        Err(STREAM_STATE_ERROR)
    } else if !local && index(id) >= c.max {
        // §4.6: a stream past the limit.
        Err(STREAM_LIMIT_ERROR)
    } else {
        Ok(())
    }
}

impl StreamIds {
    /// Every count within its limit.
    pub open spec fn inv(&self) -> bool {
        &&& self.local_bidi.inv()
        &&& self.local_uni.inv()
        &&& self.remote_bidi.inv()
        &&& self.remote_uni.inv()
    }

    /// No streams yet; the peer may open up to the limits we advertise in
    /// initial_max_streams_bidi and _uni, and we up to the peer's.
    pub fn new(server: bool, our_bidi: u64, our_uni: u64, peer_bidi: u64, peer_uni: u64) -> (r: StreamIds)
        requires
            our_bidi <= MAX_STREAMS_LIMIT,
            our_uni <= MAX_STREAMS_LIMIT,
            peer_bidi <= MAX_STREAMS_LIMIT,
            peer_uni <= MAX_STREAMS_LIMIT,
        ensures
            r.inv(),
            r.server == server,
    {
        StreamIds {
            server,
            local_bidi: Count { opened: 0, max: peer_bidi },
            local_uni: Count { opened: 0, max: peer_uni },
            remote_bidi: Count { opened: 0, max: our_bidi },
            remote_uni: Count { opened: 0, max: our_uni },
        }
    }

    /// A frame from the peer about stream `id`, used as `u`: checks it
    /// (`frame_ok`) and, for a stream the peer opens, opens it and every
    /// stream of its type with a lower index (§3.2). Returns how many
    /// streams that opened.
    pub fn on_frame(&mut self, id: u64, u: Use) -> (r: Result<u64, u64>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).server == old(self).server,
            frame_ok(*old(self), id, u) matches Err(e) ==> r == Err::<u64, u64>(e) && *final(self)
                == *old(self),
            frame_ok(*old(self), id, u) is Ok ==> r is Ok,
            r matches Ok(n) ==> {
                let local = client_initiated(id) != old(self).server;
                let uni = unidirectional(id);
                &&& final(self).local_bidi == old(self).local_bidi
                &&& final(self).local_uni == old(self).local_uni
                &&& (local || uni ==> final(self).remote_bidi == old(self).remote_bidi)
                &&& (local || !uni ==> final(self).remote_uni == old(self).remote_uni)
                &&& (local ==> n == 0)
                &&& (!local && uni ==> final(self).remote_uni.opened == if index(id) + 1
                    > old(self).remote_uni.opened { index(id) + 1 } else { old(self).remote_uni.opened as nat }
                    && final(self).remote_uni.max == old(self).remote_uni.max && n
                    == final(self).remote_uni.opened - old(self).remote_uni.opened)
                &&& (!local && !uni ==> final(self).remote_bidi.opened == if index(id) + 1
                    > old(self).remote_bidi.opened { index(id) + 1 } else { old(self).remote_bidi.opened as nat }
                    && final(self).remote_bidi.max == old(self).remote_bidi.max && n
                    == final(self).remote_bidi.opened - old(self).remote_bidi.opened)
            },
    {
        let local = (id % 2 == 0) != self.server;
        let uni = (id % 4) / 2 == 1;
        let ix = id / 4;
        let peer_sends = match u {
            Use::PeerSends => true,
            Use::PeerReceives => false,
        };
        if local && uni && peer_sends {
            return Err(STREAM_STATE_ERROR);
        }
        if !local && uni && !peer_sends {
            return Err(STREAM_STATE_ERROR);
        }
        if local {
            let c = if uni { self.local_uni } else { self.local_bidi };
            if ix >= c.opened {
                return Err(STREAM_STATE_ERROR);
            }
            return Ok(0);
        }
        let c = if uni { self.remote_uni } else { self.remote_bidi };
        if ix >= c.max {
            return Err(STREAM_LIMIT_ERROR);
        }
        if ix < c.opened {
            return Ok(0);
        }
        let n = ix + 1 - c.opened;
        let c2 = Count { opened: ix + 1, max: c.max };
        if uni {
            self.remote_uni = c2;
        } else {
            self.remote_bidi = c2;
        }
        Ok(n)
    }

    /// Opens a stream of ours, if the peer's limit allows (§4.6): its ID.
    /// `None` means STREAMS_BLOCKED.
    pub fn open(&mut self, uni: bool) -> (r: Option<u64>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).server == old(self).server,
            final(self).remote_bidi == old(self).remote_bidi,
            final(self).remote_uni == old(self).remote_uni,
            r is None ==> *final(self) == *old(self),
            r matches Some(id) ==> {
                let c = if uni { old(self).local_uni } else { old(self).local_bidi };
                &&& c.opened < c.max
                &&& id < VARINT_LIMIT
                &&& index(id) == c.opened
                &&& unidirectional(id) == uni
                &&& client_initiated(id) == !old(self).server
                &&& (if uni { final(self).local_uni } else { final(self).local_bidi }) == Count {
                    opened: (c.opened + 1) as u64,
                    max: c.max,
                }
                &&& (if uni { final(self).local_bidi == old(self).local_bidi } else { final(self).local_uni
                    == old(self).local_uni })
            },
    {
        let c = if uni { self.local_uni } else { self.local_bidi };
        if c.opened >= c.max {
            return None;
        }
        let id = c.opened * 4 + (if uni { 2 } else { 0 }) + (if self.server { 1 } else { 0 });
        let c2 = Count { opened: c.opened + 1, max: c.max };
        if uni {
            self.local_uni = c2;
        } else {
            self.local_bidi = c2;
        }
        Some(id)
    }

    /// A MAX_STREAMS frame from the peer: §4.6, "MAX_STREAMS frames that
    /// do not increase the stream limit MUST be ignored."
    pub fn on_max_streams(&mut self, bidi: bool, max: u64)
        requires
            old(self).inv(),
            max <= MAX_STREAMS_LIMIT,
        ensures
            final(self).inv(),
            final(self).server == old(self).server,
            final(self).remote_bidi == old(self).remote_bidi,
            final(self).remote_uni == old(self).remote_uni,
            bidi ==> final(self).local_uni == old(self).local_uni && final(self).local_bidi.opened
                == old(self).local_bidi.opened && final(self).local_bidi.max == if max > old(self).local_bidi.max {
                max
            } else {
                old(self).local_bidi.max
            },
            !bidi ==> final(self).local_bidi == old(self).local_bidi && final(self).local_uni.opened
                == old(self).local_uni.opened && final(self).local_uni.max == if max > old(self).local_uni.max {
                max
            } else {
                old(self).local_uni.max
            },
    {
        if bidi {
            if max > self.local_bidi.max {
                self.local_bidi.max = max;
            }
        } else if max > self.local_uni.max {
            self.local_uni.max = max;
        }
    }

    /// Raises the limit we give the peer (to send in MAX_STREAMS).
    pub fn allow(&mut self, bidi: bool, max: u64)
        requires
            old(self).inv(),
            max <= MAX_STREAMS_LIMIT,
        ensures
            final(self).inv(),
            final(self).server == old(self).server,
            final(self).local_bidi == old(self).local_bidi,
            final(self).local_uni == old(self).local_uni,
            bidi ==> final(self).remote_uni == old(self).remote_uni && final(self).remote_bidi.opened
                == old(self).remote_bidi.opened && final(self).remote_bidi.max >= old(self).remote_bidi.max,
            !bidi ==> final(self).remote_bidi == old(self).remote_bidi && final(self).remote_uni.opened
                == old(self).remote_uni.opened && final(self).remote_uni.max >= old(self).remote_uni.max,
    {
        if bidi {
            if max > self.remote_bidi.max {
                self.remote_bidi.max = max;
            }
        } else if max > self.remote_uni.max {
            self.remote_uni.max = max;
        }
    }
}

// ---------------------------------------------------------------------------
// Receiving (§3.2, §4.5)
// ---------------------------------------------------------------------------

/// The states of the receiving part of a stream (§3.2, Figure 3).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RecvState {
    /// Receiving data, final size not yet known.
    Recv,
    /// A STREAM frame with FIN arrived: the final size is known.
    SizeKnown,
    /// All data up to the final size has arrived.
    DataRecvd,
    /// The application has read all the data.
    DataRead,
    /// A RESET_STREAM arrived.
    ResetRecvd,
    /// The application has been told of the reset.
    ResetRead,
}

/// The arrows of Figure 3 (and staying put).
pub open spec fn recv_step(a: RecvState, b: RecvState) -> bool {
    a == b || match (a, b) {
        (RecvState::Recv, RecvState::SizeKnown) => true,
        (RecvState::Recv, RecvState::ResetRecvd) => true,
        (RecvState::SizeKnown, RecvState::DataRecvd) => true,
        (RecvState::SizeKnown, RecvState::ResetRecvd) => true,
        (RecvState::DataRecvd, RecvState::DataRead) => true,
        (RecvState::ResetRecvd, RecvState::ResetRead) => true,
        _ => false,
    }
}

/// The receiving part of a stream.
pub struct RecvStream {
    state: RecvState,
    final_size: Option<u64>,
    credit: RecvCredit,
}

impl RecvStream {
    /// Its state.
    pub closed spec fn state(&self) -> RecvState {
        self.state
    }

    /// Its final size, once known.
    pub closed spec fn final_size(&self) -> Option<u64> {
        self.final_size
    }

    /// The largest offset received (the stream's flow control credit used).
    pub closed spec fn highest(&self) -> nat {
        self.credit.used()
    }

    /// The stream's flow control limit.
    pub closed spec fn max(&self) -> nat {
        self.credit.max()
    }

    /// The final size is known exactly outside `Recv`, and no data was
    /// received past it or past the flow control limit.
    pub open spec fn inv(&self) -> bool {
        &&& self.highest() <= self.max() < VARINT_LIMIT
        &&& (self.state() == RecvState::Recv) == (self.final_size() is None)
        &&& (self.final_size() matches Some(f) ==> self.highest() <= f)
    }

    /// A new stream whose limit is `max` (initial_max_stream_data_*).
    pub fn new(max: u64) -> (r: RecvStream)
        requires
            max < VARINT_LIMIT,
        ensures
            r.inv(),
            r.state() == RecvState::Recv,
            r.highest() == 0,
            r.max() == max,
    {
        RecvStream { state: RecvState::Recv, final_size: None, credit: RecvCredit::new(max) }
    }

    /// The state.
    pub fn get_state(&self) -> (r: RecvState)
        ensures
            r == self.state(),
    {
        self.state
    }

    /// The final size, once known.
    pub fn get_final_size(&self) -> (r: Option<u64>)
        ensures
            r == self.final_size(),
    {
        self.final_size
    }

    /// Raises the stream's limit (to send in MAX_STREAM_DATA).
    pub fn raise(&mut self, max: u64)
        requires
            old(self).inv(),
            max < VARINT_LIMIT,
        ensures
            final(self).inv(),
            final(self).state() == old(self).state(),
            final(self).final_size() == old(self).final_size(),
            final(self).highest() == old(self).highest(),
            final(self).max() >= old(self).max(),
    {
        self.credit.raise(max);
    }

    /// Checks the bytes up to `end` against the final size and both
    /// limits, and takes the credit; `fin` says `end` is the final size.
    fn account(&mut self, conn: &mut RecvCredit, end: u64, fin: bool) -> (r: Result<(), u64>)
        requires
            old(self).inv(),
            old(conn).inv(),
            end < VARINT_LIMIT,
        ensures
            r is Err ==> *final(self) == *old(self) && *final(conn) == *old(conn),
            final(conn).inv(),
            r is Ok ==> {
                &&& old(self).final_size() matches Some(f) ==> end <= f && (fin ==> end == f)
                &&& old(self).final_size() is None && fin ==> end >= old(self).highest()
                &&& end <= old(self).max()
                &&& final(self).state() == old(self).state()
                &&& final(self).final_size() == old(self).final_size()
                &&& final(self).max() == old(self).max()
                &&& final(self).highest() == if end > old(self).highest() { end as nat } else { old(self).highest() }
                &&& final(conn).max() == old(conn).max()
                &&& final(conn).used() == old(conn).used() + (final(self).highest() - old(self).highest())
            },
            r matches Err(e) ==> e == FINAL_SIZE_ERROR || e == FLOW_CONTROL_ERROR,
    {
        if let Some(f) = self.final_size {
            if end > f || (fin && end != f) {
                return Err(FINAL_SIZE_ERROR);
            }
        } else if fin && end < self.credit.consumed() {
            return Err(FINAL_SIZE_ERROR);
        }
        let used = self.credit.consumed();
        if end <= used {
            return Ok(());
        }
        let delta = end - used;
        if end > self.credit.limit() {
            return Err(FLOW_CONTROL_ERROR);
        }
        if !conn.take(delta) {
            return Err(FLOW_CONTROL_ERROR);
        }
        let ok = self.credit.take(delta);
        assert(ok);
        Ok(())
    }

    /// A STREAM frame (§19.8) carrying `len` bytes at `offset`, counted
    /// against this stream's and the connection's limits. FIN moves
    /// `Recv` to `SizeKnown`. Errors are FINAL_SIZE_ERROR (§4.5) and
    /// FLOW_CONTROL_ERROR (§4.1), and change nothing.
    pub fn on_stream(&mut self, conn: &mut RecvCredit, offset: u64, len: u64, fin: bool) -> (r: Result<(), u64>)
        requires
            old(self).inv(),
            old(conn).inv(),
            offset + len <= VARINT_MAX,
        ensures
            final(self).inv(),
            final(conn).inv(),
            recv_step(old(self).state(), final(self).state()),
            old(self).final_size() is Some ==> final(self).final_size() == old(self).final_size(),
            r is Err ==> *final(self) == *old(self) && *final(conn) == *old(conn),
            r is Ok ==> final(self).highest() >= offset + len,
            r is Ok && fin ==> final(self).final_size() == Some((offset + len) as u64),
            r is Ok ==> final(conn).used() - old(conn).used() == final(self).highest() - old(self).highest(),
            r is Ok ==> (final(self).state() != old(self).state() ==> old(self).state() == RecvState::Recv
                && final(self).state() == RecvState::SizeKnown),
    {
        let end = offset + len;
        match self.account(conn, end, fin) {
            Err(e) => return Err(e),
            Ok(()) => {},
        }
        if fin && matches!(self.state, RecvState::Recv) {
            self.state = RecvState::SizeKnown;
            self.final_size = Some(end);
        }
        Ok(())
    }

    /// A RESET_STREAM frame (§19.4) with final size `final_size`: moves
    /// `Recv` and `SizeKnown` to `ResetRecvd` (in `DataRecvd` and later
    /// it changes nothing but is still checked). The final size counts
    /// against both limits (§4.5).
    pub fn on_reset(&mut self, conn: &mut RecvCredit, final_size: u64) -> (r: Result<(), u64>)
        requires
            old(self).inv(),
            old(conn).inv(),
            final_size < VARINT_LIMIT,
        ensures
            final(self).inv(),
            final(conn).inv(),
            recv_step(old(self).state(), final(self).state()),
            old(self).final_size() is Some ==> final(self).final_size() == old(self).final_size(),
            r is Err ==> *final(self) == *old(self) && *final(conn) == *old(conn),
            r is Ok ==> final(self).final_size() == Some(final_size),
            r is Ok ==> final(conn).used() - old(conn).used() == final(self).highest() - old(self).highest(),
            r is Ok && (old(self).state() == RecvState::Recv || old(self).state() == RecvState::SizeKnown)
                ==> final(self).state() == RecvState::ResetRecvd,
    {
        match self.account(conn, final_size, true) {
            Err(e) => return Err(e),
            Ok(()) => {},
        }
        if matches!(self.state, RecvState::Recv | RecvState::SizeKnown) {
            self.state = RecvState::ResetRecvd;
            self.final_size = Some(final_size);
        }
        Ok(())
    }

    /// All bytes up to the final size have arrived (the reassembly
    /// buffer's report): `SizeKnown` to `DataRecvd`.
    pub fn on_all_received(&mut self)
        requires
            old(self).inv(),
            old(self).state() == RecvState::SizeKnown,
        ensures
            final(self).inv(),
            final(self).state() == RecvState::DataRecvd,
            final(self).final_size() == old(self).final_size(),
            final(self).highest() == old(self).highest(),
    {
        self.state = RecvState::DataRecvd;
    }

    /// The application read everything: `DataRecvd` to `DataRead`.
    pub fn on_read_all(&mut self)
        requires
            old(self).inv(),
            old(self).state() == RecvState::DataRecvd,
        ensures
            final(self).inv(),
            final(self).state() == RecvState::DataRead,
            final(self).final_size() == old(self).final_size(),
    {
        self.state = RecvState::DataRead;
    }

    /// The application was told of the reset: `ResetRecvd` to
    /// `ResetRead`.
    pub fn on_reset_read(&mut self)
        requires
            old(self).inv(),
            old(self).state() == RecvState::ResetRecvd,
        ensures
            final(self).inv(),
            final(self).state() == RecvState::ResetRead,
            final(self).final_size() == old(self).final_size(),
    {
        self.state = RecvState::ResetRead;
    }
}

// ---------------------------------------------------------------------------
// Sending (§3.1, §4.5)
// ---------------------------------------------------------------------------

/// The states of the sending part of a stream (§3.1, Figure 2).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SendState {
    /// Created, nothing sent.
    Ready,
    /// Sending data.
    Send,
    /// Sent the FIN.
    DataSent,
    /// All data acknowledged.
    DataRecvd,
    /// Sent a RESET_STREAM.
    ResetSent,
    /// The RESET_STREAM was acknowledged.
    ResetRecvd,
}

/// The arrows of Figure 2 (and staying put).
pub open spec fn send_step(a: SendState, b: SendState) -> bool {
    a == b || match (a, b) {
        (SendState::Ready, SendState::Send) => true,
        (SendState::Ready, SendState::DataSent) => true,
        (SendState::Ready, SendState::ResetSent) => true,
        (SendState::Send, SendState::DataSent) => true,
        (SendState::Send, SendState::ResetSent) => true,
        (SendState::DataSent, SendState::DataRecvd) => true,
        (SendState::DataSent, SendState::ResetSent) => true,
        (SendState::ResetSent, SendState::ResetRecvd) => true,
        _ => false,
    }
}

/// The sending part of a stream.
pub struct SendStream {
    state: SendState,
    credit: SendCredit,
}

impl SendStream {
    /// Its state.
    pub closed spec fn state(&self) -> SendState {
        self.state
    }

    /// The bytes sent so far: the offset of the next one, the credit used.
    pub closed spec fn sent(&self) -> nat {
        self.credit.used()
    }

    /// The peer's limit for the stream.
    pub closed spec fn max(&self) -> nat {
        self.credit.max()
    }

    /// Never past the peer's limit.
    pub open spec fn inv(&self) -> bool {
        self.sent() <= self.max() < VARINT_LIMIT
    }

    /// A new stream; `max` is the peer's initial_max_stream_data_* for it.
    pub fn new(max: u64) -> (r: SendStream)
        requires
            max < VARINT_LIMIT,
        ensures
            r.inv(),
            r.state() == SendState::Ready,
            r.sent() == 0,
            r.max() == max,
    {
        SendStream { state: SendState::Ready, credit: SendCredit::new(max) }
    }

    /// The state.
    pub fn get_state(&self) -> (r: SendState)
        ensures
            r == self.state(),
    {
        self.state
    }

    /// How many bytes may be sent now, given the connection's credit.
    pub fn available(&self, conn: &SendCredit) -> (r: u64)
        requires
            self.inv(),
            conn.inv(),
        ensures
            r <= self.max() - self.sent(),
            r <= conn.max() - conn.used(),
    {
        let a = self.credit.available();
        let b = conn.available();
        if a < b {
            a
        } else {
            b
        }
    }

    /// A MAX_STREAM_DATA from the peer (ignored unless it raises the
    /// limit, §4.1).
    pub fn on_max_stream_data(&mut self, max: u64)
        requires
            old(self).inv(),
            max < VARINT_LIMIT,
        ensures
            final(self).inv(),
            final(self).state() == old(self).state(),
            final(self).sent() == old(self).sent(),
            final(self).max() >= old(self).max(),
    {
        self.credit.on_max(max);
    }

    /// Sends `n` new bytes, and the FIN with them if `fin`: returns their
    /// offset. Only in `Ready` or `Send`, and within both limits.
    pub fn send(&mut self, conn: &mut SendCredit, n: u64, fin: bool) -> (offset: u64)
        requires
            old(self).inv(),
            old(conn).inv(),
            old(self).state() == SendState::Ready || old(self).state() == SendState::Send,
            old(self).sent() + n <= old(self).max(),
            old(conn).used() + n <= old(conn).max(),
        ensures
            final(self).inv(),
            final(conn).inv(),
            send_step(old(self).state(), final(self).state()),
            offset == old(self).sent(),
            final(self).sent() == old(self).sent() + n,
            final(conn).used() == old(conn).used() + n,
            final(conn).max() == old(conn).max(),
            final(self).state() == if fin { SendState::DataSent } else { SendState::Send },
    {
        let offset = self.credit.spent();
        self.credit.spend(n);
        conn.spend(n);
        self.state = if fin { SendState::DataSent } else { SendState::Send };
        offset
    }

    /// Abandons the stream (on the application's request, or a
    /// STOP_SENDING): `ResetSent`, and returns the final size for the
    /// RESET_STREAM frame, which is exactly the bytes sent (§4.5: "the
    /// amount of flow control credit that is consumed by a stream").
    pub fn reset(&mut self) -> (final_size: u64)
        requires
            old(self).inv(),
            old(self).state() == SendState::Ready || old(self).state() == SendState::Send || old(self).state()
                == SendState::DataSent,
        ensures
            final(self).inv(),
            send_step(old(self).state(), final(self).state()),
            final(self).state() == SendState::ResetSent,
            final_size == old(self).sent(),
            final(self).sent() == old(self).sent(),
    {
        self.state = SendState::ResetSent;
        self.credit.spent()
    }

    /// All data, through the FIN, was acknowledged.
    pub fn on_all_acked(&mut self)
        requires
            old(self).inv(),
            old(self).state() == SendState::DataSent,
        ensures
            final(self).inv(),
            final(self).state() == SendState::DataRecvd,
            final(self).sent() == old(self).sent(),
    {
        self.state = SendState::DataRecvd;
    }

    /// The RESET_STREAM was acknowledged.
    pub fn on_reset_acked(&mut self)
        requires
            old(self).inv(),
            old(self).state() == SendState::ResetSent,
        ensures
            final(self).inv(),
            final(self).state() == SendState::ResetRecvd,
    {
        self.state = SendState::ResetRecvd;
    }
}

} // verus!
