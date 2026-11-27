//! Writing frames into a packet without passing its end (RFC 9000 §12.4,
//! §14; RFC 9002 §7), and the padding of a datagram.
//!
//! Proven: [`put_frame`] writes a frame (its type and varint fields) only
//! if it, and the bytes the caller reserves after it, fit before `end`, and
//! otherwise writes nothing; so a packet built only from such frames never
//! passes the end the sender gave it (the datagram size, the
//! anti-amplification allowance, or the congestion window's room). [`pad`]
//! never takes a datagram past its allowance, and pads one carrying an
//! ack-eliciting Initial packet to 1200 bytes when the allowance permits
//! (§14.1). [`packet_ends`] gives the ends for a packet's frames: the
//! datagram's room less the tag, and for ack-eliciting frames also the
//! congestion window's room (RFC 9002 §7), except for probes.
#[cfg(verus_only)]
use crate::lemmas::lemma_varint_size;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The fields' encodings, one after another.
pub open spec fn fields_enc(f: Seq<u64>) -> Seq<u8>
    decreases f.len(),
{
    if f.len() == 0 {
        Seq::empty()
    } else {
        fields_enc(f.drop_last()) + varint_enc(f.last())
    }
}

/// A frame: its type byte, then its fields.
pub open spec fn frame_enc(ty: u8, f: Seq<u64>) -> Seq<u8> {
    seq![ty] + fields_enc(f)
}

/// Appends frame type `ty` and the varints `f` to `out` if they, and
/// `extra` bytes after them, fit before `end` (and every field is below
/// 2^62); otherwise leaves `out` as it was.
pub fn put_frame(out: &mut Vec<u8>, end: usize, ty: u8, f: &[u64], extra: usize) -> (ok: bool)
    ensures
        ok ==> final(out)@ == old(out)@ + frame_enc(ty, f@),
        ok ==> final(out)@.len() + extra <= end,
        !ok ==> final(out)@ == old(out)@,
        ok == ((forall|i: int| 0 <= i < f@.len() ==> #[trigger] f@[i] < VARINT_LIMIT) && old(out)@.len()
            + frame_enc(ty, f@).len() + extra <= end),
{
    broadcast use lemma_varint_size;

    let len = out.len();
    proof {
        lemma_fields_len(f@);
    }
    if len > end || end - len < 1 || end - len - 1 < extra {
        return false;
    }
    let mut room = end - len - 1 - extra;
    let mut i = 0;
    while i < f.len()
        invariant
            0 <= i <= f@.len(),
            room == end - len - 1 - extra - fields_enc(f@.subrange(0, i as int)).len(),
            out@ == old(out)@,
            len == old(out)@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] f@[k] < VARINT_LIMIT,
        decreases f.len() - i,
    {
        proof {
            lemma_fields_step(f@, i as int);
        }
        if f[i] >= VARINT_LIMIT {
            return false;
        }
        let s = verilith_core::varint::size(f[i]);
        if s > room {
            proof {
                // The rest only adds to the length.
                lemma_fields_prefix_len(f@, i + 1);
                assert(varint_enc(f@[i as int]).len() == s);
                assert(fields_enc(f@.subrange(0, i + 1)).len() == fields_enc(f@.subrange(0, i as int)).len() + s);
                assert(frame_enc(ty, f@).len() == 1 + fields_enc(f@).len());
            }
            return false;
        }
        room = room - s;
        i = i + 1;
    }
    proof {
        assert(f@.subrange(0, f@.len() as int) =~= f@);
    }
    out.push(ty);
    let mut i = 0;
    while i < f.len()
        invariant
            0 <= i <= f@.len(),
            forall|k: int| 0 <= k < f@.len() ==> #[trigger] f@[k] < VARINT_LIMIT,
            out@ == old(out)@ + frame_enc(ty, f@.subrange(0, i as int)),
        decreases f.len() - i,
    {
        proof {
            lemma_fields_step(f@, i as int);
        }
        verilith_core::varint::write(out, f[i]);
        i = i + 1;
        proof {
            assert(out@ =~= old(out)@ + frame_enc(ty, f@.subrange(0, i as int)));
        }
    }
    proof {
        assert(f@.subrange(0, f@.len() as int) =~= f@);
    }
    true
}

proof fn lemma_fields_step(f: Seq<u64>, i: int)
    requires
        0 <= i < f.len(),
    ensures
        fields_enc(f.subrange(0, i + 1)) == fields_enc(f.subrange(0, i)) + varint_enc(f[i]),
{
    assert(f.subrange(0, i + 1).drop_last() =~= f.subrange(0, i));
}

proof fn lemma_fields_len(f: Seq<u64>)
    ensures
        fields_enc(f).len() >= 0,
    decreases f.len(),
{
}

/// A longer prefix encodes to at least as many bytes.
proof fn lemma_fields_prefix_len(f: Seq<u64>, i: int)
    requires
        0 <= i <= f.len(),
    ensures
        fields_enc(f.subrange(0, i)).len() <= fields_enc(f).len(),
    decreases f.len() - i,
{
    if i < f.len() {
        lemma_fields_step(f, i);
        lemma_fields_prefix_len(f, i + 1);
    } else {
        assert(f.subrange(0, i) =~= f);
    }
}

/// The ends for a packet's frames, when its header starts at `start` and
/// `room` bytes are left in the datagram, of which `cwnd_room` the
/// congestion window allows: `(end, end_e)`, where every frame ends by
/// `end` and an ack-eliciting one by `end_e`, each leaving `tag` bytes for
/// the AEAD tag. A probe (§6.2.4) is not limited by the window. `None` if
/// the room does not even hold the tag.
pub fn packet_ends(start: usize, room: usize, cwnd_room: usize, probing: bool, tag: usize) -> (r: Option<
    (usize, usize),
>)
    ensures
        r matches Some((end, end_e)) ==> {
            &&& end + tag == start + room
            &&& start <= end_e <= end
            &&& probing ==> end_e == end
            &&& !probing ==> end_e + tag <= start + cwnd_room || end_e == start
        },
        r is None ==> room < tag || start + room > usize::MAX,
{
    if room < tag || start > usize::MAX - room {
        return None;
    }
    let end = start + room - tag;
    let end_e = if probing {
        end
    } else if cwnd_room < tag {
        start
    } else if cwnd_room - tag < room - tag {
        start + (cwnd_room - tag)
    } else {
        end
    };
    Some((end, end_e))
}

/// The smallest datagram that may carry an ack-eliciting Initial packet
/// (§14.1).
pub const MIN_INITIAL: usize = 1200;

/// Bytes of PADDING for a datagram of `size` bytes, at most `allowance`:
/// up to 1200 bytes if it carries an ack-eliciting Initial packet, or else
/// up to `fill` (the batch's datagram size) if it comes within `slack` of
/// it.
pub fn pad(size: usize, allowance: usize, initial: bool, fill: Option<usize>, slack: usize) -> (r: usize)
    ensures
        size <= allowance ==> size + r <= allowance,
        size > allowance ==> r == 0,
        initial && size <= MIN_INITIAL && MIN_INITIAL <= allowance ==> size + r == MIN_INITIAL,
        initial && size >= MIN_INITIAL ==> r == 0,
        !initial ==> match fill {
            Some(f) => if size < f && f - size <= slack && f <= allowance {
                size + r == f
            } else {
                size + r <= f || r == 0
            },
            None => r == 0,
        },
{
    if size > allowance {
        return 0;
    }
    let room = allowance - size;
    let want = if initial {
        if size < MIN_INITIAL {
            MIN_INITIAL - size
        } else {
            0
        }
    } else {
        match fill {
            Some(f) => if size < f && f - size <= slack {
                f - size
            } else {
                0
            },
            None => 0,
        }
    };
    if want < room {
        want
    } else {
        room
    }
}

} // verus!
