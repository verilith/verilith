//! The framing format: a decoder proven equal to `spec::stream`, and an
//! encoder proven to round-trip through it.
#[cfg(verus_only)]
use crate::compress::extends;
use crate::compress::compress_into;
#[cfg(verus_only)]
use crate::decode::lemma_elems_len;
use crate::decode::{decompress_into, read_le, Error};
use crate::spec::*;
use verilith_checksum::crc32c as crc_exec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A checksum as the framing format stores it.
pub fn masked(crc: u32) -> (r: u32)
    ensures
        r as nat == mask(crc),
{
    ((crc >> 15) | (crc << 17)).wrapping_add(0xa282ead8)
}

/// Why decoding a stream failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FrameError {
    /// The input is not what the format allows (or a checksum is wrong).
    Corrupt,
    /// The content is longer than the limit given.
    TooLarge,
}

/// The stream identifier chunk.
pub const STREAM_ID: [u8; 10] = [0xff, 6, 0, 0, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59];

/// What `chunks` gives is no shorter than what it started from.
pub proof fn lemma_chunks_len(s: Seq<u8>, i: int, out: Seq<u8>)
    ensures
        chunks(s, i, out) matches Some(o) ==> o.len() >= out.len(),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && i + 4 <= s.len() {
        let t = s[i];
        let j = i + 4;
        let e = j + le(s, i + 1, 3);
        if e <= s.len() {
            if t == 0 || t == 1 {
                if e - j >= 4 {
                    let data = if t == 0 {
                        decompress(s.subrange(j + 4, e))
                    } else {
                        Some(s.subrange(j + 4, e))
                    };
                    if data.is_some() {
                        lemma_chunks_len(s, e, out + data.unwrap());
                    }
                }
            } else {
                lemma_chunks_len(s, e, out);
            }
        }
    }
}

/// Whether the 10 bytes at `i` are the stream identifier.
fn is_stream_id(src: &[u8], i: usize) -> (r: bool)
    requires
        i + 10 <= src@.len(),
    ensures
        r == (src@.subrange(i as int, i + 10) == stream_id()),
{
    let n = src.len();
    let mut k: usize = 0;
    while k < 10
        invariant
            k <= 10,
            n == src@.len(),
            i + 10 <= n,
            forall|t: int| 0 <= t < k ==> src@[i + t] == #[trigger] stream_id()[t],
        decreases 10 - k,
    {
        if src[i + k] != STREAM_ID[k] {
            proof {
                assert(src@.subrange(i as int, i + 10)[k as int] == src@[i + k]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(src@.subrange(i as int, i + 10) =~= stream_id());
    }
    true
}

/// Decodes a stream (`spec::stream`).
///
/// - `Ok(v)`: `src` is valid and `v` is its content, at most `limit`
///   long.
/// - `Err(Corrupt)`: `src` is not valid.
/// - `Err(TooLarge)`: `src` is not valid, or its content is longer than
///   `limit`.
pub fn frame_decode(src: &[u8], limit: usize) -> (r: Result<Vec<u8>, FrameError>)
    ensures
        match r {
            Ok(v) => stream(src@) == Some(v@) && v@.len() <= limit,
            Err(FrameError::Corrupt) => stream(src@).is_none(),
            Err(FrameError::TooLarge) => stream(src@) matches Some(o) ==> o.len() > limit,
        },
{
    let n = src.len();
    if n == 0 {
        return Ok(Vec::new());
    }
    if n < 10 || !is_stream_id(src, 0) {
        return Err(FrameError::Corrupt);
    }
    let mut out: Vec<u8> = Vec::new();
    let mut scratch: Vec<u8> = Vec::new();
    scratch.resize(65536, 0);
    let mut i: usize = 10;
    while i < n
        invariant
            n == src@.len(),
            10 <= i <= n,
            scratch@.len() == 65536,
            out@.len() <= limit,
            chunks(src@, i as int, out@) == stream(src@),
        decreases n - i,
    {
        if n - i < 4 {
            return Err(FrameError::Corrupt);
        }
        let ghost goal = stream(src@);
        let ghost out0 = out@;
        let t = src[i];
        let len = read_le(src, i + 1, 3);
        let j = i + 4;
        if len > n - j {
            return Err(FrameError::Corrupt);
        }
        let e = j + len;
        if t == 0 || t == 1 {
            if len < 4 {
                return Err(FrameError::Corrupt);
            }
            let crc = read_le(src, j, 4);
            let body = slice_subrange(src, j + 4, e);
            proof {
                assert(body@ == src@.subrange(j + 4, e as int));
                if t == 0 {
                    // What a chunk decompresses to is as long as it says.
                    match varint(body@, 0, 0) {
                        Some((dn, di)) => {
                            lemma_elems_len(body@, di, Seq::empty(), dn);
                        },
                        None => {},
                    }
                }
            }
            if t == 1 {
                if body.len() > 65536 || masked(crc_exec(body)) as usize != crc {
                    return Err(FrameError::Corrupt);
                }
                if body.len() > limit - out.len() {
                    proof {
                        lemma_chunks_len(src@, e as int, out@ + body@);
                    }
                    return Err(FrameError::TooLarge);
                }
                out.extend_from_slice(body);
                assert(chunks(src@, e as int, out0 + body@) == goal);
                assert(out@ =~= out0 + body@);
            } else {
                let m = match decompress_into(body, scratch.as_mut_slice()) {
                    Ok(m) => m,
                    Err(_) => {
                        return Err(FrameError::Corrupt);
                    },
                };
                let data = slice_subrange(scratch.as_slice(), 0, m);
                assert(decompress(body@) == Some(data@));
                if masked(crc_exec(data)) as usize != crc {
                    return Err(FrameError::Corrupt);
                }
                if m > limit - out.len() {
                    proof {
                        lemma_chunks_len(src@, e as int, out@ + data@);
                    }
                    return Err(FrameError::TooLarge);
                }
                out.extend_from_slice(data);
                assert(chunks(src@, e as int, out0 + data@) == goal);
                assert(out@ =~= out0 + data@);
            }
        } else if t == 0xff {
            if len != 6 || !is_stream_id(src, i) {
                proof {
                    assert(src@.subrange(i as int, e as int).len() == 4 + len);
                }
                return Err(FrameError::Corrupt);
            }
            assert(src@.subrange(i as int, e as int) == stream_id());
            assert(chunks(src@, e as int, out@) == goal);
        } else if t < 0x80 {
            return Err(FrameError::Corrupt);
        } else {
            assert(chunks(src@, e as int, out@) == goal);
        }
        i = e;
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// The encoder's invariant: `p` starts with the stream identifier, and
/// whatever is written after `p`, decoding the stream is decoding from
/// the end of `p` with `out`.
pub open spec fn freach(p: Seq<u8>, out: Seq<u8>) -> bool {
    &&& p.len() >= 10
    &&& p.subrange(0, 10) == stream_id()
    &&& forall|s: Seq<u8>| #[trigger] extends(p, s) ==> chunks(s, 10, Seq::empty()) == chunks(s, p.len() as int, out)
}

proof fn lemma_le34(s: Seq<u8>, i: int)
    requires
        0 <= i,
        i + 4 <= s.len(),
    ensures
        le(s, i, 3) == s[i] + 256 * s[i + 1] + 65536 * s[i + 2],
        le(s, i, 4) == s[i] + 256 * s[i + 1] + 65536 * s[i + 2] + 16777216 * s[i + 3],
{
    reveal_with_fuel(le, 5);
}

/// Appending one data chunk extends what the stream decodes to.
proof fn lemma_chunk_step(p: Seq<u8>, q: Seq<u8>, out: Seq<u8>, t: u8, body: Seq<u8>, d: Seq<u8>, m: u32)
    requires
        freach(p, out),
        t == 0 || t == 1,
        t == 0 ==> decompress(body) == Some(d),
        t == 1 ==> body == d,
        d.len() <= CHUNK_MAX,
        m as nat == mask(crc32c(d)),
        body.len() + 4 < 0x100_0000,
        q == p + seq![
            t,
            ((body.len() + 4) % 256) as u8,
            (((body.len() + 4) / 256) % 256) as u8,
            ((body.len() + 4) / 65536) as u8,
            (m % 256) as u8,
            ((m / 256) % 256) as u8,
            ((m / 65536) % 256) as u8,
            (m / 16777216) as u8,
        ] + body,
    ensures
        freach(q, out + d),
{
    let i = p.len() as int;
    let l = body.len() + 4;
    let h = seq![
        t,
        (l % 256) as u8,
        ((l / 256) % 256) as u8,
        (l / 65536) as u8,
        (m % 256) as u8,
        ((m / 256) % 256) as u8,
        ((m / 65536) % 256) as u8,
        (m / 16777216) as u8,
    ];
    assert(q == p + h + body);
    assert(q.len() == i + 8 + body.len());
    assert(q.subrange(0, i) =~= p);
    assert(q.subrange(0, 10) =~= p.subrange(0, 10));
    assert forall|k: int| 0 <= k < 8 implies q[i + k] == h[k] by {}
    assert(q.subrange(i + 8, q.len() as int) =~= body);
    assert forall|s: Seq<u8>| #[trigger] extends(q, s) implies chunks(s, 10, Seq::empty()) == chunks(
        s,
        q.len() as int,
        out + d,
    ) by {
        lemma_chunk_at(s, q, i, out, t, body, d, m);
        assert(s.subrange(0, i) =~= s.subrange(0, q.len() as int).subrange(0, i));
        assert(extends(p, s));
    }
}

/// A stream `s` that starts with `q`, whose last chunk (at `i`) is a
/// data chunk: decoding from `i` is decoding from the end of `q`.
proof fn lemma_chunk_at(s: Seq<u8>, q: Seq<u8>, i: int, out: Seq<u8>, t: u8, body: Seq<u8>, d: Seq<u8>, m: u32)
    requires
        extends(q, s),
        0 <= i,
        q.len() == i + 8 + body.len(),
        t == 0 || t == 1,
        t == 0 ==> decompress(body) == Some(d),
        t == 1 ==> body == d,
        d.len() <= CHUNK_MAX,
        m as nat == mask(crc32c(d)),
        body.len() + 4 < 0x100_0000,
        q[i] == t,
        q[i + 1] == ((body.len() + 4) % 256) as u8,
        q[i + 2] == (((body.len() + 4) / 256) % 256) as u8,
        q[i + 3] == ((body.len() + 4) / 65536) as u8,
        q[i + 4] == (m % 256) as u8,
        q[i + 5] == ((m / 256) % 256) as u8,
        q[i + 6] == ((m / 65536) % 256) as u8,
        q[i + 7] == (m / 16777216) as u8,
        q.subrange(i + 8, q.len() as int) == body,
    ensures
        chunks(s, i, out) == chunks(s, q.len() as int, out + d),
{
    let l = body.len() + 4;
    let e = i + 4 + l;
    let sq = s.subrange(0, q.len() as int);
    assert(sq == q);
    assert(s[i] == sq[i] && s[i + 1] == sq[i + 1] && s[i + 2] == sq[i + 2] && s[i + 3] == sq[i + 3]);
    assert(s[i + 4] == sq[i + 4] && s[i + 5] == sq[i + 5] && s[i + 6] == sq[i + 6] && s[i + 7] == sq[i + 7]);
    lemma_le34(s, i + 1);
    lemma_le34(s, i + 4);
    lemma_bytes(l as nat);
    lemma_bytes(m as nat);
    assert(le(s, i + 1, 3) == l);
    assert(le(s, i + 4, 4) == m);
    assert(s.subrange(i + 8, e) =~= sq.subrange(i + 8, e));
    assert(e == q.len() && e <= s.len());
}

/// A number is the sum of its bytes.
proof fn lemma_bytes(x: nat)
    requires
        x < 0x1_0000_0000,
    ensures
        x == x % 256 + 256 * ((x / 256) % 256) + 65536 * ((x / 65536) % 256) + 16777216 * (x / 16777216),
        x < 0x100_0000 ==> x / 65536 < 256 && x == x % 256 + 256 * ((x / 256) % 256) + 65536 * (x / 65536),
        x / 16777216 < 256,
{
}

/// Encodes `input` as a stream: chunks of up to 64 KiB, each compressed
/// unless that saves less than an eighth.
pub fn frame_encode(input: &[u8]) -> (v: Vec<u8>)
    ensures
        stream(v@) == Some(input@),
{
    let n = input.len();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&STREAM_ID);
    let mut scratch: Vec<u8> = Vec::new();
    scratch.resize(76490, 0);
    let mut pos: usize = 0;
    proof {
        assert(v@ =~= stream_id());
        assert(v@.subrange(0, 10) =~= stream_id());
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while pos < n
        invariant
            n == input@.len(),
            pos <= n,
            scratch@.len() == 76490,
            freach(v@, input@.subrange(0, pos as int)),
        decreases n - pos,
    {
        let clen = if n - pos > 65536 {
            65536
        } else {
            n - pos
        };
        let chunk = slice_subrange(input, pos, pos + clen);
        let m = masked(crc_exec(chunk));
        let ghost p = v@;
        let packed = compress_into(chunk, scratch.as_mut_slice());
        let (t, body): (u8, &[u8]) = match packed {
            Some(k) if k < clen - clen / 8 => (0u8, slice_subrange(scratch.as_slice(), 0, k)),
            _ => (1u8, chunk),
        };
        let l = body.len() + 4;
        v.push(t);
        v.push((l % 256) as u8);
        v.push(((l / 256) % 256) as u8);
        v.push((l / 65536) as u8);
        v.push((m % 256) as u8);
        v.push(((m / 256) % 256) as u8);
        v.push(((m / 65536) % 256) as u8);
        v.push((m / 16777216) as u8);
        v.extend_from_slice(body);
        proof {
            assert(v@ =~= p + seq![
                t,
                ((body@.len() + 4) % 256) as u8,
                (((body@.len() + 4) / 256) % 256) as u8,
                ((body@.len() + 4) / 65536) as u8,
                (m % 256) as u8,
                ((m / 256) % 256) as u8,
                ((m / 65536) % 256) as u8,
                (m / 16777216) as u8,
            ] + body@);
            lemma_chunk_step(p, v@, input@.subrange(0, pos as int), t, body@, chunk@, m);
            assert(input@.subrange(0, pos as int) + chunk@ =~= input@.subrange(0, pos + clen));
        }
        pos = pos + clen;
    }
    proof {
        assert(extends(v@, v@)) by {
            assert(v@.subrange(0, v@.len() as int) =~= v@);
        }
        assert(input@.subrange(0, n as int) =~= input@);
    }
    v
}

} // verus!

impl core::fmt::Display for FrameError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            FrameError::Corrupt => "corrupt Snappy framed data",
            FrameError::TooLarge => "the output would be larger than the limit",
        })
    }
}

impl std::error::Error for FrameError {}
