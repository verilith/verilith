//! The chunked transfer coding (RFC 9112 §7.1): its grammar as a byte-level
//! state machine (the spec), the proof that decoding is independent of how
//! the input is split into reads, and an in-place streaming decoder proven
//! to compute exactly the spec.
//!
//! ```text
//! chunked-body   = *chunk last-chunk trailer-section CRLF
//! chunk          = chunk-size [ chunk-ext ] CRLF chunk-data CRLF
//! chunk-size     = 1*HEXDIG
//! last-chunk     = 1*("0") [ chunk-ext ] CRLF
//! chunk-ext      = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ] )
//! chunk-ext-name = token
//! chunk-ext-val  = token / quoted-string
//! trailer-section = *( field-line CRLF )
//! ```
//!
//! Strict: every line ends in CRLF (a bare LF or CR inside a size line or
//! extension is how the 2023-2024 chunk-extension smuggling attacks worked),
//! a chunk size must fit in 64 bits, and BWS is accepted only where the
//! grammar has it (so `5 \r\n` is rejected).
#[cfg(verus_keep_ghost)]
use crate::parse::get8;
use crate::parse::{ows, tchar, value_char};
use crate::spec::*;
pub use verilith_core::prims::copy_within;
use vstd::prelude::*;

verus! {

/// Decoder state. Each variant names the grammar position the decoder is
/// at; `n` is the chunk size read so far.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CState {
    /// Start of a chunk-size: a hex digit must follow.
    SizeStart,
    /// In chunk-size.
    Size { n: u64 },
    /// BWS after chunk-size; `;` must follow.
    SizeWs { n: u64 },
    /// After `;`: BWS, then a chunk-ext-name.
    ExtPreName { n: u64 },
    /// In chunk-ext-name.
    ExtName { n: u64 },
    /// BWS after chunk-ext-name; `;` or `=` must follow.
    ExtNameWs { n: u64 },
    /// After `=`: BWS, then a chunk-ext-val.
    ExtPreVal { n: u64 },
    /// In a token chunk-ext-val.
    ExtTok { n: u64 },
    /// In a quoted-string chunk-ext-val.
    ExtQ { n: u64 },
    /// After a backslash in a quoted-string.
    ExtQEsc { n: u64 },
    /// After the closing quote of a chunk-ext-val.
    ExtValEnd { n: u64 },
    /// BWS after a chunk-ext-val; `;` must follow.
    ExtValWs { n: u64 },
    /// After the CR ending a size line.
    SizeLf { n: u64 },
    /// In chunk-data, `left` bytes to go.
    Data { left: u64 },
    /// After chunk-data: CR must follow.
    DataCr,
    /// After chunk-data and CR: LF must follow.
    DataLf,
    /// Start of a trailer line, or the final CRLF.
    TrStart,
    /// In a trailer field name.
    TrName,
    /// In a trailer field value.
    TrValue,
    /// After the CR ending a trailer line.
    TrLf,
    /// After the CR of the final CRLF.
    EndLf,
    /// The chunked body is complete.
    Done,
}

pub open spec fn is_hex(c: u8) -> bool {
    is_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

pub open spec fn hex_val(c: u8) -> u64 {
    if is_digit(c) {
        (c - 0x30) as u64
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as u64
    } else {
        (c - 0x61 + 10) as u64
    }
}

/// `qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text`
pub open spec fn is_qdtext(c: u8) -> bool {
    c == HTAB || c == SP || c == 0x21 || (0x23 <= c <= 0x5B) || (0x5D <= c <= 0x7E) || c >= 0x80
}

/// The byte allowed after a backslash: `HTAB / SP / VCHAR / obs-text`.
pub open spec fn is_qpair_char(c: u8) -> bool {
    c == HTAB || (0x20 <= c && c != 0x7F)
}

/// Largest chunk size that can take another hex digit without overflow.
pub spec const MAX_BEFORE_DIGIT: u64 = 0x0fff_ffff_ffff_ffff;

/// After the size line's CR: the state the size line's extension states
/// move to on a byte. Shared by every state where a size line may end.
pub open spec fn after_size_line(n: u64, c: u8) -> Option<CState> {
    if c == CR {
        Some(CState::SizeLf { n })
    } else {
        None
    }
}

/// One step of the decoder: the next state, and whether `c` is body data.
/// `None` means the input is invalid.
pub open spec fn step(s: CState, c: u8) -> Option<(CState, bool)> {
    match s {
        CState::SizeStart => if is_hex(c) {
            Some((CState::Size { n: hex_val(c) }, false))
        } else {
            None
        },
        CState::Size { n } => if is_hex(c) {
            if n > MAX_BEFORE_DIGIT {
                None
            } else {
                Some((CState::Size { n: (n * 16 + hex_val(c)) as u64 }, false))
            }
        } else if is_ows(c) {
            Some((CState::SizeWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::SizeWs { n } => if is_ows(c) {
            Some((CState::SizeWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else {
            None
        },
        CState::ExtPreName { n } => if is_ows(c) {
            Some((CState::ExtPreName { n }, false))
        } else if is_tchar(c) {
            Some((CState::ExtName { n }, false))
        } else {
            None
        },
        CState::ExtName { n } => if is_tchar(c) {
            Some((CState::ExtName { n }, false))
        } else if is_ows(c) {
            Some((CState::ExtNameWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else if c == 0x3D {
            Some((CState::ExtPreVal { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtNameWs { n } => if is_ows(c) {
            Some((CState::ExtNameWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else if c == 0x3D {
            Some((CState::ExtPreVal { n }, false))
        } else {
            None
        },
        CState::ExtPreVal { n } => if is_ows(c) {
            Some((CState::ExtPreVal { n }, false))
        } else if is_tchar(c) {
            Some((CState::ExtTok { n }, false))
        } else if c == 0x22 {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtTok { n } => if is_tchar(c) {
            Some((CState::ExtTok { n }, false))
        } else if is_ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtQ { n } => if c == 0x22 {
            Some((CState::ExtValEnd { n }, false))
        } else if c == 0x5C {
            Some((CState::ExtQEsc { n }, false))
        } else if is_qdtext(c) {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtQEsc { n } => if is_qpair_char(c) {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtValEnd { n } => if is_ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtValWs { n } => if is_ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if c == 0x3B {
            Some((CState::ExtPreName { n }, false))
        } else {
            None
        },
        CState::SizeLf { n } => if c != LF {
            None
        } else if n == 0 {
            Some((CState::TrStart, false))
        } else {
            Some((CState::Data { left: n }, false))
        },
        CState::Data { left } => if left <= 1 {
            Some((CState::DataCr, true))
        } else {
            Some((CState::Data { left: (left - 1) as u64 }, true))
        },
        CState::DataCr => if c == CR {
            Some((CState::DataLf, false))
        } else {
            None
        },
        CState::DataLf => if c == LF {
            Some((CState::SizeStart, false))
        } else {
            None
        },
        CState::TrStart => if c == CR {
            Some((CState::EndLf, false))
        } else if is_tchar(c) {
            Some((CState::TrName, false))
        } else {
            None
        },
        CState::TrName => if is_tchar(c) {
            Some((CState::TrName, false))
        } else if c == COLON {
            Some((CState::TrValue, false))
        } else {
            None
        },
        CState::TrValue => if is_value_char(c) {
            Some((CState::TrValue, false))
        } else if c == CR {
            Some((CState::TrLf, false))
        } else {
            None
        },
        CState::TrLf => if c == LF {
            Some((CState::TrStart, false))
        } else {
            None
        },
        CState::EndLf => if c == LF {
            Some((CState::Done, false))
        } else {
            None
        },
        CState::Done => None,
    }
}

/// The decoder stops at `Done`, and also at `TrStart` when the caller
/// handles trailers itself (picohttpparser's `consume_trailer = 0`).
pub open spec fn stops(s: CState, keep_trailers: bool) -> bool {
    s is Done || (keep_trailers && s is TrStart)
}

/// Runs the decoder over `b`: the final state, the body bytes emitted, and
/// the number of bytes consumed (less than `b.len()` only if it stopped).
/// `None` if `b` is invalid.
pub open spec fn run(s: CState, b: Seq<u8>, kt: bool) -> Option<(CState, Seq<u8>, nat)>
    decreases b.len(),
{
    if b.len() == 0 || stops(s, kt) {
        Some((s, Seq::empty(), 0))
    } else {
        match step(s, b[0]) {
            None => None,
            Some((s2, emit)) => match run(s2, b.drop_first(), kt) {
                None => None,
                Some((s3, out, k)) => Some(
                    (
                        s3,
                        (if emit {
                            seq![b[0]]
                        } else {
                            Seq::empty()
                        }) + out,
                        k + 1,
                    ),
                ),
            },
        }
    }
}

/// `o` and `k` followed by the result `r`.
pub open spec fn then(o: Seq<u8>, k: nat, r: Option<(CState, Seq<u8>, nat)>) -> Option<
    (CState, Seq<u8>, nat),
> {
    match r {
        None => None,
        Some((s, o2, k2)) => Some((s, o + o2, k + k2)),
    }
}

/// The decoder never consumes more than it is given, and consumes all of
/// it unless it stopped.
pub proof fn lemma_run_consumed(s: CState, b: Seq<u8>, kt: bool)
    ensures
        run(s, b, kt) matches Some((s2, o, k)) ==> k <= b.len() && o.len() <= k && (k < b.len()
            ==> stops(s2, kt)),
    decreases b.len(),
{
    if b.len() > 0 && !stops(s, kt) {
        if let Some((s2, _)) = step(s, b[0]) {
            lemma_run_consumed(s2, b.drop_first(), kt);
        }
    }
}

/// **Split invariance.** Decoding `a + c` in one call is the same as
/// decoding `a`, then decoding `c` from the state `a` left. So the result
/// never depends on how the body was split across reads: a peer cannot
/// change how a body is decoded by choosing where TCP segments end.
pub proof fn theorem_split(s: CState, a: Seq<u8>, c: Seq<u8>, kt: bool)
    ensures
        run(s, a + c, kt) == match run(s, a, kt) {
            None => None,
            Some((s1, o1, k1)) => if k1 < a.len() || stops(s1, kt) {
                Some((s1, o1, k1))
            } else {
                then(o1, k1, run(s1, c, kt))
            },
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        if let Some((s3, o, k)) = run(s, c, kt) {
            assert(Seq::<u8>::empty() + o =~= o);
        }
    } else if stops(s, kt) {
    } else {
        assert((a + c)[0] == a[0]);
        assert((a + c).drop_first() =~= a.drop_first() + c);
        match step(s, a[0]) {
            None => {},
            Some((s2, emit)) => {
                theorem_split(s2, a.drop_first(), c, kt);
                lemma_run_consumed(s2, a.drop_first(), kt);
                let e: Seq<u8> = if emit {
                    seq![a[0]]
                } else {
                    Seq::empty()
                };
                match run(s2, a.drop_first(), kt) {
                    None => {},
                    Some((s1, o1, k1)) => {
                        if !(k1 < a.drop_first().len() || stops(s1, kt)) {
                            if let Some((s4, o2, k2)) = run(s1, c, kt) {
                                assert(e + (o1 + o2) =~= (e + o1) + o2);
                            }
                        }
                    },
                }
            },
        }
    }
}

/// In `Data { left }`, the next `m <= left` bytes are all body data.
pub proof fn lemma_run_data(left: u64, b: Seq<u8>, m: nat, kt: bool)
    requires
        1 <= m <= left,
        m <= b.len(),
    ensures
        run(CState::Data { left }, b, kt) == then(
            b.subrange(0, m as int),
            m,
            run(
                if m == left {
                    CState::DataCr
                } else {
                    CState::Data { left: (left - m) as u64 }
                },
                b.subrange(m as int, b.len() as int),
                kt,
            ),
        ),
    decreases m,
{
    let s2 = if left <= 1 {
        CState::DataCr
    } else {
        CState::Data { left: (left - 1) as u64 }
    };
    let rest = b.drop_first();
    if m == 1 {
        assert(rest =~= b.subrange(1, b.len() as int));
        if let Some((s3, o, k)) = run(s2, rest, kt) {
            assert(seq![b[0]] + o =~= b.subrange(0, 1) + o);
        }
    } else {
        lemma_run_data((left - 1) as u64, rest, (m - 1) as nat, kt);
        assert(rest.subrange((m - 1) as int, rest.len() as int) =~= b.subrange(
            m as int,
            b.len() as int,
        ));
        if let Some((s3, o, k)) = run(
            if m == left {
                CState::DataCr
            } else {
                CState::Data { left: (left - m) as u64 }
            },
            b.subrange(m as int, b.len() as int),
            kt,
        ) {
            assert(seq![b[0]] + (rest.subrange(0, (m - 1) as int) + o) =~= b.subrange(0, m as int)
                + o);
        }
    }
}

// ---------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------

#[inline(always)]
fn hex_exec(c: u8) -> (r: Option<u64>)
    ensures
        r == (if is_hex(c) {
            Some(hex_val(c))
        } else {
            None::<u64>
        }),
{
    if c >= 0x30 && c <= 0x39 {
        Some((c - 0x30) as u64)
    } else if c >= 0x41 && c <= 0x46 {
        Some((c - 0x41 + 10) as u64)
    } else if c >= 0x61 && c <= 0x66 {
        Some((c - 0x61 + 10) as u64)
    } else {
        None
    }
}

/// One decoder step (spec `step`).
pub fn step_exec(s: CState, c: u8) -> (r: Option<(CState, bool)>)
    ensures
        r == step(s, c),
{
    let semi = c == 0x3B;
    match s {
        CState::SizeStart => match hex_exec(c) {
            Some(h) => Some((CState::Size { n: h }, false)),
            None => None,
        },
        CState::Size { n } => match hex_exec(c) {
            Some(h) => if n > 0x0fff_ffff_ffff_ffff {
                None
            } else {
                Some((CState::Size { n: n * 16 + h }, false))
            },
            None => if ows(c) {
                Some((CState::SizeWs { n }, false))
            } else if semi {
                Some((CState::ExtPreName { n }, false))
            } else if c == CR {
                Some((CState::SizeLf { n }, false))
            } else {
                None
            },
        },
        CState::SizeWs { n } => if ows(c) {
            Some((CState::SizeWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else {
            None
        },
        CState::ExtPreName { n } => if ows(c) {
            Some((CState::ExtPreName { n }, false))
        } else if tchar(c) {
            Some((CState::ExtName { n }, false))
        } else {
            None
        },
        CState::ExtName { n } => if tchar(c) {
            Some((CState::ExtName { n }, false))
        } else if ows(c) {
            Some((CState::ExtNameWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else if c == 0x3D {
            Some((CState::ExtPreVal { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtNameWs { n } => if ows(c) {
            Some((CState::ExtNameWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else if c == 0x3D {
            Some((CState::ExtPreVal { n }, false))
        } else {
            None
        },
        CState::ExtPreVal { n } => if ows(c) {
            Some((CState::ExtPreVal { n }, false))
        } else if tchar(c) {
            Some((CState::ExtTok { n }, false))
        } else if c == 0x22 {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtTok { n } => if tchar(c) {
            Some((CState::ExtTok { n }, false))
        } else if ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtQ { n } => if c == 0x22 {
            Some((CState::ExtValEnd { n }, false))
        } else if c == 0x5C {
            Some((CState::ExtQEsc { n }, false))
        } else if c == HTAB || c == SP || c == 0x21 || (0x23 <= c && c <= 0x5B) || (0x5D <= c && c
            <= 0x7E) || c >= 0x80 {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtQEsc { n } => if value_char(c) {
            Some((CState::ExtQ { n }, false))
        } else {
            None
        },
        CState::ExtValEnd { n } => if ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else if c == CR {
            Some((CState::SizeLf { n }, false))
        } else {
            None
        },
        CState::ExtValWs { n } => if ows(c) {
            Some((CState::ExtValWs { n }, false))
        } else if semi {
            Some((CState::ExtPreName { n }, false))
        } else {
            None
        },
        CState::SizeLf { n } => if c != LF {
            None
        } else if n == 0 {
            Some((CState::TrStart, false))
        } else {
            Some((CState::Data { left: n }, false))
        },
        CState::Data { left } => if left <= 1 {
            Some((CState::DataCr, true))
        } else {
            Some((CState::Data { left: left - 1 }, true))
        },
        CState::DataCr => if c == CR {
            Some((CState::DataLf, false))
        } else {
            None
        },
        CState::DataLf => if c == LF {
            Some((CState::SizeStart, false))
        } else {
            None
        },
        CState::TrStart => if c == CR {
            Some((CState::EndLf, false))
        } else if tchar(c) {
            Some((CState::TrName, false))
        } else {
            None
        },
        CState::TrName => if tchar(c) {
            Some((CState::TrName, false))
        } else if c == COLON {
            Some((CState::TrValue, false))
        } else {
            None
        },
        CState::TrValue => if value_char(c) {
            Some((CState::TrValue, false))
        } else if c == CR {
            Some((CState::TrLf, false))
        } else {
            None
        },
        CState::TrLf => if c == LF {
            Some((CState::TrStart, false))
        } else {
            None
        },
        CState::EndLf => if c == LF {
            Some((CState::Done, false))
        } else {
            None
        },
        CState::Done => None,
    }
}

/// The outcome of a `decode` call.
pub enum Decoded {
    /// The input is not a valid chunked body.
    Invalid,
    /// All input consumed; the body is not finished. `out` bytes of body
    /// data were written to the front of the buffer.
    More { out: usize },
    /// The body ended (or, with `keep_trailers`, reached the trailers)
    /// after `consumed` input bytes; `out` bytes of body data were written
    /// to the front of the buffer, and the unconsumed input was moved to
    /// follow them.
    Done { out: usize, consumed: usize },
}

/// The decoder loop invariant: `buf[src..len]` is still the unread input,
/// `buf[..dst]` holds the body bytes emitted so far, and running from `s`
/// on the rest gives the same overall result as running from `st0` on all
/// of the input.
pub open spec fn dec_inv(
    st0: CState,
    input: Seq<u8>,
    kt: bool,
    buf: Seq<u8>,
    s: CState,
    src: int,
    dst: int,
) -> bool {
    let len = input.len() as int;
    &&& 0 <= dst <= src <= len <= buf.len()
    &&& forall|j: int| src <= j < len ==> #[trigger] buf[j] == input[j]
    &&& run(st0, input, kt) == then(
        buf.subrange(0, dst),
        src as nat,
        run(s, input.subrange(src, len), kt),
    )
}

/// Copies the next `min(left, available)` bytes of chunk data.
fn data_step(
    buf: &mut [u8],
    left: u64,
    src: usize,
    dst: usize,
    len: usize,
    Ghost(st0): Ghost<CState>,
    Ghost(input): Ghost<Seq<u8>>,
    kt: bool,
) -> (r: (CState, usize, usize))
    requires
        left > 0,
        src < len,
        len == input.len(),
        dec_inv(st0, input, kt, old(buf)@, CState::Data { left }, src as int, dst as int),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        dec_inv(st0, input, kt, final(buf)@, r.0, r.1 as int, r.2 as int),
        src < r.1,
{
    let ghost rest = input.subrange(src as int, len as int);
    let ghost before = buf@;
    let avail = (len - src) as u64;
    let m: usize = if left < avail {
        left as usize
    } else {
        len - src
    };
    proof {
        lemma_run_data(left, rest, m as nat, kt);
        assert(rest.subrange(m as int, rest.len() as int) =~= input.subrange(src + m, len as int));
    }
    copy_within(buf, src, dst, m);
    let s2 = if m as u64 == left {
        CState::DataCr
    } else {
        CState::Data { left: left - m as u64 }
    };
    proof {
        assert(buf@.subrange(0, dst + m) =~= before.subrange(0, dst as int) + rest.subrange(
            0,
            m as int,
        )) by {
            assert forall|j: int| 0 <= j < dst + m implies #[trigger] buf@.subrange(0, dst + m)[j]
                == (before.subrange(0, dst as int) + rest.subrange(0, m as int))[j] by {
                if j >= dst {
                    assert(buf@[j] == before[j - dst + src]);
                }
            }
        }
        if let Some((s3, o, k)) = run(s2, input.subrange(src + m, len as int), kt) {
            assert(before.subrange(0, dst as int) + (rest.subrange(0, m as int) + o)
                =~= buf@.subrange(0, dst + m) + o);
        }
        assert forall|j: int| src + m <= j < len implies #[trigger] buf@[j] == input[j] by {
            assert(buf@[j] == before[j]);
        }
    }
    (s2, src + m, dst + m)
}

/// Decodes one byte that is not chunk data.
fn byte_step(
    buf: &mut [u8],
    s: CState,
    src: usize,
    dst: usize,
    len: usize,
    Ghost(st0): Ghost<CState>,
    Ghost(input): Ghost<Seq<u8>>,
    kt: bool,
) -> (r: Option<(CState, usize, usize)>)
    requires
        src < len,
        len == input.len(),
        !stops(s, kt),
        dec_inv(st0, input, kt, old(buf)@, s, src as int, dst as int),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        r is None ==> run(st0, input, kt) is None,
        r matches Some((s2, src2, dst2)) ==> src2 == src + 1 && dec_inv(
            st0,
            input,
            kt,
            final(buf)@,
            s2,
            src2 as int,
            dst2 as int,
        ),
{
    let ghost rest = input.subrange(src as int, len as int);
    let ghost before = buf@;
    let c = buf[src];
    proof {
        assert(rest[0] == c);
        assert(rest.drop_first() =~= input.subrange(src + 1, len as int));
    }
    match step_exec(s, c) {
        None => None,
        Some((s2, emit)) => {
            if emit {
                buf[dst] = c;
                proof {
                    assert(buf@.subrange(0, dst + 1) =~= before.subrange(0, dst as int) + seq![c]);
                    if let Some((s3, o, k)) = run(s2, input.subrange(src + 1, len as int), kt) {
                        assert(before.subrange(0, dst as int) + (seq![c] + o) =~= buf@.subrange(
                            0,
                            dst + 1,
                        ) + o);
                    }
                    assert forall|j: int| src + 1 <= j < len implies #[trigger] buf@[j]
                        == input[j] by {
                        assert(buf@[j] == before[j]);
                    }
                }
                Some((s2, src + 1, dst + 1))
            } else {
                proof {
                    if let Some((s3, o, k)) = run(s2, input.subrange(src + 1, len as int), kt) {
                        assert(Seq::<u8>::empty() + o =~= o);
                    }
                }
                Some((s2, src + 1, dst))
            }
        },
    }
}

/// Decodes the chunked data in `buf[..len]` in place, from state `*st`.
/// Body bytes are moved to the front of `buf`; on `Done`, the bytes after
/// the body follow them. `*st` is updated so the next call continues where
/// this one stopped.
///
/// Proven: the result is exactly `run(old(*st), input, keep_trailers)`,
/// and the loop takes at most `len` iterations.
pub fn decode(st: &mut CState, buf: &mut [u8], len: usize, keep_trailers: bool) -> (r: (
    Decoded,
    Ghost<nat>,
))
    requires
        len <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        r.1@ <= len,
        match run(*old(st), old(buf)@.subrange(0, len as int), keep_trailers) {
            None => r.0 is Invalid,
            Some((s, o, k)) => {
                &&& *final(st) == s
                &&& (k < len || stops(s, keep_trailers)) ==> (r.0 matches Decoded::Done {
                    out,
                    consumed,
                } && out == o.len() && consumed == k && final(buf)@.subrange(0, out as int) == o
                    && final(buf)@.subrange(out as int, out + len - k) == old(buf)@.subrange(
                    k as int,
                    len as int,
                ))
                &&& !(k < len || stops(s, keep_trailers)) ==> (r.0 matches Decoded::More { out }
                    && out == o.len() && final(buf)@.subrange(0, out as int) == o)
            },
        },
{
    let ghost input = buf@.subrange(0, len as int);
    let ghost st0 = *st;
    let mut s = *st;
    let mut src: usize = 0;
    let mut dst: usize = 0;
    let ghost mut steps: nat = 0;
    proof {
        assert(input.subrange(0, len as int) =~= input);
        assert(buf@.subrange(0, 0) =~= Seq::<u8>::empty());
        if let Some((s3, o, k)) = run(s, input, keep_trailers) {
            assert(Seq::<u8>::empty() + o =~= o);
        }
    }
    while src < len && !stops_exec(s, keep_trailers)
        invariant
            len == input.len(),
            buf@.len() == old(buf)@.len(),
            input == old(buf)@.subrange(0, len as int),
            st0 == *old(st),
            dec_inv(st0, input, keep_trailers, buf@, s, src as int, dst as int),
            steps <= src,
        decreases len - src,
    {
        let left: u64 = match s {
            CState::Data { left } => left,
            _ => 0,
        };
        if left > 0 {
            let (s2, src2, dst2) = data_step(
                buf,
                left,
                src,
                dst,
                len,
                Ghost(st0),
                Ghost(input),
                keep_trailers,
            );
            s = s2;
            src = src2;
            dst = dst2;
        } else {
            match byte_step(buf, s, src, dst, len, Ghost(st0), Ghost(input), keep_trailers) {
                None => {
                    return (Decoded::Invalid, Ghost(steps));
                },
                Some((s2, src2, dst2)) => {
                    s = s2;
                    src = src2;
                    dst = dst2;
                },
            }
        }
        proof {
            steps = steps + 1;
        }
    }
    *st = s;
    let ghost after = buf@;
    proof {
        let ghost rest = input.subrange(src as int, len as int);
        assert(run(s, rest, keep_trailers) == Some((s, Seq::<u8>::empty(), 0nat)));
        assert(buf@.subrange(0, dst as int) + Seq::<u8>::empty() =~= buf@.subrange(0, dst as int));
    }
    if src < len || stops_exec(s, keep_trailers) {
        let n = len - src;
        copy_within(buf, src, dst, n);
        proof {
            assert(buf@.subrange(0, dst as int) =~= after.subrange(0, dst as int));
            assert(buf@.subrange(dst as int, dst + n) =~= old(buf)@.subrange(src as int, len as int))
                by {
                assert forall|j: int| 0 <= j < n implies #[trigger] buf@.subrange(
                    dst as int,
                    dst + n,
                )[j] == old(buf)@.subrange(src as int, len as int)[j] by {
                    assert(buf@[dst + j] == after[src + j]);
                    assert(after[src + j] == input[src + j]);
                }
            }
        }
        (Decoded::Done { out: dst, consumed: src }, Ghost(steps))
    } else {
        (Decoded::More { out: dst }, Ghost(steps))
    }
}

#[inline(always)]
pub fn stops_exec(s: CState, keep_trailers: bool) -> (r: bool)
    ensures
        r == stops(s, keep_trailers),
{
    match s {
        CState::Done => true,
        CState::TrStart => keep_trailers,
        _ => false,
    }
}

} // verus!
