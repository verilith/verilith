//! The push parser for a document in any encoding read here (`spec::parse`).
//! Input in UTF-8 goes to the stream (`push::Stream`) as it comes; input in
//! UTF-16, ISO-8859-1 or US-ASCII is decoded to UTF-8 as it comes, and the
//! text goes to a stream that reads it as decoded from that encoding
//! (`Stream::decoded`). The encoding is known from the first bytes (a
//! UTF-16 byte order mark) or the XML declaration (`input_enc`), which the
//! UTF-8 stream reads first; until then the input is kept. A document
//! whose encoding these do not settle is handed back whole (`R_WHOLE`), as
//! the stream hands one back.
//!
//! After each chunk, for every input `s` that begins with what was fed,
//! `s` decodes to the text the stream has seen followed by the decoding of
//! the rest (`Reader::dec_ok`), so the stream's verdict on the text is
//! `parse`'s on the input.
use crate::dtd::*;
use crate::enc::*;
use crate::ent::push_utf8;
use crate::lex::*;
use crate::push::*;
use crate::spec::*;
use crate::stable_pro::*;
use crate::stream::*;
use crate::stream_spec::*;
use crate::tape::slice_len_bound;
use verilith_core::prims::{extend, get};
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

/// `Reader::kind`: the input goes to a stream as it is (UTF-8, or not
/// known yet); the input is kept until its encoding is known; it is
/// decoded to the stream; it is handed back whole; nothing more is read.
pub const K_RAW: u8 = 0;
pub const K_DECIDE: u8 = 1;
pub const K_DEC: u8 = 2;
pub const K_WHOLE: u8 = 3;
pub const K_DONE: u8 = 4;

/// The decoders: UTF-16 little- and big-endian, ISO-8859-1, US-ASCII; and
/// `decide`'s other answers.
pub const D16LE: u8 = 0;
pub const D16BE: u8 = 1;
pub const DL1: u8 = 2;
pub const DASC: u8 = 3;
pub const DNONE: u8 = 4;
pub const DWAIT: u8 = 5;

pub open spec fn dk_enc(dk: u8) -> Enc {
    if dk == D16LE || dk == D16BE {
        Enc::Utf16
    } else if dk == DL1 {
        Enc::Latin1
    } else {
        Enc::Ascii
    }
}

pub open spec fn all_ascii(s: Seq<u8>, i: int) -> bool {
    forall|k: int| i <= k < s.len() ==> #[trigger] s[k] < 0x80
}

/// `s` from `i` to the end, decoded by `dk`.
pub open spec fn rest_dec(s: Seq<u8>, i: int, dk: u8) -> Option<Seq<u8>> {
    if dk == D16LE {
        utf16_dec(s, i, true)
    } else if dk == D16BE {
        utf16_dec(s, i, false)
    } else if dk == DL1 {
        Some(latin1_dec(s, i))
    } else if all_ascii(s, i) {
        Some(s.subrange(i, s.len() as int))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Decoding a step at a time, on every input that begins with `seen`
// ---------------------------------------------------------------------------

proof fn lemma_cat_assoc(p: Seq<u8>, e: Seq<u8>, o: Option<Seq<u8>>)
    ensures
        cat(p, cat(e, o)) == cat(p + e, o),
{
    match o {
        Some(r) => assert(p + (e + r) =~= (p + e) + r),
        None => {},
    }
}

proof fn lemma_rest_end(s: Seq<u8>, dk: u8)
    ensures
        rest_dec(s, s.len() as int, dk) == Some(Seq::<u8>::empty()),
{
    assert(s.subrange(s.len() as int, s.len() as int) =~= Seq::<u8>::empty());
}

/// A code unit that is not a surrogate.
proof fn lemma_u16_one(seen: Seq<u8>, s: Seq<u8>, q: int, le: bool)
    requires
        ext(seen, s),
        0 <= q,
        q + 2 <= seen.len(),
        !(0xD800 <= unit16(seen, q, le) <= 0xDFFF),
    ensures
        utf16_dec(s, q, le) == cat(utf8_encode(unit16(seen, q, le) as u32), utf16_dec(s, q + 2, le)),
{
    lemma_ext_byte(seen, s, q);
    lemma_ext_byte(seen, s, q + 1);
    assert(unit16(s, q, le) == unit16(seen, q, le));
}

/// A surrogate pair.
proof fn lemma_u16_pair(seen: Seq<u8>, s: Seq<u8>, q: int, le: bool)
    requires
        ext(seen, s),
        0 <= q,
        q + 4 <= seen.len(),
        0xD800 <= unit16(seen, q, le) <= 0xDBFF,
        0xDC00 <= unit16(seen, q + 2, le) <= 0xDFFF,
    ensures
        utf16_dec(s, q, le) == cat(
            utf8_encode((0x10000 + (unit16(seen, q, le) - 0xD800) * 1024 + (unit16(seen, q + 2, le) - 0xDC00)) as u32),
            utf16_dec(s, q + 4, le),
        ),
{
    lemma_ext_byte(seen, s, q);
    lemma_ext_byte(seen, s, q + 1);
    lemma_ext_byte(seen, s, q + 2);
    lemma_ext_byte(seen, s, q + 3);
    assert(unit16(s, q, le) == unit16(seen, q, le));
    assert(unit16(s, q + 2, le) == unit16(seen, q + 2, le));
}

/// A surrogate that is not half of a pair.
proof fn lemma_u16_bad(seen: Seq<u8>, s: Seq<u8>, q: int, le: bool)
    requires
        ext(seen, s),
        0 <= q,
        q + 2 <= seen.len(),
        0xDC00 <= unit16(seen, q, le) <= 0xDFFF || (0xD800 <= unit16(seen, q, le) <= 0xDBFF && q + 4 <= seen.len()
            && !(0xDC00 <= unit16(seen, q + 2, le) <= 0xDFFF)),
    ensures
        utf16_dec(s, q, le) is None,
{
    lemma_ext_byte(seen, s, q);
    lemma_ext_byte(seen, s, q + 1);
    assert(unit16(s, q, le) == unit16(seen, q, le));
    if q + 4 <= seen.len() {
        lemma_ext_byte(seen, s, q + 2);
        lemma_ext_byte(seen, s, q + 3);
        assert(unit16(s, q + 2, le) == unit16(seen, q + 2, le));
    }
}

/// At the end: a code unit cut short, or half of a pair.
proof fn lemma_u16_short(b: Seq<u8>, q: int, le: bool)
    requires
        0 <= q < b.len(),
        q + 2 > b.len() || (0xD800 <= unit16(b, q, le) <= 0xDBFF && q + 4 > b.len()),
    ensures
        utf16_dec(b, q, le) is None,
{
}

/// UTF-16 from `dpos` in `seen` (`b`), decoded as far as `seen` decides:
/// the text, how far it reaches, and whether the input can be UTF-16.
fn dec16(b: &[u8], le: bool, out: &mut Vec<u8>, Ghost(seen): Ghost<Seq<u8>>, Ghost(dpos): Ghost<int>) -> (r: (
    usize,
    bool,
))
    requires
        0 <= dpos <= seen.len(),
        b@ == seen.subrange(dpos, seen.len() as int),
        old(out)@ == Seq::<u8>::empty(),
    ensures
        r.0 <= b@.len(),
        r.1 ==> forall|s: Seq<u8>| #[trigger]
            ext(seen, s) ==> utf16_dec(s, dpos, le) == cat(final(out)@, utf16_dec(s, dpos + r.0, le)),
        r.1 ==> b@.len() - r.0 <= 3,
        r.1 && r.0 < b@.len() ==> utf16_dec(seen, dpos + r.0, le) is None,
        !r.1 ==> forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> utf16_dec(s, dpos, le) is None,
{
    let n = b.len();
    let mut i: usize = 0;
    proof {
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies utf16_dec(s, dpos, le) == cat(
            out@,
            utf16_dec(s, dpos + i, le),
        ) by {
            match utf16_dec(s, dpos, le) {
                Some(r) => assert(out@ + r =~= r),
                None => {},
            }
        }
    }
    while i < n
        invariant
            i <= n,
            n == b@.len(),
            0 <= dpos <= seen.len(),
            b@ == seen.subrange(dpos, seen.len() as int),
            forall|s: Seq<u8>| #[trigger]
                ext(seen, s) ==> utf16_dec(s, dpos, le) == cat(out@, utf16_dec(s, dpos + i, le)),
        decreases n - i,
    {
        let q = Ghost(dpos + i);
        if n - i < 2 {
            proof {
                assert(seen.len() == dpos + n);
                lemma_u16_short(seen, q@, le);
            }
            return (i, true);
        }
        let x0 = get(b, i) as u32;
        let x1 = get(b, i + 1) as u32;
        let u: u32 = if le { x0 + x1 * 256 } else { x0 * 256 + x1 };
        proof {
            assert(b@[i as int] == seen[q@]);
            assert(b@[i + 1] == seen[q@ + 1]);
            assert(u == unit16(seen, q@, le));
        }
        if 0xD800 <= u && u <= 0xDBFF {
            if n - i < 4 {
                proof {
                    assert(seen.len() == dpos + n);
                    lemma_u16_short(seen, q@, le);
                }
                return (i, true);
            }
            let y0 = get(b, i + 2) as u32;
            let y1 = get(b, i + 3) as u32;
            let w: u32 = if le { y0 + y1 * 256 } else { y0 * 256 + y1 };
            proof {
                assert(b@[i + 2] == seen[q@ + 2]);
                assert(b@[i + 3] == seen[q@ + 3]);
                assert(w == unit16(seen, q@ + 2, le));
            }
            if !(0xDC00 <= w && w <= 0xDFFF) {
                proof {
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies utf16_dec(s, dpos, le) is None by {
                        lemma_u16_bad(seen, s, q@, le);
                    }
                }
                return (i, false);
            }
            let c = 0x10000 + (u - 0xD800) * 1024 + (w - 0xDC00);
            let ghost o0 = out@;
            push_utf8(out, c);
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies utf16_dec(s, dpos, le) == cat(
                    out@,
                    utf16_dec(s, dpos + i + 4, le),
                ) by {
                    lemma_u16_pair(seen, s, q@, le);
                    lemma_cat_assoc(o0, utf8_encode(c), utf16_dec(s, dpos + i + 4, le));
                }
            }
            i = i + 4;
        } else if 0xDC00 <= u && u <= 0xDFFF {
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies utf16_dec(s, dpos, le) is None by {
                    lemma_u16_bad(seen, s, q@, le);
                }
            }
            return (i, false);
        } else {
            let ghost o0 = out@;
            push_utf8(out, u);
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies utf16_dec(s, dpos, le) == cat(
                    out@,
                    utf16_dec(s, dpos + i + 2, le),
                ) by {
                    lemma_u16_one(seen, s, q@, le);
                    lemma_cat_assoc(o0, utf8_encode(u), utf16_dec(s, dpos + i + 2, le));
                }
            }
            i = i + 2;
        }
    }
    (i, true)
}

/// ISO-8859-1: every byte decodes alone.
fn dec_l1(b: &[u8], out: &mut Vec<u8>, Ghost(seen): Ghost<Seq<u8>>, Ghost(dpos): Ghost<int>)
    requires
        0 <= dpos <= seen.len(),
        b@ == seen.subrange(dpos, seen.len() as int),
        old(out)@ == Seq::<u8>::empty(),
    ensures
        forall|s: Seq<u8>| #[trigger]
            ext(seen, s) ==> latin1_dec(s, dpos) == final(out)@ + latin1_dec(s, dpos + b@.len()),
{
    let n = b.len();
    let mut i: usize = 0;
    proof {
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies latin1_dec(s, dpos) == out@ + latin1_dec(
            s,
            dpos + i,
        ) by {
            assert(out@ + latin1_dec(s, dpos) =~= latin1_dec(s, dpos));
        }
    }
    while i < n
        invariant
            i <= n,
            n == b@.len(),
            0 <= dpos <= seen.len(),
            b@ == seen.subrange(dpos, seen.len() as int),
            forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> latin1_dec(s, dpos) == out@ + latin1_dec(s, dpos + i),
        decreases n - i,
    {
        let c = get(b, i);
        let ghost o0 = out@;
        push_utf8(out, c as u32);
        proof {
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies latin1_dec(s, dpos) == out@ + latin1_dec(
                s,
                dpos + i + 1,
            ) by {
                lemma_ext_byte(seen, s, dpos + i);
                assert(b@[i as int] == seen[dpos + i]);
                assert(o0 + (utf8_encode(c as u32) + latin1_dec(s, dpos + i + 1)) =~= (o0 + utf8_encode(c as u32))
                    + latin1_dec(s, dpos + i + 1));
            }
        }
        i = i + 1;
    }
}

/// US-ASCII: every byte below 0x80 is itself; whether all of `b` is.
fn dec_ascii(b: &[u8], out: &mut Vec<u8>, Ghost(seen): Ghost<Seq<u8>>, Ghost(dpos): Ghost<int>) -> (r: bool)
    requires
        0 <= dpos <= seen.len(),
        b@ == seen.subrange(dpos, seen.len() as int),
        old(out)@ == Seq::<u8>::empty(),
    ensures
        r ==> forall|s: Seq<u8>| #[trigger]
            ext(seen, s) ==> rest_dec(s, dpos, DASC) == cat(final(out)@, rest_dec(s, dpos + b@.len(), DASC)),
        !r ==> forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> rest_dec(s, dpos, DASC) is None,
{
    let n = b.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == b@.len(),
            0 <= dpos <= seen.len(),
            b@ == seen.subrange(dpos, seen.len() as int),
            forall|q: int| 0 <= q < k ==> #[trigger] b@[q] < 0x80,
        decreases n - k,
    {
        if get(b, k) >= 0x80 {
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies rest_dec(s, dpos, DASC) is None by {
                    assert(seen.len() == dpos + n);
                    assert(b@[k as int] == seen.subrange(dpos, seen.len() as int)[k as int]);
                    lemma_ext_byte(seen, s, dpos + k);
                    assert(!all_ascii(s, dpos));
                }
            }
            return false;
        }
        k = k + 1;
    }
    extend(out, b);
    proof {
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies rest_dec(s, dpos, DASC) == cat(
            out@,
            rest_dec(s, dpos + n, DASC),
        ) by {
            assert(seen.len() == dpos + n);
            assert forall|q: int| dpos <= q < dpos + n implies s[q] == b@[q - dpos] by {
                lemma_ext_byte(seen, s, q);
            }
            assert(all_ascii(s, dpos) == all_ascii(s, dpos + n)) by {
                if all_ascii(s, dpos + n) {
                    assert forall|q: int| dpos <= q < s.len() implies #[trigger] s[q] < 0x80 by {
                        if q < dpos + n {
                            assert(b@[q - dpos] < 0x80);
                        }
                    }
                }
            }
            if all_ascii(s, dpos) {
                assert(s.subrange(dpos, s.len() as int) =~= b@ + s.subrange(dpos + n, s.len() as int));
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Knowing the encoding from the first bytes
// ---------------------------------------------------------------------------

/// The XML declaration's encoding name, read from `b`, is the one read
/// from any input that begins with `b`.
proof fn lemma_declared_stable(b: Seq<u8>, s: Seq<u8>)
    requires
        ag(b, s, b.len() as int),
        declared_enc(b) is Some,
    ensures
        declared_enc(s) == declared_enc(b),
{
    let hi = b.len() as int;
    let p0 = bom_end(b);
    assert(hi >= 6);
    lemma_bom_end_eq(b, s, hi);
    lemma_lit_eq(b, s, hi, p0, lit_xmldecl());
    lemma_byte_eq(b, s, hi, p0 + 5);
    let (v, _, _) = version_info(b, p0 + 5).unwrap();
    lemma_version_info_eq(b, s, hi, p0 + 5);
    let j = ws_end(b, v);
    assert(j > v && has_lit(b, j, lit_encoding()));
    assert(lit_encoding().len() == 8);
    lemma_ws_eq(b, s, hi, v);
    lemma_lit_eq(b, s, hi, j, lit_encoding());
    lemma_enc_span_eq(b, s, hi, j);
}

/// Which decoder reads every input that begins with `b`: `DNONE` if `b`
/// does not say (the input is read whole), `DWAIT` if the next bytes may.
fn decide(b: &[u8]) -> (r: u8)
    requires
        b@.len() >= 1,
        b@.len() <= isize::MAX,
    ensures
        r <= DWAIT,
        r <= DASC ==> forall|s: Seq<u8>| #[trigger]
            ext(b@, s) ==> input_enc(s) == dk_enc(r) && decode_input(s) == rest_dec(s, 0, r),
{
    let ghost bb = b@;
    proof {
        assert(bb.subrange(0, bb.len() as int) =~= bb);
    }
    if ex_has2(b, 0, 0xFF, 0xFE) || ex_has2(b, 0, 0xFE, 0xFF) {
        let le = get(b, 0) == 0xFF;
        proof {
            assert(bb.subrange(0, 2)[0] == bb[0]);
            assert forall|s: Seq<u8>| #[trigger] ext(bb, s) implies input_enc(s) == Enc::Utf16 && decode_input(s)
                == utf16_dec(s, 0, le) by {
                lemma_window(bb, bb, 0, s);
                lemma_lit_eq(bb, s, 2, 0, seq![0xFFu8, 0xFE]);
                lemma_lit_eq(bb, s, 2, 0, seq![0xFEu8, 0xFF]);
                lemma_ext_byte(bb, s, 0);
            }
        }
        return if le { D16LE } else { D16BE };
    }
    let b0 = get(b, 0);
    if b.len() < 2 && (b0 == 0xFE || b0 == 0xFF) {
        return DWAIT;
    }
    proof {
        lemma_enc_lits();
    }
    let d = match ex_declared_enc(b) {
        Some((x, y)) => if ex_ci_eq(b, x, y, &L_LATIN1) {
            DL1
        } else if ex_ci_eq(b, x, y, &L_ASCII) {
            DASC
        } else {
            DNONE
        },
        None => DNONE,
    };
    proof {
        if d <= DASC {
            let (x, y) = declared_enc(bb).unwrap();
            assert forall|s: Seq<u8>| #[trigger] ext(bb, s) implies input_enc(s) == dk_enc(d) && decode_input(s)
                == rest_dec(s, 0, d) by {
                lemma_window(bb, bb, 0, s);
                lemma_declared_stable(bb, s);
                lemma_ext_byte(bb, s, 0);
                if bb.len() >= 2 {
                    lemma_lit_eq(bb, s, 2, 0, seq![0xFFu8, 0xFE]);
                    lemma_lit_eq(bb, s, 2, 0, seq![0xFEu8, 0xFF]);
                } else {
                    if has_lit(s, 0, seq![0xFFu8, 0xFE]) {
                        assert(s.subrange(0, 2)[0] == s[0]);
                    }
                    if has_lit(s, 0, seq![0xFEu8, 0xFF]) {
                        assert(s.subrange(0, 2)[0] == s[0]);
                    }
                }
                assert forall|k: int| x <= k < y implies #[trigger] s[k] == bb[k] by {
                    lemma_ext_byte(bb, s, k);
                }
                assert(ci_eq(s, x, y, lit_latin1()) == ci_eq(bb, x, y, lit_latin1()));
                assert(ci_eq(s, x, y, lit_ascii()) == ci_eq(bb, x, y, lit_ascii()));
                assert(s.subrange(0, s.len() as int) =~= s);
            }
        }
    }
    d
}

// ---------------------------------------------------------------------------
// The reader
// ---------------------------------------------------------------------------

/// `dk_enc`.
fn enc_of(dk: u8) -> (e: Enc)
    ensures
        e == dk_enc(dk),
{
    if dk == D16LE || dk == D16BE {
        Enc::Utf16
    } else if dk == DL1 {
        Enc::Latin1
    } else {
        Enc::Ascii
    }
}

pub struct Reader {
    /// The stream over the text.
    pub st: Stream,
    pub kind: u8,
    /// `K_DEC`: the decoder, and the input it has not decoded yet (part of
    /// a UTF-16 code unit or pair).
    pub dk: u8,
    pub pend: Vec<u8>,
    /// The input, kept while it may be handed back whole: `K_DECIDE`,
    /// `K_WHOLE`, and `K_DEC` while `keep`.
    pub head: Vec<u8>,
    pub keep: bool,
    /// How much input has been fed, and decoded.
    pub fed: usize,
    pub done_in: usize,
    pub seen: Ghost<Seq<u8>>,
    pub dpos: Ghost<int>,
}

impl Reader {
    /// Every input that begins with `seen` decodes to the text the stream
    /// has seen, then the decoding of the rest.
    pub open spec fn dec_ok(&self) -> bool {
        &&& 0 <= self.dpos@ <= self.seen@.len()
        &&& self.done_in == self.dpos@
        &&& self.pend@ == self.seen@.subrange(self.dpos@, self.seen@.len() as int)
        &&& self.dk <= DASC
        &&& self.st.enc == dk_enc(self.dk)
        &&& forall|s: Seq<u8>| #[trigger]
            ext(self.seen@, s) ==> input_enc(s) == dk_enc(self.dk) && decode_input(s) == cat(
                self.st.seen(),
                rest_dec(s, self.dpos@, self.dk),
            )
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.st.inv()
        &&& self.kind <= K_DONE
        &&& self.fed == self.seen@.len()
        &&& self.fed <= isize::MAX
        &&& self.kind == K_RAW ==> self.st.enc == Enc::Utf8 && self.st.seen() == self.seen@
        &&& (self.kind == K_DECIDE || self.kind == K_WHOLE) ==> self.head@ == self.seen@
        &&& self.kind == K_DECIDE ==> self.head@.len() >= 1
        &&& self.kind == K_DEC ==> self.dec_ok() && (self.keep ==> self.head@ == self.seen@) && (!self.keep
            ==> self.st.phase != PH_HEAD && self.st.phase != PH_WHOLE)
    }

    /// Nothing more is read: the verdict has been given.
    pub open spec fn over(&self) -> bool {
        ||| self.kind == K_DONE
        ||| (self.kind == K_RAW || self.kind == K_DEC) && (self.st.phase == PH_FAILED || self.st.phase == PH_DONE)
    }

    /// A new reader, before any input.
    pub fn new() -> (r: Reader)
        ensures
            r.inv(),
            r.kind == K_RAW,
            r.seen@ == Seq::<u8>::empty(),
    {
        Reader {
            st: Stream::new(),
            kind: K_RAW,
            dk: 0,
            pend: Vec::new(),
            head: Vec::new(),
            keep: false,
            fed: 0,
            done_in: 0,
            seen: Ghost(Seq::empty()),
            dpos: Ghost(0),
        }
    }

    /// Feeds the next chunk (`last`: the last one). `R_MORE`: more is
    /// needed; `R_OK`, `R_ERR`: the verdict on the input; `R_WHOLE`: the
    /// input is to be read whole, from `head`, once all of it is fed;
    /// `R_LIMIT`: a limit was reached.
    pub fn feed(&mut self, data: &[u8], last: bool) -> (r: u8)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r <= R_LIMIT,
            old(self).over() ==> r == R_ERR && final(self).seen@ == old(self).seen@,
            r != R_LIMIT && !old(self).over() ==> final(self).seen@ == old(self).seen@ + data@,
            r == R_OK ==> last && parse(final(self).seen@) is Some,
            r == R_ERR && !old(self).over() ==> fails_parse(final(self).seen@, last),
            r == R_MORE ==> !last,
            r == R_WHOLE ==> final(self).kind == K_WHOLE && final(self).head@ == final(self).seen@,
    {
        hide(document);
        hide(parse);
        hide(input_enc);
        hide(decode_input);
        if self.kind == K_DONE {
            return R_ERR;
        }
        if (self.kind == K_RAW || self.kind == K_DEC) && (self.st.phase == PH_FAILED || self.st.phase == PH_DONE) {
            return R_ERR;
        }
        if data.len() > isize::MAX as usize - self.fed {
            self.kind = K_DONE;
            return R_LIMIT;
        }
        if self.kind == K_RAW {
            let r = self.st.feed(data, last);
            if r == R_LIMIT {
                self.kind = K_DONE;
                return R_LIMIT;
            }
            self.fed = self.fed + data.len();
            proof {
                self.seen@ = self.seen@ + data@;
            }
            if r != R_WHOLE {
                return r;
            }
            // Not UTF-8, or not known to be: the input decides what next.
            let mut h: Vec<u8> = Vec::new();
            extend(&mut h, self.st.w.buf.as_slice());
            proof {
                assert(h@ =~= self.seen@);
            }
            self.head = h;
            if self.head.len() == 0 {
                // No input at all: read whole.
                self.kind = K_WHOLE;
                return R_WHOLE;
            }
            self.kind = K_DECIDE;
            return self.start(last);
        }
        if self.kind == K_DECIDE || self.kind == K_WHOLE {
            extend(&mut self.head, data);
            self.fed = self.fed + data.len();
            proof {
                self.seen@ = self.seen@ + data@;
            }
            if self.kind == K_WHOLE {
                return R_WHOLE;
            }
            return self.start(last);
        }
        // Decoding.
        let ghost s0 = self.seen@;
        extend(&mut self.pend, data);
        if self.keep {
            extend(&mut self.head, data);
        }
        self.fed = self.fed + data.len();
        proof {
            self.seen@ = self.seen@ + data@;
            assert(ext(s0, self.seen@)) by {
                assert(self.seen@.subrange(0, s0.len() as int) =~= s0);
            }
            assert(self.pend@ =~= self.seen@.subrange(self.dpos@, self.seen@.len() as int));
            assert forall|s: Seq<u8>| #[trigger] ext(self.seen@, s) implies input_enc(s) == dk_enc(self.dk)
                && decode_input(s) == cat(self.st.seen(), rest_dec(s, self.dpos@, self.dk)) by {
                lemma_ext_trans(s0, self.seen@, s);
            }
        }
        self.dec_feed(last)
    }

    /// `K_DECIDE`: the input so far, in `head`, may say its encoding.
    fn start(&mut self, last: bool) -> (r: u8)
        requires
            old(self).inv(),
            old(self).kind == K_DECIDE,
        ensures
            final(self).inv(),
            final(self).seen@ == old(self).seen@,
            r <= R_LIMIT,
            r == R_OK ==> last && parse(final(self).seen@) is Some,
            r == R_ERR ==> fails_parse(final(self).seen@, last),
            r == R_MORE ==> !last,
            r == R_WHOLE ==> final(self).kind == K_WHOLE && final(self).head@ == final(self).seen@,
    {
        hide(document);
        hide(parse);
        hide(input_enc);
        hide(decode_input);
        slice_len_bound(self.head.as_slice());
        let d = decide(self.head.as_slice());
        if d == DWAIT {
            if last {
                self.kind = K_WHOLE;
                return R_WHOLE;
            }
            return R_MORE;
        }
        if d == DNONE || d > DASC {
            self.kind = K_WHOLE;
            return R_WHOLE;
        }
        self.st = Stream::decoded(enc_of(d));
        self.dk = d;
        let mut p: Vec<u8> = Vec::new();
        extend(&mut p, self.head.as_slice());
        self.pend = p;
        self.keep = true;
        self.done_in = 0;
        proof {
            self.dpos@ = 0;
            assert(self.pend@ =~= self.seen@.subrange(0, self.seen@.len() as int));
            assert forall|s: Seq<u8>| #[trigger] ext(self.seen@, s) implies input_enc(s) == dk_enc(self.dk)
                && decode_input(s) == cat(self.st.seen(), rest_dec(s, 0, self.dk)) by {
                match rest_dec(s, 0, self.dk) {
                    Some(t) => assert(Seq::<u8>::empty() + t =~= t),
                    None => {},
                }
            }
        }
        self.kind = K_DEC;
        self.dec_feed(last)
    }

    /// `K_DEC`: decodes what it can of `pend`, and feeds the text to the
    /// stream.
    #[verifier::rlimit(60)]
    fn dec_feed(&mut self, last: bool) -> (r: u8)
        requires
            old(self).inv(),
            old(self).kind == K_DEC,
            !old(self).over(),
        ensures
            final(self).inv(),
            final(self).seen@ == old(self).seen@,
            r <= R_LIMIT,
            r == R_OK ==> last && parse(final(self).seen@) is Some,
            r == R_ERR ==> fails_parse(final(self).seen@, last),
            r == R_MORE ==> !last,
            r == R_WHOLE ==> final(self).kind == K_WHOLE && final(self).head@ == final(self).seen@,
    {
        hide(document);
        hide(input_enc);
        let ghost seen = self.seen@;
        let ghost dpos = self.dpos@;
        let ghost s0 = self.st.seen();
        let mut out: Vec<u8> = Vec::new();
        let n = self.pend.len();
        let (i, ok) = if self.dk == D16LE || self.dk == D16BE {
            dec16(self.pend.as_slice(), self.dk == D16LE, &mut out, Ghost(seen), Ghost(dpos))
        } else if self.dk == DL1 {
            dec_l1(self.pend.as_slice(), &mut out, Ghost(seen), Ghost(dpos));
            (n, true)
        } else {
            let ok = dec_ascii(self.pend.as_slice(), &mut out, Ghost(seen), Ghost(dpos));
            (n, ok)
        };
        if !ok {
            proof {
                reveal(parse);
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies parse(s) is None by {
                    assert(rest_dec(s, dpos, self.dk) is None);
                }
            }
            self.kind = K_DONE;
            return R_ERR;
        }
        // What the decoder reached: every input decodes to the text, `out`,
        // then the rest from `dpos + i`.
        proof {
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies rest_dec(s, dpos, self.dk) == cat(
                out@,
                rest_dec(s, dpos + i, self.dk),
            ) by {}
        }
        let mut p: Vec<u8> = Vec::new();
        extend(&mut p, vstd::slice::slice_subrange(self.pend.as_slice(), i, n));
        self.pend = p;
        self.done_in = self.done_in + i;
        proof {
            self.dpos@ = dpos + i;
            assert(self.pend@ =~= seen.subrange(dpos + i, seen.len() as int));
        }
        if last && self.pend.len() > 0 {
            // Input cut short.
            proof {
                reveal(parse);
                assert(rest_dec(seen, dpos + i, self.dk) is None);
                lemma_ext_refl(seen);
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies parse(s) is None by {
                    lemma_cat_assoc(s0, out@, rest_dec(s, dpos + i, self.dk));
                }
            }
            self.kind = K_DONE;
            return R_ERR;
        }
        let r = self.st.feed(out.as_slice(), last);
        if r == R_LIMIT {
            self.kind = K_DONE;
            return R_LIMIT;
        }
        if r == R_WHOLE {
            self.kind = K_WHOLE;
            return R_WHOLE;
        }
        let ghost text = self.st.seen();
        proof {
            assert(text == s0 + out@);
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies input_enc(s) == dk_enc(self.dk) && decode_input(s)
                == cat(text, rest_dec(s, self.dpos@, self.dk)) by {
                lemma_cat_assoc(s0, out@, rest_dec(s, dpos + i, self.dk));
            }
        }
        if self.keep && self.st.phase != PH_HEAD && self.st.phase != PH_WHOLE {
            self.head = Vec::new();
            self.keep = false;
        }
        proof {
            if r == R_OK || r == R_ERR {
                reveal(parse);
                assert(self.st.verdict(r, last));
                assert(self.pend@.len() == 0 || !last);
                if last {
                    assert(self.dpos@ == seen.len());
                    lemma_rest_end(seen, self.dk);
                }
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies (match decode_input(s) {
                    Some(u) => ext(text, u) && (last ==> u == text),
                    None => true,
                }) by {
                    match rest_dec(s, self.dpos@, self.dk) {
                        Some(t) => {
                            assert((text + t).subrange(0, text.len() as int) =~= text);
                            if last {
                                assert(t == Seq::<u8>::empty());
                                assert(text + t =~= text);
                            }
                        },
                        None => {},
                    }
                }
                if r == R_OK {
                    lemma_ext_refl(text);
                    lemma_ext_refl(seen);
                    assert(decode_input(seen) == Some(text));
                }
                if r == R_ERR {
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies parse(s) is None by {
                        match decode_input(s) {
                            Some(u) => {
                                assert(ext(text, u));
                                assert(document(u, self.st.enc) == docx(u));
                                assert(docx(u) is None);
                            },
                            None => {},
                        }
                    }
                }
            }
        }
        r
    }
}

} // verus!
