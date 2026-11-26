//! Streaming decompression, the way zlib's `inflate()` works: input and
//! output in pieces of any size, proven against the same spec as the
//! one-shot API.
//!
//! The theorem is stated for a ghost `full` stream fixed when the `Stream`
//! is made: as long as each call's input is the next piece of `full`
//! (`ok()` stays true), every byte delivered is the spec's, `End` means
//! the spec accepts `full` with exactly the output delivered and the input
//! used, and `BadData` means the spec rejects `full`. Since `full` is
//! arbitrary, this holds for whatever the stream turns out to be. Memory
//! safety and termination hold for any input.
//!
//! Output is decoded into a window buffer that keeps the last 32 KiB for
//! matches. When the input ends inside a symbol or header, the decoder rolls
//! back to its start; the bytes from there on are kept in `pending` and
//! read again, followed by the next input, on the next call. Bits already
//! taken from a partly used byte are kept with that byte, so the decoder's
//! state never depends on input the caller still holds.
#[cfg(verus_only)]
use crate::checksum::{adler_from, crc_from, lemma_adler_append, lemma_adler_closed, lemma_adler_from, lemma_crc_append, lemma_crc_from};
use crate::inflate::*;
#[cfg(verus_only)]
use crate::ilemmas::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use crate::slemmas::*;
#[cfg(verus_only)]
use crate::spec;
use crate::wrap::*;
use vstd::prelude::*;

verus! {

/// History DEFLATE matches may reach back into.
pub const WINDOW: usize = 32768;

/// Room for new output after the history in the window buffer.
pub const CHUNK: usize = 65536;

/// Input bytes copied after `pending` to finish the symbol it starts. The
/// fast loop stops 15 bytes before the end of what it is given, so a short
/// bridge leaves the rest of the window to the careful loop: on highly
/// compressible input a few bridge bytes fill most of it.
const BRIDGE: usize = 512;

/// The container, or `Auto` to accept zlib or gzip.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Wrapper {
    Raw,
    Zlib,
    Gzip,
    Auto,
}

/// What a call to [`Stream::inflate`] achieved.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Progress {
    /// Some input was consumed or output produced (or both); call again.
    Ok,
    /// The stream is complete and all its output has been delivered.
    End,
    /// Nothing could be done: more input or more output space is needed.
    Stalled,
    /// The zlib stream was made with a preset dictionary, whose Adler-32
    /// is `dict_id()`: pass it to `set_dictionary`, then call again.
    NeedDict,
}

const P_HEADER: u8 = 0;
const P_BODY: u8 = 1;
const P_TRAILER: u8 = 2;
const P_DONE: u8 = 3;
const P_FAILED: u8 = 4;
const P_DICT: u8 = 5;

// Stages of a gzip header.
const G_FIXED: u8 = 0;
const G_XLEN: u8 = 1;
const G_EXTRA: u8 = 2;
const G_NAME: u8 = 3;
const G_COMMENT: u8 = 4;
const G_HCRC: u8 = 5;

/// The format a stream with wrapper `w` is decoded as.
pub open spec fn format_of(w: Wrapper, full: Seq<u8>) -> Format {
    match w {
        Wrapper::Raw => Format::Raw,
        Wrapper::Zlib => Format::Zlib,
        Wrapper::Gzip => Format::Gzip,
        Wrapper::Auto => if full.len() > 0 && full[0] == 31 {
            Format::Gzip
        } else {
            Format::Zlib
        },
    }
}

/// What the spec gives for the stream, with preset dictionary `dict`
/// (empty when none was set).
#[verifier::opaque]
pub open spec fn spec_stream(w: Wrapper, full: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match format_of(w, full) {
        Format::Raw => spec::inflate_dict(full, dict),
        Format::Zlib => spec::zlib_decompress_dict(full, dict),
        Format::Gzip => spec::gzip_decompress(full),
    }
}

/// A zlib header's first two bytes, apart from FDICT.
pub open spec fn zlib_cm_ok(b: Seq<u8>) -> bool {
    let cmf = b[0] as nat;
    let flg = b[1] as nat;
    &&& b.len() >= 2
    &&& cmf % 16 == 8
    &&& cmf / 16 <= 7
    &&& (cmf * 256 + flg) % 31 == 0
}

pub open spec fn zlib_fdict(b: Seq<u8>) -> bool {
    (b[1] as nat / 32) % 2 == 1
}

/// Where the DEFLATE data starts, and the output it continues (the
/// dictionary, if the stream uses one).
pub open spec fn shdr(f: Format, b: Seq<u8>, dict: Seq<u8>) -> Option<(int, Seq<u8>)> {
    match f {
        Format::Raw => Some((0, dict)),
        Format::Zlib => if !zlib_cm_ok(b) {
            None
        } else if !zlib_fdict(b) {
            Some((2, Seq::empty()))
        } else if b.len() < 6 || spec::be32(b, 2) != spec::adler32(dict) {
            None
        } else {
            Some((6, dict))
        },
        Format::Gzip => match spec::gzip_header(b) {
            None => None,
            Some(h) => Some((h, Seq::empty())),
        },
    }
}

/// `spec::inflate_blocks`, hidden from the proofs that only pass it around.
#[verifier::opaque]
pub open spec fn blocks(b: Seq<u8>, p: int, o: Seq<u8>) -> Option<(int, Seq<u8>)> {
    spec::inflate_blocks(b, p, o)
}

/// The spec as a header, DEFLATE data continuing `d0`, and a trailer.
#[verifier::opaque]
pub open spec fn sspec(f: Format, b: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match shdr(f, b, dict) {
        None => None,
        Some((h, d0)) => match blocks(b, 8 * h, d0) {
            None => None,
            Some((end, o)) => if o.len() >= d0.len() && o.subrange(0, d0.len() as int) == d0 {
                spec_trailer(f, b, (end + 7) / 8, o.subrange(d0.len() as int, o.len() as int))
            } else {
                None
            },
        },
    }
}

proof fn lemma_sspec(w: Wrapper, b: Seq<u8>, dict: Seq<u8>)
    ensures
        spec_stream(w, b, dict) == sspec(format_of(w, b), b, dict),
{
    reveal(spec_stream);
    reveal(sspec);
    reveal(blocks);
    reveal(spec_trailer);
    let f = format_of(w, b);
    if let Some((h, d0)) = shdr(f, b, dict) {
        if let Some((end, o)) = spec::inflate_blocks(b, 8 * h, d0) {
            assert(o.subrange(0, 0) =~= Seq::<u8>::empty());
            assert(o.subrange(0, o.len() as int) =~= o);
        }
    }
}

pub open spec fn trailer_len(f: Format) -> nat {
    match f {
        Format::Raw => 0,
        Format::Zlib => 4,
        Format::Gzip => 8,
    }
}

/// A result of the decoder, whose input starts at byte `base` and whose
/// output follows `pfx`, in the coordinates of the whole stream.
pub open spec fn lift(r: Option<(int, Seq<u8>)>, base: int, pfx: Seq<u8>) -> Option<(int, Seq<u8>)> {
    match r {
        None => None,
        Some((e, o)) => Some((e + 8 * base, pfx + o)),
    }
}

// The steps of `spec::gzip_header`.
pub open spec fn gz_fixed_ok(b: Seq<u8>) -> bool {
    b.len() >= 10 && b[0] == 31 && b[1] == 139 && b[2] == 8 && b[3] < 32
}

pub open spec fn gz_p1(b: Seq<u8>) -> Option<int> {
    if spec::has(b[3] as nat, spec::GZ_FEXTRA) {
        if 12 > b.len() || 12 + spec::le16(b, 10) > b.len() {
            None
        } else {
            Some(12 + spec::le16(b, 10) as int)
        }
    } else {
        Some(10)
    }
}

pub open spec fn gz_p2(b: Seq<u8>) -> Option<int> {
    match gz_p1(b) {
        None => None,
        Some(p) => if spec::has(b[3] as nat, spec::GZ_FNAME) {
            spec::skip_zstr(b, p)
        } else {
            Some(p)
        },
    }
}

pub open spec fn gz_p3(b: Seq<u8>) -> Option<int> {
    match gz_p2(b) {
        None => None,
        Some(p) => if spec::has(b[3] as nat, spec::GZ_FCOMMENT) {
            spec::skip_zstr(b, p)
        } else {
            Some(p)
        },
    }
}

pub open spec fn gz_end(b: Seq<u8>, p: int) -> Option<int> {
    if spec::has(b[3] as nat, spec::GZ_FHCRC) {
        if p + 2 > b.len() || spec::le16(b, p) != spec::crc32(b.subrange(0, p)) as nat % 65536 {
            None
        } else {
            Some(p + 2)
        }
    } else {
        Some(p)
    }
}

/// Recording that `inflate` was called keeps the state consistent.
proof fn lemma_set_fed(s1: Stream, s2: Stream)
    requires
        s1.wf(),
        s2 == (Stream { fed: true, ..s1 }),
    ensures
        s2.wf(),
{
    reveal(Stream::header_ok);
    reveal(Stream::body_ok);
    reveal(Stream::trailer_ok);
}

/// Moving the window back by `p2` keeps what the decoder will produce.
proof fn lemma_slide(s0: Inflater, s1: Inflater, b: Seq<u8>, p2: Seq<u8>, w2: Seq<u8>, pfx: Seq<u8>, base: int)
    requires
        s1.mode == s0.mode,
        s1.pos() == s0.pos(),
        s1.last == s0.last,
        s1.stored_left == s0.stored_left,
        s1.copy_len == s0.copy_len,
        s1.copy_dist == s0.copy_dist,
        s1.lit_lens == s0.lit_lens,
        s1.dist_lens == s0.dist_lens,
        w2.len() >= MAX_DIST,
        s1.mode == MODE_CODES && s1.copy_len > 0 ==> 1 <= s1.copy_dist <= MAX_DIST,
    ensures
        lift(s0.rest(b, p2 + w2), base, pfx) == lift(s1.rest(b, w2), base, pfx + p2),
{
    reveal(Inflater::rest);
    assert(s0.rest(b, p2 + w2) == s1.rest(b, p2 + w2));
    lemma_win_rest(s1, b, p2, w2);
    let r = s1.rest(b, w2);
    if let Some((e, o)) = r {
        assert(pfx + (p2 + o) =~= pfx + p2 + o);
    }
}

/// Dropping the first `c` bytes of the decoder's input keeps what it
/// will produce.
proof fn lemma_keep(
    s1: Inflater,
    s2: Inflater,
    s2a: Inflater,
    done: bool,
    full: Seq<u8>,
    xbase: int,
    c: int,
    w1: Seq<u8>,
    pfx: Seq<u8>,
)
    requires
        0 <= xbase,
        0 <= c,
        xbase + c <= full.len(),
        moved(s1, s2, c),
        s1.pos() >= 0,
        s2.pos() == s2a.pos(),
        s2.same_but_bits(&s2a),
        done ==> s2a.mode == MODE_DONE,
    ensures
        lift(s1.rest(skip(full, xbase + c), w1), xbase + c, pfx) == lift(s2a.rest(skip(full, xbase), w1), xbase, pfx),
        done ==> s2a.rest(skip(full, xbase), w1) == Some((s2a.pos(), w1)),
{
    let b = skip(full, xbase);
    if done {
        lemma_rest_done(s2a, b, w1);
    }
    lemma_rest_same(s2, s2a, b, w1);
    lemma_shift_rest(s1, s2, b, c, w1);
    lemma_skip_skip(full, xbase, c);
    let r = s2.rest(b, w1);
    assert(lift(sh(r, c), xbase + c, pfx) == lift(r, xbase, pfx));
}

/// What `run_once` keeps: of the decoder's input `y = pd ++ inp[ip..]`, the
/// bytes from `c` to `e` become `pending`, and the caller's input is used up
/// to `nip`.
proof fn lemma_keep_bytes(pd: Seq<u8>, inp: Seq<u8>, ip: int, c: int, e: int, nip: int)
    requires
        0 <= ip <= inp.len(),
        0 <= c <= e,
        pd.len() <= e,
        nip == ip + (e - pd.len()),
        nip <= inp.len(),
    ensures
        ({
            let y = pd + inp.subrange(ip, inp.len() as int);
            &&& y.subrange(c, e) + inp.subrange(nip, inp.len() as int) == skip(y, c)
            &&& e <= y.len()
        }),
{
    let y = pd + inp.subrange(ip, inp.len() as int);
    assert(y.subrange(c, e) + inp.subrange(nip, inp.len() as int) =~= y.subrange(c, y.len() as int));
}

/// The decoder's input is the stream from `xbase`.
proof fn lemma_y_full(pd: Seq<u8>, inp: Seq<u8>, ip: int, full: Seq<u8>, xbase: int, used: int, c: int, e: int)
    requires
        0 <= ip <= inp.len(),
        0 <= xbase <= used,
        used + (inp.len() - ip) <= full.len(),
        pd == full.subrange(xbase, used),
        inp.subrange(ip, inp.len() as int) == full.subrange(used, used + (inp.len() - ip)),
        0 <= c <= e <= pd.len() + (inp.len() - ip),
    ensures
        (pd + inp.subrange(ip, inp.len() as int)).subrange(c, e) == full.subrange(xbase + c, xbase + e),
{
    let y = pd + inp.subrange(ip, inp.len() as int);
    assert(y =~= full.subrange(xbase, used + (inp.len() - ip)));
    assert(y.subrange(c, e) =~= full.subrange(xbase + c, xbase + e));
}

/// A later tail of input that matched `b` from `u` still matches it.
proof fn lemma_tail(inp: Seq<u8>, ip: int, nip: int, b: Seq<u8>, u: int)
    requires
        0 <= ip <= nip <= inp.len(),
        0 <= u,
        u + (inp.len() - ip) <= b.len(),
        inp.subrange(ip, inp.len() as int) == b.subrange(u, u + (inp.len() - ip)),
    ensures
        inp.subrange(nip, inp.len() as int) == b.subrange(u + (nip - ip), u + (nip - ip) + (inp.len() - nip)),
{
    assert forall|i: int| 0 <= i < inp.len() - nip implies inp.subrange(nip, inp.len() as int)[i] == b.subrange(
        u + (nip - ip),
        u + (nip - ip) + (inp.len() - nip),
    )[i] by {
        let j = i + (nip - ip);
        assert(inp.subrange(ip, inp.len() as int)[j] == b.subrange(u, u + (inp.len() - ip))[j]);
        assert(inp.subrange(ip, inp.len() as int)[j] == inp[ip + j]);
        assert(inp.subrange(nip, inp.len() as int)[i] == inp[nip + i]);
        assert(b.subrange(u, u + (inp.len() - ip))[j] == b[u + j]);
        assert(b.subrange(u + (nip - ip), u + (nip - ip) + (inp.len() - nip))[i] == b[u + (nip - ip) + i]);
    }
    assert(inp.subrange(nip, inp.len() as int) =~= b.subrange(u + (nip - ip), u + (nip - ip) + (inp.len() - nip)));
}

proof fn lemma_gzip_header(b: Seq<u8>)
    ensures
        spec::gzip_header(b) == if !gz_fixed_ok(b) {
            None
        } else {
            match gz_p3(b) {
                None => None,
                Some(p) => gz_end(b, p),
            }
        },
{
}

proof fn lemma_skip_zstr_step(b: Seq<u8>, p: int)
    requires
        0 <= p < b.len(),
    ensures
        b[p] != 0 ==> spec::skip_zstr(b, p) == spec::skip_zstr(b, p + 1),
        b[p] == 0 ==> spec::skip_zstr(b, p) == Some(p + 1),
{
}

/// Work per held-back byte: its bits, read again when decoding resumes.
pub open spec fn held_cost() -> nat {
    8 * bit_cost()
}

/// Pays for one stop for more input inside a bridge.
pub open spec fn hold_cost() -> nat {
    50000
}

/// A decoder run that ends a block or fills the window: the byte it
/// leaves partly read, and the end of a block body.
pub open spec fn turn_cost() -> nat {
    8 * bit_cost() + body_cost()
}

/// Work paid for when nothing is held back.
pub open spec fn start_cost() -> nat {
    130000
}

/// The most a call to `inflate` spends beyond `in_cost()` per input byte
/// used and 2 per output byte delivered.
pub open spec fn call_cost() -> nat {
    600000
}

/// The most `body` spends beyond its input and output.
pub open spec fn body_call() -> nat {
    400000
}

/// Work per input byte a call uses.
pub open spec fn in_cost() -> nat {
    10000
}

/// The run that stops a call for more input.
pub open spec fn exit_cost() -> nat {
    8 * bit_cost() + fail_cost() + hold_cost()
}

/// The cost of one `run_once`, from the decoder's bound and the held-back
/// bytes before (`p`) and after (`e - c`).
proof fn lemma_once_cost(
    w0: int,
    w1: int,
    p: int,
    k: int,
    rem: int,
    c: int,
    e: int,
    used: int,
    pos0: int,
    pos1: int,
    dout: int,
    trunc: bool,
    absorb: bool,
    exit: bool,
)
    requires
        0 <= pos0,
        pos1 <= 8 * c + 8,
        0 <= c <= e,
        0 <= k <= rem,
        0 <= p,
        0 <= used,
        k < rem ==> p > 0 && k == BRIDGE,
        p == 0 ==> k == rem,
        absorb == (trunc && (k == rem || c < p)),
        absorb ==> e == p + k && used == k,
        !absorb && c >= p ==> e == c && used == c - p,
        !absorb && c < p ==> e == p && used == 0,
        exit ==> (absorb && k == rem) || used == rem,
        absorb && k == rem ==> exit,
        trunc ==> w1 <= w0 + bit_cost() * (pos1 - pos0) + dout + fail_cost(),
        !trunc ==> w1 <= w0 + bit_cost() * (pos1 - pos0) + dout + body_cost(),
    ensures
        w1 + held_cost() * (e - c) + (if e - c > 0 { hold_cost() } else { 0 }) <= w0 + held_cost() * p + (if p > 0 {
            hold_cost()
        } else {
            0
        }) + in_cost() * used + dout + if trunc {
            if exit {
                exit_cost()
            } else {
                0
            }
        } else {
            turn_cost()
        },
{
    assert(bit_cost() * (pos1 - pos0) <= 9600 * (c + 1)) by (nonlinear_arith)
        requires
            pos0 >= 0,
            pos1 <= 8 * c + 8,
            bit_cost() == 1200,
    ;
    let m = if trunc { fail_cost() } else { body_cost() };
    assert(fail_cost() == 32171);
    assert(held_cost() == 9600 && hold_cost() == 50000 && turn_cost() == 9730 && exit_cost() == 91771);
    assert(in_cost() == 10000);
    assert(w1 <= w0 + 9600 * (c + 1) + dout + m);
    if absorb {
        assert(e - c == p + k - c);
        assert(BRIDGE == 512);
        if exit {
        } else {
            assert(k == 512);
            assert(p > 0);
        }
    } else if c >= p {
        assert(e - c == 0);
    } else {
        assert(e - c == p - c);
    }
}

/// The parts of a valid gzip header, in order.
proof fn lemma_gz_parts(b: Seq<u8>)
    ensures
        spec::gzip_header(b) matches Some(h) ==> gz_fixed_ok(b) && (gz_p1(b) matches Some(p1) && 10 <= p1
            && (spec::has(b[3] as nat, spec::GZ_FEXTRA) ==> p1 == 12 + spec::le16(b, 10)) && (gz_p2(b) matches Some(p2)
            && p1 <= p2 && (gz_p3(b) matches Some(p3) && p2 <= p3 && p3 <= h && (spec::has(b[3] as nat, spec::GZ_FHCRC)
            ==> h == p3 + 2)))),
{
    lemma_gzip_header(b);
    if let Some(p1) = gz_p1(b) {
        crate::ilemmas::lemma_skip_zstr_end(b, p1);
        if let Some(p2) = gz_p2(b) {
            crate::ilemmas::lemma_skip_zstr_end(b, p2);
        }
    }
}

/// The stream needs input past byte `u` when its DEFLATE data ends past
/// bit `8 * u`.
proof fn lemma_short_of(w: Wrapper, full: Seq<u8>, dict: Seq<u8>, h: int, d0: Seq<u8>, u: int)
    requires
        shdr(format_of(w, full), full, dict) == Some((h, d0)),
        past(blocks(full, 8 * h, d0), 8 * u),
    ensures
        spec_stream(w, full, dict) matches Some((_, n)) ==> u < n,
{
    lemma_sspec(w, full, dict);
    reveal(sspec);
    reveal(spec_trailer);
    if let Some((e, o)) = blocks(full, 8 * h, d0) {
        assert((e + 7) / 8 > u) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(8 * u + 8, e + 7, 8);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(u + 1, 8);
        }
    }
}

/// `Inflater::fixed_ok`, hidden from the proofs that do not need it.
#[verifier::opaque]
spec fn dfixed(i: Inflater) -> bool {
    i.fixed_ok()
}

/// `Inflater::inv`, hidden likewise.
#[verifier::opaque]
spec fn dinv(i: Inflater, b: Seq<u8>) -> bool {
    i.inv(b)
}

/// An empty slice.
fn no_bytes() -> (r: &'static [u8])
    ensures
        r@ == Seq::<u8>::empty(),
{
    let r: &'static [u8] = &[];
    proof {
        assert(r@ =~= Seq::<u8>::empty());
    }
    r
}

/// A zlib header's first two bytes are valid, apart from FDICT.
fn zlib_cm(cmf: u8, flg: u8) -> (r: bool)
    ensures
        r == zlib_cm_ok(seq![cmf, flg]),
{
    let c = cmf as u32;
    let f = flg as u32;
    proof {
        assert(c & 0x0f == c % 16 && c >> 4u32 == c / 16) by (bit_vector)
            requires
                c < 256,
        ;
    }
    c & 0x0f == 8 && c >> 4 <= 7 && (c * 256 + f) % 31 == 0
}

/// FDICT is set.
fn fdict(flg: u8) -> (r: bool)
    ensures
        r == ((flg as nat / 32) % 2 == 1),
{
    proof {
        assert((flg & 0x20 != 0) == ((flg as nat / 32) % 2 == 1)) by (bit_vector);
    }
    flg & 0x20 != 0
}

/// Bit `f` of a flag byte.
fn flag(flg: u8, f: u8) -> (r: bool)
    requires
        f == 2 || f == 4 || f == 8 || f == 16,
    ensures
        r == spec::has(flg as nat, f as nat),
{
    proof {
        assert((flg & 2 != 0) == ((flg as nat / 2) % 2 == 1)) by (bit_vector);
        assert((flg & 4 != 0) == ((flg as nat / 4) % 2 == 1)) by (bit_vector);
        assert((flg & 8 != 0) == ((flg as nat / 8) % 2 == 1)) by (bit_vector);
        assert((flg & 16 != 0) == ((flg as nat / 16) % 2 == 1)) by (bit_vector);
    }
    flg & f != 0
}

#[derive(Clone)]
pub struct Stream {
    inf: Box<Inflater>,
    wrapper: Wrapper,
    format: Format,
    phase: u8,
    error: Error,
    // The header parser.
    stage: u8,
    hcount: usize,
    flg: u8,
    xleft: usize,
    hbuf: Vec<u8>,
    hcrc: u32,
    // The body.
    pending: Vec<u8>,
    scratch: Vec<u8>,
    window: Vec<u8>,
    out_read: usize,
    adler_a: u32,
    adler_b: u32,
    crc: u32,
    isize: u32,
    // The trailer.
    tbuf: Vec<u8>,
    tlen: usize,
    // The preset dictionary's Adler-32, and whether `inflate` was called.
    dict_id: u32,
    fed: bool,
    // The stream the theorem is about, and the caller's progress through it.
    full: Ghost<Seq<u8>>,
    // The preset dictionary set, and the output the DEFLATE data continues
    // (the dictionary once it is in use).
    dict: Ghost<Seq<u8>>,
    d0: Ghost<Seq<u8>>,
    ok: Ghost<bool>,
    used: Ghost<int>,
    delivered: Ghost<Seq<u8>>,
    // Output dropped from the front of the window.
    pfx: Ghost<Seq<u8>>,
    // Where the DEFLATE data starts, and ends once it has.
    hlen: Ghost<int>,
    eabs: Ghost<int>,
    // Where the current gzip name or comment starts.
    zstart: Ghost<int>,
}

impl Stream {
    /// The stream the spec is applied to.
    pub closed spec fn full(&self) -> Seq<u8> {
        self.full@
    }

    /// Every call so far was given the next piece of `full()`.
    pub closed spec fn ok(&self) -> bool {
        self.ok@
    }

    /// Bytes of `full()` used so far.
    pub closed spec fn used(&self) -> int {
        self.used@
    }

    /// Output delivered so far.
    pub closed spec fn delivered(&self) -> Seq<u8> {
        self.delivered@
    }

    pub closed spec fn wrapper_spec(&self) -> Wrapper {
        self.wrapper
    }

    /// The preset dictionary set (empty if none).
    pub closed spec fn dict(&self) -> Seq<u8> {
        self.dict@
    }

    /// The decoder's tables are consistent.
    spec fn fixed(&self) -> bool {
        dfixed(*self.inf)
    }

    /// The decoder's state is consistent with input `b`.
    spec fn dinv(&self, b: Seq<u8>) -> bool {
        dinv(*self.inf, b)
    }

    /// Where the decoder's input starts in `full`.
    spec fn base(&self) -> int {
        self.used@ - self.pending@.len()
    }

    /// The checksums cover the output delivered.
    spec fn sums_ok(&self) -> bool {
        &&& self.format == Format::Zlib ==> (self.adler_a as nat, self.adler_b as nat) == adler_from(
            1,
            0,
            self.delivered@,
        )
        &&& self.format == Format::Gzip ==> self.crc == crc_from(0xffff_ffff, self.delivered@)
            && self.isize as nat == self.delivered@.len() % 0x1_0000_0000
    }

    #[verifier::opaque]
    spec fn header_ok(&self) -> bool {
        let b = self.full@;
        let u = self.used@;
        if self.format == Format::Zlib {
            &&& self.hcount < 6
            &&& u == self.hcount
            &&& forall|i: int| 0 <= i < self.hcount ==> self.hbuf@[i] == b[i]
            &&& self.hcount >= 2 ==> zlib_cm_ok(b) && zlib_fdict(b)
            &&& self.dict@ == Seq::<u8>::empty()
        } else if self.format == Format::Gzip {
            &&& self.stage <= G_HCRC
            &&& self.stage == G_FIXED ==> self.hcount < 10 && u == self.hcount && forall|i: int|
                0 <= i < self.hcount ==> self.hbuf@[i] == b[i]
            &&& self.stage != G_FIXED ==> gz_fixed_ok(b) && self.flg == b[3]
            &&& self.stage < G_HCRC ==> self.hcrc == crc_from(0xffff_ffff, b.subrange(0, u))
            &&& self.stage == G_XLEN ==> spec::has(self.flg as nat, spec::GZ_FEXTRA) && self.hcount < 2
                && u == 10 + self.hcount && forall|i: int| 0 <= i < self.hcount ==> self.hbuf@[i] == b[10 + i]
            &&& self.stage == G_EXTRA ==> spec::has(self.flg as nat, spec::GZ_FEXTRA) && 12 <= u
                && u + self.xleft == 12 + spec::le16(b, 10)
            &&& self.stage == G_NAME ==> spec::has(self.flg as nat, spec::GZ_FNAME) && gz_p1(b) == Some(
                self.zstart@,
            ) && self.zstart@ <= u && spec::skip_zstr(b, self.zstart@) == spec::skip_zstr(b, u)
            &&& self.stage == G_COMMENT ==> spec::has(self.flg as nat, spec::GZ_FCOMMENT) && gz_p2(b)
                == Some(self.zstart@) && self.zstart@ <= u && spec::skip_zstr(b, self.zstart@)
                == spec::skip_zstr(b, u)
            &&& self.stage == G_HCRC ==> spec::has(self.flg as nat, spec::GZ_FHCRC) && gz_p3(b) == Some(
                self.zstart@,
            ) && self.hcount < 2 && u == self.zstart@ + self.hcount && self.hcrc == crc_from(
                0xffff_ffff,
                b.subrange(0, self.zstart@),
            ) && forall|i: int| 0 <= i < self.hcount ==> self.hbuf@[i] == b[self.zstart@ + i]
        } else {
            false
        }
    }

    #[verifier::opaque]
    spec fn body_ok(&self) -> bool {
        let base = self.base();
        let b = skip(self.full@, base);
        &&& shdr(self.format, self.full@, self.dict@) == Some((self.hlen@, self.d0@))
        &&& 0 <= self.hlen@ <= base
        &&& self.pending@ == self.full@.subrange(base, self.used@)
        &&& self.d0@ + self.delivered@ == self.pfx@ + self.window@.subrange(0, self.out_read as int)
        &&& lift(self.inf.rest(b, self.window@.subrange(0, self.inf.out_pos as int)), base, self.pfx@)
            == blocks(self.full@, 8 * self.hlen@, self.d0@)
        &&& self.pending@.len() > 0 ==> self.held_ok()
    }

    /// Bytes held back are ones the DEFLATE data still needs: it ends past
    /// the start of the last byte used.
    spec fn held_ok(&self) -> bool {
        past(blocks(self.full@, 8 * self.hlen@, self.d0@), 8 * (self.used@ - 1))
    }

    /// Work paid for but not yet done: the decoder's credit, the bits of
    /// the held-back bytes (read again on the next call), and one stop for
    /// more input while bytes are held.
    spec fn pot_in(&self) -> nat {
        credit(self.inf.fixed, self.inf.mode) + held_cost() * self.pending@.len() + if self.pending@.len() > 0 {
            hold_cost()
        } else {
            0
        }
    }

    /// `pot_in`, and the window: a slide is paid by the output decoded
    /// since the last one, and the run that fills the window by the slide.
    spec fn pot(&self) -> nat {
        if self.phase == P_FAILED {
            0
        } else {
            self.pot_in() + self.inf.out_pos as nat + (if self.inf.out_pos < self.window@.len() {
                turn_cost()
            } else {
                0
            }) + if self.inf.mode != MODE_DONE {
                turn_cost()
            } else {
                0
            }
        }
    }

    /// The decoder's work so far: loop iterations and bytes copied, counted
    /// by a ghost counter erased at compile time.
    pub closed spec fn steps(&self) -> nat {
        self.inf.work@
    }

    /// `steps`, plus work already paid for: what `inflate` bounds.
    pub closed spec fn work(&self) -> nat {
        self.inf.work@ + self.pot()
    }

    pub proof fn lemma_steps(&self)
        ensures
            self.steps() <= self.work(),
    {
    }

    /// With nothing held back, the paid-for work is at most a constant.
    proof fn lemma_pot_small(&self)
        requires
            self.wf(),
            self.pending@.len() == 0,
        ensures
            self.pot() <= start_cost(),
    {
        reveal(dfixed);
        assert(held_cost() * 0 == 0);
    }

    /// A valid stream still needs input after what has been used.
    spec fn short(&self) -> bool {
        spec_stream(self.wrapper, self.full@, self.dict@) matches Some((_, n)) ==> self.used@ < n
    }

    /// The header is not finished, so the stream needs more input.
    proof fn lemma_hdr_short(&self)
        requires
            self.wf(),
            self.ok@,
            self.phase == P_HEADER,
        ensures
            self.short(),
    {
        reveal(Stream::header_ok);
        let b = self.full@;
        let u = self.used@;
        let f = format_of(self.wrapper, b);
        lemma_sspec(self.wrapper, b, self.dict@);
        reveal(sspec);
        if let Some((h, d0)) = shdr(f, b, self.dict@) {
            lemma_gz_parts(b);
            assert(u < h) by {
                if self.stage == G_FIXED && self.hcount == 0 {
                    assert(u == 0);
                    crate::ilemmas::lemma_gzip_header_end(b);
                } else if self.format == Format::Zlib {
                    assert(f == Format::Zlib);
                } else {
                    assert(f == Format::Gzip);
                    assert(self.format == Format::Gzip);
                    if self.stage == G_NAME {
                        crate::ilemmas::lemma_skip_zstr_end(b, u);
                    } else if self.stage == G_COMMENT {
                        crate::ilemmas::lemma_skip_zstr_end(b, u);
                    }
                }
            }
            reveal(blocks);
            crate::slemmas::lemma_blocks_pos(b, 8 * h, d0);
            lemma_short_of(self.wrapper, b, self.dict@, h, d0, u);
        }
    }

    /// On a valid stream, the input used and the output delivered never
    /// pass the spec's: with `inflate`'s progress clause, a caller that
    /// keeps giving output space and the rest of the stream reaches `End`.
    pub proof fn lemma_bounds(&self)
        requires
            self.wf(),
            self.ok(),
        ensures
            spec_stream(self.wrapper_spec(), self.full(), self.dict()) matches Some((o, n)) ==> self.used() <= n
                && n <= self.full().len() && self.delivered().len() <= o.len(),
    {
        reveal(Stream::body_ok);
        reveal(Stream::trailer_ok);
        reveal(dinv);
        reveal(spec_trailer);
        let full = self.full@;
        lemma_sspec(self.wrapper, full, self.dict@);
        reveal(sspec);
        if let Some((o, n)) = spec_stream(self.wrapper, full, self.dict@) {
            if let Some((h, d0)) = shdr(format_of(self.wrapper, full), full, self.dict@) {
                reveal(blocks);
                crate::ilemmas::lemma_blocks_output(full, 8 * h, d0);
                if let Some((e, all)) = blocks(full, 8 * h, d0) {
                    assert((e + 7) / 8 <= full.len()) by {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(e + 7, 8 * full.len() as int + 7, 8);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(8 * full.len() as int + 7, 8, full.len() as int, 7);
                    }
                }
            }
            if self.phase == P_HEADER {
                self.lemma_hdr_short();
            } else if self.phase == P_DICT {
                assert(self.used@ == 6);
                let f = format_of(self.wrapper, full);
                assert(f == Format::Zlib);
                if let Some((h, d0)) = shdr(f, full, self.dict@) {
                    assert(h == 6);
                    reveal(blocks);
                    crate::slemmas::lemma_blocks_pos(full, 8 * h, d0);
                }
            } else if self.phase == P_BODY {
                let base = self.base();
                let b = skip(full, base);
                let w = self.window@.subrange(0, self.inf.out_pos as int);
                let s = *self.inf;
                assert(s.inv(self.pending@));
                crate::slemmas::lemma_rest_grows(s, b, w);
                if self.pending@.len() == 0 {
                    assert(s.in_pos == 0);
                    assert(s.pos() == 0);
                    lemma_rest_pos(s, b, w);
                }
                if let Some((e, all)) = blocks(full, 8 * self.hlen@, self.d0@) {
                    assert((e + 7) / 8 >= self.used@) by {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(8 * self.used@, e + 7, 8);
                        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(self.used@, 8);
                    }
                    let w2 = self.window@.subrange(0, self.out_read as int);
                    assert(w2.len() <= w.len());
                    assert(self.body_ok());
                    assert(self.d0@ + self.delivered@ == self.pfx@ + w2);
                    assert((self.d0@ + self.delivered@).len() == self.d0@.len() + self.delivered@.len());
                    assert((self.pfx@ + w2).len() == self.pfx@.len() + w2.len());
                    assert(self.used@ <= n);
                }
                assert(self.delivered@.len() <= o.len());
            } else if self.phase == P_TRAILER {
                self.lemma_trl_short();
                let all = self.d0@ + self.delivered@;
                assert(all.subrange(self.d0@.len() as int, all.len() as int) =~= self.delivered@);
                assert(self.delivered@.len() <= o.len());
            } else if self.phase == P_DONE {
            } else {
                assert(self.phase == P_FAILED);
            }
        }
    }

    /// The trailer is not finished, so the stream needs more input.
    proof fn lemma_trl_short(&self)
        requires
            self.wf(),
            self.ok@,
            self.phase == P_TRAILER,
        ensures
            self.short(),
    {
        reveal(Stream::trailer_ok);
        reveal(spec_trailer);
        lemma_sspec(self.wrapper, self.full@, self.dict@);
        reveal(sspec);
        let all = self.d0@ + self.delivered@;
        assert(all.subrange(0, self.d0@.len() as int) =~= self.d0@);
    }

    #[verifier::opaque]
    spec fn trailer_ok(&self) -> bool {
        let t = (self.eabs@ + 7) / 8;
        &&& shdr(self.format, self.full@, self.dict@) == Some((self.hlen@, self.d0@))
        &&& blocks(self.full@, 8 * self.hlen@, self.d0@) == Some(
            (self.eabs@, self.d0@ + self.delivered@),
        )
        &&& 0 <= t
        &&& self.used@ == t + self.tlen
        &&& forall|i: int| 0 <= i < self.tlen ==> self.tbuf@[i] == self.full@[t + i]
    }

    /// The facts about `full`, which hold while `ok()`.
    spec fn spec_ok(&self) -> bool {
        &&& 0 <= self.used@ <= self.full@.len()
        &&& self.phase != P_FAILED && !(self.phase == P_HEADER && self.wrapper == Wrapper::Auto && self.stage == G_FIXED
            && self.hcount == 0) ==> self.format
            == format_of(self.wrapper, self.full@)
        &&& self.sums_ok()
        &&& self.phase == P_HEADER ==> self.header_ok()
        &&& self.phase == P_BODY ==> self.body_ok()
        &&& self.phase == P_TRAILER ==> self.trailer_ok()
        &&& self.phase == P_DONE ==> spec_stream(self.wrapper, self.full@, self.dict@) == Some(
            (self.delivered@, self.used@),
        )
        &&& self.phase == P_FAILED ==> self.error == Error::BadData && spec_stream(
            self.wrapper,
            self.full@,
            self.dict@,
        ) is None
        &&& self.phase == P_DICT ==> zlib_cm_ok(self.full@) && zlib_fdict(self.full@) && self.full@.len() >= 6
            && self.used@ == 6 && self.dict_id as nat == spec::be32(self.full@, 2)
    }

    /// The stream's state is consistent.
    pub closed spec fn wf(&self) -> bool {
        &&& self.window@.len() == WINDOW + CHUNK
        &&& self.hbuf@.len() == 10 && self.tbuf@.len() == 8
        &&& self.fixed()
        &&& self.phase <= P_DICT
        &&& self.out_read <= self.inf.out_pos <= self.window@.len()
        &&& self.wrapper != Wrapper::Auto ==> self.format == format_of(self.wrapper, Seq::empty())
        &&& self.wrapper == Wrapper::Raw ==> self.phase != P_HEADER
        &&& self.phase == P_HEADER ==> self.hcount < 10 && self.stage <= G_HCRC
            && self.pending@ == Seq::<u8>::empty() && self.delivered@ == Seq::<u8>::empty() && (self.format
            == Format::Gzip || self.format == Format::Zlib) && (self.stage == G_EXTRA ==> self.xleft > 0) && (
            self.stage == G_FIXED && self.hcount == 0 ==> self.hcrc == 0xffff_ffff) && self.adler_a == 1
            && self.adler_b == 0 && self.crc == 0xffff_ffff && self.isize == 0 && (self.stage == G_XLEN
            || self.stage == G_HCRC ==> self.hcount < 2) && (self.format == Format::Zlib ==> self.hcount < 6
            && self.stage == G_FIXED) && self.dict@ == Seq::<u8>::empty()
        &&& self.phase == P_DICT ==> self.fed && self.format == Format::Zlib && self.pending@ == Seq::<u8>::empty()
            && self.delivered@ == Seq::<u8>::empty() && self.adler_a == 1 && self.adler_b == 0
        &&& !self.fed && self.phase == P_BODY ==> self.pending@ == Seq::<u8>::empty() && self.delivered@
            == Seq::<u8>::empty() && self.used@ == 0 && self.format == Format::Raw
        &&& self.phase == P_BODY ==> self.dinv(self.pending@) && self.inf.in_pos
            <= self.pending@.len() && (self.inf.mode == MODE_DONE ==> self.inf.cnt < 8)
        &&& self.phase == P_TRAILER ==> self.tlen < trailer_len(self.format)
        &&& self.adler_a < 65521 && self.adler_b < 65521
        &&& self.ok@ ==> self.spec_ok()
    }

    pub fn new(wrapper: Wrapper, Ghost(full): Ghost<Seq<u8>>) -> (r: Stream)
        ensures
            r.steps() == 0,
            r.work() <= start_cost(),
            r.wf(),
            r.ok(),
            r.full() == full,
            r.used() == 0,
            r.delivered() == Seq::<u8>::empty(),
            r.dict() == Seq::<u8>::empty(),
            r.wrapper_spec() == wrapper,
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        let mut s = Stream {
            inf: Inflater::new(),
            wrapper,
            format: Format::Raw,
            phase: P_HEADER,
            error: Error::BadData,
            stage: G_FIXED,
            hcount: 0,
            flg: 0,
            xleft: 0,
            hbuf: vec![0u8; 10],
            hcrc: 0xffff_ffff,
            pending: Vec::new(),
            scratch: Vec::new(),
            window: vec![0u8; WINDOW + CHUNK],
            out_read: 0,
            adler_a: 1,
            adler_b: 0,
            crc: 0xffff_ffff,
            isize: 0,
            tbuf: vec![0u8; 8],
            tlen: 0,
            dict_id: 0,
            fed: false,
            full: Ghost(full),
            dict: Ghost(Seq::empty()),
            d0: Ghost(Seq::empty()),
            ok: Ghost(true),
            used: Ghost(0),
            delivered: Ghost(Seq::empty()),
            pfx: Ghost(Seq::empty()),
            hlen: Ghost(0),
            eabs: Ghost(0),
            zstart: Ghost(0),
        };
        s.start(wrapper);
        proof {
            s.lemma_pot_small();
        }
        s
    }

    /// Starts over with a new stream `full`, keeping the buffers.
    pub fn reset(&mut self, wrapper: Wrapper, Ghost(full): Ghost<Seq<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).steps() == old(self).steps(),
            final(self).work() <= old(self).work() + start_cost(),
            final(self).wf(),
            final(self).ok(),
            final(self).full() == full,
            final(self).used() == 0,
            final(self).delivered() == Seq::<u8>::empty(),
            final(self).dict() == Seq::<u8>::empty(),
            final(self).wrapper_spec() == wrapper,
    {
        self.full = Ghost(full);
        self.ok = Ghost(true);
        self.used = Ghost(0);
        self.delivered = Ghost(Seq::empty());
        self.pfx = Ghost(Seq::empty());
        self.pending.clear();
        self.start(wrapper);
        proof {
            self.lemma_pot_small();
        }
    }

    fn start(&mut self, wrapper: Wrapper)
        requires
            old(self).window@.len() == WINDOW + CHUNK,
            old(self).hbuf@.len() == 10 && old(self).tbuf@.len() == 8,
            old(self).fixed(),
            old(self).ok@,
            old(self).used@ == 0,
            old(self).delivered@ == Seq::<u8>::empty(),
            old(self).pfx@ == Seq::<u8>::empty(),
            old(self).pending@ == Seq::<u8>::empty(),
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).wf(),
            final(self).ok@,
            final(self).full@ == old(self).full@,
            final(self).used@ == 0,
            final(self).delivered@ == Seq::<u8>::empty(),
            final(self).dict@ == Seq::<u8>::empty(),
            final(self).wrapper == wrapper,
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::header_ok);
        }
        self.wrapper = wrapper;
        self.dict = Ghost(Seq::empty());
        self.d0 = Ghost(Seq::empty());
        self.dict_id = 0;
        self.fed = false;
        self.format = match wrapper {
            Wrapper::Raw => Format::Raw,
            Wrapper::Gzip => Format::Gzip,
            _ => Format::Zlib,
        };
        self.phase = P_HEADER;
        self.stage = G_FIXED;
        self.hcount = 0;
        self.hcrc = 0xffff_ffff;
        self.adler_a = 1;
        self.adler_b = 0;
        self.crc = 0xffff_ffff;
        self.isize = 0;
        self.tlen = 0;
        self.out_read = 0;
        self.inf.reset(0);
        proof {
            assert(self.full@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        if wrapper == Wrapper::Raw {
            self.begin_body(no_bytes());
        }
    }

    /// The header ended at `used`: start the DEFLATE data, which continues
    /// the output `d` (a preset dictionary, or empty).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn begin_body(&mut self, d: &[u8])
        requires
            old(self).window@.len() == WINDOW + CHUNK,
            old(self).hbuf@.len() == 10 && old(self).tbuf@.len() == 8,
            old(self).fixed(),
            old(self).pending@ == Seq::<u8>::empty(),
            old(self).adler_a < 65521 && old(self).adler_b < 65521,
            old(self).wrapper != Wrapper::Auto ==> old(self).format == format_of(old(self).wrapper, Seq::empty()),
            old(self).fed || (old(self).used@ == 0 && old(self).delivered@ == Seq::<u8>::empty()
                && old(self).format == Format::Raw),
            old(self).ok@ ==> {
                &&& 0 <= old(self).used@ <= old(self).full@.len()
                &&& old(self).format == format_of(old(self).wrapper, old(self).full@)
                &&& shdr(old(self).format, old(self).full@, old(self).dict@) == Some((old(self).used@, d@))
                &&& old(self).delivered@ == Seq::<u8>::empty()
                &&& old(self).sums_ok()
            },
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).wf(),
            final(self).phase == P_BODY,
            final(self).ok@ == old(self).ok@,
            final(self).full@ == old(self).full@,
            final(self).used@ == old(self).used@,
            final(self).delivered@ == old(self).delivered@,
            final(self).dict@ == old(self).dict@,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).format == old(self).format,
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::body_ok);
        }
        self.inf.reset(0);
        let n = d.len();
        let k = if n < WINDOW {
            n
        } else {
            WINDOW
        };
        copy_in(self.window.as_mut_slice(), 0, d, n - k, k);
        self.inf.out_pos = k;
        self.out_read = k;
        self.phase = P_BODY;
        self.hlen = Ghost(self.used@);
        let ghost pfx = d@.subrange(0, n - k);
        self.pfx = Ghost(pfx);
        self.d0 = Ghost(d@);
        proof {
            let h = self.used@;
            let w = self.window@.subrange(0, k as int);
            assert(w =~= d@.subrange(n - k, n as int));
            assert(d@ =~= pfx + w);
            if self.ok@ {
                let s = *self.inf;
                lemma_rest_start(s, skip(self.full@, h), w);
                lemma_shift_blocks(self.full@, h, 0, w);
                assert(self.full@.subrange(h, h) =~= Seq::<u8>::empty());
                let x = spec::inflate_blocks(self.full@, 8 * h, w);
                assert(lift(sh(x, h), h, pfx) == pre(pfx, x));
                if n > k {
                    lemma_win_blocks(self.full@, 8 * h, pfx, w);
                } else {
                    assert(pfx =~= Seq::<u8>::empty());
                    assert(pfx + w =~= w);
                    if let Some((e, o)) = x {
                        assert(pfx + o =~= o);
                    }
                }
                assert(self.d0@ + self.delivered@ =~= pfx + w);
                reveal(blocks);
                assert(lift(s.rest(skip(self.full@, h), w), h, pfx) == blocks(self.full@, 8 * h, d@));
            }
        }
    }

    /// The input the decoder works on during a call: `pending`, then the
    /// caller's input from `ip`.
    spec fn y(&self, inp: Seq<u8>, ip: int) -> Seq<u8> {
        self.pending@ + inp.subrange(ip, inp.len() as int)
    }

    /// The state between decoder runs during a call with input `inp`, of
    /// which `ip` bytes are used.
    spec fn mid(&self, inp: Seq<u8>, ip: int) -> bool {
        let y = self.y(inp, ip);
        &&& 0 <= ip <= inp.len()
        &&& self.phase == P_BODY
        &&& self.fed
        &&& self.window@.len() == WINDOW + CHUNK
        &&& self.hbuf@.len() == 10 && self.tbuf@.len() == 8
        &&& self.fixed()
        &&& self.out_read <= self.inf.out_pos <= self.window@.len()
        &&& self.wrapper != Wrapper::Auto ==> self.format == format_of(self.wrapper, Seq::empty())
        &&& self.adler_a < 65521 && self.adler_b < 65521
        &&& self.dinv(y)
        &&& self.inf.in_pos <= self.pending@.len() || (self.pending@.len() == 0 && self.inf.in_pos == 1
            && ip < inp.len())
        &&& self.ok@ ==> {
            &&& 0 <= self.used@
            &&& self.used@ + (inp.len() - ip) <= self.full@.len()
            &&& inp.subrange(ip, inp.len() as int) == self.full@.subrange(
                self.used@,
                self.used@ + (inp.len() - ip),
            )
            &&& self.format == format_of(self.wrapper, self.full@)
            &&& self.sums_ok()
            &&& self.body_ok()
        }
    }

    proof fn lemma_mid_wf(&self, inp: Seq<u8>, ip: int)
        requires
            self.mid(inp, ip),
            self.inf.in_pos <= self.pending@.len(),
            self.inf.mode == MODE_DONE ==> self.inf.cnt < 8,
        ensures
            self.wf(),
    {
        reveal(dfixed);
        reveal(dinv);
        reveal(Stream::body_ok);
        let y = self.y(inp, ip);
        assert(y.subrange(0, self.pending@.len() as int) =~= self.pending@);
        lemma_inv_prefix(*self.inf, self.pending@, y);
    }

    proof fn lemma_wf_mid(&self, inp: Seq<u8>)
        requires
            self.wf(),
            self.phase == P_BODY,
            self.fed,
            self.ok@ ==> self.used@ + inp.len() <= self.full@.len() && inp == self.full@.subrange(
                self.used@,
                self.used@ + inp.len(),
            ),
        ensures
            self.mid(inp, 0),
    {
        reveal(dfixed);
        reveal(dinv);
        reveal(Stream::body_ok);
        let y = self.y(inp, 0);
        assert(inp.subrange(0, inp.len() as int) =~= inp);
        assert(prefix(self.pending@, y)) by {
            assert(y.subrange(0, self.pending@.len() as int) =~= self.pending@);
        }
        lemma_inv_prefix(*self.inf, self.pending@, y);
    }

    /// The decoder's whole input `y` is the start of what is left of
    /// `full`, so its state is consistent with that.
    proof fn lemma_mid_full(&self, inp: Seq<u8>, ip: int)
        requires
            self.mid(inp, ip),
            self.ok@,
        ensures
            prefix(self.y(inp, ip), skip(self.full@, self.base())),
            self.inf.inv(skip(self.full@, self.base())),
            self.base() >= 0,
    {
        reveal(dfixed);
        reveal(dinv);
        reveal(Stream::body_ok);
        let y = self.y(inp, ip);
        let b = skip(self.full@, self.base());
        let u = self.used@;
        let n = inp.len() - ip;
        assert(y =~= b.subrange(0, y.len() as int)) by {
            assert forall|i: int| 0 <= i < y.len() implies y[i] == b[i] by {
                if i < self.pending@.len() {
                    assert(self.pending@[i] == self.full@.subrange(self.base(), u)[i]);
                } else {
                    assert(inp.subrange(ip, inp.len() as int)[i - self.pending@.len()]
                        == self.full@.subrange(u, u + n)[i - self.pending@.len()]);
                }
            }
        }
        lemma_inv_prefix(*self.inf, y, b);
    }

    /// Copies decoded output to `output[*op..]`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn deliver(&mut self, output: &mut [u8], op: &mut usize)
        requires
            *old(op) <= old(output)@.len(),
            old(self).window@.len() == WINDOW + CHUNK,
            old(self).hbuf@.len() == 10 && old(self).tbuf@.len() == 8,
            old(self).out_read <= old(self).inf.out_pos <= old(self).window@.len(),
            old(self).adler_a < 65521 && old(self).adler_b < 65521,
            old(self).ok@ ==> old(self).sums_ok() && old(self).d0@ + old(self).delivered@ == old(self).pfx@
                + old(self).window@.subrange(0, old(self).out_read as int),
        ensures
            final(self).inf == old(self).inf,
            final(self).window == old(self).window,
            final(self).pending == old(self).pending,
            final(self).phase == old(self).phase,
            final(self).format == old(self).format,
            final(self).wrapper == old(self).wrapper,
            final(self).pfx == old(self).pfx,
            final(self).full == old(self).full,
            final(self).hbuf == old(self).hbuf && final(self).tbuf == old(self).tbuf,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).ok == old(self).ok,
            final(self).used == old(self).used,
            final(self).hlen == old(self).hlen,
            final(self).adler_a < 65521 && final(self).adler_b < 65521,
            old(self).out_read <= final(self).out_read <= final(self).inf.out_pos,
            final(output)@.len() == old(output)@.len(),
            final(output)@.subrange(0, *old(op) as int) == old(output)@.subrange(0, *old(op) as int),
            *old(op) <= *final(op) <= final(output)@.len(),
            final(self).delivered@ == old(self).delivered@ + final(output)@.subrange(
                *old(op) as int,
                *final(op) as int,
            ),
            final(self).out_read == final(self).inf.out_pos || *final(op) == final(output)@.len(),
            *final(op) - *old(op) == final(self).out_read - old(self).out_read,
            old(self).out_read < old(self).inf.out_pos && *old(op) < old(output)@.len() ==> *final(op) > *old(op),
            final(self).out_read > old(self).out_read || final(self).out_read == old(self).inf.out_pos
                || *old(op) == old(output)@.len(),
            final(self).ok@ ==> final(self).sums_ok() && final(self).d0@ + final(self).delivered@ == final(self).pfx@
                + final(self).window@.subrange(0, final(self).out_read as int),
    {
        let avail = self.inf.out_pos - self.out_read;
        let room = output.len() - *op;
        let n = if avail < room {
            avail
        } else {
            room
        };
        let ghost o0 = output@;
        let ghost d0 = self.delivered@;
        let chunk = vstd::slice::slice_subrange(self.window.as_slice(), self.out_read, self.out_read + n);
        copy_in(output, *op, self.window.as_slice(), self.out_read, n);
        if self.format == Format::Zlib {
            let (a, b) = verilith_core::checksum::cpu::adler32_update(self.adler_a, self.adler_b, chunk);
            proof {
                lemma_adler_closed(self.adler_a as nat, self.adler_b as nat, chunk@);
                if self.ok@ {
                    lemma_adler_append(1, 0, d0, chunk@);
                }
            }
            self.adler_a = a;
            self.adler_b = b;
        } else if self.format == Format::Gzip {
            self.crc = verilith_core::checksum::cpu::crc32_update(self.crc, chunk);
            proof {
                if self.ok@ {
                    lemma_crc_append(0xffff_ffff, d0, chunk@);
                }
                if self.ok@ {
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(d0.len() as int, n as int, 0x1_0000_0000);
                    vstd::arithmetic::div_mod::lemma_mod_twice(n as int, 0x1_0000_0000);
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(self.isize as int, n as int, 0x1_0000_0000);
                    vstd::arithmetic::div_mod::lemma_small_mod(self.isize as nat, 0x1_0000_0000);
                }
            }
            self.isize = ((self.isize as u64 + n as u64) % 0x1_0000_0000) as u32;
        }
        self.delivered = Ghost(self.delivered@ + chunk@);
        proof {
            assert(output@.subrange(*op as int, *op + n) =~= chunk@);
            assert(output@.subrange(0, *op as int) =~= o0.subrange(0, *op as int));
            if self.ok@ {
                assert(self.window@.subrange(0, self.out_read + n) =~= self.window@.subrange(
                    0,
                    self.out_read as int,
                ) + chunk@);
                assert(self.d0@ + (d0 + chunk@) =~= (self.d0@ + d0) + chunk@);
                assert(self.d0@ + self.delivered@ =~= self.pfx@ + self.window@.subrange(0, self.out_read + n));
            }
        }
        self.out_read = self.out_read + n;
        *op = *op + n;
    }

    /// Moves the last `WINDOW` bytes of output to the front of the window.
    fn slide(&mut self, Ghost(inp): Ghost<Seq<u8>>, Ghost(ip): Ghost<int>)
        requires
            old(self).mid(inp, ip),
            old(self).out_read == old(self).inf.out_pos,
            old(self).inf.out_pos == old(self).window@.len(),
        ensures
            final(self).mid(inp, ip),
            final(self).inf.out_pos == WINDOW,
            final(self).out_read == WINDOW,
            final(self).inf.mode == old(self).inf.mode,
            final(self).inf.cnt == old(self).inf.cnt,
            final(self).inf.in_pos == old(self).inf.in_pos,
            final(self).inf.work == old(self).inf.work,
            final(self).inf.fixed == old(self).inf.fixed,
            final(self).pending == old(self).pending,
            final(self).phase == old(self).phase,
            final(self).delivered == old(self).delivered,
            final(self).used == old(self).used,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).format == old(self).format,
            final(self).wrapper == old(self).wrapper,
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::body_ok);
        }
        let ghost w = self.window@;
        let ghost s0 = *self.inf;
        copy_to_front(self.window.as_mut_slice(), CHUNK, WINDOW);
        self.inf.out_pos = WINDOW;
        self.out_read = WINDOW;
        let ghost p2 = w.subrange(0, CHUNK as int);
        let ghost w2 = w.subrange(CHUNK as int, w.len() as int);
        self.pfx = Ghost(self.pfx@ + p2);
        proof {
            assert(self.window@.subrange(0, WINDOW as int) =~= w2);
            assert(w =~= p2 + w2);
            assert(self.y(inp, ip) == old(self).y(inp, ip));
            assert(w.subrange(0, w.len() as int) =~= w);
            assert(self.inf.fixed_ok());
            assert(self.inf.inv(self.y(inp, ip)));
            if self.ok@ {
                let b = skip(self.full@, self.base());
                lemma_slide(s0, *self.inf, b, p2, w2, old(self).pfx@, self.base());
                assert(self.d0@ + self.delivered@ =~= self.pfx@ + self.window@.subrange(0, WINDOW as int));
                assert(self.sums_ok());
                assert(self.body_ok());
            }
        }
    }

    /// Runs the decoder once on `pending` and the input from `ip`, then
    /// keeps what it has not used. Returns its status and the new `ip`.
    #[verifier::spinoff_prover]
    // Below 1431; see vwasm's `execute` for why (Verus panics reading Z3's
    // resource count once it passes 2^32).
    #[verifier::rlimit(1400)]
    fn run_once(&mut self, inp: &[u8], ip: usize) -> (r: (Status, usize))
        requires
            old(self).mid(inp@, ip as int),
            old(self).out_read == old(self).inf.out_pos,
            old(self).inf.out_pos < old(self).window@.len(),
        ensures
            r.0 != Status::BadData ==> final(self).mid(inp@, r.1 as int),
            final(self).window@.len() == WINDOW + CHUNK,
            final(self).fixed(),
            final(self).out_read <= final(self).inf.out_pos <= final(self).window@.len(),
            final(self).adler_a < 65521 && final(self).adler_b < 65521,
            ip <= r.1 <= inp@.len(),
            r.0 != Status::BadData ==> final(self).inf.cnt < 8,
            final(self).out_read == old(self).out_read,
            final(self).adler_a == old(self).adler_a && final(self).adler_b == old(self).adler_b,
            final(self).crc == old(self).crc && final(self).isize == old(self).isize,
            final(self).delivered == old(self).delivered,
            final(self).full == old(self).full,
            final(self).hbuf == old(self).hbuf && final(self).tbuf == old(self).tbuf,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).ok == old(self).ok,
            final(self).phase == old(self).phase,
            final(self).format == old(self).format,
            final(self).wrapper == old(self).wrapper,
            final(self).used@ == old(self).used@ + (r.1 - ip),
            r.0 == Status::NeedOutput ==> final(self).inf.out_pos == final(self).window@.len(),
            r.0 == Status::Done ==> final(self).inf.mode == MODE_DONE,
            r.0 == Status::Truncated ==> r.1 == inp@.len() || r.1 > ip || (old(self).pending@.len() > 0
                && final(self).pending@.len() == 0),
            r.0 == Status::BadData ==> (final(self).ok@ ==> spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None),
            r.0 != Status::BadData ==> final(self).inf.in_pos == (if final(self).inf.cnt > 0 { 1usize } else { 0usize }),
            r.0 == Status::Truncated && final(self).ok@ ==> final(self).short(),
            r.0 == Status::BadData ==> final(self).inf.work@ <= old(self).inf.work@ + old(self).pot_in() + held_cost() * (
                inp@.len() - ip) + (final(self).inf.out_pos - old(self).inf.out_pos) + header_cost() + body_cost(),
            final(self).inf.out_pos >= old(self).inf.out_pos,
            r.0 != Status::BadData ==> final(self).inf.work@ + final(self).pot_in() <= old(self).inf.work@ + old(
                self,
            ).pot_in() + in_cost() * (r.1 - ip) + (final(self).inf.out_pos - old(self).inf.out_pos) + if r.0
                == Status::Truncated {
                if r.1 == inp@.len() {
                    exit_cost()
                } else {
                    0
                }
            } else {
                turn_cost()
            },
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::body_ok);
        }
        let p = self.pending.len();
        let rem = inp.len() - ip;
        let bridge = p > 0;
        let k = if !bridge {
            rem
        } else if rem < BRIDGE {
            rem
        } else {
            BRIDGE
        };
        if bridge {
            self.scratch.clear();
            extend(&mut self.scratch, self.pending.as_slice());
            extend(&mut self.scratch, vstd::slice::slice_subrange(inp, ip, ip + k));
        }
        let ghost y = self.y(inp@, ip as int);
        let ghost xbase = self.base();
        let ghost x: Seq<u8> = if bridge {
            self.scratch@
        } else {
            inp@.subrange(ip as int, inp@.len() as int)
        };
        let xlen = if bridge {
            self.scratch.len()
        } else {
            k
        };
        let ghost bx = if self.ok@ {
            skip(self.full@, xbase)
        } else {
            x
        };
        let ghost s0 = *self.inf;
        let ghost w0 = self.window@.subrange(0, self.inf.out_pos as int);
        proof {
            assert(x.len() == xlen);
            assert(x =~= y.subrange(0, xlen as int));
            assert(prefix(x, y));
            lemma_inv_prefix(s0, x, y);
            if self.ok@ {
                self.lemma_mid_full(inp@, ip as int);
                lemma_prefix_trans(x, y, bx);
            } else {
                assert(x.subrange(0, x.len() as int) =~= x);
            }
            assert(prefix(x, bx));
            lemma_inv_prefix(s0, x, bx);
        }
        let st = if bridge {
            crate::simd::run(&mut self.inf, self.scratch.as_slice(), Ghost(bx), self.window.as_mut_slice())
        } else {
            crate::simd::run(
                &mut self.inf,
                vstd::slice::slice_subrange(inp, ip, inp.len()),
                Ghost(bx),
                self.window.as_mut_slice(),
            )
        };
        if st == Status::BadData {
            proof {
                if self.ok@ {
                    let r = s0.rest(bx, w0);
                    assert(r is None);
                    lemma_sspec(self.wrapper, self.full@, self.dict@);
                    reveal(sspec);
                }
            }
            assert(self.inf.work@ <= old(self).inf.work@ + old(self).pot_in() + held_cost() * (inp@.len() - ip) + (
                self.inf.out_pos - old(self).inf.out_pos) + header_cost() + body_cost()) by {
                assert(x.len() <= p + rem);
                assert(bit_cost() * (crate::spec::nbits(x) - s0.pos()) <= held_cost() * p + held_cost() * rem) by (nonlinear_arith)
                    requires
                        s0.pos() >= 0,
                        crate::spec::nbits(x) == 8 * x.len(),
                        x.len() <= p + rem,
                        bit_cost() == 1200,
                        held_cost() == 9600,
                ;
            }
            return (st, ip);
        }
        let ghost s2a = *self.inf;
        self.inf.drop_whole_bytes(Ghost(bx));
        let ghost s2 = *self.inf;
        let c = if self.inf.cnt > 0 {
            self.inf.in_pos - 1
        } else {
            self.inf.in_pos
        };
        let pre = if bridge {
            p
        } else {
            0
        };
        let absorb = st == Status::Truncated && (k == rem || c < pre);
        let e = if absorb {
            xlen
        } else if c >= pre {
            c
        } else {
            p
        };
        let nip = if absorb {
            ip + k
        } else if c >= pre {
            ip + (c - pre)
        } else {
            ip
        };
        let mut np: Vec<u8> = Vec::new();
        if bridge {
            extend(&mut np, vstd::slice::slice_subrange(self.scratch.as_slice(), c, e));
        } else {
            extend(&mut np, vstd::slice::slice_subrange(inp, ip + c, ip + e));
        }
        let ghost pd = self.pending@;
        proof {
            assert(np@ =~= x.subrange(c as int, e as int));
            assert(x.subrange(c as int, e as int) =~= y.subrange(c as int, e as int));
            lemma_keep_bytes(pd, inp@, ip as int, c as int, e as int, nip as int);
            if self.ok@ {
                lemma_y_full(pd, inp@, ip as int, self.full@, xbase, self.used@, c as int, e as int);
            }
        }
        self.pending = np;
        self.inf.in_pos = self.inf.in_pos - c;
        self.used = Ghost(self.used@ + (nip - ip));
        proof {
            if self.ok@ && self.pending@.len() > 0 {
                assert(old(self).body_ok());
                if absorb {
                    assert(past(s0.rest(bx, w0), crate::spec::nbits(x)));
                    assert(x.len() == xlen);
                    assert(xbase + xlen == self.used@);
                } else {
                    assert(c < pre);
                    assert(self.used@ == old(self).used@);
                    assert(old(self).pending@.len() > 0);
                    assert(old(self).held_ok());
                }
                assert(self.held_ok());
            }
            if self.ok@ && st == Status::Truncated {
                assert(old(self).body_ok());
                assert(past(s0.rest(bx, w0), crate::spec::nbits(x)));
                assert(x.len() == xlen);
                assert(self.used@ <= xbase + xlen);
                assert(past(blocks(self.full@, 8 * self.hlen@, self.d0@), 8 * self.used@));
                lemma_short_of(self.wrapper, self.full@, self.dict@, self.hlen@, self.d0@, self.used@);
            }
        }
        assert(self.inf.work@ + self.pot_in() <= old(self).inf.work@ + old(self).pot_in() + in_cost() * (nip - ip) + (
            self.inf.out_pos - old(self).inf.out_pos) + if st == Status::Truncated {
            if nip == inp@.len() {
                exit_cost()
            } else {
                0
            }
        } else {
            turn_cost()
        }) by {
            let w0 = s0.work@ + credit(s0.fixed, s0.mode);
            let w1 = s2a.work@ + credit(s2a.fixed, s2a.mode);
            assert(s2a.pos() <= 8 * c + 8);
            assert(self.inf.work@ == s2a.work@);
            assert(self.pending@.len() == e - c);
            lemma_once_cost(w0 as int, w1 as int, p as int, k as int, rem as int, c as int, e as int, nip - ip, s0.pos(), s2a.pos(),
                s2a.out_pos - s0.out_pos, st == Status::Truncated, absorb, nip == inp@.len());
        }
        proof {
            assert(moved(*self.inf, s2, c as int));
            assert(self.window@.subrange(0, self.out_read as int) =~= old(self).window@.subrange(
                0,
                self.out_read as int,
            ));
            self.lemma_run_post(*old(self), inp@, ip as int, nip as int, c as int, x, bx, s2a, s2, st == Status::Done);
        }
        (st, nip)
    }

    /// After a decoder run that did not fail, `run_once`'s state is again
    /// consistent: the proof, kept apart from `run_once` for speed.
    proof fn lemma_run_post(
        &self,
        o: Stream,
        inp: Seq<u8>,
        ip: int,
        nip: int,
        c: int,
        x: Seq<u8>,
        bx: Seq<u8>,
        s2a: Inflater,
        s2: Inflater,
        done: bool,
    )
        requires
            o.mid(inp, ip),
            self.phase == o.phase,
            self.window@.len() == o.window@.len(),
            self.hbuf == o.hbuf && self.tbuf == o.tbuf,
            self.out_read == o.out_read,
            self.adler_a == o.adler_a && self.adler_b == o.adler_b && self.crc == o.crc && self.isize == o.isize,
            self.delivered == o.delivered && self.full == o.full && self.d0 == o.d0 && self.dict == o.dict,
            self.ok == o.ok && self.format == o.format && self.wrapper == o.wrapper && self.fed == o.fed,
            self.hlen == o.hlen && self.pfx == o.pfx,
            self.out_read <= self.inf.out_pos <= self.window@.len(),
            self.inf.fixed_ok(),
            self.window@.subrange(0, self.out_read as int) == o.window@.subrange(0, self.out_read as int),
            o.out_read == o.inf.out_pos,
            x == o.y(inp, ip).subrange(0, x.len() as int),
            x.len() <= o.y(inp, ip).len(),
            o.ok@ ==> bx == skip(o.full@, o.base()),
            !o.ok@ ==> bx == x,
            s2a.inv(bx),
            s2a.out_pos == self.inf.out_pos,
            done ==> s2a.mode == MODE_DONE && o.inf.rest(bx, o.window@.subrange(0, o.inf.out_pos as int)) == Some(
                (s2a.pos(), self.window@.subrange(0, self.inf.out_pos as int)),
            ),
            !done ==> s2a.rest(bx, self.window@.subrange(0, self.inf.out_pos as int)) == o.inf.rest(
                bx,
                o.window@.subrange(0, o.inf.out_pos as int),
            ),
            s2.pos() == s2a.pos(),
            s2.same_but_bits(&s2a),
            s2.inv(bx),
            s2.in_pos <= x.len(),
            moved(*self.inf, s2, c),
            s2.cnt < 8,
            c == s2.in_pos - (if s2.cnt > 0 { 1int } else { 0int }),
            ip <= nip <= inp.len(),
            self.used@ == o.used@ + (nip - ip),
            self.pending@ + inp.subrange(nip, inp.len() as int) == skip(o.y(inp, ip), c),
            o.ok@ ==> self.pending@ == o.full@.subrange(o.base() + c, self.used@),
            self.pending@.len() == o.pending@.len() + (nip - ip) - c,
            self.inf.in_pos <= self.pending@.len() || (self.pending@.len() == 0 && self.inf.in_pos == 1 && nip
                < inp.len()),
            o.ok@ && self.pending@.len() > 0 ==> self.held_ok(),
        ensures
            self.mid(inp, nip),
    {
        reveal(Stream::body_ok);
        reveal(dfixed);
        reveal(dinv);
        let y = o.y(inp, ip);
        let s1 = *self.inf;
        let xbase = o.base();
        lemma_inv_prefix(s2, x, y);
        if o.ok@ {
            o.lemma_mid_full(inp, ip);
            lemma_inv_prefix(s2, y, bx);
        }
        assert(s2.inv(y));
        lemma_shift_inv(s1, s2, y, c);
        assert(self.y(inp, nip) == skip(y, c));
        if o.ok@ {
            let w1 = self.window@.subrange(0, self.inf.out_pos as int);
            lemma_keep(s1, s2, s2a, done, self.full@, xbase, c, w1, self.pfx@);
            assert(self.base() == xbase + c);
            lemma_tail(inp, ip, nip, self.full@, o.used@);
        }
    }

    /// The parts of `wf` every phase needs.
    spec fn base_ok(&self) -> bool {
        &&& self.window@.len() == WINDOW + CHUNK
        &&& self.hbuf@.len() == 10 && self.tbuf@.len() == 8
        &&& self.fixed()
        &&& self.out_read <= self.inf.out_pos <= self.window@.len()
        &&& self.wrapper != Wrapper::Auto ==> self.format == format_of(self.wrapper, Seq::empty())
        &&& self.wrapper == Wrapper::Raw ==> self.phase != P_HEADER
        &&& self.adler_a < 65521 && self.adler_b < 65521
        &&& self.ok@ ==> 0 <= self.used@ <= self.full@.len() && self.sums_ok()
    }

    /// The header so far is valid and ends at `used`: the next stage of a
    /// gzip header after `from` starts there.
    spec fn gz_done(&self, from: u8) -> bool {
        let b = self.full@;
        let u = self.used@;
        &&& gz_fixed_ok(b)
        &&& self.flg == b[3]
        &&& self.hcrc == crc_from(0xffff_ffff, b.subrange(0, u))
        &&& from == G_FIXED ==> u == 10
        &&& from == G_EXTRA ==> gz_p1(b) == Some(u)
        &&& from == G_NAME ==> gz_p2(b) == Some(u)
        &&& from == G_COMMENT ==> gz_p3(b) == Some(u)
    }

    /// Moves on from a finished gzip header stage.
    fn next_stage(&mut self, from: u8)
        requires
            old(self).base_ok(),
            old(self).phase == P_HEADER,
            old(self).fed,
            old(self).dict@ == Seq::<u8>::empty(),
            old(self).format == Format::Gzip,
            old(self).pending@ == Seq::<u8>::empty(),
            old(self).delivered@ == Seq::<u8>::empty(),
            old(self).adler_a == 1 && old(self).adler_b == 0 && old(self).crc == 0xffff_ffff && old(self).isize == 0,
            from == G_FIXED || from == G_EXTRA || from == G_NAME || from == G_COMMENT,
            old(self).ok@ ==> old(self).gz_done(from) && old(self).format == format_of(
                old(self).wrapper,
                old(self).full@,
            ),
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).wf(),
            final(self).phase == P_HEADER || final(self).phase == P_BODY,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).used == old(self).used,
            final(self).delivered == old(self).delivered,
            final(self).wrapper == old(self).wrapper,
            final(self).format == old(self).format,
    {
        proof {
            reveal(Stream::header_ok);
        }
        let ghost b = self.full@;
        let ghost u = self.used@;
        self.hcount = 0;
        self.zstart = Ghost(u);
        let mut s = from;
        if s == G_FIXED {
            if flag(self.flg, 4) {
                self.stage = G_XLEN;
                return;
            }
            s = G_EXTRA;
        }
        if s == G_EXTRA {
            if flag(self.flg, 8) {
                self.stage = G_NAME;
                return;
            }
            s = G_NAME;
        }
        if s == G_NAME {
            if flag(self.flg, 16) {
                self.stage = G_COMMENT;
                return;
            }
        }
        if flag(self.flg, 2) {
            self.stage = G_HCRC;
            return;
        }
        proof {
            if self.ok@ {
                lemma_gzip_header(b);
            }
        }
        self.begin_body(no_bytes());
    }

    /// One byte's CRC.
    fn crc1(c: u32, x: u8) -> (r: u32)
        ensures
            r == crc_from(c, seq![x]),
    {
        let a = [x];
        proof {
            assert(a@ =~= seq![x]);
        }
        verilith_core::checksum::cpu::crc32_update(c, a.as_slice())
    }

    /// One byte of a zlib header.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    fn zlib_byte(&mut self, x: u8) -> (r: Result<(), Error>)
        requires
            old(self).wf(),
            old(self).phase == P_HEADER,
            old(self).fed,
            old(self).format == Format::Zlib,
            old(self).ok@ ==> old(self).used@ < old(self).full@.len() && old(self).full@[old(self).used@] == x
                && old(self).format == format_of(old(self).wrapper, old(self).full@),
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).delivered == old(self).delivered,
            match r {
                Ok(()) => {
                    &&& final(self).wf()
                    &&& final(self).used@ == old(self).used@ + 1
                    &&& final(self).phase == P_HEADER || final(self).phase == P_BODY || final(self).phase == P_DICT
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                },
            },
    {
        proof {
            reveal(Stream::header_ok);
        }
        let ghost b = self.full@;
        let ghost u = self.used@;
        proof {
            if self.ok@ {
                assert(b.subrange(0, u + 1) =~= b.subrange(0, u) + seq![x]);
                lemma_crc_append(0xffff_ffff, b.subrange(0, u), seq![x]);
            }
        }
        self.hbuf.set(self.hcount, x);
        self.hcount = self.hcount + 1;
        self.used = Ghost(u + 1);
        if self.hcount == 2 {
            let cmf = self.hbuf[0];
            let flg = self.hbuf[1];
            proof {
                if self.ok@ {
                    assert(cmf == b[0] && flg == b[1]);
                }
            }
            if !zlib_cm(cmf, flg) {
                proof {
                    if self.ok@ {
                        assert(zlib_cm_ok(self.full@) == zlib_cm_ok(seq![cmf, flg]));
                        lemma_sspec(self.wrapper, self.full@, self.dict@);
                        reveal(sspec);
                    }
                }
                return Err(Error::BadData);
            }
            if !fdict(flg) {
                self.begin_body(no_bytes());
            }
        } else if self.hcount == 6 {
            self.dict_id = be32(self.hbuf.as_slice(), 2);
            self.phase = P_DICT;
            proof {
                if self.ok@ {
                    assert(spec::be32(self.hbuf@, 2) == spec::be32(b, 2));
                }
            }
        }
        proof {
            assert(self.ok@ ==> self.format == format_of(self.wrapper, self.full@));
            assert(self.ok@ && self.phase == P_HEADER ==> self.header_ok());
            assert(self.ok@ ==> self.sums_ok());
            assert(self.ok@ ==> self.spec_ok());
            assert(self.window@.len() == WINDOW + CHUNK);
            assert(self.hbuf@.len() == 10 && self.tbuf@.len() == 8);
            assert(self.fixed());
            assert(self.phase <= P_DICT);
            assert(self.out_read <= self.inf.out_pos <= self.window@.len());
            assert(self.wrapper != Wrapper::Auto ==> self.format == format_of(self.wrapper, Seq::empty()));
            assert(self.wrapper == Wrapper::Raw ==> self.phase != P_HEADER);
            assert(self.phase == P_DICT ==> self.fed && self.format == Format::Zlib && self.pending@ == Seq::<u8>::empty() && self.delivered@ == Seq::<u8>::empty() && self.adler_a == 1 && self.adler_b == 0);
            assert(!self.fed && self.phase == P_BODY ==> self.pending@ == Seq::<u8>::empty() && self.delivered@ == Seq::<u8>::empty() && self.used@ == 0 && self.format == Format::Raw);
            assert(self.phase == P_BODY ==> self.dinv(self.pending@) && self.inf.in_pos <= self.pending@.len() && (self.inf.mode == MODE_DONE ==> self.inf.cnt < 8));
            assert(self.phase == P_TRAILER ==> self.tlen <= trailer_len(self.format));
            assert(self.adler_a < 65521 && self.adler_b < 65521);
            assert(self.ok@ ==> self.spec_ok());
            assert(self.wf());
        }
        Ok(())
    }

    /// One byte of a gzip header, outside the extra field.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    fn gzip_byte(&mut self, x: u8) -> (r: Result<(), Error>)
        requires
            old(self).wf(),
            old(self).phase == P_HEADER,
            old(self).fed,
            old(self).format == Format::Gzip,
            old(self).stage != G_EXTRA,
            old(self).ok@ ==> old(self).used@ < old(self).full@.len() && old(self).full@[old(self).used@] == x
                && old(self).format == format_of(old(self).wrapper, old(self).full@),
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).delivered == old(self).delivered,
            match r {
                Ok(()) => {
                    &&& final(self).wf()
                    &&& final(self).used@ == old(self).used@ + 1
                    &&& final(self).phase == P_HEADER || final(self).phase == P_BODY || final(self).phase == P_DICT
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                },
            },
    {
        proof {
            reveal(Stream::header_ok);
        }
        let ghost b = self.full@;
        let ghost u = self.used@;
        proof {
            if self.ok@ {
                assert(b.subrange(0, u + 1) =~= b.subrange(0, u) + seq![x]);
                lemma_crc_append(0xffff_ffff, b.subrange(0, u), seq![x]);
            }
        }
        if self.stage == G_FIXED {
            self.hbuf.set(self.hcount, x);
            self.hcount = self.hcount + 1;
            self.hcrc = Self::crc1(self.hcrc, x);
            self.used = Ghost(u + 1);
            if self.hcount == 10 {
                if self.hbuf[0] != 31 || self.hbuf[1] != 139 || self.hbuf[2] != 8 || self.hbuf[3] >= 32 {
                    proof {
                        if self.ok@ {
                            lemma_gzip_header(b);
                                    lemma_sspec(self.wrapper, self.full@, self.dict@);
                                    reveal(sspec);
                        }
                    }
                    return Err(Error::BadData);
                }
                self.flg = self.hbuf[3];
                self.next_stage(G_FIXED);
            }
            proof { assert(self.wf()); }
        } else if self.stage == G_XLEN {
            self.hbuf.set(self.hcount, x);
            self.hcount = self.hcount + 1;
            self.hcrc = Self::crc1(self.hcrc, x);
            self.used = Ghost(u + 1);
            if self.hcount == 2 {
                self.xleft = self.hbuf[0] as usize + 256 * self.hbuf[1] as usize;
                self.stage = G_EXTRA;
                if self.xleft == 0 {
                    self.next_stage(G_EXTRA);
                }
            }
            proof { assert(self.wf()); }
        } else if self.stage == G_NAME || self.stage == G_COMMENT {
            self.hcrc = Self::crc1(self.hcrc, x);
            self.used = Ghost(u + 1);
            proof {
                if self.ok@ {
                    lemma_skip_zstr_step(b, u);
                }
            }
            if x == 0 {
                let from = self.stage;
                self.next_stage(from);
            }
        } else {
            self.hbuf.set(self.hcount, x);
            self.hcount = self.hcount + 1;
            self.used = Ghost(u + 1);
            if self.hcount == 2 {
                let want = self.hbuf[0] as u32 + 256 * self.hbuf[1] as u32;
                let c = !self.hcrc;
                proof {
                    assert(c & 0xffff == c % 65536) by (bit_vector);
                    if self.ok@ {
                        lemma_crc_from(b.subrange(0, self.zstart@));
                        lemma_gzip_header(b);
                        }
                }
                if c & 0xffff != want {
                    proof {
                        if self.ok@ {
                            lemma_sspec(self.wrapper, self.full@, self.dict@);
                            reveal(sspec);
                        }
                    }
                    return Err(Error::BadData);
                }
                self.begin_body(no_bytes());
            }
            proof { assert(self.wf()); }
        }
        Ok(())
    }

    /// Reads header bytes from `inp`. Returns how many it used.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    fn header(&mut self, inp: &[u8]) -> (r: Result<usize, Error>)
        requires
            old(self).wf(),
            old(self).phase == P_HEADER,
            old(self).fed,
            old(self).ok@ ==> old(self).used@ + inp@.len() <= old(self).full@.len() && inp@
                == old(self).full@.subrange(old(self).used@, old(self).used@ + inp@.len()),
        ensures
            final(self).inf.work == old(self).inf.work,
            final(self).pending == old(self).pending,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).delivered == old(self).delivered,
            match r {
                Ok(n) => {
                    &&& final(self).wf()
                    &&& n <= inp@.len()
                    &&& final(self).used@ == old(self).used@ + n
                    &&& final(self).phase == P_HEADER || final(self).phase == P_BODY || final(self).phase == P_DICT
                    &&& final(self).phase == P_HEADER ==> n == inp@.len()
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                },
            },
    {
        proof {
            reveal(Stream::header_ok);
        }
        let ghost u0 = self.used@;
        let mut i: usize = 0;
        while i < inp.len() && self.phase == P_HEADER
            invariant
                self.wf(),
                self.fed,
                self.phase == P_HEADER || self.phase == P_BODY || self.phase == P_DICT,
                i <= inp@.len(),
                self.used@ == u0 + i,
                self.ok == old(self).ok,
                self.full == old(self).full,
                self.dict == old(self).dict,
                self.fed == old(self).fed,
                self.wrapper == old(self).wrapper,
                self.delivered == old(self).delivered,
                self.delivered@ == Seq::<u8>::empty(),
                self.phase == P_HEADER ==> self.pending@ == Seq::<u8>::empty(),
                self.pending == old(self).pending,
                self.inf.work == old(self).inf.work,
                self.ok@ ==> 0 <= u0,
                self.ok@ ==> u0 + inp@.len() <= self.full@.len() && inp@ == self.full@.subrange(
                    u0,
                    u0 + inp@.len(),
                ),
            decreases inp@.len() - i,
        {
            proof {
                reveal(Stream::header_ok);
            }
            let x = inp[i];
            let ghost b = self.full@;
            let ghost u = self.used@;
            proof {
                if self.ok@ {
                    assert(inp@[i as int] == self.full@.subrange(u0, u0 + inp@.len())[i as int]);
                    assert(self.full@.subrange(u0, u0 + inp@.len())[i as int] == b[u0 + i]);
                    assert(u == u0 + i);
                    assert(x == b[u]);
                    assert(b.subrange(0, u + 1) =~= b.subrange(0, u) + seq![x]);
                    lemma_crc_append(0xffff_ffff, b.subrange(0, u), seq![x]);
                }
            }
            proof {
                if self.ok@ {
                    assert(self.header_ok());
                    assert(self.hcount == 0 && self.stage == G_FIXED ==> u == 0);
                }
            }
            if self.wrapper == Wrapper::Auto && self.stage == G_FIXED && self.hcount == 0 {
                self.format = if x == 31 {
                    Format::Gzip
                } else {
                    Format::Zlib
                };
            }
            proof {
                if self.ok@ {
                    assert(self.format == format_of(self.wrapper, self.full@));
                    assert(self.sums_ok());
                    assert(b.subrange(0, 0) =~= Seq::<u8>::empty());
                }
            }
            proof {
                if self.ok@ {
                    assert(self.format == Format::Gzip ==> self.stage == G_FIXED ==> self.hcount < 10 && u == self.hcount);
                    assert(self.format == Format::Gzip ==> self.stage < G_HCRC ==> self.hcrc == crc_from(0xffff_ffff, b.subrange(0, u)));
                    assert(self.format == Format::Zlib ==> self.hcount < 6 && u == self.hcount && self.dict@ == Seq::<u8>::empty());
                    assert(self.header_ok());
                    assert(self.spec_ok());
                }
                assert(self.wf());
            }
            if self.format == Format::Zlib {
                match self.zlib_byte(x) {
                    Ok(()) => i = i + 1,
                    Err(e) => return Err(e),
                }
            } else if self.stage == G_EXTRA {
                let avail = inp.len() - i;
                let n = if self.xleft < avail {
                    self.xleft
                } else {
                    avail
                };
                let chunk = vstd::slice::slice_subrange(inp, i, i + n);
                proof {
                    if self.ok@ {
                        assert(b.subrange(0, u + n) =~= b.subrange(0, u) + chunk@);
                        lemma_crc_append(0xffff_ffff, b.subrange(0, u), chunk@);
                    }
                }
                self.hcrc = verilith_core::checksum::cpu::crc32_update(self.hcrc, chunk);
                self.xleft = self.xleft - n;
                i = i + n;
                self.used = Ghost(u + n);
                if self.xleft == 0 {
                    self.next_stage(G_EXTRA);
                }
                proof { assert(self.wf()); }
            } else {
                match self.gzip_byte(x) {
                    Ok(()) => i = i + 1,
                    Err(e) => return Err(e),
                }
            }
        }
        Ok(i)
    }

    fn trailer_bytes(&self) -> (r: usize)
        ensures
            r as nat == trailer_len(self.format),
    {
        match self.format {
            Format::Raw => 0,
            Format::Zlib => 4,
            Format::Gzip => 8,
        }
    }

    /// Checks the complete trailer.
    fn finish_trailer(&mut self) -> (r: Result<(), Error>)
        requires
            old(self).base_ok(),
            old(self).phase == P_TRAILER,
            old(self).tlen == trailer_len(old(self).format),
            old(self).ok@ ==> old(self).trailer_ok() && old(self).format == format_of(
                old(self).wrapper,
                old(self).full@,
            ),
        ensures
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).used == old(self).used,
            final(self).delivered == old(self).delivered,
            final(self).inf == old(self).inf,
            final(self).window == old(self).window,
            final(self).pending == old(self).pending,
            final(self).base_ok(),
            r is Ok ==> final(self).wf() && final(self).phase == P_DONE,
            r matches Err(e) ==> (final(self).ok@ ==> e == Error::BadData && spec_stream(
                final(self).wrapper,
                final(self).full@,
                final(self).dict@,
            ) is None),
    {
        proof {
            reveal(Stream::trailer_ok);
        }
        let ghost b = self.full@;
        let ghost t = (self.eabs@ + 7) / 8;
        let ghost o = self.delivered@;
        proof {
            reveal(spec_trailer);
            if self.ok@ {
                lemma_sspec(self.wrapper, self.full@, self.dict@);
                reveal(sspec);
                let all = self.d0@ + o;
                assert(all.subrange(0, self.d0@.len() as int) =~= self.d0@);
                assert(all.subrange(self.d0@.len() as int, all.len() as int) =~= o);
            }
        }
        let good = if self.format == Format::Zlib {
            let v = be32(self.tbuf.as_slice(), 0);
            let want = (self.adler_b as u32) * 65536 + self.adler_a as u32;
            proof {
                if self.ok@ {
                    lemma_adler_from(o);
                    assert(spec::be32(self.tbuf@, 0) == spec::be32(b, t));
                }
            }
            v == want
        } else if self.format == Format::Gzip {
            let c = le32(self.tbuf.as_slice(), 0);
            let n = le32(self.tbuf.as_slice(), 4);
            proof {
                if self.ok@ {
                    lemma_crc_from(o);
                    assert(spec::le32(self.tbuf@, 0) == spec::le32(b, t));
                    assert(spec::le32(self.tbuf@, 4) == spec::le32(b, t + 4));
                }
            }
            c == !self.crc && n == self.isize
        } else {
            true
        };
        if !good {
            return Err(Error::BadData);
        }
        self.phase = P_DONE;
        Ok(())
    }

    /// Reads trailer bytes from `inp`. Returns how many it used.
    fn trailer(&mut self, inp: &[u8]) -> (r: Result<usize, Error>)
        requires
            old(self).wf(),
            old(self).phase == P_TRAILER,
            old(self).ok@ ==> old(self).used@ + inp@.len() <= old(self).full@.len() && inp@
                == old(self).full@.subrange(old(self).used@, old(self).used@ + inp@.len()),
        ensures
            final(self).inf == old(self).inf,
            final(self).window == old(self).window,
            final(self).pending == old(self).pending,
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).delivered == old(self).delivered,
            match r {
                Ok(n) => {
                    &&& final(self).wf()
                    &&& n <= inp@.len()
                    &&& final(self).used@ == old(self).used@ + n
                    &&& final(self).phase == P_TRAILER || final(self).phase == P_DONE
                    &&& final(self).phase == P_TRAILER ==> n == inp@.len()
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                },
            },
    {
        proof {
            reveal(Stream::trailer_ok);
        }
        let want = self.trailer_bytes();
        let mut i: usize = 0;
        while i < inp.len() && self.tlen < want
            invariant
                self.tlen <= want,
                self.tlen < want ==> self.wf(),
                self.base_ok(),
                self.ok@ ==> self.trailer_ok() && self.format == format_of(self.wrapper, self.full@),
                self.phase == P_TRAILER,
                self.inf == old(self).inf,
                self.window == old(self).window,
                self.pending == old(self).pending,
                want == trailer_len(self.format),
                i <= inp@.len(),
                self.used@ == old(self).used@ + i,
                self.ok == old(self).ok,
                self.full == old(self).full,
                self.dict == old(self).dict,
                self.fed == old(self).fed,
                self.wrapper == old(self).wrapper,
                self.delivered == old(self).delivered,
                self.ok@ ==> 0 <= old(self).used@,
                self.ok@ ==> old(self).used@ + inp@.len() <= self.full@.len() && inp@ == self.full@.subrange(
                    old(self).used@,
                    old(self).used@ + inp@.len(),
                ),
            decreases inp@.len() - i,
        {
            proof {
                reveal(Stream::trailer_ok);
            }
            proof {
                if self.ok@ {
                    assert(inp@[i as int] == self.full@.subrange(old(self).used@, old(self).used@ + inp@.len())[i as int]);
                }
            }
            let ghost tb0 = self.tbuf@;
            let ghost tl0 = self.tlen as int;
            self.tbuf.set(self.tlen, inp[i]);
            self.tlen = self.tlen + 1;
            i = i + 1;
            self.used = Ghost(self.used@ + 1);
            proof {
                if self.ok@ {
                    let t = (self.eabs@ + 7) / 8;
                    assert forall|j: int| 0 <= j < self.tlen implies self.tbuf@[j] == self.full@[t + j] by {
                        if j < tl0 {
                            assert(self.tbuf@[j] == tb0[j]);
                        } else {
                            assert(self.used@ - 1 == t + tl0);
                            assert(self.tbuf@[j] == inp@[i - 1]);
                            assert(inp@[i - 1] == self.full@.subrange(old(self).used@, old(self).used@ + inp@.len())[i - 1]);
                        }
                    }
                }
            }
            assert(self.base_ok());
            assert(self.ok@ ==> self.trailer_ok());
            assert(self.ok@ ==> self.sums_ok());
            assert(self.ok@ ==> self.spec_ok());
            assert(self.tlen < want ==> self.wf());
        }
        if self.tlen == want {
            match self.finish_trailer() {
                Ok(()) => {},
                Err(e) => return Err(e),
            }
        }
        Ok(i)
    }

    /// The DEFLATE data has ended and all its output is delivered: the
    /// trailer starts at the next byte. Takes what of it `pending` and
    /// `inp[ip..]` hold. Returns the new `ip`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(800)]
    fn begin_trailer(&mut self, inp: &[u8], ip: usize) -> (r: Result<usize, Error>)
        requires
            old(self).mid(inp@, ip as int),
            old(self).inf.mode == MODE_DONE,
            old(self).inf.cnt < 8,
            old(self).out_read == old(self).inf.out_pos,
        ensures
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).delivered == old(self).delivered,
            final(self).inf == old(self).inf,
            final(self).window == old(self).window,
            match r {
                Ok(n) => {
                    &&& final(self).wf()
                    &&& ip <= n <= inp@.len()
                    &&& final(self).used@ == old(self).used@ + (n - ip)
                    &&& final(self).phase == P_TRAILER || final(self).phase == P_DONE
                    &&& final(self).pending@.len() == 0
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                },
            },
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::body_ok);
            reveal(Stream::trailer_ok);
        }
        let want = self.trailer_bytes();
        let t = self.inf.in_pos;
        let p = self.pending.len();
        proof {
            assert(t > p ==> ip < inp@.len());
        }
        let ghost base = self.base();
        let ghost y = self.y(inp@, ip as int);
        let ghost pos = self.inf.pos();
        proof {
            if self.ok@ {
                let b = skip(self.full@, base);
                let w = self.window@.subrange(0, self.inf.out_pos as int);
                lemma_rest_done(*self.inf, b, w);
                self.lemma_mid_full(inp@, ip as int);
                assert(self.d0@ + self.delivered@ =~= self.pfx@ + w);
            }
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pos + 7, 8, t as int, 7 - self.inf.cnt);
        }
        self.eabs = Ghost(pos + 8 * base);
        // Bytes of the trailer already in `pending`.
        let k1 = if t <= p {
            p - t
        } else {
            0
        };
        assert(self.ok@ ==> k1 == 0) by {
            if self.ok@ && p > 0 {
                // Held-back bytes are ones the DEFLATE data still needs, so
                // it ends in the last of them or later.
                assert(self.held_ok());
                assert(blocks(self.full@, 8 * self.hlen@, self.d0@) matches Some((e, _)) && e == pos + 8 * base);
                assert(pos + 8 * base > 8 * (self.used@ - 1));
                assert(self.used@ == base + p);
                assert(pos == 8 * t - self.inf.cnt);
                assert(t >= p);
            }
        }
        if k1 > want {
            // Only when the input is not the stream: while `ok()` the
            // DEFLATE data ends in the last held-back byte or later, so
            // `k1` is 0.
            return Err(Error::Truncated);
        }
        let mut tb: Vec<u8> = Vec::new();
        core::mem::swap(&mut tb, &mut self.tbuf);
        proof {
            assert(tb@.len() == 8);
        }
        let mut j: usize = 0;
        while j < k1
            invariant
                j <= k1 <= want <= 8,
                k1 > 0 ==> t + k1 == p,
                p == self.pending@.len(),
                t > p ==> ip < inp@.len(),
                tb@.len() == 8,
                forall|i: int| 0 <= i < j ==> tb@[i] == self.pending@[t + i],
            decreases k1 - j,
        {
            tb.set(j, self.pending[t + j]);
            j = j + 1;
        }
        // Then from the input, after the partly used last byte if the
        // decoder holds it from there.
        let ilen = inp.len();
        proof {
            assert(t > p ==> ip < inp@.len());
        }
        let start = if t > p {
            ip + 1
        } else {
            ip
        };
        let avail = inp.len() - start;
        let k2 = if want - k1 < avail {
            want - k1
        } else {
            avail
        };
        proof {
            assert(start <= inp@.len());
            assert(start + k2 <= inp@.len());
        }
        let mut j: usize = 0;
        while j < k2
            invariant
                ilen == inp@.len(),
                tb@.len() == 8,
                j <= k2,
                k1 + k2 <= want <= 8,
                start + k2 <= inp@.len(),
                forall|i: int| 0 <= i < k1 ==> tb@[i] == self.pending@[t + i],
                forall|i: int| 0 <= i < j ==> #[trigger] tb@[k1 + i] == inp@[start + i],
            decreases k2 - j,
        {
            tb.set(k1 + j, inp[start + j]);
            j = j + 1;
        }
        self.tbuf = tb;
        self.tlen = k1 + k2;
        self.pending.clear();
        self.used = Ghost(self.used@ + (start + k2 - ip));
        self.phase = P_TRAILER;
        proof {
            if self.ok@ {
                let tt = (self.eabs@ + 7) / 8;
                assert(tt == base + t);
                assert(base == old(self).used@ - p);
                assert(t > p ==> p == 0 && t == 1);
                assert(old(self).used@ + start - ip == tt + k1);
                assert(self.used@ == tt + self.tlen);
                assert forall|i: int| 0 <= i < self.tlen implies self.tbuf@[i] == self.full@[tt + i] by {
                    if i < k1 {
                        assert(old(self).pending@[t + i] == self.full@.subrange(base, old(self).used@)[t + i]);
                    } else {
                        let m = i - k1;
                        assert(tb@[k1 + m] == inp@[start + m]);
                        assert(inp@.subrange(ip as int, inp@.len() as int)[start + m - ip] == self.full@.subrange(
                            old(self).used@,
                            old(self).used@ + (inp@.len() - ip),
                        )[start + m - ip]);
                    }
                }
            }
        }
        if self.tlen == want {
            match self.finish_trailer() {
                Ok(()) => {},
                Err(e) => return Err(e),
            }
        }
        Ok(start + k2)
    }

    /// Decodes from `inp` into `output[*op..]`. Returns the input used.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn body(&mut self, inp: &[u8], output: &mut [u8], op: &mut usize) -> (r: Result<usize, Error>)
        requires
            old(self).wf(),
            old(self).phase == P_BODY,
            old(self).fed,
            *old(op) <= old(output)@.len(),
            old(self).ok@ ==> old(self).used@ + inp@.len() <= old(self).full@.len() && inp@
                == old(self).full@.subrange(old(self).used@, old(self).used@ + inp@.len()),
        ensures
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).d0 == old(self).d0,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(output)@.len() == old(output)@.len(),
            final(output)@.subrange(0, *old(op) as int) == old(output)@.subrange(0, *old(op) as int),
            *old(op) <= *final(op) <= final(output)@.len(),
            final(self).delivered@ == old(self).delivered@ + final(output)@.subrange(
                *old(op) as int,
                *final(op) as int,
            ),
            match r {
                Ok(n) => {
                    &&& final(self).wf()
                    &&& n <= inp@.len()
                    &&& final(self).used@ == old(self).used@ + n
                    &&& final(self).phase == P_BODY || final(self).phase == P_TRAILER || final(self).phase == P_DONE
                    &&& final(self).phase == P_BODY ==> *final(op) == final(output)@.len() || (n == inp@.len() && (final(self).ok@ ==> final(self).short()))
                    &&& final(self).inf.work@ + final(self).pot() <= old(self).inf.work@ + old(self).pot() + in_cost() * n
                        + 2 * (*final(op) - *old(op)) + body_call()
                },
                Err(e) => {
                    &&& final(self).base_ok()
                    &&& final(self).ok@ ==> e == Error::BadData && spec_stream(final(self).wrapper, final(self).full@, final(self).dict@) is None
                    &&& final(self).inf.work@ <= old(self).inf.work@ + old(self).pot() + in_cost() * inp@.len()
                        + 2 * old(output)@.len() + body_call()
                },
            },
    {
        proof {
            reveal(dfixed);
            reveal(dinv);
        }
        proof {
            reveal(Stream::body_ok);
        }
        let mut ip: usize = 0;
        proof {
            self.lemma_wf_mid(inp@);
        }
        let ghost w0: int = (old(self).inf.work@ + old(self).pot()) as int;
        let ghost u0: int = old(self).inf.out_pos as int - old(self).out_read as int;
        let ghost op0: int = *old(op) as int;
        proof {
            assert(u0 >= 0);
        }
        loop
            invariant_except_break
                self.inf.work@ + self.pot() + 2 * u0 <= w0 + in_cost() * ip + 2 * (*op - op0) + 2 * (
                    self.inf.out_pos - self.out_read),
            invariant
                w0 == old(self).inf.work@ + old(self).pot(),
                u0 == old(self).inf.out_pos - old(self).out_read,
                u0 >= 0,
                op0 == *old(op),
                self.mid(inp@, ip as int),
                self.inf.mode == MODE_DONE ==> self.inf.cnt < 8,
                self.pending@.len() == 0 && self.inf.in_pos == 1 ==> 0 < self.inf.cnt < 8,
                self.used@ == old(self).used@ + ip,
                self.ok == old(self).ok,
                self.full == old(self).full,
                self.d0 == old(self).d0,
                self.dict == old(self).dict,
                self.fed == old(self).fed,
                self.wrapper == old(self).wrapper,
                output@.len() == old(output)@.len(),
                output@.subrange(0, *old(op) as int) == old(output)@.subrange(0, *old(op) as int),
                *old(op) <= *op <= output@.len(),
                self.delivered@ == old(self).delivered@ + output@.subrange(*old(op) as int, *op as int),
            ensures
                *op == output@.len() || (ip == inp@.len() && (self.ok@ ==> self.short())),
                self.inf.work@ + self.pot() + 2 * u0 <= w0 + in_cost() * ip + 2 * (*op - op0) + 2 * (
                    self.inf.out_pos - self.out_read) + exit_cost(),
            decreases
                output@.len() - *op,
                inp@.len() - ip,
                if self.inf.mode == MODE_DONE { 0int } else { 1int },
                if self.out_read == self.inf.out_pos { 1int } else { 0int },
                self.pending@.len(),
        {
            proof {
                reveal(Stream::body_ok);
                reveal(dfixed);
                reveal(dinv);
            }
            if self.out_read < self.inf.out_pos {
                if *op == output.len() {
                    break;
                }
                let ghost o1 = output@;
                let ghost op1 = *op;
                self.deliver(output, op);
                proof {
                    assert(output@.subrange(0, *old(op) as int) =~= o1.subrange(0, *old(op) as int)) by {
                        assert(output@.subrange(0, op1 as int).subrange(0, *old(op) as int) =~= output@.subrange(0, *old(op) as int));
                        assert(o1.subrange(0, op1 as int).subrange(0, *old(op) as int) =~= o1.subrange(0, *old(op) as int));
                    }
                    assert(output@.subrange(*old(op) as int, *op as int) =~= o1.subrange(*old(op) as int, op1 as int)
                        + output@.subrange(op1 as int, *op as int)) by {
                        assert forall|i: int| *old(op) <= i < op1 implies output@[i] == o1[i] by {
                            assert(output@.subrange(0, op1 as int)[i] == o1.subrange(0, op1 as int)[i]);
                        }
                    }
                    assert(old(self).delivered@ + (o1.subrange(*old(op) as int, op1 as int) + output@.subrange(
                        op1 as int,
                        *op as int,
                    )) =~= old(self).delivered@ + o1.subrange(*old(op) as int, op1 as int) + output@.subrange(
                        op1 as int,
                        *op as int,
                    ));
                }
                continue;
            }
            if self.inf.mode == MODE_DONE {
                let ghost pb = self.pot();
                let ghost wb = self.inf.work@;
                proof {
                    assert(self.out_read == self.inf.out_pos);
                    assert(wb + pb + 2 * u0 <= w0 + in_cost() * ip + 2 * (*op - op0));
                }
                let r = self.begin_trailer(inp, ip);
                proof {
                    assert(self.inf.work@ == wb);
                    assert(in_cost() * ip <= in_cost() * inp@.len()) by (nonlinear_arith)
                        requires
                            ip <= inp@.len(),
                    ;
                    assert(*op - op0 <= output@.len());
                    assert(output@.len() == old(output)@.len());
                    if let Ok(n) = r {
                        assert(self.pot() <= pb);
                        assert(in_cost() * ip <= in_cost() * n) by (nonlinear_arith)
                            requires
                                ip <= n,
                        ;
                        assert(wb + pb + 2 * u0 <= w0 + in_cost() * ip + 2 * (*op - op0));
                        assert(self.inf.work@ + self.pot() <= w0 + in_cost() * n + 2 * (*op - op0));
                        assert(w0 == old(self).inf.work@ + old(self).pot());
                        assert(op0 == *old(op));
                        assert(self.inf.work@ + self.pot() <= old(self).inf.work@ + old(self).pot() + in_cost() * n
                            + 2 * (*op - *old(op)) + body_call());
                    } else {
                        assert(self.inf.work@ <= old(self).inf.work@ + old(self).pot() + in_cost() * inp@.len()
                            + 2 * old(output)@.len() + body_call());
                    }
                }
                return r;
            }
            if self.inf.out_pos == self.window.len() {
                self.slide(Ghost(inp@), Ghost(ip as int));
            }
            let ghost sb = *self;
            let (st, nip) = self.run_once(inp, ip);
            if st == Status::BadData {
                proof {
                    assert(sb.inf.out_pos < sb.window@.len());
                    assert(self.inf.out_pos <= self.window@.len());
                    assert(sb.pot_in() + sb.inf.out_pos <= sb.pot());
                    assert(sb.out_read <= sb.inf.out_pos);
                    assert(*op <= output@.len());
                    assert(in_cost() * ip + held_cost() * (inp@.len() - ip) <= in_cost() * inp@.len()) by (nonlinear_arith)
                        requires
                            ip <= inp@.len(),
                            in_cost() == 10000,
                            held_cost() == 9600,
                    ;
                    assert(output@.len() == old(output)@.len());
                    assert(self.inf.work@ <= old(self).inf.work@ + old(self).pot() + in_cost() * inp@.len()
                        + 2 * old(output)@.len() + body_call());
                }
                return Err(Error::BadData);
            }
            proof {
                assert(sb.inf.out_pos < sb.window@.len());
                assert(self.out_read == sb.out_read);
                assert(self.phase == sb.phase);
                if st == Status::NeedOutput {
                    assert(self.inf.out_pos == self.window@.len());
                }
                if st == Status::Done {
                    assert(self.inf.mode == MODE_DONE);
                }
            }
            ip = nip;
            if st == Status::Truncated && ip == inp.len() {
                break;
            }
        }
        // Keep a partly used byte with the bits taken from it.
        let ghost wa = self.inf.work@ + self.pot();
        let ghost ipa = ip as int;
        let ghost sa = *self;
        proof {
            assert(self.inf.out_pos - self.out_read <= WINDOW + CHUNK);
            assert(wa + 2 * u0 <= w0 + in_cost() * ip + 2 * (*op - op0) + 2 * (WINDOW + CHUNK) + exit_cost());
        }
        if self.pending.len() == 0 && self.inf.in_pos == 1 {
            let ghost y = self.y(inp@, ip as int);
            let ghost u = self.used@;
            let ghost ip0 = ip as int;
            proof {
                if self.ok@ {
                    let tail = inp@.subrange(ip0, inp@.len() as int);
                    assert(tail[0] == self.full@.subrange(u, u + (inp@.len() - ip0))[0]);
                }
            }
            proof {
                if self.ok@ {
                    let b = skip(self.full@, self.base());
                    let w = self.window@.subrange(0, self.inf.out_pos as int);
                    assert(self.body_ok());
                    lemma_rest_pos(*self.inf, b, w);
                    assert(self.base() == u);
                }
            }
            self.pending.push(inp[ip]);
            ip = ip + 1;
            self.used = Ghost(self.used@ + 1);
            proof {
                if self.ok@ {
                    assert(self.held_ok());
                }
                assert(self.pending@ =~= y.subrange(0, 1));
                assert(self.y(inp@, ip as int) =~= y);
                if self.ok@ {
                    assert(self.pending@ =~= self.full@.subrange(u, u + 1));
                    assert(inp@.subrange(ip as int, inp@.len() as int) =~= self.full@.subrange(
                        u + 1,
                        u + 1 + (inp@.len() - ip),
                    )) by {
                        assert forall|i: int| 0 <= i < inp@.len() - ip implies inp@.subrange(ip as int, inp@.len() as int)[i]
                            == self.full@.subrange(u + 1, u + 1 + (inp@.len() - ip))[i] by {
                            assert(inp@.subrange(ip0, inp@.len() as int)[i + 1] == self.full@.subrange(
                                u,
                                u + (inp@.len() - ip0),
                            )[i + 1]);
                        }
                    }
                }
                assert(self.mid(inp@, ip as int));
            }
        }
        proof {
            self.lemma_mid_wf(inp@, ip as int);
            assert(self.inf == sa.inf && self.window == sa.window && self.phase == sa.phase);
            assert(self.pending@.len() == sa.pending@.len() || (self.pending@.len() == 1 && sa.pending@.len() == 0));
            if self.pending@.len() != sa.pending@.len() {
                assert(self.pending@.len() == 1);
                assert(held_cost() * 1 == held_cost());
                assert(held_cost() * self.pending@.len() == held_cost());
                assert(held_cost() * sa.pending@.len() == 0);
            }
            assert(self.pot_in() <= sa.pot_in() + held_cost() + hold_cost());
            assert(self.inf.work@ + self.pot() <= wa + held_cost() + hold_cost());
            assert(in_cost() * ipa <= in_cost() * ip) by (nonlinear_arith)
                requires
                    ipa <= ip,
            ;
            assert(self.inf.work@ + self.pot() <= old(self).inf.work@ + old(self).pot() + in_cost() * ip
                + 2 * (*op - *old(op)) + body_call());
        }
        Ok(ip)
    }

    /// Decompresses from `input` into `output`. Returns the bytes of each
    /// used, and what happened. After an error every later call fails too.
    ///
    /// While `ok()`: the output is the next part of the spec's output for
    /// `full()`, `End` means the spec accepts `full()` with the output
    /// delivered and the input used, and `BadData` means it rejects it.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1000)]
    pub fn inflate(&mut self, input: &[u8], output: &mut [u8]) -> (r: Result<(usize, usize, Progress), Error>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).full() == old(self).full(),
            final(self).dict() == old(self).dict(),
            final(self).wrapper_spec() == old(self).wrapper_spec(),
            final(self).ok() == (old(self).ok() && old(self).used() + input@.len() <= old(self).full().len()
                && input@ == old(self).full().subrange(old(self).used(), old(self).used() + input@.len())),
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((ip, op, p)) => {
                    &&& ip <= input@.len()
                    &&& op <= final(output)@.len()
                    &&& final(self).used() == old(self).used() + ip
                    &&& final(self).delivered() == old(self).delivered() + final(output)@.subrange(0, op as int)
                    &&& final(self).ok() && p == Progress::End ==> spec_stream(
                        final(self).wrapper_spec(),
                        final(self).full(),
                        final(self).dict(),
                    ) == Some((final(self).delivered(), final(self).used()))
                    // Progress: on a valid stream, a call that does not end
                    // has filled the output or used all its input, and the
                    // stream still needs more.
                    &&& final(self).ok() && p != Progress::End && p != Progress::NeedDict ==> (spec_stream(
                        final(self).wrapper_spec(),
                        final(self).full(),
                        final(self).dict(),
                    ) matches Some((_, n)) ==> op == final(output)@.len() || (ip == input@.len()
                        && final(self).used() < n))
                    // Linear work, for any input: summed over calls, the
                    // decoder's steps are at most `in_cost()` per input byte
                    // used, 2 per output byte, and `call_cost()` per call.
                    &&& final(self).work() <= old(self).work() + in_cost() * ip + 2 * op + call_cost()
                },
                Err(e) => final(self).work() <= old(self).work() + in_cost() * input@.len() + 2 * old(output)@.len()
                    + call_cost() && (final(self).ok() ==> e == Error::BadData && spec_stream(
                    final(self).wrapper_spec(),
                    final(self).full(),
                    final(self).dict(),
                ) is None),
            },
    {
        let ghost now_ok = self.ok@ && self.used@ + input@.len() <= self.full@.len() && input@
            == self.full@.subrange(self.used@, self.used@ + input@.len());
        self.ok = Ghost(now_ok);
        if self.phase == P_FAILED {
            return Err(self.error);
        }
        if self.phase == P_DICT {
            proof {
                assert(output@.subrange(0, 0) =~= Seq::<u8>::empty());
                assert(old(self).delivered@ + Seq::<u8>::empty() =~= old(self).delivered@);
            }
            return Ok((0, 0, Progress::NeedDict));
        }
        let ghost s1 = *self;
        self.fed = true;
        proof {
            lemma_set_fed(s1, *self);
        }
        let mut ip: usize = 0;
        let mut op: usize = 0;
        let ghost o0 = output@;
        let ghost u0 = self.used@;
        proof {
            assert(output@.subrange(0, 0) =~= Seq::<u8>::empty());
            assert(old(self).delivered@ + Seq::<u8>::empty() =~= old(self).delivered@);
            assert(input@.subrange(0, input@.len() as int) =~= input@);
        }
        proof {
            assert(self.work() == old(self).work());
        }
        if self.phase == P_HEADER {
            proof {
                assert(self.pending@.len() == 0);
            }
            match self.header(input) {
                Ok(n) => ip = n,
                Err(e) => {
                    proof {
                        assert(self.inf.work@ <= old(self).work());
                    }
                    return self.fail(e);
                },
            }
            proof {
                self.lemma_pot_small();
                assert(self.work() <= old(self).work() + start_cost());
            }
            if self.phase == P_DICT {
                return Ok((ip, 0, Progress::NeedDict));
            }
        }
        let ghost wk1 = self.work();
        let ghost ip1 = ip as int;
        proof {
            assert(wk1 <= old(self).work() + start_cost());
        }
        proof {
            if self.ok@ {
                assert(input@.subrange(ip as int, input@.len() as int) =~= self.full@.subrange(
                    self.used@,
                    self.used@ + (input@.len() - ip),
                ));
            }
        }
        if self.phase == P_BODY {
            let rest = vstd::slice::slice_subrange(input, ip, input.len());
            match self.body(rest, output, &mut op) {
                Ok(n) => {
                    proof {
                        assert(in_cost() * n <= in_cost() * (ip + n)) by (nonlinear_arith)
                            requires
                                ip >= 0,
                                n >= 0,
                        ;
                    }
                    ip = ip + n;
                },
                Err(e) => {
                    proof {
                        assert(in_cost() * rest@.len() <= in_cost() * input@.len()) by (nonlinear_arith)
                            requires
                                rest@.len() <= input@.len(),
                        ;
                    }
                    return self.fail(e);
                },
            }
        }
        let ghost wk2 = self.work();
        proof {
            assert(wk2 <= old(self).work() + start_cost() + in_cost() * ip + 2 * op + body_call());
        }
        proof {
            if self.ok@ {
                assert(input@.subrange(ip as int, input@.len() as int) =~= self.full@.subrange(
                    self.used@,
                    self.used@ + (input@.len() - ip),
                ));
            }
        }
        if self.phase == P_TRAILER {
            let rest = vstd::slice::slice_subrange(input, ip, input.len());
            match self.trailer(rest) {
                Ok(n) => {
                    proof {
                        assert(self.work() == wk2);
                        assert(in_cost() * ip <= in_cost() * (ip + n)) by (nonlinear_arith)
                            requires
                                ip >= 0,
                                n >= 0,
                        ;
                    }
                    ip = ip + n;
                },
                Err(e) => {
                    proof {
                        assert(in_cost() * ip <= in_cost() * input@.len()) by (nonlinear_arith)
                            requires
                                ip <= input@.len(),
                        ;
                    }
                    return self.fail(e);
                },
            }
        }
        proof {
            if self.ok@ && self.phase == P_HEADER {
                self.lemma_hdr_short();
            }
            if self.ok@ && self.phase == P_TRAILER {
                self.lemma_trl_short();
            }
        }
        let progress = if self.phase == P_DONE {
            Progress::End
        } else if ip > 0 || op > 0 {
            Progress::Ok
        } else {
            Progress::Stalled
        };
        proof {
            if self.ok@ && self.phase == P_DONE {
                lemma_sspec(self.wrapper, self.full@, self.dict@);
                reveal(sspec);
            }
        }
        Ok((ip, op, progress))
    }

    /// Sets the preset dictionary: after `inflate` returns `NeedDict` for a
    /// zlib stream, or for a raw stream before the first `inflate`. A zlib
    /// stream's dictionary must have the Adler-32 it names, `dict_id()`.
    pub fn set_dictionary(&mut self, d: &[u8]) -> (r: Result<(), Error>)
        requires
            old(self).wf(),
        ensures
            final(self).steps() == old(self).steps(),
            final(self).work() <= old(self).work() + start_cost(),
            final(self).wf(),
            final(self).full() == old(self).full(),
            final(self).ok() == old(self).ok(),
            final(self).used() == old(self).used(),
            final(self).delivered() == old(self).delivered(),
            final(self).wrapper_spec() == old(self).wrapper_spec(),
            r is Ok ==> final(self).dict() == d@,
            r is Err ==> final(self).dict() == old(self).dict(),
            r == Err::<(), Error>(Error::BadData) && final(self).ok() ==> spec_stream(
                final(self).wrapper_spec(),
                final(self).full(),
                d@,
            ) is None,
    {
        if self.phase == P_DICT {
            let (a, b) = verilith_core::checksum::cpu::adler32_update(1, 0, d);
            proof {
                lemma_adler_from(d@);
                lemma_adler_closed(1, 0, d@);
            }
            let id = b * 65536 + a;
            if id != self.dict_id {
                proof {
                    if self.ok@ {
                        lemma_sspec(self.wrapper, self.full@, d@);
                        reveal(sspec);
                    }
                }
                return Err(Error::BadData);
            }
            self.dict = Ghost(d@);
            proof {
                if self.ok@ {
                    lemma_adler_from(Seq::<u8>::empty());
                }
            }
            self.begin_body(d);
            proof {
                self.lemma_pot_small();
            }
            Ok(())
        } else if self.phase == P_BODY && !self.fed {
            self.dict = Ghost(d@);
            self.begin_body(d);
            proof {
                self.lemma_pot_small();
            }
            Ok(())
        } else {
            Err(Error::Usage)
        }
    }

    /// The Adler-32 of the preset dictionary a zlib stream needs, once
    /// `inflate` has returned `NeedDict`.
    pub fn dict_id(&self) -> u32 {
        self.dict_id
    }

    /// Records an error; every later call returns it.
    fn fail(&mut self, e: Error) -> (r: Result<(usize, usize, Progress), Error>)
        requires
            old(self).base_ok(),
            old(self).ok@ ==> e == Error::BadData && spec_stream(old(self).wrapper, old(self).full@, old(self).dict@) is None,
        ensures
            final(self).wf(),
            final(self).ok == old(self).ok,
            final(self).full == old(self).full,
            final(self).dict == old(self).dict,
            final(self).fed == old(self).fed,
            final(self).wrapper == old(self).wrapper,
            final(self).used == old(self).used,
            final(self).delivered == old(self).delivered,
            final(self).inf == old(self).inf,
            final(self).phase == P_FAILED,
            r == Err::<(usize, usize, Progress), Error>(e),
    {
        self.phase = P_FAILED;
        self.error = e;
        Err(e)
    }

    /// The wrapper this stream was set up for.
    pub fn wrapper(&self) -> (r: Wrapper)
        ensures
            r == self.wrapper_spec(),
    {
        self.wrapper
    }

    pub fn is_done(&self) -> bool {
        self.phase == P_DONE
    }

    /// The running checksum of the output delivered so far: Adler-32 for
    /// zlib, CRC-32 for gzip (0 for raw).
    pub fn check(&self) -> u32 {
        match self.format {
            Format::Zlib => ((self.adler_b as u64) * 65536 + self.adler_a as u64) as u32,
            Format::Gzip => !self.crc,
            Format::Raw => 0,
        }
    }
}

/// A valid stream fed in pieces reaches `End`: whatever the piece size and
/// the output space per call (both at least one byte), a caller that keeps
/// passing the next piece of the stream gets `End` (or `NeedDict`, for a
/// zlib stream made with a preset dictionary) and never an error. The loop's
/// measure is the input and output the spec has left, which every call
/// that does not end reduces. Checked by Verus, not compiled.
#[cfg(verus_only)]
pub fn feed_in_pieces(wrapper: Wrapper, data: &[u8], piece: usize, room: usize) -> (r: Progress)
    requires
        piece > 0,
        room > 0,
        spec_stream(wrapper, data@, Seq::empty()) is Some,
    ensures
        r == Progress::End || r == Progress::NeedDict,
{
    let ghost o = spec_stream(wrapper, data@, Seq::empty())->Some_0.0;
    let ghost n = spec_stream(wrapper, data@, Seq::empty())->Some_0.1;
    let mut s = Stream::new(wrapper, Ghost(data@));
    let mut out: Vec<u8> = Vec::new();
    while out.len() < room
        invariant
            out@.len() <= room,
        decreases room - out@.len(),
    {
        out.push(0);
    }
    let mut used: usize = 0;
    proof {
        s.lemma_bounds();
    }
    loop
        invariant
            s.wf(),
            s.ok(),
            s.full() == data@,
            s.dict() == Seq::<u8>::empty(),
            s.wrapper_spec() == wrapper,
            s.used() == used as int,
            used <= data@.len(),
            out@.len() == room,
            spec_stream(wrapper, data@, Seq::empty()) == Some((o, n)),
            s.used() <= n <= data@.len(),
            s.delivered().len() <= o.len(),
            piece > 0,
            room > 0,
        decreases (n - s.used()) + (o.len() - s.delivered().len()),
    {
        let ghost u0 = s.used();
        let ghost d0 = s.delivered().len();
        let k = if data.len() - used < piece {
            data.len() - used
        } else {
            piece
        };
        let input = vstd::slice::slice_subrange(data, used, used + k);
        match s.inflate(input, out.as_mut_slice()) {
            Ok((ip, op, p)) => {
                if p == Progress::End || p == Progress::NeedDict {
                    return p;
                }
                used = used + ip;
                proof {
                    s.lemma_bounds();
                    assert(out@.len() == room);
                    assert(s.ok());
                    assert(spec_stream(s.wrapper_spec(), s.full(), s.dict()) == Some((o, n)));
                    if op == room {
                        assert(s.delivered().len() == d0 + op);
                    } else {
                        assert(ip == input@.len());
                        assert(s.used() < n);
                        assert(input@.len() == k);
                        assert(k > 0);
                    }
                }
            },
            Err(_) => {
                return Progress::Stalled;
            },
        }
    }
}

impl Stream {
    /// `new` for callers with no ghost `full` to give. The ghost stream is
    /// empty, so `ok()` turns false at the first input byte and the proofs
    /// about `full` then say nothing; the memory safety and the error
    /// behavior do not depend on them.
    pub fn open(wrapper: Wrapper) -> (r: Stream)
        ensures
            r.wf(),
            r.wrapper_spec() == wrapper,
    {
        Stream::new(wrapper, Ghost(Seq::empty()))
    }

    /// `reset` for callers with no ghost `full` to give (see `open`).
    pub fn restart(&mut self, wrapper: Wrapper)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).wrapper_spec() == wrapper,
    {
        self.reset(wrapper, Ghost(Seq::empty()))
    }
}

} // verus!

impl Stream {

    /// The stream is still reading its zlib or gzip header.
    pub fn in_header(&self) -> bool {
        self.phase == P_HEADER
    }

    /// The header read was a gzip one (so far as it has been read).
    pub fn is_gzip(&self) -> bool {
        self.format == Format::Gzip
    }

    /// Up to the last 32 KiB of output delivered, preceded by the preset
    /// dictionary when there is less output than that: the history later
    /// matches can refer to.
    pub fn history(&self) -> &[u8] {
        &self.window[self.out_read.saturating_sub(WINDOW)..self.out_read]
    }
}
