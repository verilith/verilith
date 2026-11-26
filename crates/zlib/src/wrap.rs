//! Raw DEFLATE, zlib and gzip decompression into a buffer or a `Vec`,
//! proven to compute `spec::inflate`, `spec::zlib_decompress` and
//! `spec::gzip_decompress`.
use crate::checksum::*;
#[cfg(verus_only)]
use crate::ilemmas::{lemma_gzip_header_end, lemma_skip_zstr_end};
use crate::inflate::*;
#[cfg(verus_only)]
use crate::spec;
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Error {
    /// The input is not a valid stream.
    BadData,
    /// The input ends before the stream does.
    Truncated,
    /// The output does not fit in the space allowed.
    InsufficientSpace,
    /// The call is not allowed in the stream's current state.
    Usage,
}

/// A reusable decompressor (its Huffman tables take about 13 KiB).
pub struct Decompressor {
    pub inf: Box<Inflater>,
}

/// Which container wraps the DEFLATE data.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Format {
    Raw,
    Zlib,
    Gzip,
}

/// What decompressing `b` in format `fmt` gives: the output and the input
/// bytes used.
#[verifier::opaque]
pub open spec fn spec_decompress(fmt: Format, b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match fmt {
        Format::Raw => spec::inflate(b),
        Format::Zlib => spec::zlib_decompress(b),
        Format::Gzip => spec::gzip_decompress(b),
    }
}

/// Where the DEFLATE data of a stream in format `fmt` starts, if the header
/// is valid.
#[verifier::opaque]
pub open spec fn spec_header(fmt: Format, b: Seq<u8>) -> Option<int> {
    match fmt {
        Format::Raw => Some(0),
        Format::Zlib => if zlib_header_ok(b) {
            Some(2)
        } else {
            None
        },
        Format::Gzip => spec::gzip_header(b),
    }
}

pub open spec fn zlib_header_ok(b: Seq<u8>) -> bool {
    let cmf = b[0] as nat;
    let flg = b[1] as nat;
    &&& b.len() >= 2
    &&& cmf % 16 == 8
    &&& cmf / 16 <= 7
    &&& (cmf * 256 + flg) % 31 == 0
    &&& (flg / 32) % 2 != 1
}

/// What follows the DEFLATE data, which ended in byte `i - 1` with output
/// `o`.
#[verifier::opaque]
pub open spec fn spec_trailer(fmt: Format, b: Seq<u8>, i: int, o: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match fmt {
        Format::Raw => Some((o, i)),
        Format::Zlib => if i + 4 > b.len() || spec::be32(b, i) != spec::adler32(o) {
            None
        } else {
            Some((o, i + 4))
        },
        Format::Gzip => if i + 8 > b.len() || spec::le32(b, i) != spec::crc32(o) as nat
            || spec::le32(b, i + 4) != o.len() % 0x1_0000_0000 {
            None
        } else {
            Some((o, i + 8))
        },
    }
}

/// The formats are a header, DEFLATE data and a trailer.
pub proof fn lemma_spec_decompress(fmt: Format, b: Seq<u8>)
    ensures
        spec_decompress(fmt, b) == match spec_header(fmt, b) {
            None => None,
            Some(h) => match spec::inflate_blocks(b, 8 * h, Seq::empty()) {
                None => None,
                Some((end, o)) => spec_trailer(fmt, b, (end + 7) / 8, o),
            },
        },
{
    reveal(spec_decompress);
    reveal(spec_header);
    reveal(spec_trailer);
}

fn status_err(s: Status) -> (e: Error)
    ensures
        s == Status::NeedOutput ==> e == Error::InsufficientSpace,
        s == Status::Truncated ==> e == Error::Truncated,
        s == Status::BadData ==> e == Error::BadData,
{
    match s {
        Status::NeedOutput => Error::InsufficientSpace,
        Status::Truncated => Error::Truncated,
        _ => Error::BadData,
    }
}

/// The offset just past the first zero byte at or after `p`.
fn skip_zstr(b: &[u8], p: usize) -> (r: Option<usize>)
    requires
        p <= b@.len(),
    ensures
        match r {
            Some(q) => spec::skip_zstr(b@, p as int) == Some(q as int),
            None => spec::skip_zstr(b@, p as int) is None,
        },
{
    let mut i = p;
    while i < b.len()
        invariant
            p <= i <= b@.len(),
            spec::skip_zstr(b@, p as int) == spec::skip_zstr(b@, i as int),
        decreases b@.len() - i,
    {
        if b[i] == 0 {
            return Some(i + 1);
        }
        i = i + 1;
    }
    None
}

/// The length of a zlib header, if valid.
pub fn zlib_header(b: &[u8]) -> (r: Result<usize, Error>)
    ensures
        match r {
            Ok(h) => h == 2 && zlib_header_ok(b@),
            Err(e) => !zlib_header_ok(b@) && e != Error::InsufficientSpace,
        },
{
    if b.len() < 2 {
        return Err(Error::Truncated);
    }
    let cmf = b[0] as u32;
    let flg = b[1] as u32;
    proof {
        assert(cmf & 0x0f == cmf % 16 && cmf >> 4u32 == cmf / 16 && ((flg & 0x20 != 0) == ((flg / 32)
            % 2 == 1))) by (bit_vector)
            requires
                cmf < 256,
                flg < 256,
        ;
    }
    if cmf & 0x0f != 8 || cmf >> 4 > 7 || (cmf * 256 + flg) % 31 != 0 || flg & 0x20 != 0 {
        return Err(Error::BadData);
    }
    Ok(2)
}

/// The length of a gzip member header, if valid.
pub fn gzip_header(b: &[u8]) -> (r: Result<usize, Error>)
    ensures
        match r {
            Ok(h) => spec::gzip_header(b@) == Some(h as int),
            Err(e) => spec::gzip_header(b@) is None && e != Error::InsufficientSpace,
        },
{
    if b.len() < 10 {
        return Err(Error::Truncated);
    }
    if b[0] != 31 || b[1] != 139 || b[2] != 8 || b[3] >= 32 {
        return Err(Error::BadData);
    }
    let flg = b[3];
    let ghost f = flg as nat;
    proof {
        assert((flg & 4 != 0) == ((flg as nat / 4) % 2 == 1)) by (bit_vector)
            requires
                flg < 32,
        ;
        assert((flg & 8 != 0) == ((flg as nat / 8) % 2 == 1)) by (bit_vector)
            requires
                flg < 32,
        ;
        assert((flg & 16 != 0) == ((flg as nat / 16) % 2 == 1)) by (bit_vector)
            requires
                flg < 32,
        ;
        assert((flg & 2 != 0) == ((flg as nat / 2) % 2 == 1)) by (bit_vector)
            requires
                flg < 32,
        ;
    }
    let mut p: usize = 10;
    if flg & 4 != 0 {
        if b.len() < 12 {
            return Err(Error::Truncated);
        }
        let xlen = b[10] as usize + 256 * b[11] as usize;
        if b.len() - 12 < xlen {
            return Err(Error::Truncated);
        }
        p = 12 + xlen;
    }
    let ghost p1 = p as int;
    if flg & 8 != 0 {
        p = match skip_zstr(b, p) {
            Some(q) => q,
            None => return Err(Error::Truncated),
        };
        proof {
            lemma_skip_zstr_end(b@, p1);
        }
    }
    let ghost p2 = p as int;
    if flg & 16 != 0 {
        p = match skip_zstr(b, p) {
            Some(q) => q,
            None => return Err(Error::Truncated),
        };
        proof {
            lemma_skip_zstr_end(b@, p2);
        }
    }
    if flg & 2 != 0 {
        if b.len() - p < 2 {
            return Err(Error::Truncated);
        }
        let want = b[p] as u32 + 256 * b[p + 1] as u32;
        let c = crc32(vstd::slice::slice_subrange(b, 0, p));
        proof {
            assert(c & 0xffff == c % 65536) by (bit_vector);
        }
        if c & 0xffff != want {
            return Err(Error::BadData);
        }
        p = p + 2;
    }
    Ok(p)
}

pub fn be32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as nat == spec::be32(b@, i as int),
{
    let (x0, x1, x2, x3) = (b[i] as u32, b[i + 1] as u32, b[i + 2] as u32, b[i + 3] as u32);
    proof {
        assert(x0 << 24u32 | x1 << 16u32 | x2 << 8u32 | x3 == x0 * 16777216 + x1 * 65536 + x2 * 256
            + x3) by (bit_vector)
            requires
                x0 < 256,
                x1 < 256,
                x2 < 256,
                x3 < 256,
        ;
    }
    x0 << 24 | x1 << 16 | x2 << 8 | x3
}

pub fn le32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as nat == spec::le32(b@, i as int),
{
    let (x0, x1, x2, x3) = (b[i] as u32, b[i + 1] as u32, b[i + 2] as u32, b[i + 3] as u32);
    proof {
        assert(x0 | x1 << 8u32 | x2 << 16u32 | x3 << 24u32 == x0 + x1 * 256 + x2 * 65536 + x3
            * 16777216) by (bit_vector)
            requires
                x0 < 256,
                x1 < 256,
                x2 < 256,
                x3 < 256,
        ;
    }
    x0 | x1 << 8 | x2 << 16 | x3 << 24
}

/// Checks the trailer after the DEFLATE data ends at byte `end`, for
/// output `o` of length `n` whose checksums were computed as it was decoded:
/// `(a, b)` is its Adler-32 state and `crc` its CRC-32 register. Returns the
/// total input length used.
fn check_sums(fmt: Format, input: &[u8], end: usize, Ghost(o): Ghost<Seq<u8>>, n: usize, a: u32, b: u32, crc: u32) -> (r: Result<usize, Error>)
    requires
        end <= input@.len(),
        o.len() == n,
        fmt == Format::Zlib ==> (a as nat, b as nat) == adler_from(1, 0, o),
        fmt == Format::Gzip ==> crc == crc_from(0xffff_ffff, o),
    ensures
        match r {
            Ok(used) => spec_trailer(fmt, input@, end as int, o) == Some((o, used as int)),
            Err(err) => spec_trailer(fmt, input@, end as int, o) is None && err
                != Error::InsufficientSpace,
        },
{
    proof {
        reveal(spec_trailer);
    }
    if fmt == Format::Raw {
        Ok(end)
    } else if fmt == Format::Zlib {
        if input.len() - end < 4 {
            return Err(Error::Truncated);
        }
        proof {
            lemma_adler_from(o);
            lemma_adler_closed(1, 0, o);
            assert((b << 16u32) | a == b * 65536 + a) by (bit_vector)
                requires
                    a < 65521,
                    b < 65521,
            ;
        }
        if be32(input, end) != (b << 16) | a {
            return Err(Error::BadData);
        }
        Ok(end + 4)
    } else {
        if input.len() - end < 8 {
            return Err(Error::Truncated);
        }
        proof {
            lemma_crc_from(o);
            assert(n as u32 == n as nat % 0x1_0000_0000) by (bit_vector);
        }
        if le32(input, end) != !crc || le32(input, end + 4) != n as u32 {
            return Err(Error::BadData);
        }
        Ok(end + 8)
    }
}

/// A first guess at the output size, at most `limit`; gzip records it
/// (mod 2^32) at the end.
fn size_guess(fmt: Format, input: &[u8], limit: usize) -> (r: usize)
    ensures
        r <= limit,
{
    let mut guess: usize = if input.len() < usize::MAX / 8 {
        input.len() * 4 + 1024
    } else {
        usize::MAX
    };
    if fmt == Format::Gzip && input.len() >= 18 {
        let isize = le32(input, input.len() - 4) as usize;
        if isize < usize::MAX && isize / 256 < guess {
            guess = isize + 1;
        }
    }
    if guess > limit {
        guess = limit;
    }
    guess
}

/// Output bytes decoded between checksum updates in `decompress_into`.
pub const SUM_CHUNK: usize = 65536;

/// Most decoder work (loop iterations, see `inflate`) for one stream of
/// `n` input bytes that writes `m` output bytes: linear in both.
pub open spec fn work_bound(n: nat, m: nat) -> nat {
    fixed_cost() + bit_cost() * 8 * n + 131 * m + header_cost() + 2 * body_cost()
}

/// Sums the decoder's work into `work_bound`.
proof fn lemma_work(w: nat, w0: nat, c: nat, p: int, p0: int, n: nat, m: nat, x: nat)
    requires
        c <= fixed_cost(),
        0 <= p0,
        p <= 8 * n,
        w <= w0 + c + bit_cost() * (p - p0) + 131 * m + x,
        x <= header_cost() + 2 * body_cost(),
    ensures
        w <= w0 + work_bound(n, m),
{
    assert(bit_cost() * (p - p0) <= bit_cost() * 8 * n) by (nonlinear_arith)
        requires
            p - p0 <= 8 * n,
            bit_cost() == 1200,
    ;
}

/// The decompressor's tables are consistent.
pub open spec fn wf(d: &Decompressor) -> bool {
    d.inf.fixed_ok()
}

/// `simd::run`, which also updates the checksum that `fmt` needs over the
/// new output: `(a, b)` is the Adler-32 state and `crc` the CRC-32 register.
/// For zlib and gzip it decodes `SUM_CHUNK` bytes at a time, so each chunk
/// is summed while it is still in cache. Each call to `run` beyond the
/// first is paid for by the output of the call before it.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn run_sums(inf: &mut Inflater, fmt: Format, input: &[u8], out: &mut [u8], a: u32, b: u32, crc: u32) -> (r: (Status, u32, u32, u32))
    requires
        old(inf).in_pos <= input@.len(),
        old(inf).inv(input@),
        old(inf).out_pos <= old(out)@.len(),
        old(inf).fixed_ok(),
        a < ADLER_MOD,
        b < ADLER_MOD,
        fmt == Format::Zlib ==> (a as nat, b as nat) == adler_from(1, 0, old(out)@.subrange(0, old(inf).out_pos as int)),
        fmt == Format::Gzip ==> crc == crc_from(0xffff_ffff, old(out)@.subrange(0, old(inf).out_pos as int)),
    ensures
        ({
            let (st, a2, b2, crc2) = r;
            let (i0, i1) = (*old(inf), *final(inf));
            let (o0, o1) = (old(out)@, final(out)@);
            &&& i1.in_pos <= input@.len()
            &&& i1.fixed_ok()
            &&& o1.len() == o0.len()
            &&& o1.subrange(0, i0.out_pos as int) == o0.subrange(0, i0.out_pos as int)
            &&& i0.out_pos <= i1.out_pos <= o1.len()
            &&& a2 < ADLER_MOD
            &&& b2 < ADLER_MOD
            &&& fmt == Format::Zlib ==> (a2 as nat, b2 as nat) == adler_from(1, 0, o1.subrange(0, i1.out_pos as int))
            &&& fmt == Format::Gzip ==> crc2 == crc_from(0xffff_ffff, o1.subrange(0, i1.out_pos as int))
            &&& st == Status::Done ==> i1.inv(input@) && i1.mode == MODE_DONE && i0.rest(input@, o0.subrange(0, i0.out_pos as int))
                == Some((i1.pos(), o1.subrange(0, i1.out_pos as int)))
            &&& st == Status::NeedOutput ==> i1.inv(input@) && i1.out_pos == o1.len() && i1.rest(input@, o1.subrange(0, i1.out_pos as int))
                == i0.rest(input@, o0.subrange(0, i0.out_pos as int))
            &&& st == Status::BadData || st == Status::Truncated ==> i0.rest(input@, o0.subrange(0, i0.out_pos as int)) is None
            &&& st == Status::Done || st == Status::NeedOutput ==> i1.pos() >= i0.pos()
                && i1.work@ + credit(i1.fixed, i1.mode) <= i0.work@ + credit(i0.fixed, i0.mode) + bit_cost() * (i1.pos() - i0.pos())
                + 131 * (i1.out_pos - i0.out_pos) + body_cost()
            &&& st == Status::NeedOutput && i0.out_pos < o0.len() ==> i1.work@ + credit(i1.fixed, i1.mode) <= i0.work@ + credit(i0.fixed, i0.mode)
                + bit_cost() * (i1.pos() - i0.pos()) + 131 * (i1.out_pos - i0.out_pos)
            &&& i1.work@ <= i0.work@ + credit(i0.fixed, i0.mode) + bit_cost() * (spec::nbits(input@) - i0.pos()) + 131 * (i1.out_pos - i0.out_pos)
                + header_cost() + body_cost()
        }),
{
    let ghost i0 = *inf;
    let ghost o0 = out@;
    let ghost base = i0.work@ + credit(i0.fixed, i0.mode);
    let ghost nb = spec::nbits(input@);
    let ghost goal = i0.rest(input@, o0.subrange(0, i0.out_pos as int));
    let out_len = out.len();
    let mut lim: usize = inf.out_pos;
    let mut done: usize = inf.out_pos;
    let mut a = a;
    let mut b = b;
    let mut crc = crc;
    let mut s = Status::NeedOutput;
    let mut go = true;
    let ghost mut started = false;
    proof {
        assert(input@ =~= input@.subrange(0, input@.len() as int));
    }
    while go
        invariant
            go ==> s == Status::NeedOutput && (lim < out_len || !started),
            !go ==> !(s == Status::NeedOutput && lim < out_len),
            !started ==> go && *inf == i0 && out@ == o0 && lim == i0.out_pos,
            started ==> inf.in_pos <= input@.len() && inf.fixed_ok(),
            nb == spec::nbits(input@),
            base == i0.work@ + credit(i0.fixed, i0.mode),
            goal == i0.rest(input@, o0.subrange(0, i0.out_pos as int)),
            out_len == out@.len(),
            out@.len() == o0.len(),
            out@.subrange(0, i0.out_pos as int) == o0.subrange(0, i0.out_pos as int),
            i0.out_pos <= inf.out_pos <= lim <= out_len,
            done == inf.out_pos,
            s == Status::NeedOutput ==> inf.out_pos == lim && inf.pos() >= i0.pos() && inf.inv(input@)
                && inf.in_pos <= input@.len()
                && inf.rest(input@, out@.subrange(0, inf.out_pos as int)) == goal,
            s == Status::NeedOutput && started ==> inf.work@ + credit(inf.fixed, inf.mode) <= base
                + bit_cost() * (inf.pos() - i0.pos()) + 131 * (inf.out_pos - i0.out_pos)
                + if i0.out_pos < out_len { 0 } else { body_cost() },
            s == Status::Done ==> inf.inv(input@) && inf.mode == MODE_DONE && inf.pos() >= i0.pos()
                && goal == Some((inf.pos(), out@.subrange(0, inf.out_pos as int)))
                && inf.work@ + credit(inf.fixed, inf.mode) <= base + bit_cost() * (inf.pos() - i0.pos())
                + 131 * (inf.out_pos - i0.out_pos) + body_cost(),
            s == Status::BadData || s == Status::Truncated ==> goal is None,
            inf.work@ <= base + bit_cost() * (nb - i0.pos()) + 131 * (inf.out_pos - i0.out_pos) + header_cost() + body_cost(),
            a < ADLER_MOD,
            b < ADLER_MOD,
            fmt == Format::Zlib ==> (a as nat, b as nat) == adler_from(1, 0, out@.subrange(0, done as int)),
            fmt == Format::Gzip ==> crc == crc_from(0xffff_ffff, out@.subrange(0, done as int)),
        decreases out_len - lim + if go { 1int } else { 0int },
    {
        let q = inf.out_pos;
        lim = if fmt == Format::Raw || out_len - q <= SUM_CHUNK {
            out_len
        } else {
            q + SUM_CHUNK
        };
        let ghost before = out@;
        let ghost inf1 = *inf;
        proof {
            assert(inf.pos() <= nb);
            assert(input@ =~= input@.subrange(0, input@.len() as int));
        }
        let (head, tail) = out.split_at_mut(lim);
        proof {
            assert(head@.subrange(0, q as int) =~= before.subrange(0, q as int));
        }
        s = crate::simd::run(inf, input, Ghost(input@), head);
        proof {
            assert(out@ == head@ + tail@);
            assert(out@.subrange(0, inf.out_pos as int) =~= head@.subrange(0, inf.out_pos as int));
            assert(out@.subrange(0, q as int) =~= before.subrange(0, q as int));
            assert(out@.subrange(0, i0.out_pos as int) =~= before.subrange(0, i0.out_pos as int));
            assert(before.subrange(0, q as int).subrange(0, i0.out_pos as int) =~= before.subrange(0, i0.out_pos as int));
            if s == Status::NeedOutput {
                assert(inf.out_pos == lim);
            }
        }
        let n = inf.out_pos;
        if fmt != Format::Raw {
            let chunk = vstd::slice::slice_subrange(out, done, n);
            let ghost prev = out@.subrange(0, done as int);
            proof {
                assert(out@.subrange(0, n as int) =~= prev + chunk@);
            }
            if fmt == Format::Zlib {
                let (a2, b2) = verilith_checksum::cpu::adler32_update(a, b, chunk);
                proof {
                    lemma_adler_closed(a as nat, b as nat, chunk@);
                    lemma_adler_append(1, 0, prev, chunk@);
                }
                a = a2;
                b = b2;
            } else {
                crc = verilith_checksum::cpu::crc32_update(crc, chunk);
                proof {
                    lemma_crc_append(0xffff_ffff, prev, chunk@);
                }
            }
        }
        done = n;
        go = s == Status::NeedOutput && lim < out_len;
        proof {
            started = true;
        }
    }
    (s, a, b, crc)
}

impl Decompressor {
    pub fn new() -> (r: Decompressor)
        ensures
            wf(&r),
    {
        Decompressor { inf: Inflater::new() }
    }

    fn header(fmt: Format, input: &[u8]) -> (r: Result<usize, Error>)
        ensures
            match r {
                Ok(h) => spec_header(fmt, input@) == Some(h as int) && h <= input@.len(),
                Err(e) => spec_header(fmt, input@) is None && e != Error::InsufficientSpace,
            },
    {
        proof {
            reveal(spec_header);
        }
        if fmt == Format::Raw {
            Ok(0)
        } else if fmt == Format::Zlib {
            zlib_header(input)
        } else {
            proof {
                lemma_gzip_header_end(input@);
            }
            gzip_header(input)
        }
    }

    /// Decompresses one stream at the start of `input` into `out`. Returns
    /// the input bytes used and the output length.
    ///
    /// The result is the spec's: `Ok` exactly with its output and length;
    /// `BadData` and `Truncated` only when the input is not a valid stream.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    pub fn decompress_into(&mut self, fmt: Format, input: &[u8], out: &mut [u8]) -> (r: Result<
        (usize, usize),
        Error,
    >)
        requires
            wf(old(self)),
        ensures
            wf(final(self)),
            final(out)@.len() == old(out)@.len(),
            match r {
                Ok((used, n)) => n <= final(out)@.len() && spec_decompress(fmt, input@) == Some(
                    (final(out)@.subrange(0, n as int), used as int),
                ) && final(self).inf.work@ <= old(self).inf.work@ + work_bound(
                    input@.len(),
                    n as nat,
                ),
                Err(e) => e != Error::InsufficientSpace ==> spec_decompress(fmt, input@) is None,
            },
            // Running out of space means the output would be at least as
            // long as `out`.
            r == Err::<(usize, usize), Error>(Error::InsufficientSpace) ==> (spec_decompress(fmt, input@) matches Some((o, _)) ==> o.len() >= old(out)@.len()),
            final(self).inf.work@ <= old(self).inf.work@ + work_bound(input@.len(), old(out)@.len()),
    {
        proof {
            lemma_spec_decompress(fmt, input@);
        }
        let h = match Self::header(fmt, input) {
            Ok(h) => h,
            Err(e) => return Err(e),
        };
        self.inf.reset(h);
        let ghost s0 = *self.inf;
        proof {
            lemma_rest_start(s0, input@, Seq::empty());
            assert(out@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        let ghost w0 = old(self).inf.work@;
        let ghost c0 = credit(s0.fixed, s0.mode);
        proof { assert(input@ =~= input@.subrange(0, input@.len() as int)); }
        proof {
            assert(input@ =~= input@.subrange(0, input@.len() as int));
            assert(s0.work@ == w0);
        }
        let (s, a, b, crc) = run_sums(&mut self.inf, fmt, input, out, 1, 0, 0xffff_ffff);
        proof {
            let m = self.inf.out_pos as nat;
            let nb = 8 * input@.len();
            if s == Status::Done {
                assert(self.inf.pos() <= nb);
                lemma_work(self.inf.work@, w0, c0, self.inf.pos(), s0.pos(), input@.len(), m, body_cost());
            } else if s == Status::NeedOutput {
                assert(self.inf.pos() <= nb);
                lemma_work(self.inf.work@, w0, c0, self.inf.pos(), s0.pos(), input@.len(), m, body_cost());
            } else {
                lemma_work(self.inf.work@, w0, c0, nb as int, s0.pos(), input@.len(), m, header_cost() + body_cost());
            }
            lemma_work(self.inf.work@, w0, c0, nb as int, s0.pos(), input@.len(), out@.len(), header_cost() + body_cost());
        }
        if s != Status::Done {
            proof {
                if s == Status::NeedOutput {
                    crate::slemmas::lemma_rest_grows(*self.inf, input@, out@.subrange(0, self.inf.out_pos as int));
                    reveal(spec_trailer);
                }
            }
            return Err(status_err(s));
        }
        let n = self.inf.out_pos;
        let end = self.inf.consumed();
        match check_sums(fmt, input, end, Ghost(out@.subrange(0, n as int)), n, a, b, crc) {
            Ok(used) => Ok((used, n)),
            Err(e) => Err(e),
        }
    }

    /// Decompresses one stream at the start of `input` into a new `Vec` of
    /// at most `limit` bytes. Returns it and the input bytes used.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    pub fn decompress_vec(&mut self, fmt: Format, input: &[u8], limit: usize) -> (r: Result<
        (Vec<u8>, usize),
        Error,
    >)
        requires
            wf(old(self)),
        ensures
            wf(final(self)),
            match r {
                Ok((v, used)) => v@.len() <= limit && spec_decompress(fmt, input@) == Some(
                    (v@, used as int),
                ) && final(self).inf.work@ <= old(self).inf.work@ + work_bound(
                    input@.len(),
                    v@.len(),
                ),
                Err(e) => e != Error::InsufficientSpace ==> spec_decompress(fmt, input@) is None,
            },
            final(self).inf.work@ <= old(self).inf.work@ + work_bound(input@.len(), limit as nat),
    {
        proof {
            lemma_spec_decompress(fmt, input@);
        }
        let h = match Self::header(fmt, input) {
            Ok(h) => h,
            Err(e) => return Err(e),
        };
        self.inf.reset(h);
        let ghost s0 = *self.inf;
        let guess = size_guess(fmt, input, limit);
        let mut out: Vec<u8> = Vec::new();
        out.resize(guess, 0u8);
        let ghost goal = s0.rest(input@, Seq::empty());
        proof {
            lemma_rest_start(s0, input@, Seq::empty());
            assert(out@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        let ghost base = old(self).inf.work@ + credit(s0.fixed, s0.mode);
        let ghost nb = 8 * input@.len();
        proof { assert(input@ =~= input@.subrange(0, input@.len() as int)); }
        let (mut s, mut a, mut b, mut crc) = run_sums(&mut self.inf, fmt, input, out.as_mut_slice(), 1, 0, 0xffff_ffff);
        proof {
            assert(credit(s0.fixed, s0.mode) <= fixed_cost());
            assert(s0.pos() >= 0);
        }
        while s == Status::NeedOutput
            invariant
                wf(self),
                s0.pos() >= 0,
                base == old(self).inf.work@ + credit(s0.fixed, s0.mode),
                credit(s0.fixed, s0.mode) <= fixed_cost(),
                nb == 8 * input@.len(),
                s == Status::NeedOutput ==> self.inf.out_pos == out@.len() && self.inf.pos()
                    >= s0.pos() && self.inf.work@ + credit(self.inf.fixed, self.inf.mode) <= base
                    + bit_cost() * (self.inf.pos() - s0.pos()) + 131 * self.inf.out_pos + body_cost(),
                s == Status::Done ==> self.inf.work@ <= base + bit_cost() * (nb - s0.pos()) + 131
                    * self.inf.out_pos + 2 * body_cost(),
                a < ADLER_MOD,
                b < ADLER_MOD,
                self.inf.out_pos <= out@.len(),
                fmt == Format::Zlib ==> (a as nat, b as nat) == adler_from(1, 0, out@.subrange(0, self.inf.out_pos as int)),
                fmt == Format::Gzip ==> crc == crc_from(0xffff_ffff, out@.subrange(0, self.inf.out_pos as int)),
                s != Status::NeedOutput && s != Status::Done ==> self.inf.work@ <= base + bit_cost()
                    * (nb - s0.pos()) + 131 * self.inf.out_pos + header_cost() + 2 * body_cost(),
                out@.len() <= limit,
                self.inf.out_pos <= out@.len(),
                s == Status::NeedOutput ==> self.inf.inv(input@) && self.inf.rest(
                    input@,
                    out@.subrange(0, self.inf.out_pos as int),
                ) == goal,
                s == Status::Done ==> self.inf.inv(input@) && goal == Some(
                    (self.inf.pos(), out@.subrange(0, self.inf.out_pos as int)),
                ),
                s == Status::BadData || s == Status::Truncated ==> goal is None,
            decreases limit - out@.len(),
        {
            let len = out.len();
            if len >= limit {
                proof {
                    assert(self.inf.pos() <= nb);
                    lemma_work(self.inf.work@, old(self).inf.work@, credit(s0.fixed, s0.mode), self.inf.pos(), s0.pos(), input@.len(), limit as nat, body_cost());
                }
                return Err(Error::InsufficientSpace);
            }
            let step = if len > 1024 {
                len
            } else {
                1024
            };
            let grown = if limit - len > step {
                len + step
            } else {
                limit
            };
            let ghost before = out@;
            out.resize(grown, 0u8);
            proof {
                assert(out@.subrange(0, self.inf.out_pos as int) =~= before.subrange(
                    0,
                    self.inf.out_pos as int,
                ));
            }
            let ghost q = self.inf.out_pos;
            proof {
                assert(q == len);
                assert(self.inf.pos() <= nb);
            }
            proof { assert(input@ =~= input@.subrange(0, input@.len() as int)); }
            let r = run_sums(&mut self.inf, fmt, input, out.as_mut_slice(), a, b, crc);
            s = r.0;
            a = r.1;
            b = r.2;
            crc = r.3;
            proof {
                if s == Status::NeedOutput {
                    assert(self.inf.out_pos == grown);
                    assert(grown > q);
                }
            }
        }
        proof {
            let c = credit(s0.fixed, s0.mode);
            let w0 = old(self).inf.work@;
            if s == Status::Done {
                lemma_work(self.inf.work@, w0, c, nb as int, s0.pos(), input@.len(), self.inf.out_pos as nat, 2 * body_cost());
            } else {
                lemma_work(self.inf.work@, w0, c, nb as int, s0.pos(), input@.len(), self.inf.out_pos as nat, header_cost() + 2 * body_cost());
            }
            lemma_work(self.inf.work@, w0, c, nb as int, s0.pos(), input@.len(), limit as nat, header_cost() + 2 * body_cost());
        }
        if s != Status::Done {
            return Err(status_err(s));
        }
        let n = self.inf.out_pos;
        let ghost full = out@;
        out.truncate(n);
        let end = self.inf.consumed();
        proof {
            assert(out@ =~= full.subrange(0, n as int));
        }
        match check_sums(fmt, input, end, Ghost(out@), n, a, b, crc) {
            Ok(used) => Ok((out, used)),
            Err(e) => Err(e),
        }
    }
}

} // verus!

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::BadData => "invalid compressed data",
            Error::Truncated => "the input ends before the stream does",
            Error::InsufficientSpace => "the output does not fit in the space allowed",
            Error::Usage => "the call is not allowed in the current state",
        })
    }
}

impl std::error::Error for Error {}
