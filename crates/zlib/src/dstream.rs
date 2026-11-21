//! Streaming compression: input in pieces of any size, output taken as it
//! is produced, with zlib's flush points, in bounded memory. The theorem
//! (`Deflater::finish`) is the one-shot compressor's: all the bytes handed
//! out decompress, in the stream's format, to all the input.
//!
//! The deflater keeps a window of recent input: the 32 KiB that matches may
//! reach back into, then the input not yet compressed. Tokens only refer
//! back into the window, so they expand the same after the whole output
//! (`dlemmas::lemma_expand_shift`).
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use crate::checksum::{adler_from, crc_from, lemma_adler_append, lemma_adler_closed, lemma_adler_from, lemma_crc_append, lemma_crc_from};
use crate::deflate::*;
#[cfg(verus_only)]
use crate::dlemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
use crate::wrap::Format;
use vstd::prelude::*;

verus! {

/// Pending input that starts a block when not flushing.
pub const BLOCK: usize = 65536;

/// Input taken in at a time, so the window stays small.
pub const CHUNK: usize = 262144;

/// The most the window holds.
pub const LIMIT: usize = 2 * 32768 + BLOCK + CHUNK;

/// zlib's flush modes short of `Z_FINISH` (see `Deflater::finish`).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Flush {
    /// Compress when enough input has gathered (`Z_NO_FLUSH`).
    None,
    /// End the current block (`Z_BLOCK`).
    Block,
    /// Make all input so far decodable and byte-align with an empty stored
    /// block (`Z_SYNC_FLUSH`, `Z_PARTIAL_FLUSH`).
    Sync,
    /// As `Sync`, and forget the history so decoding can restart here
    /// (`Z_FULL_FLUSH`).
    Full,
}

/// A stream's header bytes are well-formed for its format.
pub open spec fn head_ok(fmt: Format, h: Seq<u8>) -> bool {
    match fmt {
        Format::Raw => h.len() == 0,
        Format::Zlib => {
            &&& h.len() == 2
            &&& h[0] as nat % 16 == 8
            &&& h[0] as nat / 16 <= 7
            &&& (h[0] as nat * 256 + h[1] as nat) % 31 == 0
            &&& (h[1] as nat / 32) % 2 == 0
        },
        Format::Gzip => h.len() == 10 && h[0] == 31 && h[1] == 139 && h[2] == 8 && h[3] == 0,
    }
}

/// `head_ok`, for a stream after the preset dictionary `pre` (none when
/// empty): a zlib header then has FDICT set and names the dictionary's
/// Adler-32 (RFC 1950 2.2); raw DEFLATE has no header; gzip has no
/// dictionaries.
pub open spec fn head_ok_d(fmt: Format, h: Seq<u8>, pre: Seq<u8>) -> bool {
    if pre.len() == 0 {
        head_ok(fmt, h)
    } else {
        match fmt {
            Format::Raw => h.len() == 0,
            Format::Zlib => {
                &&& h.len() == 6
                &&& h[0] as nat % 16 == 8
                &&& h[0] as nat / 16 <= 7
                &&& (h[0] as nat * 256 + h[1] as nat) % 31 == 0
                &&& (h[1] as nat / 32) % 2 == 1
                &&& be32(h, 2) == adler32(pre)
            },
            Format::Gzip => false,
        }
    }
}

/// What decompressing `b` in format `fmt` with the preset dictionary `dict`
/// gives (`spec::inflate_dict`, `spec::zlib_decompress_dict`); with no
/// dictionary, `spec_decompress`.
pub open spec fn spec_decompress_dict(fmt: Format, b: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int)> {
    if dict.len() == 0 {
        crate::wrap::spec_decompress(fmt, b)
    } else {
        match fmt {
            Format::Raw => inflate_dict(b, dict),
            Format::Zlib => zlib_decompress_dict(b, dict),
            Format::Gzip => None,
        }
    }
}

/// `s` is DEFLATE blocks, none of them final, ending on a byte boundary,
/// that add `data` to the output `pre`: whatever bytes follow `s`, decoding
/// from its start after `pre` is decoding from its end after `pre + data`.
#[verifier::opaque]
pub open spec fn is_piece(s: Seq<u8>, pre: Seq<u8>, data: Seq<u8>) -> bool {
    forall|t: Seq<u8>| #[trigger] inflate_blocks(s + t, 0, pre) == inflate_blocks(s + t, 8 * s.len() as int, pre + data)
}

/// A stream's header: nothing for raw DEFLATE, two bytes for zlib (the
/// window size and the level, RFC 1950 2.2), ten for gzip.
pub fn header(fmt: Format, level: u32, wbits: u32) -> (r: Vec<u8>)
    requires
        8 <= wbits <= 15,
        level <= 9,
    ensures
        head_ok(fmt, r@),
{
    match fmt {
        Format::Raw => Vec::new(),
        Format::Zlib => {
            let cmf: u8 = ((wbits - 8) * 16 + 8) as u8;
            let lv: u32 = if level <= 1 {
                0
            } else if level <= 5 {
                1
            } else if level == 6 {
                2
            } else {
                3
            };
            let h0: u32 = cmf as u32 * 256 + lv * 64;
            let flg: u32 = lv * 64 + 31 - h0 % 31;
            proof {
                assert((cmf as nat * 256 + flg as nat) % 31 == 0) by (nonlinear_arith)
                    requires
                        h0 == cmf as u32 * 256 + lv * 64,
                        flg == lv * 64 + 31 - h0 % 31,
                ;
                assert((flg as nat / 32) % 2 == 0) by (nonlinear_arith)
                    requires
                        flg == lv * 64 + 31 - h0 % 31,
                        lv <= 3,
                ;
            }
            let mut v = Vec::new();
            v.push(cmf);
            v.push(flg as u8);
            v
        },
        Format::Gzip => {
            let xfl: u8 = if level == 1 {
                4
            } else if level == 9 {
                2
            } else {
                0
            };
            let mut v = Vec::new();
            v.push(31u8);
            v.push(139u8);
            v.push(8u8);
            v.push(0u8);
            v.push(0u8);
            v.push(0u8);
            v.push(0u8);
            v.push(0u8);
            v.push(xfl);
            v.push(255u8);
            v
        },
    }
}

#[derive(Clone)]
pub struct Deflater {
    enc: Encoder,
    m: Matcher,
    /// `m` is a placeholder, to be sized when the first block is
    /// compressed: to the input if that block is the last, else in full.
    fresh: bool,
    level: u32,
    /// Matches reach back at most `2^wbits` bytes, the window the header
    /// declares.
    wbits: u32,
    /// Recent input; `win[pend..]` is not compressed yet.
    win: Vec<u8>,
    pend: usize,
    fmt: Format,
    a: u32,
    b: u32,
    crc: u32,
    isize: u32,
    /// All the input so far.
    all: Ghost<Seq<u8>>,
    /// The preset dictionary (empty if none): the history before the input.
    pre: Ghost<Seq<u8>>,
}

impl Deflater {
    /// All the input so far.
    pub closed spec fn input(&self) -> Seq<u8> {
        self.all@
    }

    /// All the output handed out so far.
    pub closed spec fn sent(&self) -> Seq<u8> {
        self.enc.bw.sent()
    }

    pub closed spec fn format(&self) -> Format {
        self.fmt
    }

    /// Matches reach back at most `2^window_bits()` bytes.
    pub closed spec fn window_bits(&self) -> u32 {
        self.wbits
    }

    /// The preset dictionary, empty if none.
    pub closed spec fn dict(&self) -> Seq<u8> {
        self.pre@
    }

    /// The dictionary, then the input: what matches may refer back into.
    closed spec fn hist(&self) -> Seq<u8> {
        self.pre@ + self.all@
    }

    /// Everything but "no final block yet".
    closed spec fn core(&self) -> bool {
        &&& self.enc.inv()
        &&& self.m.wf()
        &&& 8 <= self.wbits <= 15
        &&& self.m.window() == (1usize << self.wbits) as nat
        &&& self.level <= 9
        &&& self.pend <= self.win@.len()
        &&& self.win@.len() <= LIMIT
        &&& self.win@.len() <= self.hist().len()
        &&& self.win@ == self.hist().subrange(self.hist().len() - self.win@.len(), self.hist().len() as int)
        &&& self.enc.out() == self.hist().subrange(0, self.hist().len() - (self.win@.len() - self.pend))
        &&& self.enc.base@ == self.pre@
        &&& (self.a as nat, self.b as nat) == adler_from(1, 0, self.all@)
        &&& self.a < 65521
        &&& self.b < 65521
        &&& self.crc == crc_from(0xffff_ffff, self.all@)
        &&& self.isize as nat == self.all@.len() % 0x1_0000_0000
        &&& head_ok_d(self.fmt, self.enc.head@, self.pre@)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.core()
        &&& !self.enc.done@
    }

    /// Everything taken in is compressed and the output ends on a byte
    /// boundary, as after a `Sync` flush.
    pub closed spec fn synced(&self) -> bool {
        &&& self.pend == self.win@.len()
        &&& self.enc.bw.bits().len() % 8 == 0
    }

    /// A deflater for `fmt` at zlib's `level` (0 to 9; above 9 means 9),
    /// with matches reaching back at most `2^wbits` bytes (8 to 15; the
    /// zlib header says so).
    pub fn new(fmt: Format, level: u32, wbits: u32) -> (r: Deflater)
        requires
            8 <= wbits <= 15,
        ensures
            r.wf(),
            r.input() == Seq::<u8>::empty(),
            r.sent() == Seq::<u8>::empty(),
            r.format() == fmt,
            r.window_bits() == wbits,
            r.dict() == Seq::<u8>::empty(),
    {
        let lv = if level > 9 { 9 } else { level };
        let mut r = Self::with_matcher(fmt, level, wbits, Matcher::new_for(lv, 0));
        r.fresh = true;
        r
    }

    /// `new`, for a stream of at most `n` bytes in all: the match tables
    /// shrink to fit, as `compress_into`'s do. More input is still
    /// compressed correctly, only with fewer matches found.
    pub fn new_sized(fmt: Format, level: u32, wbits: u32, n: usize) -> (r: Deflater)
        requires
            8 <= wbits <= 15,
        ensures
            r.wf(),
            r.input() == Seq::<u8>::empty(),
            r.sent() == Seq::<u8>::empty(),
            r.format() == fmt,
            r.window_bits() == wbits,
            r.dict() == Seq::<u8>::empty(),
    {
        let lv = if level > 9 { 9 } else { level };
        Self::with_matcher(fmt, level, wbits, Matcher::new_for(lv, n))
    }

    fn with_matcher(fmt: Format, level: u32, wbits: u32, m: Matcher) -> (r: Deflater)
        requires
            8 <= wbits <= 15,
            m.wf(),
        ensures
            r.wf(),
            r.input() == Seq::<u8>::empty(),
            r.sent() == Seq::<u8>::empty(),
            r.format() == fmt,
            r.window_bits() == wbits,
            r.dict() == Seq::<u8>::empty(),
    {
        let level = if level > 9 { 9 } else { level };
        let hdr = header(fmt, level, wbits);
        let enc = Encoder::with_header(hdr.as_slice(), 65536);
        let mut m = m;
        m.set_window(wbits);
        let r = Deflater {
            enc,
            m,
            fresh: false,
            level,
            wbits,
            win: Vec::new(),
            pend: 0,
            fmt,
            a: 1,
            b: 0,
            crc: 0xffff_ffff,
            isize: 0,
            all: Ghost(Seq::empty()),
            pre: Ghost(Seq::empty()),
        };
        proof {
            assert(r.hist() =~= Seq::<u8>::empty());
            assert(r.win@ =~= r.hist().subrange(0, 0));
            assert(r.enc.out() =~= r.hist().subrange(0, 0));
        }
        r
    }

    /// A deflater after the preset dictionary `dict` (zlib's
    /// `deflateSetDictionary` before any input): matches may refer back into
    /// its last 32 KiB. A zlib stream's header then has FDICT set and names
    /// `adler32(dict)`. Gzip streams have no dictionaries.
    pub fn new_with_dict(fmt: Format, level: u32, wbits: u32, dict: &[u8]) -> (r: Deflater)
        requires
            8 <= wbits <= 15,
            fmt != Format::Gzip,
            dict@.len() > 0,
        ensures
            r.wf(),
            r.input() == Seq::<u8>::empty(),
            r.sent() == Seq::<u8>::empty(),
            r.format() == fmt,
            r.dict() == dict@,
            r.window_bits() == wbits,
    {
        let level = if level > 9 { 9 } else { level };
        let mut hdr: Vec<u8> = Vec::new();
        if fmt == Format::Zlib {
            let cmf: u8 = ((wbits - 8) * 16 + 8) as u8;
            let lv: u32 = if level <= 1 {
                0
            } else if level <= 5 {
                1
            } else if level == 6 {
                2
            } else {
                3
            };
            let h0: u32 = cmf as u32 * 256 + lv * 64 + 32;
            let flg: u32 = lv * 64 + 32 + 31 - h0 % 31;
            proof {
                assert((cmf as nat * 256 + flg as nat) % 31 == 0) by (nonlinear_arith)
                    requires
                        h0 == cmf as u32 * 256 + lv * 64 + 32,
                        flg == lv * 64 + 32 + 31 - h0 % 31,
                ;
                assert((flg as nat / 32) % 2 == 1 && flg < 256) by (nonlinear_arith)
                    requires
                        flg == lv * 64 + 32 + 31 - h0 % 31,
                        lv <= 3,
                ;
            }
            let (a, b) = verilith_core::checksum::cpu::adler32_update(1, 0, dict);
            proof {
                lemma_adler_closed(1, 0, dict@);
                lemma_adler_from(dict@);
                assert((b << 16u32) | a == b * 65536 + a) by (bit_vector)
                    requires
                        a < 65521,
                        b < 65521,
                ;
            }
            let t = be_bytes((b << 16) | a);
            hdr.push(cmf);
            hdr.push(flg as u8);
            hdr.push(t[0]);
            hdr.push(t[1]);
            hdr.push(t[2]);
            hdr.push(t[3]);
            proof {
                assert(hdr@[2] == t@[0] && hdr@[3] == t@[1] && hdr@[4] == t@[2] && hdr@[5] == t@[3]);
                assert(be32(hdr@, 2) == be32(t@, 0));
            }
        }
        let enc = Encoder::with_header_base(hdr.as_slice(), 65536, Ghost(dict@));
        let mut m = Matcher::new(level);
        m.set_window(wbits);
        let n = dict.len();
        let start = if n > crate::deflate::WSIZE { n - crate::deflate::WSIZE } else { 0 };
        let mut win: Vec<u8> = Vec::new();
        verilith_core::prims::extend(&mut win, vstd::slice::slice_subrange(dict, start, n));
        let wn = win.len();
        m.prime(win.as_slice());
        let r = Deflater {
            enc,
            m,
            fresh: false,
            level,
            wbits,
            win,
            pend: wn,
            fmt,
            a: 1,
            b: 0,
            crc: 0xffff_ffff,
            isize: 0,
            all: Ghost(Seq::empty()),
            pre: Ghost(dict@),
        };
        proof {
            assert(r.hist() =~= dict@);
            assert(r.win@ =~= r.hist().subrange(r.hist().len() - r.win@.len(), r.hist().len() as int));
            assert(r.enc.out() =~= r.hist().subrange(0, r.hist().len() - (r.win@.len() - r.pend)));
        }
        r
    }

    /// Adds `chunk` to the input and the window.
    fn absorb(&mut self, chunk: &[u8])
        requires
            old(self).wf(),
            old(self).win@.len() + chunk@.len() <= LIMIT,
        ensures
            final(self).wf(),
            final(self).input() == old(self).input() + chunk@,
            final(self).sent() == old(self).sent(),
            final(self).fmt == old(self).fmt,
            final(self).pre == old(self).pre,
            final(self).win@.len() == old(self).win@.len() + chunk@.len(),
            final(self).pend == old(self).pend,
    {
        let ghost all0 = self.all@;
        let ghost w0 = self.win@;
        let (a, b) = verilith_core::checksum::cpu::adler32_update(self.a, self.b, chunk);
        proof {
            lemma_adler_closed(self.a as nat, self.b as nat, chunk@);
            lemma_adler_append(1, 0, all0, chunk@);
        }
        self.a = a;
        self.b = b;
        self.crc = verilith_core::checksum::cpu::crc32_update(self.crc, chunk);
        proof {
            lemma_crc_append(0xffff_ffff, all0, chunk@);
            vstd::arithmetic::div_mod::lemma_add_mod_noop(all0.len() as int, chunk@.len() as int, 0x1_0000_0000);
        }
        self.isize = ((self.isize as u64 + (chunk.len() as u64 % 0x1_0000_0000)) % 0x1_0000_0000) as u32;
        verilith_core::prims::extend(&mut self.win, chunk);
        self.all = Ghost(all0 + chunk@);
        proof {
            let all = self.hist();
            let h0 = self.pre@ + all0;
            assert(all =~= h0 + chunk@);
            assert(self.win@ =~= all.subrange(all.len() - self.win@.len(), all.len() as int));
            assert(all.subrange(0, all.len() - (self.win@.len() - self.pend)) =~= h0.subrange(0, h0.len() - (w0.len() - self.pend)));
        }
    }

    /// Compresses one block's worth from `pend`, as the final block if
    /// `fin` and it reaches the end of the window.
    fn step(&mut self, fin: bool)
        requires
            old(self).wf(),
            old(self).pend < old(self).win@.len(),
        ensures
            final(self).core(),
            final(self).pend > old(self).pend,
            final(self).enc.done@ == (fin && final(self).pend == final(self).win@.len()),
            final(self).all == old(self).all,
            final(self).pre == old(self).pre,
            final(self).win == old(self).win,
            final(self).fmt == old(self).fmt,
            final(self).sent() == old(self).sent(),
    {
        let ghost all = self.hist();
        let ghost w = self.win@;
        let ghost p = all.subrange(0, all.len() - w.len());
        let ghost s = self.pend as int;
        proof {
            assert(p + w.subrange(0, s) =~= all.subrange(0, all.len() - (w.len() - s)));
        }
        let n = self.win.len();
        if self.level == 0 {
            let e = if n - self.pend > 65535 { self.pend + 65535 } else { n };
            let raw = vstd::slice::slice_subrange(self.win.as_slice(), self.pend, e);
            emit_stored(&mut self.enc, raw, fin && e == n);
            proof {
                assert((p + w.subrange(0, s)) + w.subrange(s, e as int) =~= p + w.subrange(0, e as int));
            }
            self.pend = e;
        } else {
            // At most one token per byte, so a short input needs few.
            let cap = if n - self.pend < crate::deflate::MAX_TOKS - 3 { n - self.pend + 3 } else { crate::deflate::MAX_TOKS };
            let mut toks: Vec<u32> = Vec::with_capacity(cap);
            let mut fr = crate::deflate::Freqs::new();
            if self.fresh {
                // A one-shot stream (the whole input, then finish) gets
                // tables to fit, as `new_sized` would give it.
                self.m = if fin { Matcher::new_for(self.level, n - self.pend) } else { Matcher::new(self.level) };
                self.m.set_window(self.wbits);
                self.fresh = false;
            }
            let e = self.m.fill(self.win.as_slice(), self.pend, &mut toks, &mut fr, cap - 3);
            // Every match stays inside the window the header declares.
            assert(forall|j: int| 0 <= j < toks@.len() ==> #[trigger] crate::deflate::tok_within(
                toks@[j],
                (1usize << self.wbits) as nat,
            ));
            let raw = vstd::slice::slice_subrange(self.win.as_slice(), self.pend, e);
            proof {
                lemma_expand_shift(p, w.subrange(0, s), toks@);
                assert(p + w.subrange(0, e as int) =~= (p + w.subrange(0, s)) + w.subrange(s, e as int));
            }
            emit_block(&mut self.enc, toks.as_slice(), &fr, raw, fin && e == n);
            self.pend = e;
        }
        proof {
            let e = self.pend as int;
            assert(p + w.subrange(0, e) =~= all.subrange(0, all.len() - (w.len() - e)));
        }
    }

    /// Compresses all pending input; the last block is final if `fin`.
    fn compress_pending(&mut self, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).core(),
            final(self).enc.done@ == fin,
            final(self).pend == final(self).win@.len(),
            final(self).all == old(self).all,
            final(self).pre == old(self).pre,
            final(self).win == old(self).win,
            final(self).fmt == old(self).fmt,
            final(self).sent() == old(self).sent(),
    {
        let mut ended = false;
        while self.pend < self.win.len()
            invariant
                self.core(),
                ended == self.enc.done@,
                ended ==> fin && self.pend == self.win@.len(),
                self.all == old(self).all,
                self.pre == old(self).pre,
                self.win == old(self).win,
                self.fmt == old(self).fmt,
                self.sent() == old(self).sent(),
            decreases self.win@.len() - self.pend,
        {
            self.step(fin);
            ended = fin && self.pend == self.win.len();
        }
        if fin && !ended {
            let ghost o = self.enc.out();
            let empty: [u8; 0] = [];
            emit_stored(&mut self.enc, &empty, true);
            proof {
                assert(o + empty@ =~= o);
            }
        }
    }

    /// Drops window bytes no match can reach any more.
    fn slide(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).all == old(self).all,
            final(self).pre == old(self).pre,
            final(self).fmt == old(self).fmt,
            final(self).sent() == old(self).sent(),
            final(self).win@.len() <= old(self).win@.len(),
            final(self).win@.len() - final(self).pend == old(self).win@.len() - old(self).pend,
            final(self).pend <= 2 * crate::deflate::WSIZE,
    {
        if self.pend > 2 * crate::deflate::WSIZE {
            let k = (self.pend - crate::deflate::WSIZE) / crate::deflate::WSIZE * crate::deflate::WSIZE;
            proof {
                assert(k <= self.pend - crate::deflate::WSIZE) by (nonlinear_arith)
                    requires
                        k == (self.pend - 32768) / 32768 * 32768,
                        self.pend > 65536,
                ;
                assert(self.pend - k <= 2 * crate::deflate::WSIZE) by (nonlinear_arith)
                    requires
                        k == (self.pend - 32768) / 32768 * 32768,
                        self.pend > 65536,
                ;
            }
            let ghost w0 = self.win@;
            let ghost all = self.hist();
            let n = self.win.len();
            let rest = vstd::slice::slice_subrange(self.win.as_slice(), k, n);
            let mut nw: Vec<u8> = Vec::new();
            verilith_core::prims::extend(&mut nw, rest);
            self.win = nw;
            self.pend = self.pend - k;
            self.m.slide(k);
            proof {
                assert(self.win@ =~= all.subrange(all.len() - self.win@.len(), all.len() as int));
            }
        }
    }

    /// Compresses while a block's worth is pending, then slides.
    fn settle(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).all == old(self).all,
            final(self).pre == old(self).pre,
            final(self).fmt == old(self).fmt,
            final(self).sent() == old(self).sent(),
            final(self).pend <= 2 * crate::deflate::WSIZE,
            final(self).win@.len() - final(self).pend < BLOCK,
    {
        while self.win.len() - self.pend >= BLOCK
            invariant
                self.wf(),
                self.all == old(self).all,
                self.pre == old(self).pre,
                self.fmt == old(self).fmt,
                self.sent() == old(self).sent(),
            decreases self.win@.len() - self.pend,
        {
            self.step(false);
        }
        self.slide();
    }

    /// Takes in `input` and compresses as `flush` asks.
    pub fn write(&mut self, input: &[u8], flush: Flush)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).input() == old(self).input() + input@,
            final(self).sent() == old(self).sent(),
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        let n = input.len();
        let mut i: usize = 0;
        proof {
            assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
        }
        self.settle();
        while i < n
            invariant
                self.wf(),
                i <= n,
                n == input@.len(),
                self.all@ == old(self).all@ + input@.subrange(0, i as int),
                self.pre == old(self).pre,
                self.sent() == old(self).sent(),
                self.fmt == old(self).fmt,
                self.pend <= 2 * crate::deflate::WSIZE,
                self.win@.len() - self.pend < BLOCK,
            decreases n - i,
        {
            let c = if n - i > CHUNK { CHUNK } else { n - i };
            let chunk = vstd::slice::slice_subrange(input, i, i + c);
            let ghost all0 = self.all@;
            self.absorb(chunk);
            proof {
                assert(all0 + chunk@ =~= old(self).all@ + input@.subrange(0, (i + c) as int));
            }
            self.settle();
            i = i + c;
        }
        if flush != Flush::None {
            self.compress_pending(false);
            if flush != Flush::Block {
                let ghost o = self.enc.out();
                let empty: [u8; 0] = [];
                emit_stored(&mut self.enc, &empty, false);
                proof {
                    assert(o + empty@ =~= o);
                }
                if flush == Flush::Full {
                    self.m = Matcher::new(self.level);
                    self.m.set_window(self.wbits);
                    proof {
                        let all = self.hist();
                        assert(Seq::<u8>::empty() =~= all.subrange(all.len() as int, all.len() as int));
                    }
                    self.win = Vec::new();
                    self.pend = 0;
                }
            }
        }
    }

    /// A `Sync` flush: compresses what is pending and byte-aligns with an
    /// empty stored block.
    fn sync(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).synced(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent(),
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        self.compress_pending(false);
        let ghost o = self.enc.out();
        let empty: [u8; 0] = [];
        emit_stored(&mut self.enc, &empty, false);
        proof {
            assert(o + empty@ =~= o);
        }
    }

    /// Compresses `input` as a stream of its own that does not end: blocks,
    /// none final, closed by a `Sync` flush. Such pieces, each made after
    /// the output of the ones before it, join into one stream (`par`).
    pub fn piece(mut self, input: &[u8]) -> (r: Vec<u8>)
        requires
            self.wf(),
            self.format() == Format::Raw,
            self.input() == Seq::<u8>::empty(),
            self.sent() == Seq::<u8>::empty(),
        ensures
            is_piece(r@, self.dict(), input@),
    {
        let ghost pre = self.pre@;
        self.write(input, Flush::None);
        self.sync();
        let r = self.enc.bw.take();
        proof {
            reveal(is_piece);
            let w = self.enc.bw.bits();
            self.enc.bw.lemma_whole();
            assert(Seq::<u8>::empty() + r@ =~= r@);
            assert(Seq::<u8>::empty() + input@ =~= input@);
            let h = self.hist();
            assert(h.subrange(0, h.len() as int) =~= h);
            assert(self.enc.out() == pre + input@);
            lemma_enc_piece(r@, w, self.enc.bs@, self.enc.ps@, self.enc.os@);
        }
        r
    }

    /// Changes the level (0 to 9) for the input still to come, ending the
    /// current block first as zlib's `deflateParams` does.
    pub fn set_level(&mut self, level: u32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent(),
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        self.compress_pending(false);
        let level = if level > 9 { 9 } else { level };
        self.level = level;
        self.m.set_level(level);
    }

    /// Hands out the output produced so far.
    pub fn take(&mut self) -> (r: Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent() + r@,
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        self.enc.bw.take()
    }

    /// Compresses the rest and ends the stream; returns the output not yet
    /// handed out. Everything handed out decompresses to all the input.
    pub fn finish(self) -> (r: Vec<u8>)
        requires
            self.wf(),
        ensures
            spec_decompress_dict(self.format(), self.sent() + r@, self.dict()) == Some((self.input(), (self.sent() + r@).len() as int)),
            self.dict().len() == 0 ==> crate::wrap::spec_decompress(self.format(), self.sent() + r@) == Some((self.input(), (self.sent() + r@).len() as int)),
    {
        self.finish_keep().0
    }

    /// `finish`, also handing back the fixed codes for another stream.
    pub fn finish_keep(mut self) -> (r: (Vec<u8>, Option<FixedCodes>))
        requires
            self.wf(),
        ensures
            spec_decompress_dict(self.format(), self.sent() + r.0@, self.dict()) == Some((self.input(), (self.sent() + r.0@).len() as int)),
            self.dict().len() == 0 ==> crate::wrap::spec_decompress(self.format(), self.sent() + r.0@) == Some((self.input(), (self.sent() + r.0@).len() as int)),
    {
        self.compress_pending(true);
        let ghost all = self.all@;
        let ghost pre = self.pre@;
        let ghost out = self.enc.out();
        let ghost g = self.enc.bw.sent();
        let ghost head = self.enc.head@;
        proof {
            assert(out =~= pre + all);
        }
        let mut tail: Vec<u8> = Vec::new();
        match self.fmt {
            Format::Raw => {},
            Format::Zlib => {
                let a = self.a;
                let b = self.b;
                proof {
                    lemma_adler_from(all);
                    assert((b << 16u32) | a == b * 65536 + a) by (bit_vector)
                        requires
                            a < 65521,
                            b < 65521,
                    ;
                }
                let t = be_bytes((b << 16) | a);
                tail.push(t[0]);
                tail.push(t[1]);
                tail.push(t[2]);
                tail.push(t[3]);
                proof {
                    assert(tail@ =~= t@);
                }
            },
            Format::Gzip => {
                proof {
                    lemma_crc_from(all);
                }
                let c = le_bytes(!self.crc);
                let l = le_bytes(self.isize);
                tail.push(c[0]);
                tail.push(c[1]);
                tail.push(c[2]);
                tail.push(c[3]);
                tail.push(l[0]);
                tail.push(l[1]);
                tail.push(l[2]);
                tail.push(l[3]);
                proof {
                    assert(tail@.subrange(0, 4) =~= c@);
                    assert(tail@.subrange(4, 8) =~= l@);
                }
            },
        }
        let ghost tl = tail@;
        let fmt = self.fmt;
        let fx = self.enc.fx.0.take();
        let r = self.enc.finish_tail(tail.as_slice());
        proof {
            if pre.len() == 0 {
                assert(pre + all =~= all);
                assert(pre =~= Seq::<u8>::empty());
                lemma_finish(fmt, g + r@, head, tl, all);
            } else {
                lemma_finish_dict(fmt, g + r@, head, tl, pre, all);
            }
        }
        (r, fx)
    }

    /// Hands the deflater fixed codes built by another stream.
    pub fn give_fx(&mut self, f: Option<FixedCodes>)
        ensures
            final(self).wf() == old(self).wf(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent(),
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        self.enc.fx = FxSlot(f);
    }

    /// Takes back the deflater's fixed codes, if it built them.
    pub fn take_fx(&mut self) -> (r: Option<FixedCodes>)
        ensures
            final(self).wf() == old(self).wf(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent(),
            final(self).format() == old(self).format(),
            final(self).dict() == old(self).dict(),
    {
        self.enc.fx.0.take()
    }
}

/// What a finished stream decompresses to.
#[verifier::spinoff_prover]
pub proof fn lemma_finish(fmt: Format, t: Seq<u8>, head: Seq<u8>, tail: Seq<u8>, all: Seq<u8>)
    requires
        head_ok(fmt, head),
        t.len() >= head.len(),
        t.subrange(0, head.len() as int) == head,
        match inflate_blocks(t, 8 * head.len() as int, Seq::empty()) {
            Some((e, o)) => o == all && 0 <= e && (e + 7) / 8 + tail.len() == t.len() && t.subrange((e + 7) / 8, t.len() as int) == tail,
            None => false,
        },
        fmt == Format::Raw ==> tail.len() == 0,
        fmt == Format::Zlib ==> tail.len() == 4 && be32(tail, 0) == adler32(all),
        fmt == Format::Gzip ==> tail.len() == 8 && le32(tail, 0) == crc32(all) as nat && le32(tail, 4) == all.len() % 0x1_0000_0000,
    ensures
        crate::wrap::spec_decompress(fmt, t) == Some((all, t.len() as int)),
{
    reveal(crate::wrap::spec_decompress);
    let (e, o) = inflate_blocks(t, 8 * head.len() as int, Seq::empty()).unwrap();
    let i = (e + 7) / 8;
    assert forall|j: int| 0 <= j < tail.len() implies #[trigger] t[i + j] == tail[j] by {
        assert(t[i + j] == t.subrange(i, t.len() as int)[j]);
    }
    assert forall|j: int| 0 <= j < head.len() implies #[trigger] t[j] == head[j] by {
        assert(t[j] == t.subrange(0, head.len() as int)[j]);
    }
    match fmt {
        Format::Raw => {},
        Format::Zlib => {
            assert(t[0] == head[0] && t[1] == head[1]);
            assert(be32(t, i) == be32(tail, 0));
        },
        Format::Gzip => {
            assert(t[0] == head[0] && t[1] == head[1] && t[2] == head[2] && t[3] == head[3]);
            assert(gzip_header(t) == Some(10int));
            assert(le32(t, i) == le32(tail, 0));
            assert(le32(t, i + 4) == le32(tail, 4));
        },
    }
}

/// What a finished stream after a preset dictionary decompresses to.
pub proof fn lemma_finish_dict(fmt: Format, t: Seq<u8>, head: Seq<u8>, tail: Seq<u8>, pre: Seq<u8>, all: Seq<u8>)
    requires
        pre.len() > 0,
        head_ok_d(fmt, head, pre),
        t.len() >= head.len(),
        t.subrange(0, head.len() as int) == head,
        match inflate_blocks(t, 8 * head.len() as int, pre) {
            Some((e, o)) => o == pre + all && 0 <= e && (e + 7) / 8 + tail.len() == t.len() && t.subrange((e + 7) / 8, t.len() as int) == tail,
            None => false,
        },
        fmt == Format::Raw ==> tail.len() == 0,
        fmt == Format::Zlib ==> tail.len() == 4 && be32(tail, 0) == adler32(all),
    ensures
        spec_decompress_dict(fmt, t, pre) == Some((all, t.len() as int)),
{
    let (e, o) = inflate_blocks(t, 8 * head.len() as int, pre).unwrap();
    let i = (e + 7) / 8;
    assert(o.subrange(0, pre.len() as int) =~= pre);
    assert(o.subrange(pre.len() as int, o.len() as int) =~= all);
    assert forall|j: int| 0 <= j < tail.len() implies #[trigger] t[i + j] == tail[j] by {
        assert(t[i + j] == t.subrange(i, t.len() as int)[j]);
    }
    assert forall|j: int| 0 <= j < head.len() implies #[trigger] t[j] == head[j] by {
        assert(t[j] == t.subrange(0, head.len() as int)[j]);
    }
    match fmt {
        Format::Raw => {},
        Format::Zlib => {
            assert(t[0] == head[0] && t[1] == head[1]);
            assert(t[2] == head[2] && t[3] == head[3] && t[4] == head[4] && t[5] == head[5]);
            assert(be32(t, 2) == be32(head, 2));
            assert(be32(t, i) == be32(tail, 0));
        },
        Format::Gzip => {},
    }
}

} // verus!

impl Deflater {
    /// The check value of the input so far: Adler-32 for zlib, CRC-32 for
    /// gzip, as zlib reports it in `z_stream.adler`.
    pub fn check(&self) -> u32 {
        match self.fmt {
            Format::Gzip => !self.crc,
            _ => (self.b << 16) | self.a,
        }
    }

    /// Output bytes and bits produced but not yet taken.
    pub fn pending(&self) -> (usize, u32) {
        (self.enc.bw.pending_bytes(), self.enc.bw.pending_bits())
    }
}
