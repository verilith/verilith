//! The top-level decoder, proven to compute `spec::decode`.
use crate::chunks::*;
use crate::geom::*;
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;
use verilith_zlib::wrap::{Decompressor, Format as ZFormat};
#[cfg(verus_only)]
use verilith_zlib::spec as z;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Error {
    /// The file is not a PNG file that the specification accepts.
    Invalid,
    /// The image needs more memory than the caller's limit allows.
    TooLarge,
    /// An allocation failed.
    OutOfMemory,
}

/// Reads the signature, IHDR and the chunks up to IEND
/// (`spec::container`).
pub fn container_exec(b: &[u8]) -> (r: Option<(Header, WalkX)>)
    ensures
        match container(b@) {
            Some((h, st)) => r matches Some((x, w)) && x.view() == h && w.wf(b@) && w.view(b@) == st
                && hdr_ok(h),
            None => r is None,
        },
{
    reveal(container);
    if b.len() < 8 || !(b[0] == 137 && b[1] == 80 && b[2] == 78 && b[3] == 71 && b[4] == 13 && b[5]
        == 10 && b[6] == 26 && b[7] == 10) {
        proof {
            if b@.len() >= 8 && b@.subrange(0, 8) == signature() {
                assert(b@.subrange(0, 8)[0] == 137u8);
                assert(b@.subrange(0, 8)[1] == 80u8);
                assert(b@.subrange(0, 8)[2] == 78u8);
                assert(b@.subrange(0, 8)[3] == 71u8);
                assert(b@.subrange(0, 8)[4] == 13u8);
                assert(b@.subrange(0, 8)[5] == 10u8);
                assert(b@.subrange(0, 8)[6] == 26u8);
                assert(b@.subrange(0, 8)[7] == 10u8);
            }
        }
        return None;
    }
    proof {
        assert(b@.subrange(0, 8) =~= signature());
    }
    let (len, ty) = match frame(b, 8) {
        Some(f) => f,
        None => return None,
    };
    if ty != 0x4948_4452 || !crc_ok(b, 8, len) {
        return None;
    }
    let h = match parse_ihdr_exec(b, 8, len) {
        Some(h) => h,
        None => return None,
    };
    match walk_exec(b, &h, 20 + len as usize) {
        Some(w) => Some((h, w)),
        None => None,
    }
}

/// The IDAT data: the concatenated ranges (`WalkX::view`'s `idat`).
pub fn gather(b: &[u8], rs: &Vec<(usize, usize)>) -> (r: Result<Vec<u8>, Error>)
    requires
        ranges_ok(b@, rs@),
    ensures
        r matches Ok(v) ==> v@ == concat(b@, rs@, rs@.len()),
        r matches Err(e) ==> e != Error::Invalid,
{
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            ranges_ok(b@, rs@),
            i <= rs@.len(),
            total == concat(b@, rs@, i as nat).len(),
        decreases rs@.len() - i,
    {
        let (_, l) = rs[i];
        if total > usize::MAX - l {
            return Err(Error::TooLarge);
        }
        total = total + l;
        i = i + 1;
    }
    let mut v = match alloc_zeroed(total) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let ghost all = concat(b@, rs@, rs@.len());
    let mut i: usize = 0;
    let mut at: usize = 0;
    proof {
        assert(v@.subrange(0, 0) =~= concat(b@, rs@, 0));
    }
    while i < rs.len()
        invariant
            ranges_ok(b@, rs@),
            i <= rs@.len(),
            all == concat(b@, rs@, rs@.len()),
            total == all.len(),
            v@.len() == total,
            at == concat(b@, rs@, i as nat).len(),
            at <= total,
            v@.subrange(0, at as int) == concat(b@, rs@, i as nat),
        decreases rs@.len() - i,
    {
        let (s, l) = rs[i];
        proof {
            assert(rs@[i as int].0 + rs@[i as int].1 <= b@.len());
            lemma_concat_mono(b@, rs@, (i + 1) as nat, rs@.len());
        }
        let ghost v0 = v@;
        copy(v.as_mut_slice(), at, b, s, l);
        proof {
            assert(v@.subrange(0, at + l) =~= v0.subrange(0, at as int) + range(b@, rs@[i as int]));
        }
        i = i + 1;
        at = at + l;
    }
    proof {
        assert(v@ =~= v@.subrange(0, at as int));
    }
    Ok(v)
}

pub proof fn lemma_concat_mono(b: Seq<u8>, rs: Seq<(usize, usize)>, i: nat, n: nat)
    requires
        i <= n <= rs.len(),
    ensures
        concat(b, rs, i).len() <= concat(b, rs, n).len(),
    decreases n - i,
{
    if i < n {
        lemma_concat_mono(b, rs, i, (n - 1) as nat);
    }
}

/// The parsed file in executable form: header, palette, transparency and
/// the decompressed image data.
pub struct PngX {
    pub hdr: Header,
    pub plte: Vec<u8>,
    pub trns: Option<Vec<u8>>,
}

impl PngX {
    pub open spec fn view(&self) -> Png {
        Png {
            hdr: self.hdr.view(),
            plte: self.plte@,
            trns: match self.trns {
                Some(t) => Some(t@),
                None => None,
            },
            raw: Seq::empty(),
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& hdr_ok(self.hdr.view())
        &&& self.plte@.len() <= 768
        &&& self.trns matches Some(t) ==> trns_len_ok(self.hdr.view(), t@)
    }
}

fn to_vec(b: &[u8], s: usize, l: usize) -> (r: Result<Vec<u8>, Error>)
    requires
        s + l <= b@.len(),
    ensures
        r matches Ok(v) ==> v@ == b@.subrange(s as int, s + l),
        r matches Err(e) ==> e == Error::OutOfMemory,
{
    let mut v = match alloc_zeroed(l) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    copy(v.as_mut_slice(), 0, b, s, l);
    proof {
        assert(v@ =~= b@.subrange(s as int, s + l));
    }
    Ok(v)
}

/// What the image data held beyond the image, which the spec ignores;
/// the libpng API reports it as libpng does. Nothing is proved about it.
pub struct Tail {
    /// The zlib stream decompresses to more than the image needs.
    pub more: bool,
    /// Bytes of image data the zlib stream used.
    pub used: usize,
}

impl Tail {
    pub fn new() -> Self {
        Tail { more: false, used: 0 }
    }
}

/// Decompresses the image data, which must be a zlib stream giving at
/// least `rs` bytes, and returns the first `rs`. Sets `tail`.
#[verifier::spinoff_prover]
pub fn inflate_exec(idat: &[u8], rs: u128, limit: usize, tail: &mut Tail) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => v@.len() == rs && rs < limit && (zlib(idat@) matches Some((o, _)) && o.len() >= rs
                && o.subrange(0, rs as int) == v@),
            Err(Error::Invalid) => !(zlib(idat@) matches Some((o, _)) && o.len() >= rs),
            Err(_) => true,
        },
{
    proof {
        verilith_zlib::ilemmas::theorem_output_bound(idat@);
        reveal(zlib);
    }
    if rs > 1032 * idat.len() as u128 {
        // More image data than any zlib stream this long can produce.
        return Err(Error::Invalid);
    }
    if rs >= limit as u128 {
        return Err(Error::TooLarge);
    }
    let n = rs as usize;
    let mut raw = match alloc_zeroed(n + 1) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut d = Decompressor::new();
    let res = d.decompress_into(ZFormat::Zlib, idat, raw.as_mut_slice());
    proof {
        reveal(verilith_zlib::wrap::spec_decompress);
        reveal(zlib);
    }
    match res {
        Ok((used, m)) => {
            if m < n {
                return Err(Error::Invalid);
            }
            tail.more = m > n;
            tail.used = used;
            raw.truncate(n);
            proof {
                assert(raw@ =~= raw@.subrange(0, n as int));
            }
            Ok(raw)
        },
        Err(verilith_zlib::wrap::Error::InsufficientSpace) => {
            // More data than the image needs (rare): decompress all of it
            // to check the stream, and keep the first `n` bytes.
            let mut d2 = Decompressor::new();
            match d2.decompress_vec(ZFormat::Zlib, idat, limit) {
                Ok((mut v, used)) => {
                    if v.len() < n {
                        return Err(Error::Invalid);
                    }
                    tail.more = v.len() > n;
                    tail.used = used;
                    v.truncate(n);
                    proof {
                        assert(v@ =~= v@.subrange(0, n as int));
                    }
                    Ok(v)
                },
                Err(verilith_zlib::wrap::Error::InsufficientSpace) => Err(Error::TooLarge),
                Err(_) => Err(Error::Invalid),
            }
        },
        Err(_) => Err(Error::Invalid),
    }
}

pub proof fn lemma_container_plte(b: Seq<u8>)
    ensures
        container(b) matches Some((h, st)) ==> plte_inv(h, st) && st.phase != 0,
{
    reveal(container);
    if let Some(c) = chunk_at(b, 8) {
        if let Some(h) = parse_ihdr(chunk_data(b, 8, c.len)) {
            lemma_walk_plte(b, h, (20 + c.len) as int, walk_start());
        }
    }
}

pub proof fn lemma_parse_none(b: Seq<u8>)
    ensures
        container(b) is None ==> parse(b) is None,
        container(b) matches Some((h, st)) ==> (!(zlib(st.idat) matches Some((o, _))
            && o.len() >= raw_size(h)) ==> parse(b) is None),
{
    reveal(parse);
}

pub proof fn lemma_parse(b: Seq<u8>, h: Ihdr, st: Walk, raw: Seq<u8>)
    requires
        container(b) == Some((h, st)),
        zlib(st.idat) matches Some((o, _)) && o.len() >= raw_size(h) && o.subrange(0, raw_size(h) as int) == raw,
    ensures
        parse(b) == Some(
            Png {
                hdr: h,
                plte: if h.ct == 3 {
                    st.plte.unwrap()
                } else {
                    Seq::empty()
                },
                trns: st.trns,
                raw,
            },
        ),
{
    reveal(parse);
}

/// Parses the file and decompresses its image data (`spec::parse`).
/// `limit` bounds the decompressed data's size. Sets `tail`.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn parse_exec(b: &[u8], limit: usize, tail: &mut Tail) -> (r: Result<(PngX, Vec<u8>), Error>)
    ensures
        match r {
            Ok((p, raw)) => p.wf() && raw@.len() == raw_size(p.hdr.view()) && parse(b@) == Some(Png { raw: raw@, ..p.view() }),
            Err(Error::Invalid) => parse(b@) is None,
            Err(_) => true,
        },
{
    proof {
        lemma_parse_none(b@);
    }
    let (h, w) = match container_exec(b) {
        Some(x) => x,
        None => return Err(Error::Invalid),
    };
    let ghost st = w.view(b@);
    let idat = match gather(b, &w.idat) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let rs = raw_size_exec(&h);
    let raw = match inflate_exec(idat.as_slice(), rs, limit, tail) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let n = rs as usize;
    proof {
        assert(st.idat == idat@);
        assert(n as int == rs);
    }
    let plte = match w.plte {
        Some((s, l)) => if h.color_type == 3 {
            match to_vec(b, s, l) {
                Ok(v) => v,
                Err(e) => return Err(e),
            }
        } else {
            Vec::new()
        },
        None => Vec::new(),
    };
    let trns = match w.trns {
        Some((s, l)) => match to_vec(b, s, l) {
            Ok(v) => Some(v),
            Err(e) => return Err(e),
        },
        None => None,
    };
    proof {
        lemma_container_plte(b@);
        assert(container(b@) == Some((h.view(), st)));
        assert(st.idat == idat@);
        lemma_parse(b@, h.view(), st, raw@);
        assert(plte@ == if h.view().ct == 3 {
            st.plte.unwrap()
        } else {
            Seq::<u8>::empty()
        });
    }
    Ok((PngX { hdr: h, plte, trns }, raw))
}

} // verus!
