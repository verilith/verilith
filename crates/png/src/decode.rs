//! The top-level decoder, proven to compute `spec::decode`.
use crate::chunks::*;
use crate::geom::*;
use crate::prims::*;
use crate::spec::*;
use crate::work::Meter;
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
    let tracked mut m = Meter { n: 0 };
    container_counted(b, Tracked(&mut m))
}

/// `container_exec`, counting its steps: at most two for each byte of the
/// file (each CRC'd byte once, and the walk), and 20.
pub fn container_counted(b: &[u8], Tracked(m): Tracked<&mut Meter>) -> (r: Option<(Header, WalkX)>)
    ensures
        match container(b@) {
            Some((h, st)) => r matches Some((x, w)) && x.view() == h && w.wf(b@) && w.view(b@) == st
                && hdr_ok(h),
            None => r is None,
        },
        final(m).n <= old(m).n + 2 * b@.len() + 20,
        r matches Some((x, w)) ==> idat_cost(b@, w.idat@) <= b@.len(),
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
    proof {
        m.n = (m.n + len + 4) as nat;
    }
    if ty != 0x4948_4452 || !crc_ok(b, 8, len) {
        return None;
    }
    let h = match parse_ihdr_exec(b, 8, len) {
        Some(h) => h,
        None => return None,
    };
    match walk_exec(b, &h, 20 + len as usize, Tracked(m)) {
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
    let tracked mut m = Meter { n: 0 };
    gather_counted(b, rs, Tracked(&mut m))
}

/// `gather`, counting its steps: two walks over the ranges, and the data
/// zeroed and copied.
pub fn gather_counted(b: &[u8], rs: &Vec<(usize, usize)>, Tracked(m): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, Error>)
    requires
        ranges_ok(b@, rs@),
    ensures
        r matches Ok(v) ==> v@ == concat(b@, rs@, rs@.len()),
        r matches Err(e) ==> e != Error::Invalid,
        final(m).n <= old(m).n + 2 * rs@.len() + 2 * concat(b@, rs@, rs@.len()).len(),
{
    let ghost m0 = m.n;
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            ranges_ok(b@, rs@),
            i <= rs@.len(),
            total == concat(b@, rs@, i as nat).len(),
            m.n == m0 + i,
            m0 == old(m).n,
        decreases rs@.len() - i,
    {
        proof {
            m.n = m.n + 1;
        }
        let (_, l) = rs[i];
        if total > usize::MAX - l {
            return Err(Error::TooLarge);
        }
        total = total + l;
        i = i + 1;
    }
    let mut v = match alloc_u8(total) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    proof {
        m.n = (m.n + total) as nat;
    }
    let ghost m1 = m.n;
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
            m.n == m1 + i + at,
            m1 == m0 + rs@.len() + total,
            m0 == old(m).n,
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
        proof {
            m.n = (m.n + 1 + l) as nat;
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

fn to_vec(b: &[u8], s: usize, l: usize, Tracked(m): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, Error>)
    requires
        s + l <= b@.len(),
    ensures
        r matches Ok(v) ==> v@ == b@.subrange(s as int, s + l),
        r matches Err(e) ==> e == Error::OutOfMemory,
        final(m).n <= old(m).n + 2 * l,
{
    proof {
        m.n = (m.n + 2 * l) as nat;
    }
    let mut v = match alloc_u8(l) {
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

/// What setting up a Deflate decoder costs: more than the entries of the
/// fixed-size tables `Decompressor::new` zeroes (about 3,800).
pub open spec fn znew_cost() -> nat {
    4096
}

/// verilith-zlib's `decompress_into` for a zlib stream, with a new
/// decoder, and the steps it counts.
fn z_into(d: &[u8], out: &mut [u8]) -> (r: (Result<(usize, usize), verilith_zlib::wrap::Error>, Ghost<nat>))
    ensures
        final(out)@.len() == old(out)@.len(),
        match r.0 {
            Ok((used, n)) => n <= final(out)@.len() && verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) == Some(
                (final(out)@.subrange(0, n as int), used as int),
            ),
            Err(e) => e != verilith_zlib::wrap::Error::InsufficientSpace ==> verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) is None,
        },
        r.0 == Err::<(usize, usize), verilith_zlib::wrap::Error>(verilith_zlib::wrap::Error::InsufficientSpace) ==> (verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) matches Some((o, _)) ==> o.len() >= old(out)@.len()),
        r.1@ <= verilith_zlib::wrap::work_bound(d@.len(), old(out)@.len() as nat),
{
    let mut dz = Decompressor::new();
    let ghost z0 = dz.inf.work@;
    let ghost ol = out@.len();
    let res = dz.decompress_into(ZFormat::Zlib, d, out);
    let ghost z1 = dz.inf.work@;
    (res, Ghost(if z1 >= z0 { (z1 - z0) as nat } else { 0 }))
}

/// verilith-zlib's `decompress_vec` for a zlib stream, with a new decoder,
/// and the steps it counts.
fn z_vec(d: &[u8], limit: usize) -> (r: (Result<(Vec<u8>, usize), verilith_zlib::wrap::Error>, Ghost<nat>))
    ensures
        match r.0 {
            Ok((v, used)) => v@.len() <= limit && verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) == Some((v@, used as int)),
            Err(e) => e != verilith_zlib::wrap::Error::InsufficientSpace ==> verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) is None,
        },
        r.1@ <= verilith_zlib::wrap::work_bound(d@.len(), limit as nat),
{
    let mut dz = Decompressor::new();
    let ghost z0 = dz.inf.work@;
    let res = dz.decompress_vec(ZFormat::Zlib, d, limit);
    let ghost z1 = dz.inf.work@;
    (res, Ghost(if z1 >= z0 { (z1 - z0) as nat } else { 0 }))
}

/// The bound on `inflate_exec`'s work for `n` bytes of image data.
pub open spec fn inflate_work(n: nat) -> nat {
    300_000 * n + 80_000
}

/// `work_bound` for up to `max_output` bytes, as a number.
proof fn lemma_inflate_work(i: nat, m1: nat, m2: nat)
    requires
        m1 <= 1032 * i + 1,
        m2 <= 1032 * i + 1,
    ensures
        m1 + znew_cost() + verilith_zlib::wrap::work_bound(i, m1) + znew_cost() + verilith_zlib::wrap::work_bound(i, m2) + 3 * m2
            <= inflate_work(i),
{
    assert(verilith_zlib::inflate::fixed_cost() == 10834);
    assert(verilith_zlib::inflate::bit_cost() == 1200);
    assert(verilith_zlib::inflate::header_cost() == 21207);
    assert(verilith_zlib::inflate::body_cost() == 130);
    assert(verilith_zlib::wrap::work_bound(i, m1) == 32301 + 9600 * i + 131 * m1);
    assert(verilith_zlib::wrap::work_bound(i, m2) == 32301 + 9600 * i + 131 * m2);
    assert(132 * m1 + 134 * m2 + 19200 * i + 72794 <= 300_000 * i + 80_000) by (nonlinear_arith)
        requires
            m1 <= 1032 * i + 1,
            m2 <= 1032 * i + 1,
    ;
}

/// Decompresses the image data, which must be a zlib stream giving at
/// least `rs` bytes, and returns the first `rs`. Sets `tail`.
#[verifier::spinoff_prover]
pub fn inflate_exec(idat: &[u8], rs: u128, limit: usize, tail: &mut Tail, Tracked(m): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => v@.len() == rs && rs < limit && rs <= 1032 * idat@.len() && (zlib(idat@) matches Some((o, _)) && o.len() >= rs
                && o.subrange(0, rs as int) == v@),
            Err(Error::Invalid) => !(zlib(idat@) matches Some((o, _)) && o.len() >= rs),
            Err(_) => true,
        },
        final(m).n <= old(m).n + inflate_work(idat@.len()),
{
    let ghost m0 = m.n;
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
    let mut raw = match alloc_u8(n + 1) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let (res, Ghost(w1)) = z_into(idat, raw.as_mut_slice());
    proof {
        m.n = (m.n + n + 1 + znew_cost() + w1) as nat;
        lemma_inflate_work(idat@.len(), (n + 1) as nat, 0);
    }
    let ghost m1 = m.n;
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
            // to check the stream, and keep the first `n` bytes. No stream
            // this long gives more than `1032 * idat.len()` bytes, so a
            // limit one above that is no limit, and keeps the work linear.
            let most = 1032 * idat.len() as u128 + 1;
            let lim = if (limit as u128) < most { limit } else { most as usize };
            let (res2, Ghost(w2)) = z_vec(idat, lim);
            proof {
                // The output vector grows to at most `lim` bytes, doubling:
                // zeroing and moving it costs at most `3 * lim`.
                m.n = (m.n + znew_cost() + w2 + 3 * lim) as nat;
                lemma_inflate_work(idat@.len(), (n + 1) as nat, lim as nat);
                verilith_zlib::ilemmas::theorem_output_bound(idat@);
                reveal(verilith_zlib::wrap::spec_decompress);
            }
            match res2 {
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
pub fn parse_exec(b: &[u8], limit: usize, tail: &mut Tail) -> (r: Result<(PngX, Vec<u8>), Error>)
    ensures
        match r {
            Ok((p, raw)) => p.wf() && raw@.len() == raw_size(p.hdr.view()) && parse(b@) == Some(Png { raw: raw@, ..p.view() }),
            Err(Error::Invalid) => parse(b@) is None,
            Err(_) => true,
        },
{
    let tracked mut m = Meter { n: 0 };
    parse_counted(b, limit, tail, Tracked(&mut m))
}

/// The bound on `parse_exec`'s work for an `n`-byte file.
pub open spec fn parse_work(n: nat) -> nat {
    8 * n + 20 + inflate_work(n)
}

/// `parse_exec`, counting its steps: at most `parse_work(b.len())`.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn parse_counted(b: &[u8], limit: usize, tail: &mut Tail, Tracked(m): Tracked<&mut Meter>) -> (r: Result<(PngX, Vec<u8>), Error>)
    ensures
        match r {
            Ok((p, raw)) => p.wf() && raw@.len() == raw_size(p.hdr.view()) && raw@.len() <= 1032 * b@.len() && parse(b@) == Some(Png { raw: raw@, ..p.view() }),
            Err(Error::Invalid) => parse(b@) is None,
            Err(_) => true,
        },
        final(m).n <= old(m).n + parse_work(b@.len()),
{
    proof {
        lemma_parse_none(b@);
    }
    let ghost m0 = m.n;
    let (h, w) = match container_counted(b, Tracked(m)) {
        Some(x) => x,
        None => return Err(Error::Invalid),
    };
    let ghost st = w.view(b@);
    let idat = match gather_counted(b, &w.idat, Tracked(m)) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    proof {
        assert(idat@.len() <= b@.len());
    }
    let ghost m1 = m.n;
    let rs = raw_size_exec(&h);
    let raw = match inflate_exec(idat.as_slice(), rs, limit, tail, Tracked(m)) {
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
            match to_vec(b, s, l, Tracked(m)) {
                Ok(v) => v,
                Err(e) => return Err(e),
            }
        } else {
            Vec::new()
        },
        None => Vec::new(),
    };
    let trns = match w.trns {
        Some((s, l)) => match to_vec(b, s, l, Tracked(m)) {
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

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Invalid => "not a valid PNG file",
            Error::TooLarge => "the image needs more memory than the limit",
            Error::OutOfMemory => "out of memory",
        })
    }
}

impl std::error::Error for Error {}
