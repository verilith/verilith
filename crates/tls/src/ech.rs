//! Encrypted Client Hello on the server (RFC 9849), proven to compute
//! `spec_ech`: the outer encrypted_client_hello extension, the additional
//! data ClientHelloInner was sealed with, ClientHelloInner from the
//! decrypted EncodedClientHelloInner, and the acceptance confirmation.
//! The decryption itself (HPKE) is the provider's (`crypto::ech_opened`).
use crate::hello::*;
use crate::keys::*;
use crate::messages::put;
use crate::spec::*;
use crate::spec_ech::*;
use crate::spec_keys::*;
use crate::spec_server::*;
use alloc::vec::Vec;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// An outer ECHClientHello (`SpecEchOuter`).
pub struct EchOuter {
    pub kdf: u16,
    pub aead: u16,
    pub config_id: u8,
    pub enc: Span,
    pub payload: Span,
}

impl EchOuter {
    pub open spec fn models(self, s: SpecEchOuter) -> bool {
        &&& self.kdf == s.kdf
        &&& self.aead == s.aead
        &&& self.config_id == s.config_id
        &&& self.enc@ == s.enc
        &&& self.payload@ == s.payload
    }
}

/// `spec_ech::ech_outer`.
pub fn ech_outer_x(b: &[u8], s: usize, e: usize) -> (r: Option<EchOuter>)
    requires
        s <= e <= b@.len(),
    ensures
        r matches Some(x) ==> ech_outer(b@, s as int, e as int) matches Some(o) && x.models(o)
            && x.enc.start <= x.enc.end <= x.payload.start <= x.payload.end == e,
        r is None ==> ech_outer(b@, s as int, e as int) is None,
{
    if e - s < 6 || b[s] != 0 {
        return None;
    }
    let enc = match vec16_x(b, s + 6, e) {
        Some(v) => v,
        None => return None,
    };
    let payload = match whole16_x(b, enc.end, e) {
        Some(v) => v,
        None => return None,
    };
    if payload.end - payload.start < 1 {
        return None;
    }
    let kdf = (b[s + 1] as u16) * 256 + b[s + 2] as u16;
    let aead = (b[s + 3] as u16) * 256 + b[s + 4] as u16;
    proof {
        assert(kdf == be16(b@, s + 1) as u16);
        assert(aead == be16(b@, s + 3) as u16);
    }
    Some(EchOuter { kdf, aead, config_id: b[s + 5], enc, payload })
}

/// `spec_ech::ech_inner`.
pub fn ech_inner_x(b: &[u8], s: usize, e: usize) -> (r: bool)
    requires
        s <= e <= b@.len(),
    ensures
        r == ech_inner(b@, s as int, e as int),
{
    e - s == 1 && b[s] == 1
}

/// `spec_ech::outer_aad`.
pub fn outer_aad_x(b: &[u8], p: Span) -> (r: Vec<u8>)
    requires
        p.start <= p.end <= b@.len(),
    ensures
        r@ == outer_aad(b@, p@),
{
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    put(&mut out, vstd::slice::slice_subrange(b, 0, p.start));
    let mut i = p.start;
    while i < p.end
        invariant
            p.start <= i <= p.end,
            out@ == b@.take(p.start as int) + zeros((i - p.start) as nat),
        decreases p.end - i,
    {
        out.push(0);
        proof {
            assert(zeros((i - p.start) as nat).push(0u8) =~= zeros((i + 1 - p.start) as nat));
            assert(out@ =~= b@.take(p.start as int) + zeros((i + 1 - p.start) as nat));
        }
        i = i + 1;
    }
    put(&mut out, vstd::slice::slice_subrange(b, p.end, b.len()));
    assert(out@ =~= outer_aad(b@, p@));
    out
}

/// One extension: its type and the span of its data.
#[derive(Clone, Copy)]
pub struct ExtX {
    pub typ: u16,
    pub data: Span,
}

pub open spec fn exts_view(v: Seq<ExtX>) -> Seq<SpecExt> {
    v.map_values(|x: ExtX| SpecExt { typ: x.typ, data: x.data@ })
}

/// `spec::parse_exts`, as a list.
pub fn exts_x(b: &[u8], xs: usize, xe: usize) -> (r: Option<Vec<ExtX>>)
    requires
        xs <= xe <= b@.len(),
    ensures
        r matches Some(v) ==> parse_exts(b@, xs as int, xe as int) == Some(exts_view(v@)) && forall|i: int|
            0 <= i < v@.len() ==> xs + 4 <= #[trigger] v@[i].data.start <= v@[i].data.end <= xe,
        r is None ==> parse_exts(b@, xs as int, xe as int) is None,
{
    let mut out: Vec<ExtX> = Vec::new();
    let mut pos = xs;
    proof {
        if let Some(x) = parse_exts(b@, xs as int, xe as int) {
            assert(exts_view(out@) + x =~= x);
        }
    }
    loop
        invariant
            xs <= pos <= xe <= b@.len(),
            parse_exts(b@, xs as int, xe as int) == app_exts(exts_view(out@), parse_exts(b@, pos as int, xe as int)),
            forall|i: int| 0 <= i < out@.len() ==> xs + 4 <= #[trigger] out@[i].data.start <= out@[i].data.end <= pos,
        decreases xe - pos,
    {
        if pos == xe {
            proof {
                assert(exts_view(out@) + Seq::<SpecExt>::empty() =~= exts_view(out@));
            }
            return Some(out);
        }
        if xe - pos < 2 {
            return None;
        }
        let v = match vec16_x(b, pos + 2, xe) {
            Some(v) => v,
            None => return None,
        };
        let t = (b[pos] as u16) * 256 + b[pos + 1] as u16;
        let ghost x = SpecExt { typ: t, data: (v.start as int, v.end as int) };
        let ghost before = exts_view(out@);
        out.push(ExtX { typ: t, data: v });
        proof {
            assert(t == be16(b@, pos as int) as u16);
            assert(exts_view(out@) =~= before.push(x));
            if let Some(rest) = parse_exts(b@, v.end as int, xe as int) {
                assert(before + (seq![x] + rest) =~= before.push(x) + rest);
            }
        }
        pos = v.end;
    }
}

/// `spec_ech::find_from`.
fn find_from_x(oe: &Vec<ExtX>, cur: usize, t: u16) -> (r: Option<usize>)
    ensures
        r matches Some(j) ==> j < oe@.len(),
        opt_int(r) == find_from(exts_view(oe@), cur as int, t),
{
    let mut i = cur;
    while i < oe.len()
        invariant
            cur <= i,
            find_from(exts_view(oe@), cur as int, t) == find_from(exts_view(oe@), i as int, t),
        decreases oe@.len() - i,
    {
        if oe[i].typ == t {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

pub open spec fn opt_int(r: Option<usize>) -> Option<int> {
    match r {
        Some(j) => Some(j as int),
        None => None,
    }
}

/// `spec_ech::copy_outer`, appended to `out`: where the search stopped.
fn copy_outer_x(x: &[u8], s: usize, e: usize, ob: &[u8], oe: &Vec<ExtX>, cur: usize, out: &mut Vec<u8>) -> (r: Option<usize>)
    requires
        s <= e <= x@.len(),
        cur <= oe@.len(),
        forall|i: int| 0 <= i < oe@.len() ==> 4 <= #[trigger] oe@[i].data.start <= oe@[i].data.end <= ob@.len(),
        old(out)@.len() <= 0x10000,
    ensures
        r matches Some(c) ==> copy_outer(x@, s as int, e as int, ob@, exts_view(oe@), cur as int) == Some(
            (final(out)@.skip(old(out)@.len() as int), c as int),
        ) && c <= oe@.len() && final(out)@.take(old(out)@.len() as int) == old(out)@ && final(out)@.len() <= 0x10000,
        r is None ==> match copy_outer(x@, s as int, e as int, ob@, exts_view(oe@), cur as int) {
            None => true,
            Some((all, _)) => old(out)@.len() + all.len() > 0x10000,
        },
{
    let ghost o = out@;
    let ghost ov = exts_view(oe@);
    let ol = oe.len();
    let mut i = s;
    let mut c = cur;
    proof {
        if let Some((rest, c2)) = copy_outer(x@, s as int, e as int, ob@, ov, cur as int) {
            assert(Seq::<u8>::empty() + rest =~= rest);
        }
    }
    while i < e
        invariant
            s <= i <= e <= x@.len(),
            c <= oe@.len(),
            ol == oe@.len(),
            o == old(out)@,
            ov == exts_view(oe@),
            forall|k: int| 0 <= k < oe@.len() ==> 4 <= #[trigger] oe@[k].data.start <= oe@[k].data.end <= ob@.len(),
            out@.take(o.len() as int) == o,
            o.len() <= out@.len(),
            out@.len() <= 0x10000,
            match copy_outer(x@, s as int, e as int, ob@, ov, cur as int) {
                None => copy_outer(x@, i as int, e as int, ob@, ov, c as int) is None,
                Some((all, cf)) => copy_outer(x@, i as int, e as int, ob@, ov, c as int) matches Some((rest, cf2))
                    && cf2 == cf && all == out@.skip(o.len() as int) + rest,
            },
        decreases e - i,
    {
        if e - i < 2 {
            return None;
        }
        let t = (x[i] as u16) * 256 + x[i + 1] as u16;
        proof {
            assert(t == be16(x@, i as int) as u16);
        }
        if t == 0xfe0d {
            return None;
        }
        let j = match find_from_x(oe, c, t) {
            Some(j) => j,
            None => return None,
        };
        let d = oe[j].data;
        proof {
            assert(ov[j as int].data == d@);
        }
        let piece = vstd::slice::slice_subrange(ob, d.start - 4, d.end);
        proof {
            assert(j < oe@.len());
            assert(piece@ == ext_bytes(ob@, ov[j as int].data));
        }
        if piece.len() > 0x10000 - out.len() {
            proof {
                if let Some((all, cf)) = copy_outer(x@, s as int, e as int, ob@, ov, cur as int) {
                    let (rest, _) = copy_outer(x@, i + 2, e as int, ob@, ov, j + 1).unwrap();
                    assert(all == out@.skip(o.len() as int) + (piece@ + rest));
                    assert(o.len() + all.len() >= out@.len() + piece@.len());
                }
            }
            return None;
        }
        let ghost before = out@;
        put(out, piece);
        proof {
            assert(piece@ == ext_bytes(ob@, ov[j as int].data));
            assert(out@.take(o.len() as int) =~= o);
            assert(out@.skip(o.len() as int) =~= before.skip(o.len() as int) + piece@);
            if let Some((all, cf)) = copy_outer(x@, s as int, e as int, ob@, ov, cur as int) {
                let (rest, _) = copy_outer(x@, i + 2, e as int, ob@, ov, j + 1).unwrap();
                assert(all =~= out@.skip(o.len() as int) + rest);
            }
        }
        c = j + 1;
        i = i + 2;
    }
    proof {
        if let Some((all, cf)) = copy_outer(x@, s as int, e as int, ob@, ov, cur as int) {
            assert(all =~= out@.skip(o.len() as int));
        }
    }
    Some(c)
}

/// `spec_ech::expand_exts`, appended to `out`.
fn expand_exts_x(x: &[u8], ie: &Vec<ExtX>, ob: &[u8], oe: &Vec<ExtX>, out: &mut Vec<u8>) -> (r: bool)
    requires
        forall|i: int| 0 <= i < ie@.len() ==> 4 <= #[trigger] ie@[i].data.start <= ie@[i].data.end <= x@.len(),
        forall|i: int| 0 <= i < oe@.len() ==> 4 <= #[trigger] oe@[i].data.start <= oe@[i].data.end <= ob@.len(),
        old(out)@.len() == 0,
    ensures
        r ==> expand_exts(x@, exts_view(ie@), ob@, exts_view(oe@), 0) == Some(final(out)@) && final(out)@.len() <= 0x10000,
        !r ==> match expand_exts(x@, exts_view(ie@), ob@, exts_view(oe@), 0) {
            None => true,
            Some(all) => all.len() > 0x10000,
        },
{
    let ghost iv = exts_view(ie@);
    let ghost ov = exts_view(oe@);
    let mut k: usize = 0;
    let mut c: usize = 0;
    proof {
        assert(iv.skip(0) =~= iv);
        if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
            assert(all =~= out@ + all);
        }
    }
    while k < ie.len()
        invariant
            k <= ie@.len(),
            c <= oe@.len(),
            iv == exts_view(ie@),
            ov == exts_view(oe@),
            forall|i: int| 0 <= i < ie@.len() ==> 4 <= #[trigger] ie@[i].data.start <= ie@[i].data.end <= x@.len(),
            forall|i: int| 0 <= i < oe@.len() ==> 4 <= #[trigger] oe@[i].data.start <= oe@[i].data.end <= ob@.len(),
            out@.len() <= 0x10000,
            match expand_exts(x@, iv, ob@, ov, 0) {
                None => expand_exts(x@, iv.skip(k as int), ob@, ov, c as int) is None,
                Some(all) => expand_exts(x@, iv.skip(k as int), ob@, ov, c as int) matches Some(rest) && all == out@ + rest,
            },
        decreases ie@.len() - k,
    {
        let it = ie[k];
        let ghost rest_v = iv.skip(k as int);
        proof {
            assert(rest_v[0] == SpecExt { typ: it.typ, data: it.data@ });
            assert(rest_v.drop_first() =~= iv.skip(k + 1));
        }
        let ghost before = out@;
        if it.typ == 0xfd00 {
            let l = match whole8_x(x, it.data.start, it.data.end) {
                Some(l) => l,
                None => return false,
            };
            if l.end - l.start < 2 || (l.end - l.start) % 2 != 0 {
                return false;
            }
            let mut piece: Vec<u8> = Vec::new();
            let c2 = match copy_outer_x(x, l.start, l.end, ob, oe, c, &mut piece) {
                Some(c2) => c2,
                None => {
                    proof {
                        if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
                            let (cp, c3) = copy_outer(x@, l.start as int, l.end as int, ob@, ov, c as int).unwrap();
                            let r2 = expand_exts(x@, iv.skip(k + 1), ob@, ov, c3).unwrap();
                            assert(all == out@ + (cp + r2));
                        }
                    }
                    return false;
                },
            };
            proof {
                assert(piece@.skip(0) =~= piece@);
            }
            if piece.len() > 0x10000 - out.len() {
                proof {
                    if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
                        let r2 = expand_exts(x@, iv.skip(k + 1), ob@, ov, c2 as int).unwrap();
                        assert(all == out@ + (piece@ + r2));
                    }
                }
                return false;
            }
            put(out, piece.as_slice());
            proof {
                assert(piece@.skip(0) =~= piece@);
                if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
                    let r2 = expand_exts(x@, iv.skip(k + 1), ob@, ov, c2 as int).unwrap();
                    assert(all =~= out@ + r2);
                }
            }
            c = c2;
        } else {
            let piece = vstd::slice::slice_subrange(x, it.data.start - 4, it.data.end);
            proof {
                assert(piece@ == ext_bytes(x@, it.data@));
            }
            if piece.len() > 0x10000 - out.len() {
                proof {
                    if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
                        let r2 = expand_exts(x@, iv.skip(k + 1), ob@, ov, c as int).unwrap();
                        assert(all == out@ + (piece@ + r2));
                    }
                }
                return false;
            }
            put(out, piece);
            proof {
                assert(piece@ == ext_bytes(x@, it.data@));
                if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
                    let r2 = expand_exts(x@, iv.skip(k + 1), ob@, ov, c as int).unwrap();
                    assert(all =~= out@ + r2);
                }
            }
        }
        k = k + 1;
    }
    proof {
        assert(iv.skip(k as int) =~= Seq::<SpecExt>::empty());
        if let Some(all) = expand_exts(x@, iv, ob@, ov, 0) {
            assert(all =~= out@);
        }
    }
    true
}

/// `spec_ech::decode_inner`: ClientHelloInner's body from
/// EncodedClientHelloInner `x`, ClientHelloOuter's body `ob` (its
/// extension block `[oxs, oxe)` parsed as `oexts`) and its session id.
#[verifier::rlimit(60)]
pub fn decode_inner_x(x: &[u8], ob: &[u8], oxs: usize, oxe: usize, sid: Span, Ghost(oexts): Ghost<Seq<SpecExt>>) -> (r: Option<Vec<u8>>)
    requires
        oxs <= oxe <= ob@.len(),
        parse_exts(ob@, oxs as int, oxe as int) == Some(oexts),
        sid.start <= sid.end <= ob@.len(),
    ensures
        r matches Some(v) ==> decode_inner(x@, ob@, oexts, sid@) == Some(v@),
        r is None ==> decode_inner(x@, ob@, oexts, sid@) is None,
{
    let n = x.len();
    if n < 35 || x[34] != 0 {
        return None;
    }
    let cs = match vec16_x(x, 35, n) {
        Some(v) => v,
        None => return None,
    };
    let ms = match vec8_x(x, cs.end, n) {
        Some(v) => v,
        None => return None,
    };
    let xs = match vec16_x(x, ms.end, n) {
        Some(v) => v,
        None => return None,
    };
    if !zeros_from(x, xs.end) {
        return None;
    }
    let oe = match exts_x(ob, oxs, oxe) {
        Some(v) => v,
        None => {
            proof { assert(false); }
            return None;
        },
    };
    let ie = match exts_x(x, xs.start, xs.end) {
        Some(v) => v,
        None => return None,
    };
    let mut ex: Vec<u8> = Vec::new();
    proof {
        assert(exts_view(oe@) == oexts);
    }
    if !expand_exts_x(x, &ie, ob, &oe, &mut ex) {
        return None;
    }
    if ex.len() >= 65536 || sid.end - sid.start > 32 {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    put(&mut out, vstd::slice::slice_subrange(x, 0, 34));
    out.push((sid.end - sid.start) as u8);
    put(&mut out, sid.of(ob));
    put(&mut out, vstd::slice::slice_subrange(x, 35, ms.end));
    let l = ex.len();
    out.push((l / 256) as u8);
    out.push((l % 256) as u8);
    put(&mut out, ex.as_slice());
    proof {
        let ghost want = x@.take(34) + seq![(sid.end - sid.start) as u8] + ob@.subrange(sid.start as int, sid.end as int)
            + x@.subrange(35, ms.end as int) + be2(ex@.len()) + ex@;
        assert(out@ =~= want);
    }
    Some(out)
}

/// Whether `x[k..]` is all zeros.
fn zeros_from(x: &[u8], k: usize) -> (r: bool)
    requires
        k <= x@.len(),
    ensures
        r == !(exists|j: int| k <= j < x@.len() && x@[j] != 0),
{
    let mut i = k;
    while i < x.len()
        invariant
            k <= i <= x@.len(),
            forall|j: int| k <= j < i ==> x@[j] == 0,
        decreases x@.len() - i,
    {
        if x[i] != 0 {
            assert(k <= i < x@.len() && x@[i as int] != 0);
            return false;
        }
        i = i + 1;
    }
    true
}

/// "ech accept confirmation".
pub const L_ECH_CONF: [u8; 23] = [101, 99, 104, 32, 97, 99, 99, 101, 112, 116, 32, 99, 111, 110, 102, 105, 114, 109, 97, 116, 105, 111, 110];

/// `spec_ech::ech_confirm`, with `th` the transcript hash.
pub fn ech_confirm_x(a: HashAlg, inner_random: &[u8], th: &Secret, Ghost(messages): Ghost<Seq<u8>>) -> (r: Secret)
    requires
        th.wf(),
        th@ == hash(a, messages),
        th@.len() <= 255,
    ensures
        r.wf(),
        r@.len() == 8,
        r@ == ech_confirm(a, inner_random@, messages),
{
    let z = Secret::zeros_of(a);
    let prk = hmac_x(a, z.as_slice(), inner_random);
    proof {
        assert(L_ECH_CONF@ =~= l_ech_conf());
        assert(hash_len(a) >= 8);
    }
    expand_label_x(a, prk.as_slice(), &L_ECH_CONF, th.as_slice(), 8)
}

} // verus!
