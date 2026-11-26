//! The specification of Encrypted Client Hello (RFC 9849) on the server:
//! the encrypted_client_hello extension, the additional data the client
//! sealed ClientHelloInner with, how an EncodedClientHelloInner becomes
//! ClientHelloInner, and the acceptance signal in ServerHello.random.
//! Trusted, like the other spec files: read it against the RFC.
use crate::crypto::*;
use crate::spec::*;
use crate::spec_keys::*;
use crate::spec_server::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// ech_outer_extensions (§5.1).
pub const EXT_ECH_OUTER_EXTENSIONS: u16 = 0xfd00;

/// ECHClientHello of type `outer` (§5), its fields as spans of the
/// ClientHelloOuter body.
pub struct SpecEchOuter {
    pub kdf: u16,
    pub aead: u16,
    pub config_id: u8,
    pub enc: (int, int),
    pub payload: (int, int),
}

/// encrypted_client_hello's data `[s, e)` as an outer ECHClientHello:
///
/// ```text
/// struct {
///    ECHClientHelloType type;            // outer(0)
///    HpkeSymmetricCipherSuite cipher_suite;  // kdf_id, aead_id
///    uint8 config_id;
///    opaque enc<0..2^16-1>;
///    opaque payload<1..2^16-1>;
/// } ECHClientHello;
/// ```
pub open spec fn ech_outer(b: Seq<u8>, s: int, e: int) -> Option<SpecEchOuter> {
    if 0 <= s && s + 6 <= e && e <= b.len() && b[s] == 0 {
        match vec16(b, s + 6, e) {
            None => None,
            Some((es, ee)) => match whole16(b, ee, e) {
                None => None,
                Some((ps, pe)) => if pe - ps >= 1 {
                    Some(SpecEchOuter { kdf: be16(b, s + 1) as u16, aead: be16(b, s + 3) as u16, config_id: b[s + 5], enc: (es, ee), payload: (ps, pe) })
                } else {
                    None
                },
            },
        }
    } else {
        None
    }
}

/// An ECHClientHello of type `inner` (§5): the type byte 1 and nothing
/// else.
pub open spec fn ech_inner(b: Seq<u8>, s: int, e: int) -> bool {
    0 <= s && s + 1 == e && e <= b.len() && b[s] == 1
}

/// ClientHelloOuterAAD (§5.2): the ClientHelloOuter body with the
/// payload's bytes replaced by zeros.
pub open spec fn outer_aad(b: Seq<u8>, p: (int, int)) -> Seq<u8> {
    b.take(p.0) + zeros((p.1 - p.0) as nat) + b.skip(p.1)
}

/// The whole extension (type, length and data) whose data is `d`.
pub open spec fn ext_bytes(b: Seq<u8>, d: (int, int)) -> Seq<u8> {
    b.subrange(d.0 - 4, d.1)
}

/// The first of `exts[cur..]` of type `t`.
pub open spec fn find_from(exts: Seq<SpecExt>, cur: int, t: u16) -> Option<int>
    decreases exts.len() - cur,
{
    if cur < 0 || cur >= exts.len() {
        None
    } else if exts[cur].typ == t {
        Some(cur)
    } else {
        find_from(exts, cur + 1, t)
    }
}

/// The extensions an `OuterExtensions` list at `x[s..e)` (2 bytes each)
/// names, copied from ClientHelloOuter `ob` (its extensions `oexts`), and
/// where in `oexts` the search stops (§5.1). Each must be found after the
/// last one found ("in the same relative order"), and none may be
/// encrypted_client_hello, else the server aborts (`None`).
pub open spec fn copy_outer(x: Seq<u8>, s: int, e: int, ob: Seq<u8>, oexts: Seq<SpecExt>, cur: int) -> Option<(Seq<u8>, int)>
    decreases e - s,
{
    if s >= e {
        Some((Seq::empty(), cur))
    } else if s + 2 > e {
        None
    } else {
        let t = be16(x, s) as u16;
        if t == EXT_ECH {
            None
        } else {
            match find_from(oexts, cur, t) {
                None => None,
                Some(j) => match copy_outer(x, s + 2, e, ob, oexts, j + 1) {
                    None => None,
                    Some((rest, c)) => Some((ext_bytes(ob, oexts[j].data) + rest, c)),
                },
            }
        }
    }
}

/// The extension block of ClientHelloInner from EncodedClientHelloInner's
/// `iexts` (in `x`): each extension as it is, except ech_outer_extensions,
/// which is replaced by the outer extensions it names (§5.1).
pub open spec fn expand_exts(x: Seq<u8>, iexts: Seq<SpecExt>, ob: Seq<u8>, oexts: Seq<SpecExt>, cur: int) -> Option<Seq<u8>>
    decreases iexts.len(),
{
    if iexts.len() == 0 {
        Some(Seq::empty())
    } else {
        let ie = iexts[0];
        let here: Option<(Seq<u8>, int)> = if ie.typ == EXT_ECH_OUTER_EXTENSIONS {
            match whole8(x, ie.data.0, ie.data.1) {
                None => None,
                Some((ls, le)) => if le - ls < 2 || (le - ls) % 2 != 0 {
                    None
                } else {
                    copy_outer(x, ls, le, ob, oexts, cur)
                },
            }
        } else {
            Some((ext_bytes(x, ie.data), cur))
        };
        match here {
            None => None,
            Some((h, c)) => match expand_exts(x, iexts.drop_first(), ob, oexts, c) {
                None => None,
                Some(r) => Some(h + r),
            },
        }
    }
}

/// ClientHelloInner's body from EncodedClientHelloInner `x` and
/// ClientHelloOuter's body `ob` (its extensions `oexts`, its
/// legacy_session_id `sid`), §5.1: `x` is a ClientHello with an empty
/// legacy_session_id, an extension block, then zeros (padding); the
/// session id is the outer's, and ech_outer_extensions is expanded. `None`
/// is an abort with illegal_parameter (§7.1).
pub open spec fn decode_inner(x: Seq<u8>, ob: Seq<u8>, oexts: Seq<SpecExt>, sid: (int, int)) -> Option<Seq<u8>> {
    let n = x.len() as int;
    if n < 35 || x[34] != 0 {
        None
    } else {
        match vec16(x, 35, n) {
            None => None,
            Some((cs, ce)) => match vec8(x, ce, n) {
                None => None,
                Some((ms, me)) => match vec16(x, me, n) {
                    None => None,
                    Some((xs, xe)) => if exists|i: int| xe <= i < n && x[i] != 0 {
                        None
                    } else {
                        match parse_exts(x, xs, xe) {
                            None => None,
                            Some(iexts) => match expand_exts(x, iexts, ob, oexts, 0) {
                                None => None,
                                Some(ex) => if ex.len() >= 65536 || sid.1 - sid.0 > 32 {
                                    None
                                } else {
                                    Some(x.take(34) + seq![(sid.1 - sid.0) as u8] + ob.subrange(sid.0, sid.1) + x.subrange(35, me)
                                        + be2(ex.len()) + ex)
                                },
                            },
                        }
                    },
                },
            },
        }
    }
}

/// ClientHelloInner `ch` (a message) is what the server's ECH key opened
/// from ClientHelloOuter `outer` (`pt`, `crypto::ech_opened`), decoded
/// (§5.1), and it carries encrypted_client_hello of type inner.
pub open spec fn ech_decrypted(outer: Seq<u8>, pt: Seq<u8>, ch: Seq<u8>) -> bool {
    let ob = outer.skip(4);
    &&& is_msg(outer, 1)
    &&& parse_client_hello(ob) matches Ok(so) && so.ech matches Some((es, ee)) && ech_outer(ob, es, ee) matches Some(eo) && {
        &&& ech_opened(eo.config_id, eo.kdf, eo.aead, bytes(ob, eo.enc), outer_aad(ob, eo.payload), bytes(ob, eo.payload), pt)
        &&& decode_inner(pt, ob, so.outer.exts, so.outer.session_id) == Some(ch.skip(4))
    }
    &&& ch == hs_msg(1, ch.skip(4))
    &&& parse_client_hello(ch.skip(4)) matches Ok(si) && si.ech matches Some((is_, ie)) && ech_inner(ch.skip(4), is_, ie)
}

/// "ech accept confirmation".
pub open spec fn l_ech_conf() -> Seq<u8> {
    seq![101, 99, 104, 32, 97, 99, 99, 101, 112, 116, 32, 99, 111, 110, 102, 105, 114, 109, 97, 116, 105, 111, 110]
}

/// accept_confirmation (§7.2): the last 8 bytes of ServerHello.random
/// when the server accepted ECH, with `th` the transcript ClientHelloInner
/// .. ServerHello, that ServerHello's last 8 random bytes zeros.
pub open spec fn ech_confirm(a: HashAlg, inner_random: Seq<u8>, th: Seq<u8>) -> Seq<u8> {
    expand_label(a, hkdf_extract(a, zeros(hash_len(a)), inner_random), l_ech_conf(), hash(a, th), 8)
}

} // verus!
