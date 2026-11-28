//! Checking one RRSIG over one RRset with one key (RFC 4035 §5.3), and a
//! DS against a DNSKEY (RFC 4035 §5.2): proven to establish
//! `dspec::rrset_signed` and `dspec::ds_matches`.
use crate::canon::*;
use crate::crypto::verify_sig;
use crate::dspec::*;
use crate::name::*;
use crate::rr::*;
use crate::sha1::sha1_x;
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub fn u16_at_x(b: &[u8], i: usize) -> (r: u16)
    requires
        i + 2 <= b@.len(),
    ensures
        r == u16_at(b@, i as int),
{
    (b[i] as u16) * 256 + b[i + 1] as u16
}

pub fn u32_at_x(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r == u32_at(b@, i as int),
{
    (b[i] as u32) * 0x100_0000 + (b[i + 1] as u32) * 0x1_0000 + (b[i + 2] as u32) * 0x100 + b[i + 3] as u32
}

pub fn serial_le_x(a: u32, b: u32) -> (r: bool)
    ensures
        r == serial_le(a, b),
{
    let d: u64 = ((b as u64) + 0x1_0000_0000 - (a as u64)) % 0x1_0000_0000;
    proof {
        assert((b as int - a as int) % 0x1_0000_0000 == ((b as int) + 0x1_0000_0000 - (a as int)) % 0x1_0000_0000);
    }
    d < 0x8000_0000
}

/// The key tag of DNSKEY RDATA (RFC 4034 Appendix B). Only a hint for
/// which key to try; nothing depends on it.
pub fn key_tag(k: &[u8]) -> u16 {
    let mut ac: u64 = 0;
    let mut i: usize = 0;
    while i < k.len() && i < 0x1_0000
        invariant
            ac <= 65536 * i,
            i <= 0x1_0000,
        decreases k@.len() - i,
    {
        if i % 2 == 0 {
            ac = ac + (k[i] as u64) * 256;
        } else {
            ac = ac + k[i] as u64;
        }
        i = i + 1;
    }
    ac = ac + (ac / 0x1_0000) % 0x1_0000;
    (ac % 0x1_0000) as u16
}

pub fn key_ok_x(k: &[u8]) -> (r: bool)
    ensures
        r == key_ok(k@),
{
    k.len() > 4 && k[0] % 2 == 1 && k[1] < 128 && k[2] == 3
}

pub fn alg_supported_x(a: u8) -> (r: bool)
    ensures
        r == alg_supported(a),
{
    a == 8 || a == 10 || a == 13 || a == 14 || a == 15
}

pub fn digest_supported_x(d: u8) -> (r: bool)
    ensures
        r == digest_supported(d),
{
    d == 1 || d == 2 || d == 4
}

/// `rrset_ok(rs)`.
pub fn rrset_ok_x(rs: &Vec<Rr>) -> (r: bool)
    ensures
        r == rrset_ok(rrs(rs@)),
{
    if rs.len() == 0 {
        return false;
    }
    let ghost v = rrs(rs@);
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            v == rrs(rs@),
            rs@.len() > 0,
            i <= rs@.len(),
            forall|j: int| 0 <= j < i ==> {
                &&& eq_ci((#[trigger] v[j]).name, v[0].name)
                &&& v[j].rtype == v[0].rtype
                &&& v[j].rclass == CLASS_IN
            },
        decreases rs@.len() - i,
    {
        if !(eq_ci_exec(&rs[i].name, &rs[0].name) && rs[i].rtype == rs[0].rtype && rs[i].rclass == CLASS_IN) {
            proof {
                assert(v[i as int] == rs@[i as int]@);
                assert(v[0] == rs@[0]@);
            }
            return false;
        }
        proof {
            assert(v[i as int] == rs@[i as int]@);
            assert(v[0] == rs@[0]@);
        }
        i = i + 1;
    }
    true
}

/// The checks of `rrset_signed` that do not involve the key: the RRSIG
/// fits the RRset, names `zone` as its signer, and is current.
pub fn sig_fits(rs: &Vec<Rr>, sig: &Rr, zone: &[u8], now: u32) -> (r: bool)
    ensures
        r ==> {
            let v = rrs(rs@);
            let rd = sig@.rdata;
            let t = v[0].rtype;
            &&& rrset_ok(v)
            &&& t != TYPE_RRSIG
            &&& sig@.rtype == TYPE_RRSIG
            &&& sig@.rclass == CLASS_IN
            &&& eq_ci(sig@.name, v[0].name)
            &&& sig_wf(rd)
            &&& sig_covered(rd) == t
            &&& eq_ci(sig_signer(rd), zone@)
            &&& is_sub(v[0].name, zone@)
            &&& (t == TYPE_DS ==> !eq_ci(v[0].name, zone@))
            &&& (t == TYPE_DNSKEY ==> eq_ci(v[0].name, zone@))
            &&& (sig_labels(rd) as nat) <= sig_label_count(v[0].name)
            &&& time_ok(rd, now)
            &&& alg_supported(sig_alg(rd))
        },
{
    if !rrset_ok_x(rs) {
        return false;
    }
    let r0 = &rs[0];
    proof {
        assert(rrs(rs@)[0] == rs@[0]@);
    }
    let t = r0.rtype;
    let rd = &sig.rdata;
    if t == TYPE_RRSIG || sig.rtype != TYPE_RRSIG || sig.rclass != CLASS_IN || !eq_ci_exec(&sig.name, &r0.name) {
        return false;
    }
    if rd.len() < 19 {
        return false;
    }
    let end = match name_len_x(rd, 18) {
        Some(l) => 18 + l,
        None => {
            return false;
        },
    };
    if u16_at_x(rd, 0) != t {
        return false;
    }
    let signer = slice_subrange(rd.as_slice(), 18, end);
    if !eq_ci_exec(signer, zone) || !is_sub_exec(&r0.name, zone) {
        return false;
    }
    if t == TYPE_DS && eq_ci_exec(&r0.name, zone) {
        return false;
    }
    if t == TYPE_DNSKEY && !eq_ci_exec(&r0.name, zone) {
        return false;
    }
    if rd[3] as usize > sig_label_count_x(&r0.name) {
        return false;
    }
    if !(serial_le_x(u32_at_x(rd, 12), now) && serial_le_x(now, u32_at_x(rd, 8))) {
        return false;
    }
    alg_supported_x(rd[2])
}

/// Does RRSIG `sig`, with DNSKEY RDATA `key` of `zone`, validate the RRset
/// `rs` at time `now`? `true` only if `rrset_signed` holds.
pub fn rrset_valid(rs: &Vec<Rr>, sig: &Rr, key: &[u8], zone: &[u8], now: u32) -> (r: bool)
    ensures
        r ==> rrset_signed(rrs(rs@), sig@, key@, zone@, now),
{
    if !sig_fits(rs, sig, zone, now) {
        return false;
    }
    let rd = &sig.rdata;
    if !key_ok_x(key) || key[3] != rd[2] {
        return false;
    }
    let t = rs[0].rtype;
    proof {
        assert(rrs(rs@)[0] == rs@[0]@);
    }
    let ords = sorted_rdata(rs, t);
    let data = match signed_data_x(rd, &rs[0].name, t, &ords) {
        Some(d) => d,
        None => {
            return false;
        },
    };
    let n = rd.len();
    let end = match name_len_x(rd, 18) {
        Some(l) => 18 + l,
        None => {
            return false;
        },
    };
    let ok = verify_sig(rd[2], slice_subrange(key, 4, key.len()), &data, slice_subrange(rd.as_slice(), end, rd.len()));
    proof {
        if ok {
            let o = views(ords@);
            assert(sorted_strict(o) && rdata_set(o, rrs(rs@), t) && sig_valid(
                sig_alg(rd@),
                key_pub(key@),
                signed_data(rd@, signed_owner(rrs(rs@)[0].name, sig_labels(rd@)), t, o),
                sig_bytes(rd@),
            ));
        }
    }
    ok
}

/// Does DS RDATA `ds` identify DNSKEY RDATA `key` of zone `owner`?
pub fn ds_match_x(ds: &[u8], owner: &[u8], key: &[u8]) -> (r: bool)
    ensures
        r ==> ds_matches(ds@, owner@, key@),
{
    if ds.len() < 4 || key.len() < 4 || ds[2] != key[3] || !digest_supported_x(ds[3]) {
        return false;
    }
    if owner.len() >= 0x0800_0000 || key.len() >= 0x0800_0000 {
        return false;
    }
    let mut data: Vec<u8> = Vec::new();
    push_lower(&mut data, owner);
    push_bytes(&mut data, key);
    let want = slice_subrange(ds, 4, ds.len());
    let dt = ds[3];
    if dt == 1 {
        let h = sha1_x(&data);
        bytes_eq(want, h.as_slice())
    } else if dt == 2 {
        let h = verilith_sha2::sha256(&data);
        bytes_eq(want, h.as_slice())
    } else {
        let h = verilith_sha2::sha384(&data);
        bytes_eq(want, h.as_slice())
    }
}

} // verus!
