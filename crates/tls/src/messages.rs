//! The handshake messages a server sends, proven to be exactly the bytes
//! `spec_server.rs` gives.
use crate::keys::*;
use crate::spec_keys::*;
use crate::spec_server::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// The bytes of an optional slice.
pub open spec fn opt_view(x: Option<&[u8]>) -> Option<Seq<u8>> {
    match x {
        Some(p) => Some(p@),
        None => None,
    }
}

pub fn put1(out: &mut Vec<u8>, v: u8)
    ensures
        final(out)@ == old(out)@ + seq![v],
{
    out.push(v);
}

pub fn put2(out: &mut Vec<u8>, n: usize)
    requires
        n < 65536,
    ensures
        final(out)@ == old(out)@ + be2(n as nat),
{
    out.push((n / 256) as u8);
    out.push((n % 256) as u8);
    assert(final(out)@ =~= old(out)@ + be2(n as nat));
}

pub fn put3(out: &mut Vec<u8>, n: usize)
    requires
        n < 0x100_0000,
    ensures
        final(out)@ == old(out)@ + be3(n as nat),
{
    out.push((n / 65536) as u8);
    out.push(((n / 256) % 256) as u8);
    out.push((n % 256) as u8);
    assert(final(out)@ =~= old(out)@ + be3(n as nat));
}

pub fn put(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    out.extend_from_slice(s);
}

/// Appends a ServerHello's extensions.
#[verifier::spinoff_prover]
fn server_hello_exts_x(out: &mut Vec<u8>, group: u16, share: &[u8], psk: bool)
    requires
        share@.len() <= 16000,
    ensures
        final(out)@ == old(out)@ + ext_version() + ext(51, be2(group as nat) + be2(share@.len()) + share@) + (if psk {
            ext(41, be2(0))
        } else {
            Seq::<u8>::empty()
        }),
{
    put2(out, 43);
    put2(out, 2);
    put1(out, 3);
    put1(out, 4);
    put2(out, 51);
    put2(out, 4 + share.len());
    put2(out, group as usize);
    put2(out, share.len());
    put(out, share);
    if psk {
        put2(out, 41);
        put2(out, 2);
        put2(out, 0);
    }
    proof {
        let ks = be2(group as nat) + be2(share@.len()) + share@;
        assert(ks.len() == 4 + share@.len());
        let pe = if psk { ext(41, be2(0)) } else { Seq::<u8>::empty() };
        assert(final(out)@ =~= old(out)@ + ext_version() + ext(51, ks) + pe);
    }
}

/// Appends a ServerHello.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn server_hello_x(out: &mut Vec<u8>, random: &[u8; 32], sid: &[u8], suite: u16, group: u16, share: &[u8], psk: bool)
    requires
        sid@.len() <= 32,
        share@.len() <= 16000,
    ensures
        final(out)@ == old(out)@ + server_hello(random@, sid@, suite, group, share@, psk),
{
    let mut exts: Vec<u8> = Vec::new();
    server_hello_exts_x(&mut exts, group, share, psk);
    proof {
        assert(exts@.len() <= 6 + 4 + 4 + 16000 + 6);
    }
    let el = exts.len();
    let bl = 2 + 32 + 1 + sid.len() + 2 + 1 + 2 + el;
    put1(out, 2);
    put3(out, bl);
    put1(out, 3);
    put1(out, 3);
    put(out, random);
    put1(out, sid.len() as u8);
    put(out, sid);
    put2(out, suite as usize);
    put1(out, 0);
    put2(out, el);
    put(out, exts.as_slice());
    proof {
        let body = server_hello_body(random@, sid@, suite, exts@);
        assert(body.len() == bl);
        assert(exts@ =~= ext_version() + ext(51, be2(group as nat) + be2(share@.len()) + share@) + (if psk {
            ext(41, be2(0))
        } else {
            Seq::<u8>::empty()
        }));
        assert(final(out)@ =~= old(out)@ + server_hello(random@, sid@, suite, group, share@, psk));
    }
}

/// Appends a HelloRetryRequest.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn hello_retry_request_x(out: &mut Vec<u8>, sid: &[u8], suite: u16, group: u16)
    requires
        sid@.len() <= 32,
    ensures
        final(out)@ == old(out)@ + hello_retry_request(sid@, suite, group),
{
    let random: [u8; 32] = [
        0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8,
        0x91, 0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8,
        0x33, 0x9c,
    ];
    let el: usize = 6 + 6;
    let bl = 2 + 32 + 1 + sid.len() + 2 + 1 + 2 + el;
    put1(out, 2);
    put3(out, bl);
    put1(out, 3);
    put1(out, 3);
    put(out, &random);
    put1(out, sid.len() as u8);
    put(out, sid);
    put2(out, suite as usize);
    put1(out, 0);
    put2(out, el);
    put2(out, 43);
    put2(out, 2);
    put1(out, 3);
    put1(out, 4);
    put2(out, 51);
    put2(out, 2);
    put2(out, group as usize);
    proof {
        assert(random@ =~= hrr_random());
        let exts = ext_version() + ext(51, be2(group as nat));
        assert(exts.len() == el);
        let body = server_hello_body(hrr_random(), sid@, suite, exts);
        assert(body.len() == bl);
        assert(final(out)@ =~= old(out)@ + hello_retry_request(sid@, suite, group));
    }
}

/// Appends EncryptedExtensions: ALPN's choice, if any, early_data,
/// ECH's retry_configs, then the transport parameters `tp` over QUIC.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn encrypted_extensions_x(out: &mut Vec<u8>, alpn: Option<&[u8]>, tp: Option<&[u8]>, early: bool, retry: Option<&[u8]>)
    requires
        alpn matches Some(p) ==> p@.len() <= 255,
        tp matches Some(t) ==> t@.len() <= 60000,
        retry matches Some(l) ==> l@.len() <= 4096,
    ensures
        final(out)@ == old(out)@ + encrypted_extensions(
            opt_view(alpn),
            opt_view(tp),
            early,
            opt_view(retry),
        ),
        encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry)).len() <= 65000,
{
    reveal(encrypted_extensions);
    let na0: usize = match alpn {
        None => 0,
        Some(p) => p.len() + 7,
    };
    let na1: usize = if early { na0 + 4 } else { na0 };
    let na: usize = match retry {
        None => na1,
        Some(l) => na1 + l.len() + 4,
    };
    let nt: usize = match tp {
        None => 0,
        Some(t) => t.len() + 4,
    };
    let ghost o = out@;
    put1(out, 8);
    put3(out, na + nt + 2);
    put2(out, na + nt);
    let ghost o1 = out@;
    match alpn {
        None => {},
        Some(p) => {
            let n = p.len();
            put2(out, 16);
            put2(out, n + 3);
            put2(out, n + 1);
            put1(out, n as u8);
            put(out, p);
        },
    }
    let ghost o15 = out@;
    if early {
        put2(out, 42);
        put2(out, 0);
    }
    let ghost o16 = out@;
    match retry {
        None => {},
        Some(l) => {
            put2(out, 0xfe0d);
            put2(out, l.len());
            put(out, l);
        },
    }
    let ghost o2 = out@;
    match tp {
        None => {},
        Some(t) => {
            put2(out, 57);
            put2(out, t.len());
            put(out, t);
        },
    }
    proof {
        let av = opt_view(alpn);
        let tv = opt_view(tp);
        let rv = opt_view(retry);
        assert(o15.skip(o1.len() as int) =~= alpn_ext(av));
        assert(o16.skip(o15.len() as int) =~= early_ext(early));
        assert(o2.skip(o16.len() as int) =~= ech_retry_ext(rv));
        assert(o2.skip(o1.len() as int) =~= alpn_ext(av) + early_ext(early) + ech_retry_ext(rv));
        assert(out@.skip(o2.len() as int) =~= tp_ext(tv));
        let e = alpn_ext(av) + early_ext(early) + ech_retry_ext(rv) + tp_ext(tv);
        assert(e.len() == na + nt);
        assert(out@ =~= o + (seq![8u8] + be3(e.len() + 2) + (be2(e.len()) + e)));
        assert(hs_msg(8, be2(e.len()) + e) =~= seq![8u8] + be3(e.len() + 2) + (be2(e.len()) + e));
        assert(encrypted_extensions(av, tv, early, rv).len() == out@.len() - o.len());
    }
}

/// The chain as byte strings.
pub open spec fn chain_view(chain: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    chain.map_values(|c: Vec<u8>| c@)
}

/// The Certificate message for `chain`, or `None` if it would not fit in
/// a handshake message.
pub fn certificate_x(chain: &Vec<Vec<u8>>) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(m) ==> m@ == certificate(chain_view(chain@)) && m@.len() < 0x100_0000,
{
    let mut entries: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < chain.len()
        invariant
            i <= chain@.len(),
            entries@ == cert_entries(chain_view(chain@.take(i as int))),
            entries@.len() < 0x100_0000,
        decreases chain@.len() - i,
    {
        let c = &chain[i];
        if c.len() >= 0x100_0000 - 16 || entries.len() >= 0x100_0000 - 16 - c.len() {
            return None;
        }
        put3(&mut entries, c.len());
        put(&mut entries, c.as_slice());
        put1(&mut entries, 0);
        put1(&mut entries, 0);
        proof {
            let v = chain_view(chain@.take(i as int + 1));
            assert(v.drop_last() =~= chain_view(chain@.take(i as int)));
            assert(v.last() == c@);
            assert(entries@ =~= cert_entries(v));
        }
        i = i + 1;
    }
    assert(chain@.take(chain@.len() as int) =~= chain@);
    if entries.len() >= 0x100_0000 - 8 {
        return None;
    }
    let mut m: Vec<u8> = Vec::new();
    put1(&mut m, 11);
    put3(&mut m, entries.len() + 4);
    put1(&mut m, 0);
    put3(&mut m, entries.len());
    put(&mut m, entries.as_slice());
    assert(m@ =~= certificate(chain_view(chain@)));
    Some(m)
}

/// Appends what a CertificateVerify signs, for transcript hash `th`.
pub fn cv_content_x(out: &mut Vec<u8>, th: &Secret)
    requires
        th.wf(),
    ensures
        final(out)@ == old(out)@ + cv_content(th@),
{
    let label: [u8; 33] = [
        84, 76, 83, 32, 49, 46, 51, 44, 32, 115, 101, 114, 118, 101, 114, 32, 67, 101, 114, 116,
        105, 102, 105, 99, 97, 116, 101, 86, 101, 114, 105, 102, 121,
    ];
    let ghost o = out@;
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            out@ == o + Seq::new(i as nat, |j: int| 0x20u8),
        decreases 64 - i,
    {
        out.push(0x20);
        assert(out@ =~= o + Seq::new(i as nat + 1, |j: int| 0x20u8));
        i = i + 1;
    }
    put(out, &label);
    put1(out, 0);
    put(out, th.as_slice());
    reveal(cv_content);
    assert(label@ =~= cv_label());
    assert(final(out)@ =~= old(out)@ + cv_content(th@));
}

/// Appends a CertificateVerify.
pub fn certificate_verify_x(out: &mut Vec<u8>, scheme: u16, sig: &[u8])
    requires
        sig@.len() <= 65535 - 4,
    ensures
        final(out)@ == old(out)@ + certificate_verify(scheme, sig@),
{
    put1(out, 15);
    put3(out, sig.len() + 4);
    put2(out, scheme as usize);
    put2(out, sig.len());
    put(out, sig);
    assert(final(out)@ =~= old(out)@ + certificate_verify(scheme, sig@));
}

/// Appends a Finished.
pub fn finished_x(out: &mut Vec<u8>, vd: &Secret)
    requires
        vd.wf(),
    ensures
        final(out)@ == old(out)@ + finished(vd@),
{
    put1(out, 20);
    put3(out, vd.len());
    put(out, vd.as_slice());
    assert(final(out)@ =~= old(out)@ + finished(vd@));
}

/// Appends `message_hash` of a ClientHello whose transcript hash is `h`.
pub fn message_hash_x(out: &mut Vec<u8>, h: &Secret)
    requires
        h.wf(),
    ensures
        final(out)@ == old(out)@ + hs_msg(254, h@),
{
    put1(out, 254);
    put3(out, h.len());
    put(out, h.as_slice());
    assert(final(out)@ =~= old(out)@ + hs_msg(254, h@));
}

/// Appends a plaintext record header for a fragment of `n` bytes.
pub fn plain_header_x(out: &mut Vec<u8>, ct: u8, n: usize)
    requires
        n < 65536,
    ensures
        final(out)@ == old(out)@ + seq![ct, 3u8, 3u8] + be2(n as nat),
{
    put1(out, ct);
    put1(out, 3);
    put1(out, 3);
    put2(out, n);
}

pub fn put4(out: &mut Vec<u8>, n: u32)
    ensures
        final(out)@ == old(out)@ + be4(n as nat),
{
    put2(out, (n / 65536) as usize);
    put2(out, (n % 65536) as usize);
    assert(final(out)@ =~= old(out)@ + be4(n as nat));
}

pub fn put8(out: &mut Vec<u8>, n: u64)
    ensures
        final(out)@ == old(out)@ + be8(n as nat),
{
    put4(out, (n / 0x1_0000_0000) as u32);
    put4(out, (n % 0x1_0000_0000) as u32);
    assert(final(out)@ =~= old(out)@ + be8(n as nat));
}

/// Appends a ticket state.
pub fn ticket_state_x(out: &mut Vec<u8>, suite: u16, time: u64, age_add: u32, psk: &Secret, max_early: u32, alpn: &[u8])
    requires
        psk.wf(),
        alpn@.len() <= 255,
    ensures
        final(out)@ == old(out)@ + ticket_state(suite, time, age_add, psk@, max_early, alpn@),
{
    put1(out, 2);
    put2(out, suite as usize);
    put8(out, time);
    put4(out, age_add);
    put1(out, psk.len() as u8);
    put(out, psk.as_slice());
    put4(out, max_early);
    put1(out, alpn.len() as u8);
    put(out, alpn);
    assert(final(out)@ =~= old(out)@ + ticket_state(suite, time, age_add, psk@, max_early, alpn@));
}

/// Appends a NewSessionTicket.
pub fn new_session_ticket_x(out: &mut Vec<u8>, lifetime: u32, age_add: u32, nonce: &[u8], ticket: &[u8], max_early: u32)
    requires
        nonce@.len() <= 255,
        ticket@.len() <= 65535,
    ensures
        final(out)@ == old(out)@ + new_session_ticket(lifetime, age_add, nonce@, ticket@, max_early),
{
    let mut x: Vec<u8> = Vec::new();
    if max_early > 0 {
        put2(&mut x, 42);
        put2(&mut x, 4);
        put4(&mut x, max_early);
    }
    assert(x@ =~= nst_exts(max_early));
    let bl = 4 + 4 + 1 + nonce.len() + 2 + ticket.len() + 2 + x.len();
    let ghost body = be4(lifetime as nat) + be4(age_add as nat) + seq![nonce@.len() as u8] + nonce@ + be2(
        ticket@.len(),
    ) + ticket@ + be2(x@.len()) + x@;
    assert(body.len() == bl);
    put1(out, 4);
    put3(out, bl);
    let ghost o1 = out@;
    put4(out, lifetime);
    put4(out, age_add);
    put1(out, nonce.len() as u8);
    put(out, nonce);
    put2(out, ticket.len());
    put(out, ticket);
    put2(out, x.len());
    put(out, x.as_slice());
    assert(out@ =~= o1 + body);
    assert(final(out)@ =~= old(out)@ + new_session_ticket(lifetime, age_add, nonce@, ticket@, max_early));
}

} // verus!
