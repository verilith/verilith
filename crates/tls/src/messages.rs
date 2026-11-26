//! The handshake messages a server sends, proven to be exactly the bytes
//! `spec_server.rs` gives.
use crate::keys::*;
use crate::spec_keys::*;
use crate::spec_server::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

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

/// Appends a ServerHello.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn server_hello_x(out: &mut Vec<u8>, random: &[u8; 32], sid: &[u8], suite: u16, group: u16, share: &[u8])
    requires
        sid@.len() <= 32,
        share@.len() <= 16000,
    ensures
        final(out)@ == old(out)@ + server_hello(random@, sid@, suite, group, share@),
{
    let el = 6 + 4 + 4 + share.len();
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
    put2(out, 43);
    put2(out, 2);
    put1(out, 3);
    put1(out, 4);
    put2(out, 51);
    put2(out, 4 + share.len());
    put2(out, group as usize);
    put2(out, share.len());
    put(out, share);
    proof {
        let ks = be2(group as nat) + be2(share@.len()) + share@;
        let exts = ext_version() + ext(51, ks);
        assert(ks.len() == 4 + share@.len());
        assert(exts.len() == el);
        let body = server_hello_body(random@, sid@, suite, exts);
        assert(body.len() == bl);
        assert(final(out)@ =~= old(out)@ + server_hello(random@, sid@, suite, group, share@));
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

/// Appends EncryptedExtensions.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn encrypted_extensions_x(out: &mut Vec<u8>, alpn: Option<&[u8]>)
    requires
        alpn matches Some(p) ==> p@.len() <= 255,
    ensures
        final(out)@ == old(out)@ + encrypted_extensions(
            match alpn {
                Some(p) => Some(p@),
                None => None,
            },
        ),
{
    match alpn {
        None => {
            put1(out, 8);
            put3(out, 2);
            put2(out, 0);
            assert(final(out)@ =~= old(out)@ + encrypted_extensions(None));
        },
        Some(p) => {
            let n = p.len();
            put1(out, 8);
            put3(out, n + 9);
            put2(out, n + 7);
            put2(out, 16);
            put2(out, n + 3);
            put2(out, n + 1);
            put1(out, n as u8);
            put(out, p);
            proof {
                let e = ext(16, be2(p@.len() + 1) + seq![p@.len() as u8] + p@);
                assert(e.len() == n + 7);
                assert(final(out)@ =~= old(out)@ + encrypted_extensions(Some(p@)));
            }
        },
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

} // verus!
