//! QUIC packet protection (RFC 9001 §5): the AEAD over a packet's payload
//! with its header as additional data, header protection, and key
//! updates, proven to compute exactly `protected` and its inverse.
//!
//! - [`Aead::seal`] turns a header and payload in a buffer into
//!   `protected`: the payload encrypted with the nonce of §5.3 (the IV
//!   XOR the packet number) and the header as AAD, then the first byte's
//!   low bits (4 for long headers, 5 for short) and the packet number
//!   bytes masked with the header protection mask of a 16-byte sample
//!   taken 4 bytes after the start of the packet number (§5.4.2).
//! - [`unmask`] removes header protection in place and reports the packet
//!   number's length and truncated value; masking is an involution and
//!   the sample is untouched, so on a packet `seal` made it restores the
//!   header (`lemma_unmask_protected`).
//! - [`Aead::open`] then decrypts the payload with the full packet number.
//! - [`keys`] derives a secret's AEAD key, IV and header protection key
//!   (§5.1), and [`update`] the next generation's (§6.1: "quic ku"; the
//!   header protection key is not updated).
//!
//! The AEAD and the header protection cipher are the provider's
//! (`crypto::aead_seal`, `crypto::hp_mask`), trusted.
use crate::crypto::*;
use crate::keys::*;
use crate::server::{suite_hash_x, suite_key_len_x};
use crate::spec_keys::*;
use crate::spec_server::*;
use vstd::prelude::*;

verus! {

/// The first-byte bits header protection masks (§5.4.1): 4 in a long
/// header, 5 in a short one.
pub open spec fn mask_bits(first: u8) -> u8 {
    if first & 0x80 != 0 { 0x0f } else { 0x1f }
}

/// `p` with header protection mask `m` applied (or removed) for a packet
/// number at `pn_off` of `pn_len` bytes.
pub open spec fn apply_mask(p: Seq<u8>, m: Seq<u8>, pn_off: int, pn_len: int) -> Seq<u8> {
    Seq::new(
        p.len(),
        |i: int|
            if i == 0 {
                p[0] ^ (m[0] & mask_bits(p[0]))
            } else if pn_off <= i < pn_off + pn_len {
                p[i] ^ m[1 + i - pn_off]
            } else {
                p[i]
            },
    )
}

/// The header protection sample (§5.4.2).
pub open spec fn sample_of(p: Seq<u8>, pn_off: int) -> Seq<u8> {
    p.subrange(pn_off + 4, pn_off + 20)
}

/// A protected packet (§5.3, §5.4): `hdr` ends with the `pn_len` bytes of
/// the packet number, which starts at `pn_off`.
pub open spec fn protected(
    suite: u16,
    key: Seq<u8>,
    iv: Seq<u8>,
    hp: Seq<u8>,
    pn: u64,
    hdr: Seq<u8>,
    pn_off: int,
    payload: Seq<u8>,
) -> Seq<u8> {
    let p = hdr + aead_seal(suite, key, record_nonce(iv, pn), hdr, payload);
    apply_mask(p, hp_mask(suite, hp, sample_of(p, pn_off)), pn_off, hdr.len() - pn_off)
}

/// A big-endian unsigned integer.
pub open spec fn be(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        be(s.drop_last()) * 256 + s.last() as nat
    }
}

/// Masking twice is the identity, and leaves the sample alone.
pub proof fn lemma_mask_twice(p: Seq<u8>, m: Seq<u8>, pn_off: int, pn_len: int)
    requires
        1 <= pn_off,
        1 <= pn_len <= 4,
        pn_off + 20 <= p.len(),
        m.len() == 5,
    ensures
        apply_mask(apply_mask(p, m, pn_off, pn_len), m, pn_off, pn_len) == p,
        sample_of(apply_mask(p, m, pn_off, pn_len), pn_off) == sample_of(p, pn_off),
        mask_bits(apply_mask(p, m, pn_off, pn_len)[0]) == mask_bits(p[0]),
{
    let q = apply_mask(p, m, pn_off, pn_len);
    let (a, b) = (p[0], m[0]);
    assert((a ^ (b & 0x0f)) & 0x80 == a & 0x80) by (bit_vector);
    assert((a ^ (b & 0x1f)) & 0x80 == a & 0x80) by (bit_vector);
    assert(mask_bits(q[0]) == mask_bits(p[0]));
    let c = mask_bits(p[0]);
    assert((a ^ (b & c)) ^ (b & c) == a) by (bit_vector);
    assert forall|i: int| pn_off <= i < pn_off + pn_len implies (#[trigger] p[i] ^ m[1 + i - pn_off]) ^ m[1 + i
        - pn_off] == p[i] by {
        let (x, y) = (p[i], m[1 + i - pn_off]);
        assert((x ^ y) ^ y == x) by (bit_vector);
    }
    assert(apply_mask(q, m, pn_off, pn_len) =~= p);
    assert(sample_of(q, pn_off) =~= sample_of(p, pn_off));
}

/// One direction's packet protection at one encryption level and key
/// phase: the AEAD key and the IV.
pub struct Aead<K: AeadKey> {
    key: K,
    iv: [u8; 12],
}

impl<K: AeadKey> Aead<K> {
    /// The suite.
    pub closed spec fn suite(&self) -> u16 {
        self.key.suite()
    }

    /// The AEAD key.
    pub closed spec fn key(&self) -> Seq<u8> {
        self.key.key()
    }

    /// The IV.
    pub closed spec fn iv(&self) -> Seq<u8> {
        self.iv@
    }

    /// Protects a packet: `buf[hdr..start]` is its header, whose packet
    /// number `pn` is encoded in `buf[pn_off..start]` (1 to 4 bytes), and
    /// `buf[start..]` its payload, at least `4 - pn_len` bytes so there is
    /// a sample (§5.4.2). On return `buf[hdr..]` is the protected packet.
    pub fn seal<H: HpKey>(&self, hp: &H, pn: u64, buf: &mut Vec<u8>, hdr: usize, pn_off: usize, start: usize)
        requires
            hp.suite() == self.suite(),
            hdr < pn_off < start <= old(buf)@.len(),
            start - pn_off <= 4,
            old(buf)@.len() - pn_off >= 4,
        ensures
            final(buf)@ == old(buf)@.take(hdr as int) + protected(
                self.suite(),
                self.key(),
                self.iv(),
                hp.key(),
                pn,
                old(buf)@.subrange(hdr as int, start as int),
                pn_off - hdr,
                old(buf)@.skip(start as int),
            ),
    {
        let ghost o = buf@;
        let nonce = record_nonce_x(&self.iv, pn);
        self.key.seal_after(&nonce, buf, hdr, start);
        let ghost h = o.subrange(hdr as int, start as int);
        let ghost p = buf@.skip(hdr as int);
        assert(buf@.len() == o.len() + TAG_LEN);
        proof {
            assert(p =~= h + aead_seal(self.suite(), self.key(), nonce@, h, o.skip(start as int)));
        }
        let bl = buf.len();
        let m = hp.mask(slice_sub(buf.as_slice(), pn_off + 4, pn_off + 20));
        proof {
            assert(buf@.subrange(pn_off + 4, pn_off + 20) =~= sample_of(p, pn_off - hdr));
        }
        let ghost before = buf@;
        let bits: u8 = if buf[hdr] & 0x80 != 0 { 0x0f } else { 0x1f };
        let f = buf[hdr] ^ (m[0] & bits);
        buf.set(hdr, f);
        assert(buf@ == before.update(hdr as int, f));
        let mut i = pn_off;
        while i < start
            invariant
                pn_off <= i <= start <= before.len(),
                hdr < pn_off,
                buf@.len() == before.len(),
                buf@[hdr as int] == f,
                forall|j: int| 0 <= j < buf@.len() && j != hdr && !(pn_off <= j < i) ==> buf@[j] == before[j],
                forall|j: int| pn_off <= j < i ==> buf@[j] == before[j] ^ m@[1 + j - pn_off],
                start - pn_off <= 4,
            decreases start - i,
        {
            let b = buf[i] ^ m[1 + i - pn_off];
            buf.set(i, b);
            i = i + 1;
        }
        proof {
            let q = apply_mask(p, m@, pn_off - hdr, start - pn_off);
            assert(buf@ =~= o.take(hdr as int) + q);
        }
    }

    /// Decrypts the payload `buf[start..]` (ciphertext and tag) of a
    /// packet whose header protection is removed, with packet number `pn`
    /// and `buf[..start]` as the header. `Some(n)`: the payload is
    /// `buf[start..start + n]`.
    pub fn open(&self, pn: u64, buf: &mut [u8], start: usize) -> (r: Option<usize>)
        requires
            start <= old(buf)@.len(),
        ensures
            final(buf)@.len() == old(buf)@.len(),
            final(buf)@.take(start as int) == old(buf)@.take(start as int),
            match r {
                Some(n) => start + n <= final(buf)@.len() && aead_open(
                    self.suite(),
                    self.key(),
                    record_nonce(self.iv(), pn),
                    old(buf)@.take(start as int),
                    old(buf)@.skip(start as int),
                ) == Some(final(buf)@.subrange(start as int, start + n)),
                None => aead_open(
                    self.suite(),
                    self.key(),
                    record_nonce(self.iv(), pn),
                    old(buf)@.take(start as int),
                    old(buf)@.skip(start as int),
                ) is None,
            },
    {
        let nonce = record_nonce_x(&self.iv, pn);
        self.key.open_after(&nonce, buf, start)
    }
}

/// `s[a..b]`.
fn slice_sub(s: &[u8], a: usize, b: usize) -> (r: &[u8])
    requires
        a <= b <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    vstd::slice::slice_subrange(s, a, b)
}

/// Removes header protection (§5.4) from the packet `buf`, whose packet
/// number starts at `pn_off`: `Some((pn_len, truncated))`, or `None` if
/// the packet is too short for a sample.
pub fn unmask<H: HpKey>(hp: &H, buf: &mut [u8], pn_off: usize) -> (r: Option<(usize, u32)>)
    requires
        1 <= pn_off,
    ensures
        r is None ==> final(buf)@ == old(buf)@ && old(buf)@.len() < pn_off + 20,
        r matches Some((n, t)) ==> {
            &&& pn_off + 20 <= old(buf)@.len()
            &&& 1 <= n <= 4
            &&& n == (final(buf)@[0] & 3) + 1
            &&& final(buf)@ == apply_mask(
                old(buf)@,
                hp_mask(hp.suite(), hp.key(), sample_of(old(buf)@, pn_off as int)),
                pn_off as int,
                n as int,
            )
            &&& t as nat == be(final(buf)@.subrange(pn_off as int, pn_off + n))
        },
{
    if buf.len() < 20 || pn_off > buf.len() - 20 {
        return None;
    }
    let ghost o = buf@;
    let m = hp.mask(slice_sub(buf, pn_off + 4, pn_off + 20));
    let bits: u8 = if buf[0] & 0x80 != 0 { 0x0f } else { 0x1f };
    let f = buf[0] ^ (m[0] & bits);
    buf[0] = f;
    assert(f & 3 <= 3) by (bit_vector);
    let n = ((f & 3) + 1) as usize;
    let mut t: u32 = 0;
    let mut i = pn_off;
    while i < pn_off + n
        invariant
            1 <= pn_off <= i <= pn_off + n,
            1 <= n <= 4,
            pn_off + 20 <= o.len(),
            buf@.len() == o.len(),
            buf@[0] == f,
            forall|j: int| 1 <= j < o.len() && !(pn_off <= j < i) ==> buf@[j] == o[j],
            forall|j: int| pn_off <= j < i ==> buf@[j] == o[j] ^ m@[1 + j - pn_off],
            t as nat == be(buf@.subrange(pn_off as int, i as int)),
            t < pow256((i - pn_off) as nat),
        decreases pn_off + n - i,
    {
        let ghost prev = buf@.subrange(pn_off as int, i as int);
        let b = buf[i] ^ m[1 + i - pn_off];
        buf[i] = b;
        proof {
            let s = buf@.subrange(pn_off as int, i + 1);
            assert(s.drop_last() =~= prev);
            assert(s.last() == b);
            assert(be(s) == be(prev) * 256 + b as nat);
            lemma_pow256_step((i - pn_off) as nat);
            assert(pow256((i - pn_off) as nat) <= 0x100_0000) by {
                lemma_pow256_le((i - pn_off) as nat, 3);
                reveal_with_fuel(pow256, 4);
            }
        }
        t = t * 256 + b as u32;
        i = i + 1;
    }
    proof {
        assert(buf@ =~= apply_mask(o, m@, pn_off as int, n as int));
    }
    Some((n, t))
}

proof fn lemma_pow256_step(n: nat)
    ensures
        pow256(n + 1) == pow256(n) * 256,
{
    reveal_with_fuel(pow256, 2);
}

proof fn lemma_pow256_le(n: nat, m: nat)
    requires
        n <= m,
    ensures
        pow256(n) <= pow256(m),
    decreases m,
{
    if n < m {
        lemma_pow256_le(n, (m - 1) as nat);
        lemma_pow256_step((m - 1) as nat);
        lemma_pow256_pos((m - 1) as nat);
    }
}

proof fn lemma_pow256_pos(n: nat)
    ensures
        pow256(n) >= 1,
    decreases n,
{
    reveal_with_fuel(pow256, 2);
    if n > 0 {
        lemma_pow256_pos((n - 1) as nat);
        lemma_pow256_step((n - 1) as nat);
    }
}

/// On a packet `Aead::seal` made, `unmask` restores the header and payload
/// ciphertext it encrypted: the packet number length is the header's.
pub proof fn lemma_unmask_protected(
    suite: u16,
    key: Seq<u8>,
    iv: Seq<u8>,
    hp: Seq<u8>,
    pn: u64,
    hdr: Seq<u8>,
    pn_off: int,
    payload: Seq<u8>,
)
    requires
        1 <= pn_off < hdr.len() <= pn_off + 4,
        (hdr[0] & 3) + 1 == hdr.len() - pn_off,
        aead_seal(suite, key, record_nonce(iv, pn), hdr, payload).len() == payload.len() + TAG_LEN,
        payload.len() + hdr.len() - pn_off >= 4,
        hp_mask(suite, hp, sample_of(hdr + aead_seal(suite, key, record_nonce(iv, pn), hdr, payload), pn_off)).len()
            == 5,
    ensures
        ({
            let p = hdr + aead_seal(suite, key, record_nonce(iv, pn), hdr, payload);
            let q = protected(suite, key, iv, hp, pn, hdr, pn_off, payload);
            &&& apply_mask(q, hp_mask(suite, hp, sample_of(q, pn_off)), pn_off, hdr.len() - pn_off) == p
            &&& p[0] == hdr[0]
        }),
{
    let p = hdr + aead_seal(suite, key, record_nonce(iv, pn), hdr, payload);
    let m = hp_mask(suite, hp, sample_of(p, pn_off));
    lemma_mask_twice(p, m, pn_off, hdr.len() - pn_off);
}

/// A secret's packet protection (§5.1): the AEAD key and IV, and the
/// header protection key.
pub fn keys<P: Provider>(prov: &P, suite: u16, sec: &Secret) -> (r: (Aead<P::Key>, P::Hp))
    requires
        sec.wf(),
    ensures
        r.0.suite() == suite && r.1.suite() == suite,
        r.0.key() == quic_key(suite_hash(suite), sec@, suite_key_len(suite)),
        r.0.iv() == quic_iv(suite_hash(suite), sec@),
        r.1.key() == quic_hp(suite_hash(suite), sec@, suite_key_len(suite)),
{
    let a = suite_hash_x(suite);
    let kl = suite_key_len_x(suite);
    let (k, iv, hp) = quic_keys_x(a, sec, kl);
    let mut ivb = [0u8; 12];
    let ivs = iv.as_slice();
    let mut i = 0;
    while i < 12
        invariant
            ivs@ == iv@,
            iv@.len() == 12,
            0 <= i <= 12,
            forall|j: int| 0 <= j < i ==> ivb@[j] == ivs@[j],
        decreases 12 - i,
    {
        ivb[i] = ivs[i];
        i = i + 1;
    }
    assert(ivb@ =~= iv@);
    (Aead { key: prov.aead_key(suite, k.as_slice()), iv: ivb }, prov.hp_key(suite, hp.as_slice()))
}

/// A key update (§6.1): the next secret and its AEAD key and IV.
pub fn update<P: Provider>(prov: &P, suite: u16, sec: &Secret) -> (r: (Secret, Aead<P::Key>))
    requires
        sec.wf(),
    ensures
        r.0.wf(),
        r.0@ == quic_next(suite_hash(suite), sec@),
        r.1.suite() == suite,
        r.1.key() == quic_key(suite_hash(suite), r.0@, suite_key_len(suite)),
        r.1.iv() == quic_iv(suite_hash(suite), r.0@),
{
    let a = suite_hash_x(suite);
    let next = quic_next_x(a, sec);
    let (aead, _) = keys(prov, suite, &next);
    (next, aead)
}

} // verus!
