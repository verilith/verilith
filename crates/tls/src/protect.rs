//! Record protection (§5.2, §5.3), proven to compute exactly
//! `spec_record.rs`, and proven never to use one nonce twice under a key:
//! each direction's sequence number goes up by one per record and stops
//! before it would wrap, and distinct sequence numbers give distinct
//! nonces (`lemma_nonce_injective`).
use crate::crypto::*;
use crate::keys::*;
use crate::spec_keys::*;
use crate::spec_record::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

proof fn lemma_xor_cancel(a: u8, x: u8, y: u8)
    requires
        a ^ x == a ^ y,
    ensures
        x == y,
{
    assert(x == y) by (bit_vector)
        requires
            a ^ x == a ^ y,
    ;
}

/// The value of the sequence number's bytes 4..12 (big-endian).
spec fn digits(seq: u64, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        digits(seq, (k - 1) as nat) * 256 + seq_byte(seq, 4 + k - 1) as nat
    }
}

proof fn lemma_digits(seq: u64, k: nat)
    requires
        k <= 8,
    ensures
        digits(seq, k) == seq as nat / pow256((8 - k) as nat),
    decreases k,
{
    lemma_pow_pos((8 - k) as nat);
    if k == 0 {
        lemma_pow_u64((8 - k) as nat);
        assert(seq as nat / pow256(8) == 0) by {
            vstd::arithmetic::div_mod::lemma_basic_div(seq as int, pow256(8) as int);
        }
    } else {
        lemma_digits(seq, (k - 1) as nat);
        let p = pow256((8 - k) as nat);
        assert(pow256((9 - k) as nat) == 256 * p);
        lemma_pow_pos((8 - k) as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(seq as int, p as int, 256);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(seq as int / p as int, 256);
        assert(p * 256 == 256 * p) by (nonlinear_arith);
        assert(seq_byte(seq, 4 + k - 1) == ((seq as nat / p) % 256) as u8);
    }
}

proof fn lemma_pow_pos(n: nat)
    ensures
        pow256(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow_pos((n - 1) as nat);
    }
}

proof fn lemma_pow_u64(n: nat)
    requires
        n == 8,
    ensures
        pow256(n) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(pow256, 9);
}

/// Distinct sequence numbers give distinct nonces, for any IV.
pub proof fn lemma_nonce_injective(iv: Seq<u8>, a: u64, b: u64)
    requires
        iv.len() == 12,
        record_nonce(iv, a) == record_nonce(iv, b),
    ensures
        a == b,
{
    assert forall|i: int| 4 <= i < 12 implies seq_byte(a, i) == seq_byte(b, i) by {
        let na = record_nonce(iv, a);
        let nb = record_nonce(iv, b);
        assert(na[i] == iv[i] ^ seq_byte(a, i));
        assert(nb[i] == iv[i] ^ seq_byte(b, i));
        assert(na[i] == nb[i]);
        lemma_xor_cancel(iv[i], seq_byte(a, i), seq_byte(b, i));
    }
    lemma_digits_eq(a, b, 8);
    lemma_digits(a, 8);
    lemma_digits(b, 8);
    assert(pow256(0) == 1);
    assert(a as nat / 1 == a as nat);
    assert(b as nat / 1 == b as nat);
}

proof fn lemma_digits_eq(a: u64, b: u64, k: nat)
    requires
        k <= 8,
        forall|i: int| 4 <= i < 12 ==> seq_byte(a, i) == seq_byte(b, i),
    ensures
        digits(a, k) == digits(b, k),
    decreases k,
{
    if k > 0 {
        lemma_digits_eq(a, b, (k - 1) as nat);
    }
}

/// One direction's record protection: its key, IV and next sequence
/// number.
pub struct Protect<K: AeadKey> {
    key: K,
    iv: [u8; 12],
    seq: u64,
}

pub enum RecErr {
    Overflow,
    BadMac,
    NoType,
    Exhausted,
}

impl RecErr {
    pub open spec fn spec(self) -> SpecRecErr {
        match self {
            RecErr::Overflow => SpecRecErr::Overflow,
            RecErr::BadMac => SpecRecErr::BadMac,
            RecErr::NoType => SpecRecErr::NoType,
            RecErr::Exhausted => SpecRecErr::Exhausted,
        }
    }
}

impl<K: AeadKey> Protect<K> {
    pub closed spec fn suite(&self) -> u16 {
        self.key.suite()
    }

    pub closed spec fn key(&self) -> Seq<u8> {
        self.key.key()
    }

    pub closed spec fn iv(&self) -> Seq<u8> {
        self.iv@
    }

    pub closed spec fn seq(&self) -> u64 {
        self.seq
    }

    pub fn new(key: K, iv: &Secret) -> (r: Self)
        requires
            iv.wf(),
            iv@.len() == 12,
        ensures
            r.suite() == key.suite(),
            r.key() == key.key(),
            r.iv() == iv@,
            r.seq() == 0,
    {
        let s = iv.as_slice();
        let mut a = [0u8; 12];
        let mut i: usize = 0;
        while i < 12
            invariant
                i <= 12,
                s@.len() == 12,
                forall|j: int| 0 <= j < i ==> a@[j] == s@[j],
            decreases 12 - i,
        {
            a[i] = s[i];
            i = i + 1;
        }
        assert(a@ =~= iv@);
        Protect { key, iv: a, seq: 0 }
    }

    /// Appends a protected record of type `ct` holding `content` to
    /// `out`; `false`, and nothing written, if the sequence number is
    /// used up.
    pub fn seal(&mut self, ct: u8, content: &[u8], out: &mut Vec<u8>) -> (r: bool)
        requires
            content@.len() <= 16384,
            old(out)@.len() + 16384 + 32 <= usize::MAX,
        ensures
            r == (old(self).seq() < 0xffff_ffff_ffff_ffffu64),
            r ==> final(out)@ == old(out)@ + seal_record(
                old(self).suite(),
                old(self).key(),
                old(self).iv(),
                old(self).seq(),
                ct,
                content@,
            ),
            r ==> final(self).seq() == old(self).seq() + 1,
            r ==> final(out)@.len() == old(out)@.len() + content@.len() + 22,
            !r ==> final(out)@ == old(out)@ && final(self).seq() == old(self).seq(),
            final(self).suite() == old(self).suite(),
            final(self).key() == old(self).key(),
            final(self).iv() == old(self).iv(),
    {
        if self.seq == 0xffff_ffff_ffff_ffffu64 {
            return false;
        }
        let n = content.len() + 1 + TAG_LEN;
        let hdr: [u8; 5] = [23u8, 3u8, 3u8, (n / 256) as u8, (n % 256) as u8];
        let start = out.len();
        let ghost o = out@;
        let mut i: usize = 0;
        while i < 5
            invariant
                i <= 5,
                out@ == o + hdr@.take(i as int),
            decreases 5 - i,
        {
            out.push(hdr[i]);
            assert(o + hdr@.take(i as int + 1) =~= o + hdr@.take(i as int) + seq![hdr@[i as int]]);
            i = i + 1;
        }
        let body = start + 5;
        out.extend_from_slice(content);
        out.push(ct);
        let ghost pt = content@ + seq![ct];
        proof {
            assert(out@.take(body as int) =~= o + hdr@);
            assert(out@.skip(body as int) =~= pt);
        }
        let nonce = record_nonce_x(&self.iv, self.seq);
        self.key.seal_in_place(&nonce, &hdr, out, body);
        proof {
            assert(hdr@ =~= protected_header(n as nat));
            assert(out@ =~= old(out)@ + seal_record(
                self.key.suite(),
                self.key.key(),
                self.iv@,
                self.seq,
                ct,
                content@,
            ));
        }
        self.seq = self.seq + 1;
        true
    }

    #[inline(always)]
    pub fn seq_x(&self) -> (r: u64)
        ensures
            r == self.seq(),
    {
        self.seq
    }

    /// Appends `data` of type `ct` as protected records of at most 2^14
    /// bytes of content; `false`, and nothing written, if the sequence
    /// numbers would run out.
    pub fn seal_all(&mut self, ct: u8, data: &[u8], out: &mut Vec<u8>) -> (r: bool)
        requires
            old(out)@.len() + data@.len() + 22 * (data@.len() / 16384 + 1) + 16384 + 32 <= usize::MAX,
        ensures
            r ==> final(out)@ == old(out)@ + seal_chunks(
                old(self).suite(),
                old(self).key(),
                old(self).iv(),
                old(self).seq(),
                ct,
                data@,
            ),
            r ==> final(self).seq() == old(self).seq() + chunks(data@.len()),
            !r ==> final(out)@ == old(out)@ && final(self).seq() == old(self).seq(),
            r == (old(self).seq() as nat + chunks(data@.len()) < 0xffff_ffff_ffff_ffffu64),
            final(self).suite() == old(self).suite(),
            final(self).key() == old(self).key(),
            final(self).iv() == old(self).iv(),
    {
        reveal(seal_chunks);
        let n = data.len();
        let k: u64 = if n == 0 { 0 } else { ((n - 1) / 16384 + 1) as u64 };
        if self.seq >= 0xffff_ffff_ffff_ffffu64 - k {
            return false;
        }
        let ghost o = out@;
        let ghost seq0 = self.seq;
        let mut p: usize = 0;
        assert(data@.skip(0) =~= data@);
        while p < n
            invariant
                p <= n,
                n == data@.len(),
                p % 16384 == 0 || p == n,
                self.suite() == old(self).suite(),
                self.key() == old(self).key(),
                self.iv() == old(self).iv(),
                self.seq() as nat == seq0 as nat + chunks(p as nat),
                seq0 == old(self).seq(),
                (seq0 as nat) + k < 0xffff_ffff_ffff_ffffu64,
                k == chunks(n as nat),
                out@.len() == o.len() + p + 22 * chunks(p as nat),
                chunks(p as nat) <= n / 16384 + 1,
                o.len() + n + 22 * (n / 16384 + 1) + 16384 + 32 <= usize::MAX,
                o + seal_chunks(self.suite(), self.key(), self.iv(), seq0, ct, data@) == out@
                    + seal_chunks(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    self.seq(),
                    ct,
                    data@.skip(p as int),
                ),
            decreases n - p,
        {
            let m = if n - p > 16384 { 16384 } else { n - p };
            let ghost before = out@;
            let ghost rest = data@.skip(p as int);
            proof {
                assert(chunks(p as nat) < k) by {
                    if p == 0 {
                    } else {
                        assert(p % 16384 == 0);
                        assert((p - 1) / 16384 + 1 == p / 16384) by (nonlinear_arith)
                            requires p % 16384 == 0, p > 0;
                        assert(p / 16384 < (n - 1) / 16384 + 1) by (nonlinear_arith)
                            requires p < n, p % 16384 == 0;
                    }
                }
                assert(rest.take(m as int) =~= data@.subrange(p as int, (p + m) as int));
                assert(rest.skip(m as int) =~= data@.skip((p + m) as int));
            }
            let ok = self.seal(ct, &data[p..p + m], out);
            assert(ok);
            proof {
                assert(data@.subrange(p as int, (p + m) as int) == rest.take(m as int));
                assert(out@ == before + seal_record(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    (self.seq() - 1) as u64,
                    ct,
                    rest.take(m as int),
                ));
                assert(rest.len() > 0);
                assert(seal_chunks(self.suite(), self.key(), self.iv(), (self.seq() - 1) as u64, ct, rest)
                    == seal_record(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    (self.seq() - 1) as u64,
                    ct,
                    rest.take(m as int),
                ) + seal_chunks(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    self.seq(),
                    ct,
                    data@.skip((p + m) as int),
                ));
                vstd::seq_lib::lemma_concat_associative::<u8>(before, seal_record(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    (self.seq() - 1) as u64,
                    ct,
                    rest.take(m as int),
                ), seal_chunks(
                    self.suite(),
                    self.key(),
                    self.iv(),
                    self.seq(),
                    ct,
                    data@.skip((p + m) as int),
                ));
                if p + m < n {
                    assert(m == 16384);
                    assert((p + m) % 16384 == 0) by (nonlinear_arith)
                        requires p % 16384 == 0, m == 16384;
                    assert(chunks((p + m) as nat) == chunks(p as nat) + 1) by (nonlinear_arith)
                        requires p % 16384 == 0, m == 16384, p + m > 0;
                } else {
                    assert(chunks((p + m) as nat) == chunks(p as nat) + 1) by (nonlinear_arith)
                        requires p % 16384 == 0 || p == n, p + m == n, m <= 16384, m > 0,
                            p == 0 || p % 16384 == 0;
                }
                assert(chunks(n as nat) <= n / 16384 + 1) by (nonlinear_arith)
                    requires n > 0;
                assert(chunks((p + m) as nat) <= chunks(n as nat)) by (nonlinear_arith)
                    requires p + m <= n, p + m > 0;
            }
            p = p + m;
        }
        proof {
            assert(data@.skip(n as int).len() == 0);
            assert(o + seal_chunks(self.suite(), self.key(), self.iv(), seq0, ct, data@) =~= out@);
        }
        true
    }

    /// Opens the protected record with header `hdr` and
    /// encrypted_record `body`, in place. `Ok((ct, n))`: the content is
    /// `body[..n]`.
    pub fn open(&mut self, hdr: &[u8; 5], body: &mut [u8]) -> (r: Result<(u8, usize), RecErr>)
        ensures
            match r {
                Ok((ct, n)) => open_record(
                    old(self).suite(),
                    old(self).key(),
                    old(self).iv(),
                    old(self).seq(),
                    hdr@,
                    old(body)@,
                ) == Ok::<(u8, Seq<u8>), SpecRecErr>((ct, final(body)@.take(n as int)))
                    && n < final(body)@.len() && final(self).seq() == old(self).seq() + 1,
                Err(e) => open_record(
                    old(self).suite(),
                    old(self).key(),
                    old(self).iv(),
                    old(self).seq(),
                    hdr@,
                    old(body)@,
                ) == Err::<(u8, Seq<u8>), SpecRecErr>(e.spec()) && final(self).seq() == old(
                    self,
                ).seq(),
            },
            final(self).suite() == old(self).suite(),
            final(self).key() == old(self).key(),
            final(self).iv() == old(self).iv(),
    {
        if self.seq == 0xffff_ffff_ffff_ffffu64 {
            return Err(RecErr::Exhausted);
        }
        if body.len() > 16640 {
            return Err(RecErr::Overflow);
        }
        let nonce = record_nonce_x(&self.iv, self.seq);
        let n = match self.key.open_in_place(&nonce, hdr, body) {
            Some(n) => n,
            None => return Err(RecErr::BadMac),
        };
        if n > 16385 {
            return Err(RecErr::Overflow);
        }
        // The last non-zero byte is the type.
        let ghost inner = body@.take(n as int);
        let mut k = n;
        while k > 0 && body[k - 1] == 0
            invariant
                k <= n,
                n <= body@.len(),
                inner == body@.take(n as int),
                unpad(inner, n as nat) == unpad(inner, k as nat),
            decreases k,
        {
            k = k - 1;
        }
        if k == 0 {
            return Err(RecErr::NoType);
        }
        let ct = body[k - 1];
        self.seq = self.seq + 1;
        proof {
            assert(inner.take(k - 1) =~= body@.take(k - 1));
        }
        Ok((ct, k - 1))
    }
}

} // verus!
