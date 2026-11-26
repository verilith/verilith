//! The TLS 1.3 key schedule (§7), proven to compute exactly the functions
//! of `spec_keys.rs`. HMAC and SHA-2 are verilith-sha2's, which are
//! themselves proven; nothing here is assumed. Nothing allocates: secrets
//! are 48-byte arrays and the HkdfLabel is fed to HMAC in pieces.
use crate::spec_keys::*;
use verilith_sha2::{HmacSha256, HmacSha384, Sha256, Sha384};
#[cfg(verus_only)]
use verilith_sha2::{spec::sha256, spec512::sha384, spec_hmac::{hmac_sha256, hmac_sha384}};
use vstd::prelude::*;

verus! {

/// `"derived"`
pub const L_DERIVED: [u8; 7] = [100, 101, 114, 105, 118, 101, 100];

/// `"c hs traffic"`
pub const L_C_HS: [u8; 12] = [99, 32, 104, 115, 32, 116, 114, 97, 102, 102, 105, 99];

/// `"s hs traffic"`
pub const L_S_HS: [u8; 12] = [115, 32, 104, 115, 32, 116, 114, 97, 102, 102, 105, 99];

/// `"c ap traffic"`
pub const L_C_AP: [u8; 12] = [99, 32, 97, 112, 32, 116, 114, 97, 102, 102, 105, 99];

/// `"s ap traffic"`
pub const L_S_AP: [u8; 12] = [115, 32, 97, 112, 32, 116, 114, 97, 102, 102, 105, 99];

/// `"exp master"`
pub const L_EXP: [u8; 10] = [101, 120, 112, 32, 109, 97, 115, 116, 101, 114];

/// `"res master"`
pub const L_RES: [u8; 10] = [114, 101, 115, 32, 109, 97, 115, 116, 101, 114];

/// `"key"`
pub const L_KEY: [u8; 3] = [107, 101, 121];

/// `"iv"`
pub const L_IV: [u8; 2] = [105, 118];

/// `"finished"`
pub const L_FINISHED: [u8; 8] = [102, 105, 110, 105, 115, 104, 101, 100];

/// `"traffic upd"`
pub const L_UPD: [u8; 11] = [116, 114, 97, 102, 102, 105, 99, 32, 117, 112, 100];

/// `"tls13 "`
pub const L_TLS13: [u8; 6] = [116, 108, 115, 49, 51, 32];

/// A secret, key, IV or hash: up to 48 bytes.
#[derive(Clone, Copy)]
pub struct Secret {
    bytes: [u8; 48],
    len: usize,
}

impl View for Secret {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.bytes@.take(self.len as int)
    }
}

impl Secret {
    pub closed spec fn wf(&self) -> bool {
        self.len <= 48
    }

    #[inline(always)]
    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self@.len(),
    {
        self.len
    }

    /// Its bytes.
    #[inline(always)]
    pub fn as_slice(&self) -> (r: &[u8])
        requires
            self.wf(),
        ensures
            r@ == self@,
    {
        let s = vstd::array::array_as_slice(&self.bytes);
        vstd::slice::slice_subrange(s, 0, self.len)
    }

    /// The first `l` bytes of `src`.
    fn from_slice(src: &[u8], l: usize) -> (r: Secret)
        requires
            l <= src@.len(),
            l <= 48,
        ensures
            r.wf(),
            r@.len() == l,
            r@ == src@.take(l as int),
    {
        let mut b = [0u8; 48];
        let mut i: usize = 0;
        while i < l
            invariant
                i <= l <= 48,
                l <= src@.len(),
                forall|j: int| 0 <= j < i ==> b@[j] == src@[j],
            decreases l - i,
        {
            b[i] = src[i];
            i = i + 1;
        }
        let r = Secret { bytes: b, len: l };
        assert(r@ =~= src@.take(l as int));
        r
    }

    /// Zeros, `Hash.length` of them.
    fn zeros_of(a: HashAlg) -> (r: Secret)
        ensures
            r.wf(),
            r@.len() == hash_len(a),
            r@ == zeros(hash_len(a)),
    {
        let l = hash_len_x(a);
        let r = Secret { bytes: [0u8; 48], len: l };
        assert(r@ =~= zeros(hash_len(a)));
        r
    }
}

#[inline(always)]
pub fn hash_len_x(a: HashAlg) -> (r: usize)
    ensures
        r == hash_len(a),
        r == 32 || r == 48,
{
    match a {
        HashAlg::Sha256 => 32,
        HashAlg::Sha384 => 48,
    }
}

/// A running transcript hash (§4.4.1): every handshake message given to
/// `update`, in order.
#[derive(Clone, Copy)]
pub enum Transcript {
    S256(Sha256),
    S384(Sha384),
}

impl Transcript {
    pub open spec fn alg(&self) -> HashAlg {
        match self {
            Transcript::S256(_) => HashAlg::Sha256,
            Transcript::S384(_) => HashAlg::Sha384,
        }
    }

    pub open spec fn data(&self) -> Seq<u8> {
        match self {
            Transcript::S256(h) => h.data(),
            Transcript::S384(h) => h.data(),
        }
    }

    pub open spec fn wf(&self) -> bool {
        match self {
            Transcript::S256(h) => h.wf(),
            Transcript::S384(h) => h.wf(),
        }
    }

    pub fn new(a: HashAlg) -> (r: Transcript)
        ensures
            r.wf(),
            r.alg() == a,
            r.data() == Seq::<u8>::empty(),
    {
        match a {
            HashAlg::Sha256 => Transcript::S256(Sha256::new()),
            HashAlg::Sha384 => Transcript::S384(Sha384::new()),
        }
    }

    pub fn update(&mut self, d: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).alg() == old(self).alg(),
            final(self).data() == old(self).data() + d@,
    {
        match self {
            Transcript::S256(h) => h.update(d),
            Transcript::S384(h) => h.update(d),
        }
    }

    /// `Transcript-Hash` of everything so far; the transcript goes on.
    pub fn hash(&self) -> (r: Secret)
        requires
            self.wf(),
        ensures
            r.wf(),
            r@.len() == hash_len(self.alg()),
            r@ == hash(self.alg(), self.data()),
    {
        match self {
            Transcript::S256(h) => {
                let d = h.finalize();
                Secret::from_slice(&d, 32)
            },
            Transcript::S384(h) => {
                let d = h.finalize();
                Secret::from_slice(&d, 48)
            },
        }
    }
}

/// `HMAC(k, m1 | m2 | ... )` over up to six pieces.
fn hmac6(a: HashAlg, k: &[u8], m: [&[u8]; 6]) -> (r: Secret)
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == hmac(a, k@, m[0]@ + m[1]@ + m[2]@ + m[3]@ + m[4]@ + m[5]@),
{
    match a {
        HashAlg::Sha256 => {
            let mut h = HmacSha256::new(k);
            h.update(m[0]);
            h.update(m[1]);
            h.update(m[2]);
            h.update(m[3]);
            h.update(m[4]);
            h.update(m[5]);
            let t = h.finalize();
            assert(Seq::<u8>::empty() + m[0]@ =~= m[0]@);
            Secret::from_slice(&t, 32)
        },
        HashAlg::Sha384 => {
            let mut h = HmacSha384::new(k);
            h.update(m[0]);
            h.update(m[1]);
            h.update(m[2]);
            h.update(m[3]);
            h.update(m[4]);
            h.update(m[5]);
            let t = h.finalize();
            assert(Seq::<u8>::empty() + m[0]@ =~= m[0]@);
            Secret::from_slice(&t, 48)
        },
    }
}

/// `HMAC(k, m)`.
pub fn hmac_x(a: HashAlg, k: &[u8], m: &[u8]) -> (r: Secret)
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == hmac(a, k@, m@),
{
    let e: [u8; 0] = [];
    let es = vstd::array::array_as_slice(&e);
    let r = hmac6(a, k, [m, es, es, es, es, es]);
    assert(m@ + es@ + es@ + es@ + es@ + es@ =~= m@);
    r
}

/// For `1 <= l <= Hash.length`, HKDF-Expand is the first `l` bytes of
/// `T(1)`.
proof fn lemma_expand_one(a: HashAlg, prk: Seq<u8>, info: Seq<u8>, l: nat)
    requires
        1 <= l <= hash_len(a),
    ensures
        hkdf_expand(a, prk, info, l) == hmac(a, prk, info + seq![1u8]).take(l as int),
{
    let hl = hash_len(a);
    assert((l + hl - 1) as int / hl as int == 1) by (nonlinear_arith)
        requires
            1 <= l <= hl,
            hl == 32 || hl == 48,
    ;
    assert(t_block(a, prk, info, 0) == Seq::<u8>::empty());
    assert(Seq::<u8>::empty() + info =~= info);
    assert(t_concat(a, prk, info, 0) == Seq::<u8>::empty());
    assert(t_concat(a, prk, info, 1) =~= t_block(a, prk, info, 1));
}

/// `HKDF-Expand-Label(secret, label, ctx, l)`, for `l` up to
/// `Hash.length` (all TLS 1.3 needs).
pub fn expand_label_x(a: HashAlg, secret: &[u8], label: &[u8], ctx: &[u8], l: usize) -> (r: Secret)
    requires
        1 <= l <= hash_len(a),
        label@.len() <= 249,
        ctx@.len() <= 255,
    ensures
        r.wf(),
        r@.len() == l,
        r@ == expand_label(a, secret@, label@, ctx@, l as nat),
{
    let hdr: [u8; 3] = [(l / 256) as u8, (l % 256) as u8, (6 + label.len()) as u8];
    let cl: [u8; 2] = [ctx.len() as u8, 1u8];
    let tls13 = L_TLS13;
    let h = vstd::array::array_as_slice(&hdr);
    let t = vstd::array::array_as_slice(&tls13);
    let c0 = vstd::slice::slice_subrange(vstd::array::array_as_slice(&cl), 0, 1);
    let c1 = vstd::slice::slice_subrange(vstd::array::array_as_slice(&cl), 1, 2);
    let full = hmac6(a, secret, [h, t, label, c0, ctx, c1]);
    proof {
        assert(h@ =~= seq![(l / 256) as u8, (l % 256) as u8, (6 + label@.len()) as u8]);
        assert(t@ =~= l_tls13());
        assert(c0@ =~= seq![ctx@.len() as u8]);
        assert(c1@ =~= seq![1u8]);
        assert(h@ + t@ + label@ + c0@ + ctx@ + c1@ =~= hkdf_label(l as nat, label@, ctx@) + seq![
            1u8,
        ]);
        lemma_expand_one(a, secret@, hkdf_label(l as nat, label@, ctx@), l as nat);
    }
    let r = Secret::from_slice(full.as_slice(), l);
    assert(r@ =~= full@.take(l as int));
    r
}

/// `Derive-Secret(secret, label, Messages)`, given `th` =
/// `Transcript-Hash(Messages)`.
pub fn derive_secret_x(a: HashAlg, secret: &Secret, label: &[u8], th: &Secret, Ghost(messages): Ghost<
    Seq<u8>,
>) -> (r: Secret)
    requires
        secret.wf(),
        th.wf(),
        th@ == hash(a, messages),
        label@.len() <= 249,
        th@.len() <= 255,
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == derive_secret(a, secret@, label@, messages),
{
    expand_label_x(a, secret.as_slice(), label, th.as_slice(), hash_len_x(a))
}

/// `Transcript-Hash` of no messages.
fn empty_hash(a: HashAlg) -> (r: Secret)
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == hash(a, Seq::empty()),
{
    Transcript::new(a).hash()
}

/// The Handshake Secret, from the (EC)DHE shared secret, with no PSK.
pub fn handshake_secret_x(a: HashAlg, dhe: &[u8]) -> (r: Secret)
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == handshake_secret(a, dhe@),
{
    let z = Secret::zeros_of(a);
    let early = hmac_x(a, z.as_slice(), z.as_slice());
    let eh = empty_hash(a);
    let derived = derive_secret_x(a, &early, &L_DERIVED, &eh, Ghost(Seq::empty()));
    proof {
        assert(L_DERIVED@ =~= l_derived());
    }
    hmac_x(a, derived.as_slice(), dhe)
}

/// The Master Secret, from the Handshake Secret.
pub fn master_secret_x(a: HashAlg, hs: &Secret, Ghost(dhe): Ghost<Seq<u8>>) -> (r: Secret)
    requires
        hs.wf(),
        hs@ == handshake_secret(a, dhe),
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == master_secret(a, dhe),
{
    let eh = empty_hash(a);
    let derived = derive_secret_x(a, hs, &L_DERIVED, &eh, Ghost(Seq::empty()));
    let z = Secret::zeros_of(a);
    proof {
        assert(L_DERIVED@ =~= l_derived());
    }
    hmac_x(a, derived.as_slice(), z.as_slice())
}

/// client_ and server_handshake_traffic_secret, given the transcript hash
/// of ClientHello to ServerHello.
pub fn hs_traffic_x(a: HashAlg, hs: &Secret, th: &Secret, Ghost(dhe): Ghost<Seq<u8>>, Ghost(messages): Ghost<
    Seq<u8>,
>) -> (r: (Secret, Secret))
    requires
        hs.wf(),
        th.wf(),
        hs@ == handshake_secret(a, dhe),
        th@ == hash(a, messages),
        th@.len() <= 255,
    ensures
        r.0.wf() && r.1.wf(),
        r.0@.len() == hash_len(a) && r.1@.len() == hash_len(a),
        r.0@ == client_hs_traffic(a, dhe, messages),
        r.1@ == server_hs_traffic(a, dhe, messages),
{
    let c = derive_secret_x(a, hs, &L_C_HS, th, Ghost(messages));
    let s = derive_secret_x(a, hs, &L_S_HS, th, Ghost(messages));
    proof {
        assert(L_C_HS@ =~= l_c_hs());
        assert(L_S_HS@ =~= l_s_hs());
    }
    (c, s)
}

/// client_ and server_application_traffic_secret_0 and
/// exporter_master_secret, given the transcript hash of ClientHello to
/// server Finished.
pub fn ap_traffic_x(a: HashAlg, ms: &Secret, th: &Secret, Ghost(dhe): Ghost<Seq<u8>>, Ghost(messages): Ghost<
    Seq<u8>,
>) -> (r: (Secret, Secret, Secret))
    requires
        ms.wf(),
        th.wf(),
        ms@ == master_secret(a, dhe),
        th@ == hash(a, messages),
        th@.len() <= 255,
    ensures
        r.0.wf() && r.1.wf() && r.2.wf(),
        r.0@.len() == hash_len(a) && r.1@.len() == hash_len(a) && r.2@.len() == hash_len(a),
        r.0@ == client_ap_traffic(a, dhe, messages),
        r.1@ == server_ap_traffic(a, dhe, messages),
        r.2@ == exporter_master(a, dhe, messages),
{
    let c = derive_secret_x(a, ms, &L_C_AP, th, Ghost(messages));
    let s = derive_secret_x(a, ms, &L_S_AP, th, Ghost(messages));
    let e = derive_secret_x(a, ms, &L_EXP, th, Ghost(messages));
    proof {
        assert(L_C_AP@ =~= l_c_ap());
        assert(L_S_AP@ =~= l_s_ap());
        assert(L_EXP@ =~= l_exp());
    }
    (c, s, e)
}

/// resumption_master_secret, given the transcript hash of ClientHello to
/// client Finished.
pub fn resumption_master_x(a: HashAlg, ms: &Secret, th: &Secret, Ghost(dhe): Ghost<Seq<u8>>, Ghost(messages): Ghost<
    Seq<u8>,
>) -> (r: Secret)
    requires
        ms.wf(),
        th.wf(),
        ms@ == master_secret(a, dhe),
        th@ == hash(a, messages),
        th@.len() <= 255,
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == resumption_master(a, dhe, messages),
{
    proof {
        assert(L_RES@ =~= l_res());
    }
    derive_secret_x(a, ms, &L_RES, th, Ghost(messages))
}

/// The next application traffic secret (§7.2).
pub fn next_traffic_secret_x(a: HashAlg, s: &Secret) -> (r: Secret)
    requires
        s.wf(),
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == next_traffic_secret(a, s@),
{
    let e: [u8; 0] = [];
    proof {
        assert(L_UPD@ =~= l_upd());
        assert(vstd::array::array_view(e) =~= Seq::<u8>::empty());
    }
    expand_label_x(a, s.as_slice(), &L_UPD, vstd::array::array_as_slice(&e), hash_len_x(a))
}

/// The traffic key (of `key_len` bytes: 16 or 32) and IV of a secret
/// (§7.3).
pub fn traffic_keys_x(a: HashAlg, s: &Secret, key_len: usize) -> (r: (Secret, Secret))
    requires
        s.wf(),
        key_len == 16 || key_len == 32,
    ensures
        r.0.wf() && r.1.wf(),
        r.0@.len() == key_len,
        r.1@.len() == 12,
        r.0@ == traffic_key(a, s@, key_len as nat),
        r.1@ == traffic_iv(a, s@),
{
    let e: [u8; 0] = [];
    let es = vstd::array::array_as_slice(&e);
    proof {
        assert(L_KEY@ =~= l_key());
        assert(L_IV@ =~= l_iv());
        assert(es@ =~= Seq::<u8>::empty());
    }
    let k = expand_label_x(a, s.as_slice(), &L_KEY, es, key_len);
    let iv = expand_label_x(a, s.as_slice(), &L_IV, es, 12);
    (k, iv)
}

/// `verify_data` of a Finished message (§4.4.4), given the transcript
/// hash `th` of the messages it covers.
pub fn verify_data_x(a: HashAlg, base: &Secret, th: &Secret, Ghost(messages): Ghost<Seq<u8>>) -> (r: Secret)
    requires
        base.wf(),
        th.wf(),
        th@ == hash(a, messages),
    ensures
        r.wf(),
        r@.len() == hash_len(a),
        r@ == verify_data(a, base@, messages),
{
    let e: [u8; 0] = [];
    let es = vstd::array::array_as_slice(&e);
    proof {
        assert(L_FINISHED@ =~= l_finished());
        assert(es@ =~= Seq::<u8>::empty());
    }
    let fk = expand_label_x(a, base.as_slice(), &L_FINISHED, es, hash_len_x(a));
    hmac_x(a, fk.as_slice(), th.as_slice())
}

// ---------------------------------------------------------------------------
// Record nonces (§5.3)
// ---------------------------------------------------------------------------

proof fn lemma_pow256_pos(n: nat)
    ensures
        pow256(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow256_pos((n - 1) as nat);
    }
}

/// The nonce of the record with sequence number `seq`.
pub fn record_nonce_x(iv: &[u8; 12], seq: u64) -> (r: [u8; 12])
    ensures
        r@ == record_nonce(iv@, seq),
{
    let mut out = *iv;
    let mut s = seq;
    let mut i: usize = 12;
    assert(pow256(0) == 1);
    while i > 4
        invariant
            4 <= i <= 12,
            s as nat == seq as nat / pow256((12 - i) as nat),
            forall|j: int| 0 <= j < i ==> out@[j] == iv@[j],
            forall|j: int| i <= j < 12 ==> out@[j] == iv@[j] ^ seq_byte(seq, j),
        decreases i,
    {
        i = i - 1;
        out[i] = iv[i] ^ ((s % 256) as u8);
        proof {
            lemma_pow256_pos((11 - i) as nat);
            assert(pow256((12 - i) as nat) == 256 * pow256((11 - i) as nat));
            vstd::arithmetic::div_mod::lemma_div_denominator(
                seq as int,
                pow256((11 - i) as nat) as int,
                256,
            );
            assert(seq_byte(seq, i as int) == ((seq as nat / pow256((11 - i) as nat)) % 256) as u8);
        }
        s = s / 256;
        proof {
            assert(pow256((11 - i) as nat) * 256 == 256 * pow256((11 - i) as nat)) by (nonlinear_arith);
        }
    }
    proof {
        assert forall|j: int| 0 <= j < 4 implies seq_byte(seq, j) == 0u8 by {}
        assert forall|j: int| 0 <= j < 4 implies out@[j] == iv@[j] ^ 0u8 by {
            let x = iv@[j];
            assert(x ^ 0u8 == x) by (bit_vector);
        }
        assert(out@ =~= record_nonce(iv@, seq));
    }
    out
}

} // verus!
