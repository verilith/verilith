//! HMAC (FIPS 198-1, RFC 2104) over each of the six hashes, proven: for
//! any key, and whatever the sizes of the pieces given to `update`,
//! `finalize` returns `spec_hmac::hmac_*` of the key and all of them in
//! order.
//!
//! Each MAC keeps three hashers: the inner hash with K0 ⊕ ipad absorbed
//! and the message so far, the outer hash with K0 ⊕ opad absorbed, and a
//! copy of the inner hash as the key left it, for `reset`. The key is
//! processed once, in `new`; `finalize` costs two compressions of the
//! outer hash (one for the inner digest and the padding, one for K0 ⊕ opad
//! already done) plus the inner hash's padding.
use crate::hash::{sha224, sha256, Sha224, Sha256};
use crate::hash512::{sha384, sha512, sha512_224, sha512_256, Sha384, Sha512, Sha512_224, Sha512_256};
use crate::spec;
use crate::spec512;
use crate::spec_hmac;
use verilith_core::prims::copy_in;
use vstd::prelude::*;

verus! {

/// K0 ⊕ `pad`, for a block of `B` bytes.
#[inline(always)]
fn xor_block<const B: usize>(k0: &[u8; B], pad: u8) -> (r: [u8; B])
    ensures
        r@ == spec_hmac::xor_pad(k0@, pad),
{
    let mut r = [0u8; B];
    let mut i: usize = 0;
    while i < B
        invariant
            i <= B,
            r@.len() == B,
            k0@.len() == B,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] spec_hmac::xor_pad(k0@, pad)[j],
        decreases B - i,
    {
        r[i] = k0[i] ^ pad;
        i = i + 1;
    }
    assert(r@ =~= spec_hmac::xor_pad(k0@, pad));
    r
}

/// The bytes of `d` followed by zeros, in a block of `B` bytes.
#[inline(always)]
fn zero_padded<const B: usize>(d: &[u8]) -> (r: [u8; B])
    requires
        d@.len() <= B,
    ensures
        r@ == d@ + Seq::new((B - d@.len()) as nat, |i: int| 0u8),
{
    let mut r = [0u8; B];
    copy_in(&mut r, 0, d, 0, d.len());
    assert(r@ =~= d@ + Seq::new((B - d@.len()) as nat, |i: int| 0u8));
    r
}

} // verus!

/// One HMAC type: `$name` over the hasher `$h`, whose one-shot function is
/// `$hfn` and specification `$hspec`, with block size `$b` and output size
/// `$l`, proven against `spec_hmac::$mspec`.
macro_rules! hmac_impl {
    ($name:ident, $h:ident, $hfn:ident, $hspec:path, $mspec:ident, $b:literal, $l:literal, $doc:literal) => {
        verus! {

        #[doc = $doc]
        #[derive(Clone, Copy)]
        pub struct $name {
            inner: $h,
            outer: $h,
            /// `inner` as the key left it, for `reset`.
            inner0: $h,
            // Read only by the proofs.
            #[allow(dead_code)]
            key: Ghost<Seq<u8>>,
            data: Ghost<Seq<u8>>,
        }

        impl $name {
            /// The key.
            pub closed spec fn key(&self) -> Seq<u8> {
                self.key@
            }

            /// Every byte given to `update` since `new` or `reset`, in order.
            pub closed spec fn data(&self) -> Seq<u8> {
                self.data@
            }

            pub closed spec fn wf(&self) -> bool {
                let k0 = spec_hmac::key0(|m: Seq<u8>| $hspec(m), $b, self.key@);
                &&& self.inner.wf()
                &&& self.outer.wf()
                &&& self.inner0.wf()
                &&& self.inner0.data() == spec_hmac::xor_pad(k0, spec_hmac::ipad())
                &&& self.inner.data() == spec_hmac::xor_pad(k0, spec_hmac::ipad()) + self.data@
                &&& self.outer.data() == spec_hmac::xor_pad(k0, spec_hmac::opad())
            }

            /// K0 (FIPS 198-1 §4 steps 1 to 3).
            fn key0(key: &[u8]) -> (r: [u8; $b])
                ensures
                    r@ == spec_hmac::key0(|m: Seq<u8>| $hspec(m), $b, key@),
            {
                if key.len() > $b {
                    let d = $hfn(key);
                    zero_padded::<$b>(&d)
                } else {
                    zero_padded::<$b>(key)
                }
            }

            /// A MAC keyed with `key`, of any length.
            pub fn new(key: &[u8]) -> (r: Self)
                ensures
                    r.wf(),
                    r.key() == key@,
                    r.data() == Seq::<u8>::empty(),
            {
                let k0 = Self::key0(key);
                let ip = xor_block(&k0, 0x36);
                let op = xor_block(&k0, 0x5c);
                let mut inner = $h::new();
                inner.update(&ip);
                let mut outer = $h::new();
                outer.update(&op);
                proof {
                    assert(Seq::<u8>::empty() + ip@ =~= ip@);
                    assert(Seq::<u8>::empty() + op@ =~= op@);
                    assert(ip@ + Seq::<u8>::empty() =~= ip@);
                }
                $name { inner, outer, inner0: inner, key: Ghost(key@), data: Ghost(Seq::empty()) }
            }

            /// Continues with the bytes of `d`.
            pub fn update(&mut self, d: &[u8])
                requires
                    old(self).wf(),
                ensures
                    final(self).wf(),
                    final(self).key() == old(self).key(),
                    final(self).data() == old(self).data() + d@,
            {
                let ghost k0 = spec_hmac::key0(|m: Seq<u8>| $hspec(m), $b, self.key@);
                let ghost d0 = self.data@;
                self.inner.update(d);
                self.data = Ghost(d0 + d@);
                assert(spec_hmac::xor_pad(k0, spec_hmac::ipad()) + d0 + d@
                    =~= spec_hmac::xor_pad(k0, spec_hmac::ipad()) + (d0 + d@));
            }

            /// Forgets the message, keeping the key.
            pub fn reset(&mut self)
                requires
                    old(self).wf(),
                ensures
                    final(self).wf(),
                    final(self).key() == old(self).key(),
                    final(self).data() == Seq::<u8>::empty(),
            {
                self.inner = self.inner0;
                self.data = Ghost(Seq::empty());
                let ghost k0 = spec_hmac::key0(|m: Seq<u8>| $hspec(m), $b, self.key@);
                assert(spec_hmac::xor_pad(k0, spec_hmac::ipad()) + Seq::<u8>::empty()
                    =~= spec_hmac::xor_pad(k0, spec_hmac::ipad()));
            }

            /// The MAC of everything so far. The MAC is left as it was, so
            /// it can be continued.
            pub fn finalize(&self) -> (r: [u8; $l])
                requires
                    self.wf(),
                ensures
                    r@ == spec_hmac::$mspec(self.key(), self.data()),
            {
                let ih = self.inner.finalize();
                let mut o = self.outer;
                o.update(&ih);
                o.finalize()
            }

            /// Whether `tag` is the MAC of everything so far, compared in
            /// time that depends only on the lengths.
            pub fn verify(&self, tag: &[u8]) -> (r: bool)
                requires
                    self.wf(),
                ensures
                    r == (tag@ == spec_hmac::$mspec(self.key(), self.data())),
            {
                let t = self.finalize();
                ct_eq(&t, tag)
            }
        }

        /// The MAC of `d` keyed with `key`.
        pub fn $mspec(key: &[u8], d: &[u8]) -> (r: [u8; $l])
            ensures
                r@ == spec_hmac::$mspec(key@, d@),
        {
            let mut m = $name::new(key);
            m.update(d);
            assert(Seq::<u8>::empty() + d@ =~= d@);
            m.finalize()
        }

        } // verus!

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(concat!(stringify!($name), " { .. }"))
            }
        }
    };
}

verus! {

/// Whether `a` and `b` are equal, in time that depends only on their
/// lengths: every byte is read and the differences are OR-ed together.
fn ct_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            (acc == 0) == (forall|j: int| 0 <= j < i ==> a@[j] == b@[j]),
        decreases a@.len() - i,
    {
        let (p, q) = (a[i], b[i]);
        let x = p ^ q;
        proof {
            assert((x == 0) == (p == q)) by (bit_vector)
                requires x == p ^ q;
            assert(((acc | x) == 0) == (acc == 0 && x == 0)) by (bit_vector);
        }
        acc = acc | x;
        i = i + 1;
    }
    proof {
        if acc == 0 {
            assert(a@ =~= b@);
        }
    }
    acc == 0
}

} // verus!

hmac_impl!(HmacSha224, Sha224, sha224, spec::sha224, hmac_sha224, 64, 28, "An HMAC-SHA-224 computation in progress.");
hmac_impl!(HmacSha256, Sha256, sha256, spec::sha256, hmac_sha256, 64, 32, "An HMAC-SHA-256 computation in progress.");
hmac_impl!(HmacSha384, Sha384, sha384, spec512::sha384, hmac_sha384, 128, 48, "An HMAC-SHA-384 computation in progress.");
hmac_impl!(HmacSha512, Sha512, sha512, spec512::sha512, hmac_sha512, 128, 64, "An HMAC-SHA-512 computation in progress.");
hmac_impl!(
    HmacSha512_224,
    Sha512_224,
    sha512_224,
    spec512::sha512_224,
    hmac_sha512_224,
    128,
    28,
    "An HMAC-SHA-512/224 computation in progress."
);
hmac_impl!(
    HmacSha512_256,
    Sha512_256,
    sha512_256,
    spec512::sha512_256,
    hmac_sha512_256,
    128,
    32,
    "An HMAC-SHA-512/256 computation in progress."
);
