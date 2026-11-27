//! Comparing secrets, and the points where a value computed from secrets
//! is allowed to decide anything.
//!
//! The handshake learns from a secret only whether a MAC matched: the
//! client's Finished (RFC 8446 §4.4.4) and a PSK binder (§4.2.11). Each
//! comparison is [`ct_eq`], whose time depends only on the lengths, and its
//! result goes through [`declassify`], a function the compiler keeps as a
//! call, so that the static check of the machine code (`scripts/ctcheck.py`)
//! sees where a secret becomes public and treats only that value as public.
use vstd::prelude::*;

verus! {

proof fn lemma_or_xor(acc: u8, x: u8, y: u8)
    ensures
        ((acc | (x ^ y)) == 0) == (acc == 0 && x == y),
{
    assert(((acc | (x ^ y)) == 0) == (acc == 0 && x == y)) by (bit_vector);
}

/// Whether `a` and `b` are equal, in time that depends only on their
/// lengths. The result is secret until it is passed to [`declassify`].
pub fn ct_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    let n = a.len();
    if b.len() != n {
        return false;
    }
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            (acc == 0) == (forall|j: int| 0 <= j < i ==> a@[j] == b@[j]),
        decreases n - i,
    {
        proof {
            lemma_or_xor(acc, a@[i as int], b@[i as int]);
        }
        acc = acc | (a[i] ^ b[i]);
        i = i + 1;
    }
    proof {
        if acc == 0 {
            assert(a@ =~= b@);
        }
    }
    acc == 0
}

/// `b`, made public. Trusted to return `b`; kept out of line (and opaque to
/// the optimizer, through `black_box`) so that a decision on it is a
/// decision on the call's result, where the binary check can see it.
#[verifier::external_body]
#[inline(never)]
pub fn declassify(b: bool) -> (r: bool)
    ensures
        r == b,
{
    #[cfg(all(feature = "ctgrind", target_arch = "x86_64"))]
    valgrind_defined(&b);
    core::hint::black_box(b)
}

} // verus!

/// Under Valgrind (the `ctgrind` feature, for `examples/ctgrind.rs` only):
/// tells memcheck that `b` is defined, as declassifying it says. Elsewhere,
/// and without Valgrind, a no-op.
#[cfg(all(feature = "ctgrind", target_arch = "x86_64"))]
fn valgrind_defined(b: &bool) {
    const MC: usize = (b'M' as usize) << 24 | (b'C' as usize) << 16;
    let args: [usize; 6] = [MC + 2, b as *const bool as usize, 1, 0, 0, 0];
    // SAFETY: Valgrind's client-request sequence: rotates rdi by 128 bits
    // in all (leaving it as it was) and exchanges rbx with itself.
    unsafe {
        core::arch::asm!(
            "rol rdi, 3", "rol rdi, 13", "rol rdi, 61", "rol rdi, 51", "xchg rbx, rbx",
            inout("rdx") 0usize => _,
            in("rax") args.as_ptr(),
            inout("rdi") 0usize => _,
            options(nostack),
        );
    }
}

