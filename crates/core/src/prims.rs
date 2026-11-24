//! Memory primitives with hand-written specs. This file is the trusted base
//! shared by every Verilith library: nothing else in vcore, and
//! nothing in the libraries built on it, needs `unsafe` to read or write
//! memory.
//!
//! The indexing ones (`get`, `get16`, `get32`, `set`, `set16`, `set32`, `store_at`) skip Rust's bounds
//! check: their `requires` clause is the bounds check, and Verus proves it
//! at every call site, so they cannot go out of bounds in verified code.
//! They are themselves verified, against vstd's specs of `get_unchecked`.
//!
//! The rest are trusted (`external_body`): each is a one-line wrapper (six
//! lines for `copy16_pick`) that
//! Verus has no spec for, and the `ensures` clause is the spec. The
//! unaligned ones keep a `debug_assert!` of their precondition for
//! unverified callers. To audit: check each `external_body` function's
//! `ensures` against the line under it.
use vstd::prelude::*;
use alloc::vec::Vec;

verus! {


/// The little-endian value of the 8 bytes at `i`.
pub open spec fn le_word(b: Seq<u8>, i: int) -> nat {
    le_bytes(b, i, 8)
}

/// The little-endian value of the `n` bytes at `i`.
pub open spec fn le_bytes(b: Seq<u8>, i: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        b[i] as nat + 256 * le_bytes(b, i + 1, (n - 1) as nat)
    }
}

/// The little-endian `u64` at `b[i..i + 8]`.
///
/// ```text
/// requires i + 8 <= b@.len()
/// ensures  r as nat == le_word(b@, i as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn load_u64_le(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
    ensures
        r as nat == le_word(b@, i as int),
{
    debug_assert!(i + 8 <= b.len());
    // SAFETY: the precondition puts the 8 bytes inside `b`.
    unsafe { u64::from_le(core::ptr::read_unaligned(b.as_ptr().add(i) as *const u64)) }
}

/// `b[i]`.
///
/// ```text
/// requires i < b@.len()
/// ensures  r == b@[i as int]
/// ```
#[inline(always)]
pub fn get(b: &[u8], i: usize) -> (r: u8)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

/// `b[i]`.
///
/// ```text
/// requires i < b@.len()
/// ensures  r == b@[i as int]
/// ```
#[inline(always)]
pub fn get16(b: &[i16], i: usize) -> (r: i16)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

/// `b[i]`.
///
/// ```text
/// requires i < b@.len()
/// ensures  r == b@[i as int]
/// ```
#[inline(always)]
pub fn get32(b: &[u32], i: usize) -> (r: u32)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

/// Sets `b[i]` to `v`.
///
/// ```text
/// requires i < old(b)@.len()
/// ensures  final(b)@ == old(b)@.update(i as int, v)
/// ```
#[inline(always)]
pub fn set(b: &mut [u8], i: usize, v: u8)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// Sets `b[i]` to `v`.
///
/// ```text
/// requires i < old(b)@.len()
/// ensures  final(b)@ == old(b)@.update(i as int, v)
/// ```
#[inline(always)]
pub fn set16(b: &mut [i16], i: usize, v: i16)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// Sets `b[i]` to `v`.
///
/// ```text
/// requires i < old(b)@.len()
/// ensures  final(b)@ == old(b)@.update(i as int, v)
/// ```
#[inline(always)]
pub fn set32(b: &mut [u32], i: usize, v: u32)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// `v[at] = x` without the bounds check.
#[inline(always)]
pub fn store_at<T>(v: &mut Vec<T>, at: usize, x: T)
    requires
        at < old(v)@.len(),
    ensures
        final(v)@ == old(v)@.update(at as int, x),
{
    let s = v.as_mut_slice();
    // SAFETY: in bounds by the precondition.
    unsafe {
        *s.get_unchecked_mut(at) = x;
    }
}

/// Copies `out[src..src + 8]` to `out[dst..dst + 8]`; the ranges must not
/// overlap.
#[verifier::external_body]
#[inline(always)]
pub fn copy8(out: &mut [u8], src: usize, dst: usize)
    requires
        src + 8 <= dst,
        dst + 8 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
                old(out)@[k - dst + src]
            } else {
                old(out)@[k]
            },
{
    debug_assert!(src + 8 <= dst && dst + 8 <= out.len());
    // SAFETY: both ranges are inside `out` by the precondition.
    unsafe {
        let p = out.as_mut_ptr();
        let w = core::ptr::read_unaligned(p.add(src) as *const u64);
        core::ptr::write_unaligned(p.add(dst) as *mut u64, w);
    }
}

/// Copies `out[src..src + 16]` to `out[dst..dst + 16]`; the ranges must
/// not overlap.
#[verifier::external_body]
#[inline(always)]
pub fn copy16(out: &mut [u8], src: usize, dst: usize)
    requires
        src + 16 <= dst,
        dst + 16 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 16 {
                old(out)@[k - dst + src]
            } else {
                old(out)@[k]
            },
{
    debug_assert!(src + 16 <= dst && dst + 16 <= out.len());
    // SAFETY: both ranges are inside `out` by the precondition.
    unsafe {
        let p = out.as_mut_ptr();
        let w = core::ptr::read_unaligned(p.add(src) as *const [u8; 16]);
        core::ptr::write_unaligned(p.add(dst) as *mut [u8; 16], w);
    }
}

/// `out[dst..dst + 8]` becomes what `out[src..src + 8]` was: the 8 bytes
/// are loaded, then stored, so the ranges may overlap.
#[verifier::external_body]
#[inline(always)]
pub fn move8(out: &mut [u8], src: usize, dst: usize)
    requires
        src + 8 <= old(out)@.len(),
        dst + 8 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
                old(out)@[k - dst + src]
            } else {
                old(out)@[k]
            },
{
    debug_assert!(src + 8 <= out.len() && dst + 8 <= out.len());
    // SAFETY: both ranges are inside `out` by the precondition; the load
    // completes before the store.
    unsafe {
        let p = out.as_mut_ptr();
        let w = core::ptr::read_unaligned(p.add(src) as *const u64);
        core::ptr::write_unaligned(p.add(dst) as *mut u64, w);
    }
}

/// Copies `input[src..src + 16]` to `out[dst..dst + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn copy16_in(out: &mut [u8], dst: usize, input: &[u8], src: usize)
    requires
        src + 16 <= input@.len(),
        dst + 16 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 16 {
                input@[k - dst + src]
            } else {
                old(out)@[k]
            },
{
    debug_assert!(src + 16 <= input.len() && dst + 16 <= out.len());
    // SAFETY: both ranges are inside their slices by the precondition, and
    // `out` and `input` are distinct borrows.
    unsafe {
        let w = core::ptr::read_unaligned(input.as_ptr().add(src) as *const [u8; 16]);
        core::ptr::write_unaligned(out.as_mut_ptr().add(dst) as *mut [u8; 16], w);
    }
}

/// `a` if `c`, otherwise `b`, chosen without a branch. For a choice the
/// processor cannot predict that sits on the path from one step of a
/// loop to the next: the compiler is free to turn an ordinary `if` into
/// a branch there, and this tells it not to.
#[verifier::external_body]
#[inline(always)]
pub fn pick(c: bool, a: usize, b: usize) -> (r: usize)
    ensures
        r == if c {
            a
        } else {
            b
        },
{
    core::hint::select_unpredictable(c, a, b)
}

/// `copy16_in(out, dst, input, src_in)` if `from_input`, otherwise
/// `copy16(out, src_out, dst)`, with the source chosen without a branch.
/// For a decoder whose next element is a literal or a copy and cannot be
/// predicted. The source not chosen need not be in range. The 16 bytes
/// are loaded, then stored, so a source inside `out` may overlap `dst`.
#[verifier::external_body]
#[inline(always)]
pub fn copy16_pick(out: &mut [u8], dst: usize, input: &[u8], src_in: usize, src_out: usize, from_input: bool)
    requires
        dst + 16 <= old(out)@.len(),
        from_input ==> src_in + 16 <= input@.len(),
        !from_input ==> src_out + 16 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 16 {
                if from_input {
                    input@[k - dst + src_in]
                } else {
                    old(out)@[k - dst + src_out]
                }
            } else {
                old(out)@[k]
            },
{
    debug_assert!(dst + 16 <= out.len());
    debug_assert!(if from_input { src_in + 16 <= input.len() } else { src_out + 16 <= out.len() });
    // SAFETY: the 16 bytes written are inside `out`, and the 16 read are
    // inside whichever slice was chosen, by the precondition; they are read
    // before any is written. The address not chosen is formed with wrapping
    // arithmetic and never read.
    unsafe {
        let p = out.as_mut_ptr();
        let a = input.as_ptr().wrapping_add(src_in);
        let b = (p as *const u8).wrapping_add(src_out);
        let s = core::hint::select_unpredictable(from_input, a, b);
        let w = core::ptr::read_unaligned(s as *const [u8; 16]);
        core::ptr::write_unaligned(p.add(dst) as *mut [u8; 16], w);
    }
}

/// Writes 8 copies of `v` at `dst`.
#[verifier::external_body]
#[inline(always)]
pub fn fill8(out: &mut [u8], dst: usize, v: u8)
    requires
        dst + 8 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|k: int|
            0 <= k < final(out)@.len() ==> #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
                v
            } else {
                old(out)@[k]
            },
{
    debug_assert!(dst + 8 <= out.len());
    // SAFETY: inside `out` by the precondition.
    unsafe {
        core::ptr::write_unaligned(out.as_mut_ptr().add(dst) as *mut u64, (v as u64) * 0x0101_0101_0101_0101);
    }
}

/// Copies `input[src..src + n]` to `out[dst..dst + n]`.
#[verifier::external_body]
#[inline]
pub fn copy_in(out: &mut [u8], dst: usize, input: &[u8], src: usize, n: usize)
    requires
        src + n <= input@.len(),
        dst + n <= old(out)@.len(),
    ensures
        final(out)@ == old(out)@.subrange(0, dst as int) + input@.subrange(
            src as int,
            src + n,
        ) + old(out)@.subrange(dst + n, old(out)@.len() as int),
{
    debug_assert!(src + n <= input.len() && dst + n <= out.len());
    // SAFETY: both ranges are inside their slices by the precondition, and
    // `out` and `input` are distinct borrows, so they do not overlap.
    unsafe { core::ptr::copy_nonoverlapping(input.as_ptr().add(src), out.as_mut_ptr().add(dst), n) }
}

/// Copies `b[src..src + n]` to the front of `b`.
#[verifier::external_body]
#[inline]
pub fn copy_to_front(b: &mut [u8], src: usize, n: usize)
    requires
        src + n <= old(b)@.len(),
    ensures
        final(b)@ == old(b)@.subrange(src as int, src + n) + old(b)@.subrange(
            n as int,
            old(b)@.len() as int,
        ),
{
    b.copy_within(src..src + n, 0);
}

/// Appends `s` to `v` (a single `memcpy`).
#[inline]
pub fn extend(v: &mut Vec<u8>, s: &[u8])
    ensures
        final(v)@ == old(v)@ + s@,
{
    v.extend_from_slice(s);
    proof {
        assert forall|i: int| 0 <= i < final(v)@.len() implies #[trigger] final(v)@[i] == (old(
            v,
        )@ + s@)[i] by {
            if i >= old(v)@.len() {
                assert(cloned::<u8>(s@[i - old(v)@.len()], final(v)@[i]));
            }
        }
        assert(final(v)@ =~= old(v)@ + s@);
    }
}

/// `buf[dst..dst + n] = buf[src..src + n]`; the ranges may overlap (a
/// `memmove`).
#[verifier::external_body]
#[inline(always)]
pub fn copy_within(buf: &mut [u8], src: usize, dst: usize, n: usize)
    requires
        src + n <= old(buf)@.len(),
        dst + n <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        forall|j: int|
            0 <= j < final(buf)@.len() ==> #[trigger] final(buf)@[j] == if dst <= j < dst + n {
                old(buf)@[j - dst + src]
            } else {
                old(buf)@[j]
            },
{
    buf.copy_within(src..src + n, dst);
}

/// A vector of `n` zeros, or `None` if the allocation fails.
#[verifier::external_body]
pub fn alloc_u32(n: usize) -> (r: Option<Vec<u32>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u32),
{
    // `alloc_zeroed` gets pages the OS already zeroed, instead of writing
    // `n` zeros through the cache as `resize` does.
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match alloc::alloc::Layout::array::<u32>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    let p = unsafe { alloc::alloc::alloc_zeroed(layout) } as *mut u32;
    if p.is_null() {
        return None;
    }
    Some(unsafe { Vec::from_raw_parts(p, n, n) })
}

} // verus!
