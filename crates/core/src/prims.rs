//! Memory primitives with hand-written specs. This file is the trusted base
//! shared by every Verilith library: nothing else in vcore, and
//! nothing in the libraries built on it, needs `unsafe` to read or write
//! memory.
//!
//! The indexing ones (`get`, `get16`, `get32`, `set`, `set16`, `set32`, `store_at`) skip Rust's bounds
//! check: their `requires` clause is the bounds check, and Verus proves it
//! at every call site, so they cannot go out of bounds in verified code.
//! They are themselves verified, against vstd's specs of `get_unchecked`.
//! So are the loads and copies (`load_u64_le`, `copy8`, `copy16`, `move8`,
//! `copy16_in`, `fill8`, `copy_in`, `copy_to_front`, `copy_within`): they
//! read and write through `get_unchecked`, `get_unchecked_mut`,
//! `copy_from_slice` and `copy_within`, and with a fixed length LLVM
//! compiles each to the one load or store the unsafe version was.
//!
//! The rest are trusted (`external_body`): each is a one-line wrapper (six
//! lines for `copy16_pick`) that
//! Verus has no spec for, and the `ensures` clause is the spec.
//! To audit: check each `external_body` function's
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
#[inline(always)]
pub fn load_u64_le(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
    ensures
        r as nat == le_word(b@, i as int),
{
    // Eight byte loads that LLVM combines into one unaligned load.
    let w = bytes8(b, i);
    let x7 = w[7] as u64;
    assert(x7 * 256 < 0x1_0000) by (nonlinear_arith) requires x7 < 256;
    let x6 = w[6] as u64 + x7 * 256;
    assert(x6 * 256 < 0x100_0000) by (nonlinear_arith) requires x6 < 0x1_0000;
    let x5 = w[5] as u64 + x6 * 256;
    assert(x5 * 256 < 0x1_0000_0000) by (nonlinear_arith) requires x5 < 0x100_0000;
    let x4 = w[4] as u64 + x5 * 256;
    assert(x4 * 256 < 0x100_0000_0000) by (nonlinear_arith) requires x4 < 0x1_0000_0000;
    let x3 = w[3] as u64 + x4 * 256;
    assert(x3 * 256 < 0x1_0000_0000_0000) by (nonlinear_arith) requires x3 < 0x100_0000_0000;
    let x2 = w[2] as u64 + x3 * 256;
    assert(x2 * 256 < 0x100_0000_0000_0000) by (nonlinear_arith) requires x2 < 0x1_0000_0000_0000;
    let x1 = w[1] as u64 + x2 * 256;
    assert(x1 * 256 <= 0xFFFF_FFFF_FFFF_FF00) by (nonlinear_arith) requires x1 < 0x100_0000_0000_0000;
    let x0 = w[0] as u64 + x1 * 256;
    proof {
        reveal_with_fuel(le_bytes, 9);
        assert(w@ == b@.subrange(i as int, i + 8));
        assert(w@[0] == b@[i as int] && w@[1] == b@[i + 1] && w@[2] == b@[i + 2] && w@[3] == b@[i + 3]);
        assert(w@[4] == b@[i + 4] && w@[5] == b@[i + 5] && w@[6] == b@[i + 6] && w@[7] == b@[i + 7]);
    }
    x0
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

// ---------------------------------------------------------------------------
// Unchecked loads and stores of byte ranges, through vstd's specs of
// `get_unchecked`, `get_unchecked_mut` and `copy_from_slice`. With a
// constant length, each compiles to one load or one store.
// ---------------------------------------------------------------------------

/// `b[i..i + n]`, without the bounds check.
#[inline(always)]
fn get_range(b: &[u8], i: usize, n: usize) -> (r: &[u8])
    requires
        i + n <= b@.len(),
    ensures
        r@ == b@.subrange(i as int, i + n),
{
    let _ = b.len();  // bounds `i + n` by `usize::MAX` for Verus
    // SAFETY: in bounds by the precondition.
    unsafe { b.get_unchecked(i..i + n) }
}

/// The 8 bytes at `i`.
#[inline(always)]
fn bytes8(b: &[u8], i: usize) -> (r: [u8; 8])
    requires
        i + 8 <= b@.len(),
    ensures
        r@ == b@.subrange(i as int, i + 8),
{
    let mut w = [0u8; 8];
    w.copy_from_slice(get_range(b, i, 8));
    w
}

/// The 16 bytes at `i`.
#[inline(always)]
fn bytes16(b: &[u8], i: usize) -> (r: [u8; 16])
    requires
        i + 16 <= b@.len(),
    ensures
        r@ == b@.subrange(i as int, i + 16),
{
    let mut w = [0u8; 16];
    w.copy_from_slice(get_range(b, i, 16));
    w
}

/// Writes `w` at `out[dst..]`, without the bounds check.
#[inline(always)]
fn put_at(out: &mut [u8], dst: usize, w: &[u8])
    requires
        dst + w@.len() <= old(out)@.len(),
    ensures
        final(out)@ == old(out)@.subrange(0, dst as int) + w@ + old(out)@.subrange(
            dst + w@.len(),
            old(out)@.len() as int,
        ),
{
    let n = w.len();
    let _ = out.len();  // bounds `dst + n` by `usize::MAX` for Verus
    // SAFETY: in bounds by the precondition.
    let d = unsafe { out.get_unchecked_mut(dst..dst + n) };
    d.copy_from_slice(w);
}

/// Copies `out[src..src + 8]` to `out[dst..dst + 8]`; the ranges must not
/// overlap.
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
    let w = bytes8(out, src);
    put_at(out, dst, &w);
    proof {
        assert forall|k: int| 0 <= k < final(out)@.len() implies #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
            old(out)@[k - dst + src]
        } else {
            old(out)@[k]
        } by {}
    }
}

/// Copies `out[src..src + 16]` to `out[dst..dst + 16]`; the ranges must
/// not overlap.
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
    let w = bytes16(out, src);
    put_at(out, dst, &w);
    proof {
        assert forall|k: int| 0 <= k < final(out)@.len() implies #[trigger] final(out)@[k] == if dst <= k < dst + 16 {
            old(out)@[k - dst + src]
        } else {
            old(out)@[k]
        } by {}
    }
}

/// `out[dst..dst + 8]` becomes what `out[src..src + 8]` was: the 8 bytes
/// are loaded, then stored, so the ranges may overlap.
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
    let w = bytes8(out, src);
    put_at(out, dst, &w);
    proof {
        assert forall|k: int| 0 <= k < final(out)@.len() implies #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
            old(out)@[k - dst + src]
        } else {
            old(out)@[k]
        } by {}
    }
}

/// Copies `input[src..src + 16]` to `out[dst..dst + 16]`.
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
    let w = bytes16(input, src);
    put_at(out, dst, &w);
    proof {
        assert forall|k: int| 0 <= k < final(out)@.len() implies #[trigger] final(out)@[k] == if dst <= k < dst + 16 {
            input@[k - dst + src]
        } else {
            old(out)@[k]
        } by {}
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
    let w = [v; 8];
    put_at(out, dst, &w);
    proof {
        assert forall|k: int| 0 <= k < final(out)@.len() implies #[trigger] final(out)@[k] == if dst <= k < dst + 8 {
            v
        } else {
            old(out)@[k]
        } by {}
    }
}

/// Copies `input[src..src + n]` to `out[dst..dst + n]`.
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
    let w = get_range(input, src, n);
    put_at(out, dst, w);
    proof {
        assert(final(out)@ =~= old(out)@.subrange(0, dst as int) + input@.subrange(src as int, src + n)
            + old(out)@.subrange(dst + n, old(out)@.len() as int));
    }
}

/// Copies `b[src..src + n]` to the front of `b`.
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
    let _ = b.len();  // bounds `src + n` by `usize::MAX` for Verus
    b.copy_within(src..src + n, 0);
    proof {
        assert(final(b)@ =~= old(b)@.subrange(src as int, src + n) + old(b)@.subrange(n as int, old(b)@.len() as int));
    }
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
    let _ = buf.len();  // bounds `src + n` by `usize::MAX` for Verus
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

/// A vector of `n` zero bytes, or `None` if the allocation fails.
#[verifier::external_body]
pub fn alloc_u8(n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u8),
{
    // As in `alloc_u32`: large allocations come from `calloc`, which maps
    // zeroed pages lazily.
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match alloc::alloc::Layout::array::<u8>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    let p = unsafe { alloc::alloc::alloc_zeroed(layout) };
    if p.is_null() {
        return None;
    }
    Some(unsafe { Vec::from_raw_parts(p, n, n) })
}

/// A vector of `n` zeros, or `None` if the allocation fails.
#[verifier::external_body]
pub fn alloc_i16(n: usize) -> (r: Option<Vec<i16>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0i16),
{
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match alloc::alloc::Layout::array::<i16>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    let p = unsafe { alloc::alloc::alloc_zeroed(layout) } as *mut i16;
    if p.is_null() {
        return None;
    }
    Some(unsafe { Vec::from_raw_parts(p, n, n) })
}

} // verus!
