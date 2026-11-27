//! Huffman code lengths from symbol frequencies, limited in length:
//! verilith-zlib's `huff_lens`, for alphabets of up to 1024 symbols. Only
//! the compression ratio depends on it: the lengths are checked
//! (`pcode::make_code`, `pcode::Plan`) before they are used.
use verilith_core::sort::*;
use vstd::prelude::*;

verus! {

/// Huffman code lengths of at most `maxbits` bits for the frequencies
/// `freq`: a Huffman tree, then lengths over `maxbits` shortened as miniz
/// does. Only the ratio depends on this; the caller checks the lengths.
pub fn huff_lens(freq: &[u32], maxbits: usize) -> (r: Vec<u8>)
    requires
        freq@.len() <= 1024,
        1 <= maxbits <= 15,
    ensures
        r@.len() == freq@.len(),
{
    let nsym = freq.len();
    let mut lens: Vec<u8> = vec![0u8; nsym];
    // The symbols used, by increasing frequency (ties by symbol): sort
    // `freq << 10 | symbol` keys, then read the symbols back, checking each.
    let mut keys: Vec<u64> = Vec::with_capacity(nsym);
    let mut s: usize = 0;
    while s < nsym
        invariant
            s <= nsym,
            nsym == freq@.len(),
            nsym <= 1024,
            lens@.len() == nsym,
        decreases nsym - s,
    {
        if freq[s] > 0 {
            keys.push(((freq[s] as u64) << 10u64) | s as u64);
        }
        s = s + 1;
    }
    let by_key = |a: usize, b: usize| -> (r: bool)
        requires
            a < keys@.len(),
            b < keys@.len(),
        ensures
            r == (keys@[a as int] <= keys@[b as int]),
        { keys[a] <= keys[b] };
    let ord = order_by(keys.len(), &by_key, Ghost(|a: usize, b: usize| keys@[a as int] <= keys@[b as int]));
    let mut syms: Vec<usize> = Vec::with_capacity(keys.len());
    let mut i: usize = 0;
    while i < ord.len()
        invariant
            i <= ord@.len(),
            ord@.len() == keys@.len(),
            below(ord@, keys@.len()),
            nsym == freq@.len(),
            lens@.len() == nsym,
            syms@.len() <= i,
            forall|k: int| 0 <= k < syms@.len() ==> #[trigger] syms@[k] < nsym,
        decreases ord@.len() - i,
    {
        let sym = (keys[ord[i]] & 1023) as usize;
        if sym >= nsym {
            return lens;
        }
        syms.push(sym);
        i = i + 1;
    }
    let m = syms.len();
    if m > nsym {
        return lens;
    }
    if m == 0 {
        return lens;
    }
    if m == 1 {
        lens.set(syms[0], 1);
        return lens;
    }
    // The tree: leaves 0..m (in `syms` order), then internal nodes, each
    // made from the two lightest nodes left.
    let total = 2 * m - 1;
    let mut w: Vec<u64> = vec![0u64; total];
    let mut parent: Vec<usize> = vec![0usize; total];
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            m == syms@.len(),
            nsym == freq@.len(),
            w@.len() == total,
            total == 2 * m - 1,
            forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
            forall|q: int| 0 <= q < k ==> #[trigger] w@[q] < 0x1_0000_0000,
            lens@.len() == nsym,
            nsym == freq@.len(),
        decreases m - k,
    {
        w.set(k, freq[syms[k]] as u64);
        k = k + 1;
    }
    let mut leaf: usize = 0;
    let mut node: usize = m;
    let mut k: usize = m;
    while k < total
        invariant
            m <= k <= total,
            total == 2 * m - 1,
            m >= 2,
            m <= 1024,
            leaf <= m,
            m <= node <= k,
            w@.len() == total,
            parent@.len() == total,
            forall|q: int| 0 <= q < total ==> #[trigger] parent@[q] < total,
            lens@.len() == nsym,
            nsym == freq@.len(),
            forall|q: int| 0 <= q < k ==> #[trigger] w@[q] <= 0x4_0000_0000_0000,
        decreases total - k,
    {
        let mut pair = [0usize; 2];
        let mut t: usize = 0;
        while t < 2
            invariant
                t <= 2,
                leaf <= m,
                m <= node <= k,
                k < total,
                pair@.len() == 2,
                w@.len() == total,
                total == 2 * m - 1,
                lens@.len() == nsym,
            nsym == freq@.len(),
                forall|z: int| 0 <= z < t ==> #[trigger] pair@[z] < k,
            decreases 2 - t,
        {
            if leaf < m && (node >= k || w[leaf] <= w[node]) {
                pair[t] = leaf;
                leaf = leaf + 1;
            } else if node < k {
                pair[t] = node;
                node = node + 1;
            } else {
                // Not reachable for a well-formed queue; give up safely.
                return lens;
            }
            t = t + 1;
        }
        let a0 = w[pair[0]];
        let a1 = w[pair[1]];
        let sum = if a0 + a1 > 0x4_0000_0000_0000 { 0x4_0000_0000_0000 } else { a0 + a1 };
        w.set(k, sum);
        parent.set(pair[0], k);
        parent.set(pair[1], k);
        k = k + 1;
    }
    // Depths, from the root down: a parent comes after its children, so
    // `parent[x]` becomes `x`'s depth once `x`'s parent's depth is known.
    let mut depth = parent;
    depth.set(total - 1, 0);
    let mut x = total - 1;
    while x > 0
        invariant
            x < total,
            depth@.len() == total,
            forall|q: int| 0 <= q < total ==> #[trigger] depth@[q] <= total,
            lens@.len() == nsym,
            nsym == freq@.len(),
        decreases x,
    {
        x = x - 1;
        let px = depth[x];
        if px > x && px < total && depth[px] < total {
            depth.set(x, depth[px] + 1);
        } else {
            depth.set(x, total);
        }
    }
    // How many codes of each length, the long ones cut to `maxbits`.
    let mut count = [0u64; 16];
    let mut q: usize = 0;
    while q < m
        invariant
            q <= m,
            m <= 1024,
            depth@.len() == total,
            total == 2 * m - 1,
            1 <= maxbits <= 15,
            forall|z: int| 0 <= z < 16 ==> #[trigger] count@[z] <= q,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
        decreases m - q,
    {
        let mut d = depth[q];
        if d > maxbits {
            d = maxbits;
        }
        if d == 0 {
            d = 1;
        }
        count[d] = count[d] + 1;
        q = q + 1;
    }
    // Make the code fit: while the code space is over-subscribed, move a
    // code from the longest length to a shorter one's subtree.
    let mut kraft: u64 = 0;
    let mut l: usize = 1;
    while l <= maxbits
        invariant
            1 <= l <= maxbits + 1,
            maxbits <= 15,
            forall|z: int| 0 <= z < 16 ==> #[trigger] count@[z] <= 1024,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
            kraft <= 1024 * 32768 * l,
        decreases maxbits + 1 - l,
    {
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma_pow2_strictly_increases((maxbits - l) as nat, 15);
        }
        let sh = (maxbits - l) as u64;
        proof {
            assert((1u64 << sh) <= 32768) by {
                verilith_core::bits::lemma_mask(sh);
                if sh < 15 {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases(sh as nat, 15);
                }
            }
            assert(count@[l as int] * (1u64 << sh) <= 1024 * 32768) by (nonlinear_arith)
                requires
                    count@[l as int] <= 1024,
                    (1u64 << sh) <= 32768,
            ;
        }
        proof {
            assert(kraft + count@[l as int] * (1u64 << sh) <= 1024 * 32768 * (l + 1)) by (nonlinear_arith)
                requires
                    kraft <= 1024 * 32768 * l,
                    count@[l as int] * (1u64 << sh) <= 1024 * 32768,
            ;
        }
        kraft = kraft + count[l] * (1u64 << sh);
        l = l + 1;
    }
    let full: u64 = 1u64 << (maxbits as u64);
    while kraft > full
        invariant
            maxbits <= 15,
            1 <= maxbits,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
        decreases kraft,
    {
        if count[maxbits] == 0 {
            return lens;
        }
        count[maxbits] = count[maxbits] - 1;
        let mut i = maxbits - 1;
        while i > 0
            invariant
                i < maxbits <= 15,
                count@.len() == 16,
            decreases i,
        {
            if count[i] > 0 && count[i + 1] < 0x1_0000 && count[maxbits] < 0x1_0000 {
                count[i] = count[i] - 1;
                count[i + 1] = count[i + 1] + 2;
                break;
            }
            i = i - 1;
        }
        kraft = kraft - 1;
    }
    // The longest codes go to the rarest symbols.
    let mut idx: usize = 0;
    let mut l = maxbits;
    while l > 0
        invariant
            l <= maxbits <= 15,
            idx <= m,
            m == syms@.len(),
            nsym == freq@.len(),
            lens@.len() == nsym,
            nsym == freq@.len(),
            count@.len() == 16,
            forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
        decreases l,
    {
        let mut c = count[l];
        while c > 0 && idx < m
            invariant
                idx <= m,
                m == syms@.len(),
                lens@.len() == nsym,
            nsym == freq@.len(),
                1 <= l <= 15,
                forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
            decreases c,
        {
            lens.set(syms[idx], l as u8);
            idx = idx + 1;
            c = c - 1;
        }
        l = l - 1;
    }
    lens
}



} // verus!
