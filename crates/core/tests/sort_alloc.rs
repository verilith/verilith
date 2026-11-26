//! `sort::order_by` against the standard library's stable sort, and the
//! zeroed allocators in `prims`.

#[test]
fn alloc_u8_i16_zeroed() {
    use verilith_core::prims::{alloc_i16, alloc_u8};
    assert_eq!(alloc_u8(0), Some(vec![]));
    assert_eq!(alloc_i16(0), Some(vec![]));
    let v = alloc_u8(100_000).unwrap();
    assert_eq!(v.len(), 100_000);
    assert!(v.iter().all(|&x| x == 0));
    let v = alloc_i16(100_000).unwrap();
    assert_eq!(v.len(), 100_000);
    assert!(v.iter().all(|&x| x == 0));
    assert_eq!(alloc_u8(usize::MAX), None);
    assert_eq!(alloc_i16(usize::MAX), None);
}

#[test]
fn order_by_matches_stable_sort() {
    use verilith_core::sort::order_by;
    use vstd::prelude::Ghost;
    let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
    for n in 0..200usize {
        for range in [1u64, 3, 1000, u64::MAX] {
            let keys: Vec<u64> = (0..n)
                .map(|_| {
                    seed ^= seed << 13;
                    seed ^= seed >> 7;
                    seed ^= seed << 17;
                    if range == u64::MAX { seed } else { seed % range }
                })
                .collect();
            let got = order_by(n, &|i: usize, j: usize| keys[i] <= keys[j], Ghost::assume_new());
            let mut want: Vec<usize> = (0..n).collect();
            want.sort_by_key(|&i| keys[i]);
            assert_eq!(got, want, "n = {n}, range = {range}");
        }
    }
}
