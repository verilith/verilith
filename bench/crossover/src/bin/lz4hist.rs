//! Literal-run lengths in LZ4 blocks as verilith-lz4 compresses them:
//! `lz4hist FILE...` prints, per length of 15 or more (those reach
//! `copy_lits`), how many runs have it, over all files. Exact counts.
fn main() {
    let mut h = std::collections::BTreeMap::<usize, u64>::new();
    let mut total = 0u64;
    for f in std::env::args().skip(1) {
        let d = std::fs::read(&f).unwrap();
        for part in d.chunks(4 << 20) {
            let mut c = vec![0u8; verilith_lz4::compress::compress_bound(part.len())];
            let n = verilith_lz4::compress::compress_into(part, &mut c, 1).unwrap();
            let s = &c[..n];
            let mut i = 0;
            while i < s.len() {
                let t = s[i];
                i += 1;
                let mut ll = (t >> 4) as usize;
                if ll == 15 {
                    loop {
                        let b = s[i];
                        i += 1;
                        ll += b as usize;
                        if b != 255 {
                            break;
                        }
                    }
                }
                i += ll;
                total += 1;
                if ll >= 15 {
                    *h.entry(ll).or_default() += 1;
                }
                if i >= s.len() {
                    break;
                }
                i += 2;
                if t & 15 == 15 {
                    loop {
                        let b = s[i];
                        i += 1;
                        if b != 255 {
                            break;
                        }
                    }
                }
            }
        }
    }
    println!("# sequences\t{total}");
    for (l, c) in h {
        println!("{l}\t{c}");
    }
}
