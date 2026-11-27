//! Block types of a level-N frame: BLOCKS LEVEL FILE
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let lv: i32 = a[1].parse().unwrap();
    let src = std::fs::read(&a[2]).unwrap();
    let f = verilith_zstd::compress(&src, lv, false);
    let fhd = f[4];
    let ss = fhd & 0x20 != 0;
    let fcs = [if ss { 1 } else { 0 }, 2, 4, 8][(fhd >> 6) as usize];
    let did = [0, 1, 2, 4][(fhd & 3) as usize];
    let mut p = 5 + if ss { 0 } else { 1 } + did + fcs;
    let mut n = [0usize; 4];
    let mut sz = [0usize; 4];
    loop {
        let h = f[p] as u32 | (f[p + 1] as u32) << 8 | (f[p + 2] as u32) << 16;
        let t = ((h >> 1) & 3) as usize;
        let s = (h >> 3) as usize;
        n[t] += 1;
        p += 3 + if t == 1 { 1 } else { s };
        sz[t] += if t == 1 { 1 } else { s };
        if h & 1 == 1 { break; }
    }
    println!("raw {} ({} B) rle {} compressed {} ({} B), total {}", n[0], sz[0], n[1], n[2], sz[2], f.len());
}
