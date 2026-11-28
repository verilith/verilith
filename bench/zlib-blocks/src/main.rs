//! Prints the size of each file compressed by `deflate::compress_raw`
//! (one-shot raw DEFLATE) at each level given: `zlib-blocks LEVELS FILE...`,
//! LEVELS as `1,6,9`. Output sizes are a function of the input and the
//! code alone, so the numbers are exact and the same on every machine.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let levels: Vec<u32> = a[1].split(',').map(|l| l.parse().unwrap()).collect();
    println!("block_tokens\t{}", verilith_zlib::deflate::MAX_TOKS);
    for f in &a[2..] {
        let d = std::fs::read(f).unwrap();
        for &l in &levels {
            let c = verilith_zlib::deflate::compress_raw(&d, l);
            let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy();
            println!("{name}\t{l}\t{}\t{}", d.len(), c.len());
        }
    }
}
