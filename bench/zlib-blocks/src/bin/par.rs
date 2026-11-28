//! Prints the size of each file compressed by `par::compress` (gzip, the
//! input cut into chunks compressed apart) for each chunk size and level:
//! `par CHUNKS LEVELS FILE...`, both lists comma-separated, CHUNKS in KiB.
//! The output does not depend on the number of threads, only on the chunk
//! size, so the sizes are exact.
use verilith_zlib::wrap::Format;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let chunks: Vec<usize> = a[1].split(',').map(|c| c.parse::<usize>().unwrap() * 1024).collect();
    let levels: Vec<u32> = a[2].split(',').map(|l| l.parse().unwrap()).collect();
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    for f in &a[3..] {
        let d = std::fs::read(f).unwrap();
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy();
        for &l in &levels {
            let whole = verilith_zlib::par::compress(Format::Gzip, &d, l, 15, d.len().max(32768), 1).len();
            print!("{name}\t{l}\t{}\t{whole}", d.len());
            for &c in &chunks {
                print!("\t{}", verilith_zlib::par::compress(Format::Gzip, &d, l, 15, c, threads).len());
            }
            println!();
        }
    }
}
