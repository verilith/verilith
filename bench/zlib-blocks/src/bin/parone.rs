//! One `par::compress` call on one thread: `parone FILE LEVEL CHUNK_KIB`.
//! Run under `valgrind --tool=cachegrind` by `par-cost.sh`, whose
//! instruction counts give the work each chunk adds.
use verilith_zlib::wrap::Format;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let d = std::fs::read(&a[1]).unwrap();
    let level: u32 = a[2].parse().unwrap();
    let chunk = a[3].parse::<usize>().unwrap() * 1024;
    let c = verilith_zlib::par::compress(Format::Gzip, &d, level, 15, chunk, 1);
    std::hint::black_box(c);
}
