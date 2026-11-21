// Profiling driver: `valgrind --tool=callgrind target/release/prof <what> <file>`.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let b = std::fs::read(&a[2]).unwrap();
    let m = verilith_dns::parse(&b).unwrap();
    let mut n = 0;
    for _ in 0..20000 {
        n += match a[1].as_str() {
            "parse" => std::hint::black_box(verilith_dns::parse(&b)).unwrap().answer_count(),
            "data" => {
                let m = verilith_dns::parse(&b).unwrap();
                let mut c = 0;
                for s in [verilith_dns::Section::Answer, verilith_dns::Section::Authority, verilith_dns::Section::Additional] {
                    for rr in m.records(s) {
                        c += std::hint::black_box(rr.data()).is_some() as usize;
                    }
                }
                c
            }
            "write" => std::hint::black_box(m.to_bytes_compressed()).len(),
            _ => panic!(),
        };
    }
    println!("{n}");
}
