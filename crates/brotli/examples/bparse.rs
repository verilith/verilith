// Times the parse alone, per quality (for tuning the match finder).
use verilith_brotli::compress::*;
fn main() {
    let q: u32 = std::env::args().nth(1).unwrap().parse().unwrap();
    for f in std::env::args().skip(2) {
        let d = std::fs::read(&f).unwrap();
        let p = params(q);
        let wmax = (1usize << 22) - 16;
        let t = std::time::Instant::now();
        let mut mf = Mf::new(d.len(), p.depth, p.lazy, p.quick, p.ways, p.hlen, wmax, p.opt, p.dict);
        let t0 = t.elapsed().as_secs_f64();
        let mut i = 0;
        let mut n = 0;
        let mut last = 4;
        while i < d.len() {
            let k = (d.len() - i).min(p.block);
            let lz = parse(&mut mf, &d, i, i + k, last);
            n += lz.len();
            if let Some(x) = lz.iter().rev().find(|x| x.dist != 0) { last = x.dist as usize; }
            i += k;
        }
        println!("{f}\tq{q}\tsetup {:.3}s\tparse {:.3}s\t{} commands", t0, t.elapsed().as_secs_f64() - t0, n);
    }
}
