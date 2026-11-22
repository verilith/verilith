//! The verified conversion `float::to_bits` against `f64::from_str`.
use verilith_json::float::to_bits;

fn std_bits(w: u64, q: i64) -> u64 {
    format!("{w}e{q}").parse::<f64>().unwrap().to_bits()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn check(w: u64, q: i64, none: &mut usize) {
    match to_bits(w, q) {
        Some(b) => assert_eq!(b, std_bits(w, q), "{w}e{q}"),
        None => *none += 1,
    }
}

#[test]
fn random_against_std() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let mut none = 0;
    let n = 400_000;
    for i in 0..n {
        let w = match i % 4 {
            0 => r.next(),
            1 => r.next() >> (r.next() % 64),
            2 => r.next() % 100_000,
            _ => r.next() % (1 << 53),
        };
        let q = (r.next() % 700) as i64 - 360;
        check(w, q, &mut none);
    }
    // Short decimals and integers.
    for w in 0..2000u64 {
        for q in -30..=30 {
            check(w, q, &mut none);
        }
    }
    eprintln!("undecided: {none}");
}

#[test]
fn edges() {
    let mut none = 0;
    for &(w, q) in &[
        (1u64, -324i64), (2, -324), (3, -324), (24703282292062327, -340), (24703282292062328, -340),
        (17976931348623157, 292), (17976931348623158, 292), (17976931348623159, 292),
        (u64::MAX, 289), (u64::MAX, -343), (1, 308), (2, 308), (9007199254740993, 0),
        (9007199254740995, 0), (u64::MAX, 0), (22250738585072011, -324), (22250738585072014, -324),
        (49406564584124654, -340), (1, 23), (7, -1), (5, -1), (125, -3), (u64::MAX, -1),
    ] {
        check(w, q, &mut none);
    }
}
