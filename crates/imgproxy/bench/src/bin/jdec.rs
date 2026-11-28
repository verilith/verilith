use std::time::Instant;
fn main() {
    let data = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    for _ in 0..3 {
        let t = Instant::now();
        let pic = verilith_jpeg::decode::decode(&data).ok().unwrap();
        let d = t.elapsed();
        let t = Instant::now();
        let px = verilith_imgproxy::pixels::expand(&pic.px, pic.nc as usize).unwrap();
        println!("decode {:?} expand {:?} {}", d, t.elapsed(), px.len());
    }
}
