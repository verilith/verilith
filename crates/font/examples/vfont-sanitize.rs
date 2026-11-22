//! `vfont-sanitize IN [OUT]`: sanitize a font file. Exit status 0 if it
//! was accepted, 1 if refused.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 2 {
        eprintln!("usage: vfont-sanitize IN [OUT]");
        std::process::exit(2);
    }
    let input = std::fs::read(&a[1]).expect("read");
    match verilith_font::sanitize(&input) {
        Some(out) => {
            if a.len() > 2 {
                std::fs::write(&a[2], &out).expect("write");
            }
            println!("ok {} -> {} bytes", input.len(), out.len());
        }
        None => {
            println!("refused");
            std::process::exit(1);
        }
    }
}
