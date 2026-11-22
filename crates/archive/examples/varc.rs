//! `varc list ARCHIVE` prints the members; `varc extract ARCHIVE DIR`
//! unpacks them under DIR (which must exist), or says why it will not.
use verilith_archive::{Archive, Kind};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: varc list ARCHIVE | varc extract ARCHIVE DIR");
        std::process::exit(2);
    }
    let bytes = std::fs::read(&args[2]).expect("read");
    let a = match Archive::open(&bytes) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("{}: {:?}", args[2], e);
            std::process::exit(1);
        }
    };
    match args[1].as_str() {
        "list" => {
            for e in a.entries() {
                let k = match e.kind {
                    Kind::File => '-',
                    Kind::Dir => 'd',
                    Kind::Symlink => 'l',
                    Kind::Hardlink => 'h',
                    Kind::Other => '?',
                };
                println!("{} {:>10} {}", k, e.size, String::from_utf8_lossy(&e.name));
            }
        }
        #[cfg(unix)]
        "extract" => match verilith_archive::extract::extract(&a, std::path::Path::new(&args[3])) {
            Ok(n) => println!("{} members extracted", n),
            Err(e) => {
                eprintln!("refused: {:?}", e);
                std::process::exit(1);
            }
        },
        _ => std::process::exit(2),
    }
}
