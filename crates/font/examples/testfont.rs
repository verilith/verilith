//! `testfont OUT`: writes the small hand-built font the tests use.
#[path = "../tests/common/mod.rs"]
mod common;

fn main() {
    let out = std::env::args().nth(1).expect("usage: testfont OUT");
    std::fs::write(out, common::font()).expect("write");
}
