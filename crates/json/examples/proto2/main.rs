//! See `x86.rs`. The prototype is x86_64 only.
#[cfg(target_arch = "x86_64")]
mod x86;

fn main() {
    #[cfg(target_arch = "x86_64")]
    x86::main();
    #[cfg(not(target_arch = "x86_64"))]
    eprintln!("proto2 runs on x86_64 only");
}
