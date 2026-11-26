# verilith-quic against quinn-proto and quiche

```sh
./setup.sh                              # vendor/: quinn-proto 0.11.19 and quiche 0.24.9 from crates.io
./run.sh                                # the benchmarks, each row in its own process, best of 3
cargo run --release --bin agree [N]     # the differential test (default 200,000 frames each way)
```

`setup.sh` copies both crates from the Cargo registry and changes only
visibility (`mod frame` to `pub mod frame`, and the fields and types the
tests read), so their parsers can be called directly. quiche builds its
vendored BoringSSL, which needs cmake, Go and a C compiler.

The inputs are built with verilith-quic's encoder (`src/payloads.rs`),
whose output the round-trip proof shows is RFC 9000's encoding, and all
three implementations must accept them. Results are in the crate README.
