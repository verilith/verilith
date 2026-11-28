# What verilith-serverless trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc), what
[verilith-wasm](../wasm#trusted-base) and
[verilith-server](../server/TRUST.md) trust, and the specifications its
theorems are stated with (`abi::step` and `abi::field_ok` here,
verilith-server's `respond::name_ok`/`value_ok`, verilith-http's
`spec.rs`, verilith-wasm's `sem.rs`), this crate has no `external_body`,
axiom or `assume`. `src/abi.rs` and `src/host.rs` are verified; the
plain Rust is:

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/lib.rs` `load` | Decodes and instantiates a module with verilith-wasm's (unverified, checked) API, refuses imports that are not the ABI's, builds the import table `ops` from the verified `abi::op_of` (import `i` is the ABI function its name says), finds `handle` | Nothing for isolation: a wrong `ops` entry makes an import behave as another ABI function, which still does exactly `step`; a wrong entry index runs another function of the same module, in the same sandbox. The memory cap is checked again by the verified `Func::new` |
| `src/lib.rs` `field_lines` | Writes the request's header lines into one buffer (request part 2) | That the guest gets the server's parsed fields; a bug costs correctness of what the guest reads, not isolation |
| `src/lib.rs` `respond` | Runs `Func::serve` and hands the reply's status, fields and body to `Response::send`; 500/503 for traps | Passes exactly the reply's fields and body (each field already satisfies `respond::name_ok`/`value_ok`, which `send` checks again) |
| `src/lib.rs` `Functions` | The `Handler`: routes with the verified `route`, keeps one `Func` per function per worker thread | A `Func` is used by one request at a time (Rust ownership: it is moved into `serve` and back) |
| `src/bin/verilith-serverless.rs` | The command line | Application code |
| verilith-wasm `api::Instance::into_checked`, `export_func` | Hands the checked instance to the verified host | Part of verilith-wasm's unverified API; `Checked`'s type invariant holds whatever it does |

`scripts/trust-ledger.py` counts these files in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).
