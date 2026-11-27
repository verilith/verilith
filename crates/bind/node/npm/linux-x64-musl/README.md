# `verilith-linux-x64-musl`

The prebuilt Linux x64 (musl) binary (`x86_64-unknown-linux-musl`) of
[`verilith`](https://www.npmjs.com/package/verilith), Node.js bindings for
[Verilith](https://github.com/verilith/verilith)'s formally verified WHATWG
URL and JSON parsers, proved with [Verus](https://github.com/verus-lang/verus).

Don't install this package directly. Install `verilith`:

```
npm install verilith
```

npm then installs this package as an optional dependency, only on
Linux x64 (musl). It holds nothing but the compiled Node-API addon; `verilith`'s
loader picks it up.

- Main package: https://www.npmjs.com/package/verilith
- Source: https://github.com/verilith/verilith/tree/main/crates/bind
- Issues: https://github.com/verilith/verilith/issues

Licensed under MIT or Apache-2.0, at your option.
