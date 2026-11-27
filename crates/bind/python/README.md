# verilith (Python)

Python bindings for [Verilith](https://github.com/verilith/verilith)'s
formally verified parsers: a WHATWG URL parser (verilith-url) and a JSON
parser (verilith-json), both proved with [Verus](https://github.com/verus-lang/verus).
The module only converts types; every parsing decision is made by the
verified Rust code.

```
pip install verilith
```

```python
import vbind
u = vbind.URL("../d?x", "https://example.org/a/b/c")   # ada_url's URL shape
u.href, u.hostname, u.search; u.port = "8080"
vbind.URL.can_parse("/x", "http://a")
vbind.loads('{"a": [1, 2.5, null]}')                   # json.loads' output types
```

Errors raise `ValueError`. Wheels are built for CPython 3.11 and later
(one abi3 wheel per platform) on Linux (x86_64 and aarch64, glibc and
musl), macOS (x86_64 and arm64) and Windows (x64).

Licensed under MIT or Apache-2.0, at your option.
