# verilith (Node.js)

Node.js bindings for [Verilith](https://github.com/verilith/verilith)'s
formally verified parsers: a WHATWG URL parser (verilith-url) and a JSON
parser (verilith-json), both proved with [Verus](https://github.com/verus-lang/verus).
The addon only converts types; every parsing decision is made by the
verified Rust code.

```
npm install verilith
```

```js
const vbind = require('verilith');
new vbind.URL('../d', 'https://example.org/a/b/c').href;
vbind.URL.canParse('/x', 'http://a');
vbind.parseJSON('{"a":1}');   // SyntaxError on invalid JSON, like JSON.parse
```

`URL` has the getters, setters and `canParse` of the WHATWG `URL` class.
It is for runtimes that ship their own URL and JSON (Bun, Electron, older
Node) or that want the verified parser explicitly.

Prebuilt binaries (Node-API 9, Node 18.17 or later) are published for
Linux (x64 and arm64, glibc and musl), macOS (x64 and arm64) and Windows
(x64). npm installs only the one for your platform.

Licensed under MIT or Apache-2.0, at your option.
