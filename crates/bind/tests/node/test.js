// Tests for the Node-API addon. Run after building: scripts/test-node.sh
'use strict';
const assert = require('node:assert');
const test = require('node:test');
const vbind = require(process.env.VBIND_NODE || '../../target/vbind.node');

test('URL getters match the built-in URL', () => {
  for (const [input, base] of [
    ['https://user:pw@EXAMPLE.com:8080/a/../b?q=1#h'],
    ['../d', 'http://a/b/c'],
    ['file:///tmp/x y'],
    ['http://[::1]:80/'],
  ]) {
    const a = new vbind.URL(input, base);
    const b = new URL(input, base);
    for (const k of ['href', 'origin', 'protocol', 'username', 'password', 'host',
                     'hostname', 'port', 'pathname', 'search', 'hash']) {
      assert.strictEqual(a[k], b[k], `${k} of ${input}`);
    }
    assert.strictEqual(String(a), b.href);
    assert.strictEqual(JSON.stringify(a), JSON.stringify(b));
  }
});

test('canParse and errors', () => {
  assert.strictEqual(vbind.URL.canParse('/x', 'http://a'), true);
  assert.strictEqual(vbind.URL.canParse('/x'), false);
  assert.throws(() => new vbind.URL('http://[::1'));
});

test('setters', () => {
  const u = new vbind.URL('http://a/');
  u.hostname = 'b.org';
  u.port = '81';
  u.port = '99999';  // ignored, as the URL Standard says
  u.pathname = '/x y';
  u.search = 'q';
  u.hash = 'f';
  assert.strictEqual(u.href, 'http://b.org:81/x%20y?q#f');
});

test('parseJSON matches JSON.parse', () => {
  for (const s of [
    '{"a":[1,2.5,-3e2,true,false,null],"b":{},"__proto__":{"x":1}}',
    '"\\u00e9\\n\\ud83d\\ude00"', '[]', '0', '-0', '1e400', '{"a":1,"a":2}',
  ]) {
    assert.deepStrictEqual(vbind.parseJSON(s), JSON.parse(s), s);
    assert.deepStrictEqual(vbind.parseJSON(Buffer.from(s)), JSON.parse(s), s);
  }
  for (const s of ['[1,]', '{"a"}', '01', '[', '', '[1] x']) {
    assert.throws(() => vbind.parseJSON(s), SyntaxError, s);
  }
});
