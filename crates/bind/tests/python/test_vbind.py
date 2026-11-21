"""Tests for the Python bindings. Run after building: scripts/test-python.sh"""
import json
import unittest

import vbind


class URLTest(unittest.TestCase):
    def test_parse(self):
        u = vbind.URL("https://user:pw@EXAMPLE.com:8080/a/../b?q=1#h")
        self.assertEqual(u.href, "https://user:pw@example.com:8080/b?q=1#h")
        self.assertEqual(
            (u.protocol, u.username, u.password, u.host, u.hostname, u.port,
             u.pathname, u.search, u.hash, u.origin),
            ("https:", "user", "pw", "example.com:8080", "example.com", "8080",
             "/b", "?q=1", "#h", "https://example.com:8080"))
        self.assertEqual(str(u), u.href)

    def test_base(self):
        self.assertEqual(vbind.URL("../d", "http://a/b/c").href, "http://a/d")
        self.assertTrue(vbind.URL.can_parse("/x", "http://a"))
        self.assertFalse(vbind.URL.can_parse("/x"))

    def test_invalid(self):
        with self.assertRaises(ValueError):
            vbind.URL("http://[::1")

    def test_setters(self):
        u = vbind.URL("http://a/")
        u.hostname = "b.org"
        u.port = "81"
        u.pathname = "/x y"
        u.search = "q"
        u.hash = "f"
        self.assertEqual(u.href, "http://b.org:81/x%20y?q#f")
        with self.assertRaises(ValueError):
            u.port = "99999"
        self.assertEqual(u.port, "81")

    def test_wpt(self):
        import os
        path = os.environ.get("URLTESTDATA")
        if not path:
            self.skipTest("set URLTESTDATA to WPT urltestdata.json")
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        for t in data:
            if isinstance(t, str):
                continue
            base = t.get("base")
            try:
                u = vbind.URL(t["input"], base)
            except ValueError:
                self.assertTrue(t.get("failure"), t)
                continue
            self.assertFalse(t.get("failure"), t)
            self.assertEqual(u.href, t["href"], t)


class JSONTest(unittest.TestCase):
    CASES = [
        '{"a":[1,2.5,-3e2,123456789012345678901234567890,true,false,null],"b":{}}',
        '"\\u00e9\\n\\ud83d\\ude00"',
        '[]', '0', '-0', '1e400', '{"a":1,"a":2}', ' [ 1 , [ [ ] ] ] ',
    ]

    def test_matches_json_loads(self):
        for c in self.CASES:
            self.assertEqual(repr(vbind.loads(c)), repr(json.loads(c)), c)
            self.assertEqual(repr(vbind.loads(c.encode())), repr(json.loads(c)), c)

    def test_errors(self):
        for c in ['[1,]', '{"a"}', '01', '"\\x"', '[', '', 'nul', '[1] x']:
            with self.assertRaises(ValueError):
                vbind.loads(c)


if __name__ == "__main__":
    unittest.main()
