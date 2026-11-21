#!/usr/bin/env python3
"""Writes the HTTP messages for the http suites (one message per file).
req-small, req-pico-bench (the request from picohttpparser's bench.c),
req-browser and resp-typical are the messages of vhttp/bench; the POST and
the chunked response add bodies, which llhttp frames as Node uses it.
resp-typical carries a short body so that every message is complete."""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
MESSAGES = {
    'req-small': (
        'GET / HTTP/1.1\r\n'
        'Host: example.com\r\n'
        '\r\n'
        ''
    ),
    'req-pico-bench': (
        'GET /wp-content/uploads/2010/03/hello-kitty-darth-vader-pink.jpg HTTP/1.1\r\n'
        'Host: www.kittyhell.com\r\n'
        'User-Agent: Mozilla/5.0 (Macintosh; U; Intel Mac OS X 10.6; ja-JP-mac; rv:1.9.2.3) Gecko/20100401 Firefox/3.6.3 Pathtraq/0.9\r\n'
        'Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n'
        'Accept-Language: ja,en-us;q=0.7,en;q=0.3\r\n'
        'Accept-Encoding: gzip,deflate\r\n'
        'Accept-Charset: Shift_JIS,utf-8;q=0.7,*;q=0.7\r\n'
        'Keep-Alive: 115\r\n'
        'Connection: keep-alive\r\n'
        'Cookie: wp_ozh_wsa_visits=2; wp_ozh_wsa_visit_lasttime=xxxxxxxxxx; __utma=xxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.x; __utmz=xxxxxxxxx.xxxxxxxxxx.x.x.utmccn=(referral)|utmcsr=reader.livedoor.com|utmcct=/reader/|utmcmd=referral\r\n'
        '\r\n'
        ''
    ),
    'req-browser': (
        'GET /search?q=formal+verification+http+parser&source=hp&ei=AbCdEfGhIjKlMnOp&iflsig=AL9hbdgAAAAAZ HTTP/1.1\r\n'
        'Host: www.example.com\r\n'
        'Connection: keep-alive\r\n'
        'sec-ch-ua: "Chromium";v="130", "Google Chrome";v="130", "Not?A_Brand";v="99"\r\n'
        'sec-ch-ua-mobile: ?0\r\n'
        'sec-ch-ua-platform: "macOS"\r\n'
        'Upgrade-Insecure-Requests: 1\r\n'
        'User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36\r\n'
        'Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7\r\n'
        'Sec-Fetch-Site: same-origin\r\n'
        'Sec-Fetch-Mode: navigate\r\n'
        'Sec-Fetch-User: ?1\r\n'
        'Sec-Fetch-Dest: document\r\n'
        'Referer: https://www.example.com/\r\n'
        'Accept-Encoding: gzip, deflate, br, zstd\r\n'
        'Accept-Language: en-US,en;q=0.9,fr;q=0.8\r\n'
        'Cookie: AEC=AVYB7cqVxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; NID=518=Zxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; SID=g.a000xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; __Secure-1PSID=g.a000yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy; 1P_JAR=2026-10-26-03\r\n'
        '\r\n'
        ''
    ),
    'resp-typical': (
        'HTTP/1.1 200 OK\r\n'
        'Date: Mon, 26 Oct 2026 03:38:48 GMT\r\n'
        'Content-Type: text/html; charset=utf-8\r\n'
        'Content-Length: 104\r\n'
        'Connection: keep-alive\r\n'
        'Cache-Control: private, max-age=0\r\n'
        'Expires: -1\r\n'
        'Server: nginx/1.27.2\r\n'
        'Strict-Transport-Security: max-age=31536000; includeSubDomains\r\n'
        'X-Content-Type-Options: nosniff\r\n'
        'X-Frame-Options: SAMEORIGIN\r\n'
        'Vary: Accept-Encoding\r\n'
        'Set-Cookie: session=abcdef0123456789; Path=/; Secure; HttpOnly; SameSite=Lax\r\n'
        '\r\n'
        ''
        '<!doctype html><html><head><title>vbench</title></head><body><p>A short response body.</p></body></html>'
    ),
    'req-post-json': (
        'POST /api/v1/search HTTP/1.1\r\n'
        'Host: api.example.com\r\n'
        'User-Agent: node-fetch/3.3.2\r\n'
        'Accept: application/json\r\n'
        'Content-Type: application/json\r\n'
        'Authorization: Bearer eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.dozjgNryP4J3jVmNHl0w5N_XgL0n3I9PlFUP0THsR8U\r\n'
        'Content-Length: 96\r\n'
        'Connection: keep-alive\r\n'
        '\r\n'
        '{"query":"formal verification","page":2,"filters":{"lang":"en","since":"2026-01-01"},"limit":50}'
    ),
    'resp-chunked': (
        'HTTP/1.1 200 OK\r\n'
        'Date: Mon, 26 Oct 2026 03:38:48 GMT\r\n'
        'Content-Type: text/html; charset=utf-8\r\n'
        'Transfer-Encoding: chunked\r\n'
        'Connection: keep-alive\r\n'
        'Server: nginx/1.27.2\r\n'
        'Vary: Accept-Encoding\r\n'
        '\r\n'
        '37\r\n'
        '<!doctype html><html><head><title>vbench</title></head>\r\n'
        '29a\r\n'
        '<body><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p><p>lorem ipsum dolor sit amet</p>\r\n'
        'e\r\n'
        '</body></html>\r\n'
        '0\r\n'
        '\r\n'
        ''
    ),
}

for name, text in MESSAGES.items():
    with open(os.path.join(HERE, name + ".http"), "wb") as f:
        f.write(text.encode("latin-1"))
