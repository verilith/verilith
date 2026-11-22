"""A line-by-line Python transliteration of src/spec.rs, used to check the
spec itself against the web-platform-tests data before (and independently
of) the verified implementation.  Run: python3 tools/model.py urltestdata.json
"""
import json, sys

def lower(c): return c + 32 if 65 <= c <= 90 else c
def digit(c): return 48 <= c <= 57
def alpha(c): return 65 <= c <= 90 or 97 <= c <= 122
def alnum(c): return digit(c) or alpha(c)
def hexd(c): return digit(c) or 65 <= c <= 70 or 97 <= c <= 102
def hexv(c):
    if digit(c): return c - 48
    if 65 <= c <= 70: return c - 55
    return c - 87

def c0(c): return c < 0x20 or c > 0x7E
def frag(c): return c0(c) or c in b' "<>`'
def query(c): return c0(c) or c in b' "#<>'
def squery(c): return query(c) or c == ord("'")
def path(c): return query(c) or c in b'?^`{}'
def userinfo(c): return path(c) or c in b'/:;=@|' or 0x5B <= c <= 0x5D
SETS = dict(C0=c0, Fragment=frag, Query=query, SpecialQuery=squery, Path=path, Userinfo=userinfo)

def pe(c, s):
    return b'%%%02X' % c if SETS[s](c) else bytes([c])
def pe_seq(b, s): return b''.join(pe(c, s) for c in b)

def percent_decode(s):
    out = bytearray(); i = 0
    while i < len(s):
        if s[i] == 37 and i + 2 < len(s) + 0 and len(s) - i >= 3 and hexd(s[i+1]) and hexd(s[i+2]):
            out.append(hexv(s[i+1]) * 16 + hexv(s[i+2])); i += 3
        else:
            out.append(s[i]); i += 1
    return bytes(out)

FORBIDDEN_HOST = set(b'\x00\t\n\r #/:<>?@[\\]^|')
def forbidden_domain(c): return c in FORBIDDEN_HOST or c <= 0x1F or c == 37 or c == 0x7F

def split(s, d): return s.split(bytes([d]))

def radix_digit(c, r):
    if r == 16: return hexd(c)
    if r == 10: return digit(c)
    return 48 <= c <= 55

def ipv4_number(s):
    if not s: return None
    if len(s) >= 2 and s[0] == 48 and s[1] in b'xX': r, t, ve = 16, s[2:], True
    elif len(s) >= 2 and s[0] == 48: r, t, ve = 8, s[1:], True
    else: r, t, ve = 10, s, False
    if not t: return (0, True)
    if any(not radix_digit(c, r) for c in t): return None
    v = 0
    for c in t: v = v * r + hexv(c)
    return (v, ve)

def ends_in_a_number(s):
    parts = split(s, 46)
    if parts[-1] == b'': parts = parts[:-1]
    if not parts: return False
    last = parts[-1]
    if last and all(digit(c) for c in last): return True
    return ipv4_number(last) is not None

def ipv4_parse(s):
    parts = split(s, 46)
    if parts[-1] == b'' and len(parts) > 1: parts = parts[:-1]
    if len(parts) > 4: return None
    nums = []
    for p in parts:
        r = ipv4_number(p)
        if r is None: return None
        nums.append(r[0])
    if any(n > 255 for n in nums[:-1]): return None
    if nums[-1] >= 256 ** (5 - len(nums)): return None
    v = nums[-1]
    for i, n in enumerate(nums[:-1]): v += n * 256 ** (3 - i)
    return v

def ipv6_parse(s):
    a = [0] * 8; pi = 0; comp = None; p = 0
    n = len(s)
    if n > 0 and s[0] == 58:
        if n < 2 or s[1] != 58: return None
        p = 2; pi = 1; comp = 1
    while p < n:
        if pi == 8: return None
        if s[p] == 58:
            if comp is not None: return None
            p += 1; pi += 1; comp = pi; continue
        value = length = 0
        while length < 4 and p < n and hexd(s[p]):
            value = value * 16 + hexv(s[p]); p += 1; length += 1
        if p < n and s[p] == 46:
            if length == 0: return None
            p -= length
            if pi > 6: return None
            ns = 0
            while p < n:
                piece = None
                if ns > 0:
                    if s[p] == 46 and ns < 4: p += 1
                    else: return None
                if not (p < n and digit(s[p])): return None
                while p < n and digit(s[p]):
                    num = s[p] - 48
                    if piece is None: piece = num
                    elif piece == 0: return None
                    else: piece = piece * 10 + num
                    if piece > 255: return None
                    p += 1
                a[pi] = a[pi] * 0x100 + piece
                ns += 1
                if ns in (2, 4): pi += 1
            if ns != 4: return None
            break
        elif p < n and s[p] == 58:
            p += 1
            if p >= n: return None
        elif p < n:
            return None
        a[pi] = value; pi += 1
    if comp is not None:
        swaps = pi - comp; pi = 7
        while pi != 0 and swaps > 0:
            j = comp + swaps - 1
            a[pi], a[j] = a[j], a[pi]
            pi -= 1; swaps -= 1
    elif pi != 8:
        return None
    return a

def domain_to_ascii(b):
    import idna
    try:
        d = b.decode('utf-8', errors='replace')
        return idna.encode(d, uts46=True, transitional=False, std3_rules=False).decode()
    except Exception:
        try:
            return d.encode('idna').decode()
        except Exception:
            return None

def domain_parse(d):
    if all(c < 0x80 for c in d):
        r = bytes(lower(c) for c in d)
    else:
        r = domain_to_ascii(d)
        if r is None: return None
        r = r.encode()
        if not all(c < 0x80 for c in r): return None
    if len(r) == 0: return None
    if any(forbidden_domain(c) for c in r): return None
    return r

def host_parse(s, opaque):
    if len(s) > 0 and s[0] == 91:
        if s[-1] != 93: return None
        a = ipv6_parse(s[1:-1])
        return None if a is None else ('ipv6', tuple(a))
    if opaque:
        if any(c in FORBIDDEN_HOST for c in s): return None
        e = pe_seq(s, 'C0')
        return ('empty',) if not e else ('opaque', e)
    a = domain_parse(percent_decode(s))
    if a is None: return None
    if ends_in_a_number(a):
        v = ipv4_parse(a)
        return None if v is None else ('ipv4', v)
    return ('domain', a)

def lower_hex(n): return b'%x' % n

def ipv6_compress(p):
    li, ls, fi, fs = None, 1, None, 0
    for i in range(8):
        if p[i] != 0:
            if fs > ls: li, ls = fi, fs
            fi, fs = None, 0
        else:
            if fi is None: fi = i
            fs += 1
    if fs > ls: return fi
    return li

def ipv6_serialize(p):
    out = b''; comp = ipv6_compress(p); ign = False
    for i in range(8):
        if ign and p[i] == 0: continue
        ign = False
        if comp == i:
            out += b'::' if i == 0 else b':'; ign = True; continue
        out += lower_hex(p[i])
        if i != 7: out += b':'
    return out

def host_serialize(h):
    k = h[0]
    if k in ('domain', 'opaque'): return h[1]
    if k == 'empty': return b''
    if k == 'ipv4':
        a = h[1]
        return b'.'.join(b'%d' % x for x in (a >> 24, (a >> 16) & 255, (a >> 8) & 255, a & 255))
    return b'[' + ipv6_serialize(h[1]) + b']'

SPECIAL = {b'ftp': 21, b'file': None, b'http': 80, b'https': 443, b'ws': 80, b'wss': 443}
def default_port(s): return SPECIAL.get(s)

class Url:
    def __init__(s):
        s.scheme = b''; s.username = b''; s.password = b''; s.host = None; s.port = None
        s.path = []  # list => list path, bytes => opaque
        s.query = None; s.fragment = None
    def copy(s):
        u = Url(); u.__dict__.update(s.__dict__)
        u.path = list(s.path) if isinstance(s.path, list) else s.path
        return u

def special(u): return u.scheme in SPECIAL
def creds(u): return bool(u.username) or bool(u.password)
def wdl(s): return len(s) == 2 and alpha(s[0]) and s[1] in b':|'
def nwdl(s): return len(s) == 2 and alpha(s[0]) and s[1] == 58
def swdl(s): return len(s) >= 2 and alpha(s[0]) and s[1] in b':|' and (len(s) == 2 or s[2] in b'/\\?#')
def single_dot(s): return s == b'.' or s.lower() == b'%2e'
def double_dot(s): return s == b'..' or s.lower() in (b'.%2e', b'%2e.', b'%2e%2e')
def shorten(u):
    if not isinstance(u.path, list): return
    if u.scheme == b'file' and len(u.path) == 1 and nwdl(u.path[0]): return
    if u.path: u.path.pop()
def push(u, seg):
    if isinstance(u.path, list): u.path.append(seg)

class Fail(Exception): pass

def run(inp, base, ov, state, url):
    buf = b''; at = False; ib = False; pts = False
    p = 0; n = len(inp)
    while True:
        eof = p >= n
        c = None if eof else inp[p]
        def cis(x): return c == ord(x)
        def rem(x): return p + 1 < n and inp[p + 1] == ord(x)
        sp = special(url)
        if state == 'SchemeStart':
            if not eof and alpha(c): buf += bytes([lower(c)]); state = 'Scheme'
            elif ov is None: state = 'NoScheme'; p -= 1
            else: return None
        elif state == 'Scheme':
            if not eof and (alnum(c) or c in b'+-.'): buf += bytes([lower(c)])
            elif cis(':'):
                if ov is not None:
                    if url.scheme in SPECIAL and buf not in SPECIAL: return url
                    if url.scheme not in SPECIAL and buf in SPECIAL: return url
                    if (creds(url) or url.port is not None) and buf == b'file': return url
                    if url.scheme == b'file' and url.host == ('empty',): return url
                url.scheme = buf
                if ov is not None:
                    if url.port == default_port(url.scheme): url.port = None
                    return url
                buf = b''
                if url.scheme == b'file': state = 'File'
                elif special(url) and base is not None and base.scheme == url.scheme: state = 'SpecialRelativeOrAuthority'
                elif special(url): state = 'SpecialAuthoritySlashes'
                elif rem('/'): state = 'PathOrAuthority'; p += 1
                else: url.path = b''; state = 'OpaquePath'
            elif ov is None: buf = b''; state = 'NoScheme'; p = -1
            else: return None
        elif state == 'NoScheme':
            if base is None: return None
            opq = not isinstance(base.path, list)
            if opq and cis('#'):
                url.scheme = base.scheme; url.path = base.path; url.query = base.query; url.fragment = b''; state = 'Fragment'
            elif opq: return None
            elif base.scheme != b'file': state = 'Relative'; p -= 1
            else: state = 'File'; p -= 1
        elif state == 'SpecialRelativeOrAuthority':
            if cis('/') and rem('/'): state = 'SpecialAuthorityIgnoreSlashes'; p += 1
            else: state = 'Relative'; p -= 1
        elif state == 'PathOrAuthority':
            if cis('/'): state = 'Authority'
            else: state = 'Path'; p -= 1
        elif state == 'Relative':
            url.scheme = base.scheme
            if cis('/') or (special(url) and cis('\\')): state = 'RelativeSlash'
            else:
                url.username = base.username; url.password = base.password; url.host = base.host
                url.port = base.port; url.path = list(base.path) if isinstance(base.path, list) else base.path
                url.query = base.query
                if cis('?'): url.query = b''; state = 'Query'
                elif cis('#'): url.fragment = b''; state = 'Fragment'
                elif not eof: url.query = None; shorten(url); state = 'Path'; p -= 1
        elif state == 'RelativeSlash':
            if sp and (cis('/') or cis('\\')): state = 'SpecialAuthorityIgnoreSlashes'
            elif cis('/'): state = 'Authority'
            else:
                url.username = base.username; url.password = base.password; url.host = base.host; url.port = base.port
                state = 'Path'; p -= 1
        elif state == 'SpecialAuthoritySlashes':
            if cis('/') and rem('/'): state = 'SpecialAuthorityIgnoreSlashes'; p += 1
            else: state = 'SpecialAuthorityIgnoreSlashes'; p -= 1
        elif state == 'SpecialAuthorityIgnoreSlashes':
            if not cis('/') and not cis('\\'): state = 'Authority'; p -= 1
        elif state == 'Authority':
            if cis('@'):
                b = (b'%40' + buf) if at else buf
                at = True
                for ch in b:
                    if ch == 58 and not pts: pts = True; continue
                    e = pe(ch, 'Userinfo')
                    if pts: url.password += e
                    else: url.username += e
                buf = b''
            elif eof or c in b'/?#' or (sp and cis('\\')):
                if at and not buf: return None
                p -= len(buf) + 1; buf = b''; state = 'Host'
            else: buf += bytes([c])
        elif state in ('Host', 'Hostname'):
            if ov is not None and url.scheme == b'file': p -= 1; state = 'FileHost'
            elif cis(':') and not ib:
                if not buf: return None
                if ov == 'Hostname': return None
                h = host_parse(buf, not sp)
                if h is None: return None
                url.host = h; buf = b''; state = 'Port'
            elif eof or c in b'/?#' or (sp and cis('\\')):
                p -= 1
                if sp and not buf: return None
                elif ov is not None and not buf and (creds(url) or url.port is not None): return None
                h = host_parse(buf, not sp)
                if h is None: return None
                url.host = h; buf = b''; state = 'PathStart'
                if ov is not None: return url
            else:
                if c == 91: ib = True
                if c == 93: ib = False
                buf += bytes([c])
        elif state == 'Port':
            if not eof and digit(c): buf += bytes([c])
            elif eof or c in b'/?#' or (sp and cis('\\')) or ov is not None:
                if buf:
                    port = int(buf)
                    if port > 65535: return None
                    url.port = None if default_port(url.scheme) == port else port
                    buf = b''
                    if ov is not None: return url
                if ov is not None: return None
                state = 'PathStart'; p -= 1
            else: return None
        elif state == 'File':
            url.scheme = b'file'; url.host = ('empty',)
            if cis('/') or cis('\\'): state = 'FileSlash'
            elif base is not None and base.scheme == b'file':
                url.host = base.host; url.path = list(base.path) if isinstance(base.path, list) else base.path; url.query = base.query
                if cis('?'): url.query = b''; state = 'Query'
                elif cis('#'): url.fragment = b''; state = 'Fragment'
                elif not eof:
                    url.query = None
                    if not swdl(inp[p:]): shorten(url)
                    else: url.path = []
                    state = 'Path'; p -= 1
            else: state = 'Path'; p -= 1
        elif state == 'FileSlash':
            if cis('/') or cis('\\'): state = 'FileHost'
            else:
                if base is not None and base.scheme == b'file':
                    url.host = base.host
                    if isinstance(base.path, list) and not swdl(inp[p:]) and base.path and nwdl(base.path[0]):
                        push(url, base.path[0])
                state = 'Path'; p -= 1
        elif state == 'FileHost':
            if eof or c in b'/\\?#':
                p -= 1
                if ov is None and wdl(buf): state = 'Path'
                elif not buf:
                    url.host = ('empty',)
                    if ov is not None: return url
                    state = 'PathStart'
                else:
                    h = host_parse(buf, not sp)
                    if h is None: return None
                    if h == ('domain', b'localhost'): h = ('empty',)
                    url.host = h
                    if ov is not None: return url
                    buf = b''; state = 'PathStart'
            else: buf += bytes([c])
        elif state == 'PathStart':
            if sp:
                state = 'Path'
                if not cis('/') and not cis('\\'): p -= 1
            elif ov is None and cis('?'): url.query = b''; state = 'Query'
            elif ov is None and cis('#'): url.fragment = b''; state = 'Fragment'
            elif not eof:
                state = 'Path'
                if c != 47: p -= 1
            elif ov is not None and url.host is None: push(url, b'')
        elif state == 'Path':
            slash = cis('/') or (sp and cis('\\'))
            if eof or slash or (ov is None and c in b'?#'):
                if double_dot(buf):
                    shorten(url)
                    if not slash: push(url, b'')
                elif single_dot(buf) and not slash: push(url, b'')
                elif not single_dot(buf):
                    if url.scheme == b'file' and url.path == [] and wdl(buf): buf = buf[:1] + b':'
                    push(url, buf)
                buf = b''
                if cis('?'): url.query = b''; state = 'Query'
                if cis('#'): url.fragment = b''; state = 'Fragment'
            else: buf += pe(c, 'Path')
        elif state == 'OpaquePath':
            if cis('?'): url.query = b''; state = 'Query'
            elif cis('#'): url.fragment = b''; state = 'Fragment'
            elif not eof:
                if c == 32: add = b'%20' if (rem('?') or rem('#')) else b' '
                else: add = pe(c, 'C0')
                url.path += add
        elif state == 'Query':
            if (ov is None and cis('#')) or eof:
                url.query = (url.query or b'') + pe_seq(buf, 'SpecialQuery' if sp else 'Query')
                buf = b''
                if cis('#'): url.fragment = b''; state = 'Fragment'
            else: buf += bytes([c])
        elif state == 'Fragment':
            if not eof: url.fragment = (url.fragment or b'') + pe(c, 'Fragment')
        if p >= n: return url
        p += 1

def trim(s):
    i, j = 0, len(s)
    while i < j and s[i] <= 0x20: i += 1
    while j > i and s[j-1] <= 0x20: j -= 1
    return s[i:j]

def parse_url(inp, base=None):
    inp = bytes(c for c in trim(inp) if c not in b'\t\n\r')
    return run(inp, base, None, 'SchemeStart', Url())

def serialize(u, exclude_fragment=False):
    out = u.scheme + b':'
    if u.host is not None:
        out += b'//'
        if creds(u):
            out += u.username
            if u.password: out += b':' + u.password
            out += b'@'
        out += host_serialize(u.host)
        if u.port is not None: out += b':%d' % u.port
    if isinstance(u.path, list):
        if u.host is None and len(u.path) > 1 and u.path[0] == b'': out += b'/.'
        out += b''.join(b'/' + s for s in u.path)
    else:
        out += u.path
    if u.query is not None: out += b'?' + u.query
    if u.fragment is not None and not exclude_fragment: out += b'#' + u.fragment
    return out

def enc(s):
    return s.encode('utf-16', 'surrogatepass').decode('utf-16', 'replace').encode('utf-8')

if __name__ == '__main__':
    data = json.load(open(sys.argv[1]))
    ok = bad = 0
    for t in data:
        if isinstance(t, str): continue
        try:
            inp = enc(t['input'])
        except Exception:
            continue
        base = None
        if t.get('base') is not None:
            base = parse_url(enc(t['base']))
        r = parse_url(inp, base)
        if t.get('failure'):
            good = r is None
        else:
            good = r is not None and serialize(r).decode('latin1') == t['href'].encode('utf-8').decode('latin1')
        if good: ok += 1
        else:
            bad += 1
            print('FAIL', repr(t['input']), 'base', repr(t.get('base')), 'want', t.get('href', 'failure'),
                  'got', None if r is None else serialize(r))
    print(ok, 'ok', bad, 'bad')
