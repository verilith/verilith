#!/usr/bin/env python3
"""Writes the DNS responses for the dns suite, in wire format with name
compression, as a recursive resolver would send them.

small, typical and large are the three messages of vdns/bench (one A
record; CNAME + 4 A + 4 NS + 4 glue A; 30 A + 13 NS + 13 glue A). mixed
adds the record types c-ares decodes into structures: AAAA, MX, TXT, SRV,
SOA, CAA and an EDNS OPT record."""
import os
import struct

HERE = os.path.dirname(os.path.abspath(__file__))
TYPES = {"ANY": 255, "A": 1, "NS": 2, "CNAME": 5, "SOA": 6, "MX": 15, "TXT": 16, "AAAA": 28, "SRV": 33, "OPT": 41, "CAA": 257}


class Msg:
    def __init__(self):
        self.buf = bytearray()
        self.names = {}

    def name(self, n, compress=True):
        labels = [l for l in n.rstrip(".").split(".") if l]
        for i in range(len(labels)):
            suffix = ".".join(labels[i:]).lower()
            if compress and suffix in self.names:
                self.buf += struct.pack(">H", 0xC000 | self.names[suffix])
                return
            if len(self.buf) < 0x3FFF:
                self.names.setdefault(suffix, len(self.buf))
            lab = labels[i].encode()
            self.buf += bytes([len(lab)]) + lab
        self.buf += b"\0"


def build(question, qtype, answers=(), authority=(), additional=(), opt=False):
    m = Msg()
    m.buf += struct.pack(">HHHHHH", 0x1234, 0x8180, 1, len(answers), len(authority), len(additional) + opt)
    m.name(question)
    m.buf += struct.pack(">HH", TYPES[qtype], 1)
    for sec in (answers, authority, additional):
        for owner, ttl, t, rdata in sec:
            m.name(owner)
            m.buf += struct.pack(">HHI", TYPES[t], 1, ttl)
            at = len(m.buf)
            m.buf += b"\0\0"
            rdata(m)
            struct.pack_into(">H", m.buf, at, len(m.buf) - at - 2)
    if opt:
        m.buf += b"\0" + struct.pack(">HHIH", TYPES["OPT"], 1232, 0, 0)
    return bytes(m.buf)


def a(ip):
    return lambda m: m.buf.extend(bytes(ip))


def aaaa(ip):
    return lambda m: m.buf.extend(bytes(ip))


def nm(target):
    return lambda m: m.name(target)


def mx(pref, target):
    def f(m):
        m.buf += struct.pack(">H", pref)
        m.name(target)
    return f


def txt(*strings):
    def f(m):
        for s in strings:
            b = s.encode()
            m.buf += bytes([len(b)]) + b
    return f


def srv(prio, weight, port, target):
    def f(m):
        m.buf += struct.pack(">HHH", prio, weight, port)
        m.name(target, compress=False)
    return f


def soa(mname, rname, serial):
    def f(m):
        m.name(mname)
        m.name(rname)
        m.buf += struct.pack(">IIIII", serial, 7200, 3600, 1209600, 3600)
    return f


def caa(flags, tag, value):
    def f(m):
        m.buf += bytes([flags, len(tag)]) + tag.encode() + value.encode()
    return f


MESSAGES = {
    "small": build("example.com.", "A", [("example.com.", 300, "A", a([93, 184, 215, 14]))]),
    "typical": build(
        "www.example.com.", "A",
        [("www.example.com.", 300, "CNAME", nm("www.example.com.cdn.example.net."))]
        + [("www.example.com.cdn.example.net.", 300, "A", a([192, 0, 2, i])) for i in range(4)],
        [("example.net.", 86400, "NS", nm(f"ns{i}.example.net.")) for i in range(4)],
        [(f"ns{i}.example.net.", 300, "A", a([198, 51, 100, i])) for i in range(4)],
    ),
    "large": build(
        "big.example.org.", "A",
        [("big.example.org.", 300, "A", a([203, 0, 113, i])) for i in range(30)],
        [("example.org.", 86400, "NS", nm(f"{chr(97 + i)}.ns.example-servers.org.")) for i in range(13)],
        [(f"{chr(97 + i)}.ns.example-servers.org.", 300, "A", a([198, 51, 100, i])) for i in range(13)],
    ),
    "mixed": build(
        "example.com.", "ANY",
        [
            ("example.com.", 300, "A", a([93, 184, 215, 14])),
            ("example.com.", 300, "AAAA", aaaa([0x26, 0x06, 0x28, 0x00, 0x02, 0x1F, 0xCB, 0x07] + [0] * 6 + [0x68, 0x13])),
            ("example.com.", 3600, "MX", mx(10, "mail.example.com.")),
            ("example.com.", 3600, "MX", mx(20, "mail2.example.com.")),
            ("example.com.", 3600, "TXT", txt("v=spf1 include:_spf.example.com ~all")),
            ("example.com.", 3600, "TXT", txt("google-site-verification=abcdefghijklmnopqrstuvwxyz0123456789ABCDEFG")),
            ("_sip._tcp.example.com.", 3600, "SRV", srv(10, 60, 5060, "sip.example.com.")),
            ("example.com.", 3600, "CAA", caa(0, "issue", "letsencrypt.org")),
        ],
        [("example.com.", 3600, "SOA", soa("ns.icann.org.", "noc.dns.icann.org.", 2026110301))],
        [("mail.example.com.", 300, "A", a([93, 184, 215, 20]))],
        opt=True,
    ),
}

if __name__ == "__main__":
    for name, b in MESSAGES.items():
        with open(os.path.join(HERE, name + ".dns"), "wb") as f:
            f.write(b)
