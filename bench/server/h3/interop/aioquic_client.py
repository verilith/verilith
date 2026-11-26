"""Interop check: aioquic's HTTP/3 client against verilith-server.

  python3 -m venv aq && aq/bin/pip install aioquic
  verilith-server --threads 2 --http 18081 --h3 18444 --cert C --key K --root DIR
  aq/bin/python aioquic_client.py 18444

DIR holds 64k.bin and 1m.bin (65536 and 1048576 bytes): 32 requests over
one connection, with three key updates started by the client.
"""
import asyncio, ssl, sys
from aioquic.asyncio.protocol import QuicConnectionProtocol
from aioquic.h3.connection import H3_ALPN, H3Connection
from aioquic.h3.events import DataReceived, HeadersReceived
from aioquic.quic.configuration import QuicConfiguration
from aioquic.quic.events import QuicEvent


class Client(QuicConnectionProtocol):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.h3 = H3Connection(self._quic)
        self.waiting = {}

    def quic_event_received(self, event: QuicEvent):
        for e in self.h3.handle_event(event):
            if isinstance(e, (HeadersReceived, DataReceived)):
                st = self.waiting.get(e.stream_id)
                if st is None:
                    continue
                if isinstance(e, HeadersReceived):
                    st["headers"] = dict(e.headers)
                else:
                    st["body"] += e.data
                if e.stream_ended:
                    st["fut"].set_result(st)

    async def get(self, path):
        sid = self._quic.get_next_available_stream_id()
        self.h3.send_headers(sid, [(b":method", b"GET"), (b":scheme", b"https"), (b":authority", b"localhost"), (b":path", path.encode())], end_stream=True)
        fut = asyncio.get_event_loop().create_future()
        self.waiting[sid] = {"fut": fut, "body": b"", "headers": None}
        self.transmit()
        return await asyncio.wait_for(fut, 30)


async def main(port, sizes):
    cfg = QuicConfiguration(is_client=True, alpn_protocols=H3_ALPN, verify_mode=ssl.CERT_NONE, server_name="localhost")
    from aioquic.quic.connection import QuicConnection
    loop = asyncio.get_event_loop()
    _, c = await loop.create_datagram_endpoint(lambda: Client(QuicConnection(configuration=cfg)), local_addr=("127.0.0.1", 0))
    c.connect(("127.0.0.1", port))
    await c.wait_connected()
    if True:
        r = await c.get("/plaintext")
        assert r["headers"][b":status"] == b"200" and r["body"] == b"Hello, World!", r
        for rnd in range(3):
            rs = await asyncio.gather(*[c.get("/static/" + n) for n in sizes for _ in range(5)])
            for (n, r) in zip([n for n in sizes for _ in range(5)], rs):
                want = {"64k.bin": 65536, "1m.bin": 1 << 20}[n]
                assert r["headers"][b":status"] == b"200" and len(r["body"]) == want, (n, len(r["body"]))
            # A key update started by the client between rounds.
            c._quic.request_key_update()
            c.transmit()
        r = await c.get("/plaintext")
        assert r["body"] == b"Hello, World!"
        c.close()
        await c.wait_closed()
    print("aioquic interop ok: 32 requests, 3 key updates")


asyncio.run(main(int(sys.argv[1]), ["64k.bin", "1m.bin"]))
