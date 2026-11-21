# c-ares with verilith-dns as its parser

`c-ares-use-vdns.patch` makes c-ares use verilith_dns for every DNS message it
parses or writes. c-ares keeps everything else: sockets, retries, caching
and the query API. Apply it to c-ares at commit `4c60465` or later.

The patch adds 31 lines. When `CARES_VDNS_LIB` is set, it compiles out
c-ares's own `ares_dns_parse` and `ares_expand_name`, links verilith-dns in their
place, and makes `ares_dns_write_buf` (behind `ares_dns_write` and the TCP
writer) call verilith-dns, passing the record's private TTL decrement along. Every
c-ares path that reads a response goes through the first two: `ares_process`
for answers, `ares_send` and the cache, and the legacy `ares_parse_*_reply`
functions. Every query c-ares sends, and every record it copies with
`ares_dns_record_duplicate`, goes through the third.

```sh
# verilith-dns, exporting its functions under c-ares's names
cargo build --release --features cares,ares-abi      # target/release/libverilith_dns.a

# c-ares
cd c-ares && git apply /path/to/verilith/crates/dns/cares/c-ares-use-vdns.patch
cmake -B build -DCARES_VDNS_LIB=/path/to/verilith/target/release/libverilith_dns.a -DCARES_BUILD_TESTS=ON
cmake --build build
./build/bin/arestest --gtest_filter='-*Live*'
```

## How it works

`src/cares.rs` parses the message with the verified `verilith_dns::parse` and decodes
each record with the verified `RecordRef::data`. It then builds c-ares's own
`ares_dns_record_t` with c-ares's public setters, so callers get the same
structure, the same allocator and the same accessors as before. The adapter
is not verified. It only copies fields that are already decoded, and it
applies c-ares's policies that go beyond the RFCs:

- exactly one question;
- printable HINFO, NAPTR and URI strings;
- non-empty TLSA, CAA and DNSSEC trailing fields;
- the `ARES_DNS_PARSE_*_RAW` flags;
- extended RCODEs from OPT;
- at most one OPT record;
- bytes after the last record are ignored;
- with the `*_RAW` flags, RDATA is passed on exactly as received
  (compression pointers included), as c-ares does, while verilith-dns itself keeps
  it with names decompressed;
- c-ares's error codes (`ARES_EBADNAME` for a bad name, `ARES_EBADRESP`
  otherwise).

For writing, `dns_write` reads the record with c-ares's public getters,
converts each name with the verified presentation-format parser, and hands
the fields to the verified `encode::encode_rdata`, which lays out each
type's RDATA as c-ares does and is proven to write bytes that decode back to
exactly those fields. A verilith-dns `Message` built from them is written by the
verified `to_bytes_compressed`. It applies c-ares's rules: the header
flag bits, SERVFAIL for an extended RCODE without an OPT record to carry it,
hostname characters in owner and question names, the field limits of each
type, the TTL decrement of cached answers, and the 64 KiB message limit. It
differs in four places, all listed in [DEPARTURES.md](../DEPARTURES.md):
SVCB and HTTPS keys are written in increasing order, raw RDATA holding
compression pointers into the message it came from is refused rather than
copied, names whose escaped text is over 255 characters are written, and
fields that do not fit their type's format (such as a CAA tag with
characters other than letters and digits) are refused rather than written.

## Results

c-ares's test suite on the patched build (Live tests and IPv6 tests left
out, because the build machine has no network or IPv6): **758 of 759 pass**.
The failure is deliberate: c-ares accepts something an RFC says to reject.

| Test | What c-ares expects | What verilith-dns does |
| --- | --- | --- |
| `LibraryTest.ParseAcceptsMaxLengthName` | It accepts a name of four 63-octet labels: 255 presentation octets, but 257 wire octets | Rejects it. RFC 1035 §2.3.4 limits names to 255 wire octets |

`LibraryTest.DNSRecord`, which failed with only the parser replaced, passes
now: c-ares's writer put SVCB keys in the order they were added (key 6, then
3), which verilith-dns's parser rejects as RFC 9460 §2.2 requires; verilith-dns's writer
puts them in order.

`tests/cares_abi.rs` checks the adapter against c-ares's own
`ares_dns_parse` on 200,000 random responses, half of them mutated, with
four flag settings each. Whenever both accept, the two records written back
with `ares_dns_write` are byte for byte identical. verilith-dns never accepts a
message that c-ares rejects. The 1.2% that only c-ares accepts are all
cases where c-ares is looser than the RFCs, and each one is classified by
reason (see the main README). Most of them are malformed NS, CNAME, SOA,
PTR, MX, SIG, SRV or NAPTR RDATA, which c-ares keeps when a caller asks
for raw RDATA and verilith-dns always drops (RFC 9267 §5).

The same file checks the vdns-backed `ares_dns_write` against c-ares's own
on 141,236 records built by c-ares's parser (see the main README), and the
`ares_dns_write` fuzz target does the same under AddressSanitizer.

The c-ares fuzz corpora (`test/fuzzinput`, `test/fuzznames`) run clean through
`aresfuzz` and `aresfuzzname` on the patched build.

Speed: building the full c-ares record takes 0.47, 3.1 and 11.7 µs for the
small, typical and large benchmark messages with verilith-dns, against 0.71, 6.6 and
25 µs for c-ares's own parser built with `-O3`. Writing it back takes 0.48,
5.7 and 19.9 µs, against 0.91, 7.2 and 24.5 µs, and the output is smaller
(948 bytes for the large message, against 1,226). See the main README's
performance table.
