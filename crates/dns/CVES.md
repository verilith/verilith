# verilith-dns against recent DNS parsing CVEs

Each CVE below is a bug in another DNS parser. For each one, the table gives
the proven verilith-dns property that rules out the whole bug class for every input,
and a test in `tests/cves.rs` that reproduces the attack packet's shape and
checks how verilith-dns handles it. Run them with `cargo test --release --test cves`.

| CVE | Where | CVSS | Bug | Why verilith-dns is not affected (proven) | Test |
| --- | --- | --- | --- | --- | --- |
| CVE-2026-114605 | dnspython < 2.9.0 (Oct 2026) | 7.5 | Name decompression follows a pointer chain with no hop limit (CPU DoS) | A pointer must land on a label, never on another pointer (RFC 9267 §2), and each name takes at most 256 loop steps | `cve_2026_114605_and_64194_pointer_chains`: chains of up to 8k hops (the most 14-bit pointers allow) rejected at the first hop |
| CVE-2026-64194 | Net::DNS (Perl) ≤ 1.55 (Jul 2026) | n/a | The same chain overflows the stack in a recursive decoder | The decoder is a loop with no recursion and a proven step bound | same test; a legal label/pointer chain is cut off by the 255-octet limit |
| CVE-2025-2962 | Zephyr < 3.7.2 / 4.2.0 | 7.5 | Infinite loop in `dns_copy_qname` on crafted pointers | Termination is proven: every pointer targets an offset strictly before the current label run | `cve_2025_2962_pointer_loops`: self, mutual and label loops |
| CVE-2025-1675 | Zephyr < 3.7.2 | 8.2 (NVD 9.1) | `memcpy` with an untrusted label length, reading out of bounds | Verus checks every index: no out-of-bounds read is possible | `cve_2025_1675_lengths_past_the_end`: long labels, out-of-range or truncated pointers, oversized RDLENGTH, every truncation of a valid message |
| CVE-2026-2291 | dnsmasq (May 2026) | high | Heap overflow in `extract_name` on crafted name data | Decoded names are proven to be at most 255 octets, however they are built from pointers, and are written to a growable arena, never a fixed buffer | `cve_2026_2291_names_that_expand_past_255`: 255 accepted, 257 rejected |
| CVE-2017-1000381 | c-ares < 1.13.0 | 7.5 | `ares_parse_naptr_reply` reads past the input on crafted NAPTR RDATA | Typed RDATA decoding is proven exact against the spec and free of out-of-bounds reads; every field must fit inside the RDATA | `tests/rdata.rs` `cve_2017_1000381_naptr_out_of_bounds`: every truncation and every overstated string length |
| CVE-2021-3672 | c-ares < 1.17.2 | 5.6 | Host names from DNS were not validated, so a label containing `.` or control bytes printed as a different name | Presentation output escapes `.`, specials and non-printable bytes, and printing then parsing is proven to give back the same name, so two names never print alike | `tests/rdata.rs` `cve_2021_3672_hostile_labels_are_escaped` |
| CVE-2023-4408 | BIND 9 | 7.5 | Super-linear cost parsing large messages with many names | At most 256 steps per name, and counts are checked against the message size before decoding (≥5 bytes per question, ≥11 per record), so total work is linear in the message size | `cve_2023_4408_large_message_is_linear`: a 64 KB message with 5,438 records whose owner names each expand to up to 255 octets parses in about 2 ms |

## What this does not cover

- **Bugs outside parsing.** For example, c-ares CVE-2025-31498 (CVSS 8.3) is
  a use-after-free in connection handling (`read_answers`) when a query is
  re-sent. verilith-dns replaces c-ares's parser, not its networking: with the
  patch in `cares/`, c-ares parses every response with verilith-dns but keeps its
  own sockets, retries and cache, so a bug there is still c-ares's.
- **DNSSEC validation and resolver logic.** Every DNSSEC record type c-ares
  decodes (RRSIG, NSEC, NSEC3, DNSKEY, DS and the rest) is now decoded and
  proven against its spec, but checking signatures, KeyTrap
  (CVE-2023-50387), cache poisoning and similar issues are about
  validation and caching, not parsing.
- **Types neither verilith-dns nor c-ares decodes** are handed over as raw bytes
  (RFC 3597), so a caller's own decoder for them is outside this crate.
- **The trusted base.** The guarantees assume the specs (`src/spec*.rs`) say
  what RFC 1035, RFC 9267 and the RDATA RFCs say, and that Verus, Z3 and
  rustc are correct. `src/name.rs` (iterators), `src/capi.rs` and
  `src/cares.rs` (the c-ares adapters) are unverified; they only copy
  fields the verified code has already decoded.

## Sources

- CVE-2026-114605: <https://www.strix.ai/cve/CVE-2026-114605>
- CVE-2026-64194: <https://lists.security.metacpan.org/cve-announce/msg/41989541/>
- CVE-2025-2962: <https://osv.dev/vulnerability/CVE-2025-2962>
- CVE-2025-1675: <https://db.gcve.eu/vuln/cve-2025-1675>
- CVE-2026-2291: <https://windowsforum.com/news/cve-2026-2291-dnsmasq-dns-parsing-bug-patch-focus-for-windows-hybrid-environments.420061/>
- CVE-2023-4408: <https://kb.isc.org/cve-2023-4408>
- CVE-2017-1000381: <https://tenable.com/cve/CVE-2017-1000381>
- CVE-2021-3672: <https://tenable.com/cve/CVE-2021-3672>
- CVE-2025-31498: <https://tenable.com/cve/CVE-2025-31498>
