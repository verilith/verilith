# Where verilith-dns departs from the RFCs, and from c-ares

Every place where verilith-dns reads a rule more strictly or more loosely than the
text of an RFC, chooses between readings, or behaves differently from
c-ares. The parser and serializer rules are those of the trusted specs
(`src/spec.rs`, `src/spec_rdata.rs`, `src/spec_text.rs`), so this table is
also a reading guide to them. Rows marked *adapter* are policies of the
unverified c-ares adapter (`src/cares.rs`), which copies c-ares's own
behaviour so that the patched c-ares accepts and writes what c-ares does,
except where noted.

Each c-ares difference is measured by a differential test that fails on any
difference it cannot classify (`tests/differential.rs`,
`tests/differential_rdata.rs`, `tests/cares_abi.rs`; see the README).

## Parsing

| Topic | What the RFCs say | verilith-dns | c-ares |
| --- | --- | --- | --- |
| Name length | 255 octets (RFC 1035 §2.3.4, §3.1), counting decompressed parts and the root octet (RFC 9267 §3) | Exactly that: at most 255 wire octets, however the name is assembled | Caps the presentation length at 255, so it accepts names of 256 and 257 wire octets |
| Pointer target | A pointer refers to a "prior occurrence" (RFC 1035 §4.1.4); RFC 9267 §2 asks only that it point before the pointer | Strictly before the start of the current run of labels, which also rules out every loop | Same rule |
| Pointer to a pointer | A pointer must land on a label length octet (RFC 9267 §2) | Rejected | Accepted, up to 128 in a chain |
| Pointer to a root octet | Not addressed | Accepted, as a zero-length label | Accepted |
| Nested compression (a pointer to a name that itself ends in a pointer) | "Should be discouraged" (RFC 9267 §2) | Accepted, since every mainstream compressor produces it | Accepted |
| Label types 0b01 and 0b10 | Reserved (RFC 1035 §4.1.4; RFC 6891 §5 retired extended labels) | Rejected | Rejected |
| Bytes after the last record | Counts must match the data (RFC 9267 §6) | `parse` rejects them. *adapter*: ignored, as c-ares does | Ignored |
| Counts larger than the message can hold | Drop the message (RFC 9267 §6) | Rejected before any decoding, which is proven never to reject a message the spec accepts | Rejected while decoding |
| QDCOUNT | At most 1 for opcode QUERY (RFC 9619 §3) | `parse` accepts any count. *adapter*: exactly one, as c-ares requires | Exactly one |
| RDATA that does not conform to its TYPE | Drop the message (RFC 9267 §5) | For the types with names in RDATA (NS, CNAME, SOA, PTR, MX, SIG, SRV, NAPTR), the message is rejected. For other types, `record.data()` returns `None` and the message is kept, its RDATA available as bytes | Rejects the message, except under the `ARES_DNS_PARSE_*_RAW` flags, where it keeps malformed RDATA as bytes |
| Compressed names inside RDATA | Allowed only in the RFC 1035 types (RFC 3597 §4); receivers must still decompress them in the types that predate it | Decompressed while parsing, for all eight name-bearing types, and stored uncompressed, so a record means the same thing wherever it is copied (proven) | Decompressed into the typed record; under the raw flags, RDATA is kept with its pointers, which refer to the original message |
| Character strings (TXT, HINFO, NAPTR, CAA tag excluded) | Any octets (RFC 1035 §3.3) | Any octets. *adapter*: HINFO, NAPTR and URI strings must be printable ASCII, as c-ares requires | Printable ASCII for HINFO, NAPTR and URI |
| SVCB and HTTPS keys | Strictly increasing; other orders are malformed (RFC 9460 §2.2) | `data()` refuses other orders | Accepts any order |
| CAA tag | Non-empty, ASCII letters and digits (RFC 8659 §4.1) | Checked | Not checked |
| Trailing bytes inside RDATA | RDATA must be consumed exactly by its type (RFC 9267 §5) | Checked for every typed RDATA | Ignored in some types |
| Empty trailing fields (TLSA data, CAA value, signatures, digests, keys, NSEC bit maps) | Allowed by the wire format | Allowed. *adapter*: refused, as c-ares does | Refused |
| Classes other than IN, CH, HS and NONE | Allowed | Allowed. *adapter*: refused by c-ares's record builder | Refused |
| More than one OPT record | Malformed (RFC 6891 §6.1.1) | `parse` keeps every record. *adapter*: refused | Refused |
| Several EDNS options with the same code | Allowed | All kept | Only one kept per code |
| TTL with the high bit set | "Should" be treated as zero (RFC 2181 §8) | Returned as received | Returned as received |

## Writing

| Topic | What the RFCs say | verilith-dns | c-ares |
| --- | --- | --- | --- |
| Which names are compressed | Owner and question names, and names in the RDATA of the RFC 1035 types; never in other types (RFC 3597 §4, RFC 4034 §3.1.7 and §4.1.1, RFC 2782) | Owner and question names, and the names in NS, CNAME, SOA, PTR and MX RDATA. Everything else is written uncompressed | Same |
| Pointer targets | 14-bit offsets (RFC 1035 §4.1.4) | Only offsets up to 0x3FFF are offered as targets | Same |
| Matching suffixes | Not specified | Byte-exact, so the case of every name is kept (DNS 0x20) | Byte-exact |
| Result | | `to_bytes_compressed` is proven to parse back to the message it was given | Not verified |
| Name length | 255 wire octets | Longer names are refused (`ARES_EBADNAME` from the adapter) | Limits the unescaped text to 255 characters, so it writes names of up to 257 wire octets. It also refuses any name whose *escaped* text is over 255 characters, though its own parser produces such names (seen once in 141k records) |
| SVCB and HTTPS keys | Must be written in increasing order (RFC 9460 §2.2) | Sorted on output | Written in the order they were added, which c-ares's test `LibraryTest.DNSRecord` relies on and which verilith-dns, like any RFC 9460 client, then rejects. With the verilith-dns writer the test passes |
| Raw RDATA of a type with names in it (from a raw-flag parse) | Compression pointers are offsets into the message they came from | Refused (`ARES_EFORMERR`) if it holds a pointer or does not decode as its type | Copied as is, so its pointers now point at whatever is at those offsets in the new message |
| Escapes in presentation names | `\DDD` is three digits (RFC 1035 §5.1) | *adapter*: `\` and a digit must be followed by two more digits, and owner and question names may hold only letters, digits and `-._/*`, as in c-ares | Same |
| Typed fields that do not fit their format | A CAA tag is 1 to 15 ASCII letters and digits (RFC 8659 §4.1); an EDNS option or SVCB value is at most 65535 octets; SVCB keys appear once each (RFC 9460 §2.2) | Refused (`ARES_EFORMERR`): the verified encoder writes only RDATA that decodes back to the record's fields | Written anyway (11 CAA records in 141k), producing RDATA its own parser and verilith-dns's reject. Oversized option values were truncated by the earlier verilith-dns adapter |
| A raw record with empty RDATA | Allowed | *adapter*: refused, as c-ares does | Refused |
| Messages over 65535 octets | The largest DNS message, even over TCP | Refused (`ARES_EBADQUERY`) | Same |

## The builder

`Message::add_record` takes RDATA as bytes. Names in it are resolved against
the RDATA alone (a pointer means an offset into the RDATA), stored
uncompressed, and RDATA that does not decode as its type is refused
(`BuildError::BadRdata`). There is no RFC rule for this; it is the reading
under which a record's bytes mean the same thing everywhere.
