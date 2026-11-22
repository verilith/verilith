# Where verilith-snappy departs from google/snappy

verilith-snappy decodes exactly what `src/spec.rs` accepts, and the spec follows
format_description.txt and framing_format.txt.

## The raw format

No difference in what is accepted or produced on decoding has been
found: on 100,000 corrupted inputs (60,000 through the Rust API, 40,000
through the C API) verilith-snappy and libsnappy 1.1.10 give the same verdict,
the same `snappy_status` and the same bytes, and
`snappy_validate_compressed_buffer` agrees with `snappy_uncompress`.

| case | verilith-snappy | libsnappy |
| --- | --- | --- |
| Bytes of compressed output | its own; the same size as libsnappy's to within 0.6% on Silesia. Both decode each other's output. | |
| Inputs of 4 GiB or more | `SNAPPY_INVALID_INPUT` from `snappy_compress` | the format cannot hold them either; the C++ API takes a 32-bit length |
| Bytes of the output buffer after the result, on a failed `snappy_uncompress` | may have been written, within the length the input declares | the same is true of libsnappy, with different bytes |

## The framing format

google/snappy's library does not implement the framing format, so there
is nothing of its own to depart from. Against the `snap` crate, 30,000
corrupted streams get the same verdict. Choices made:

| case | verilith-snappy |
| --- | --- |
| A stream of no bytes | valid, with no content (as `snap` and Go's `snappy` do), although the document says a stream starts with the identifier |
| A second stream identifier later in the stream | accepted if it is exactly the identifier, as the document says, so concatenated streams decode |
| When to store a chunk uncompressed | when compressing saves less than an eighth, as the document suggests and Go does |

## Not provided

The C++ API (`snappy::Compress`, `snappy::Uncompress`, `Source`/`Sink`,
`RawUncompressToIOVec`), and a streaming reader and writer for the
framing format: `frame_encode` and `frame_decode` work on whole buffers.
