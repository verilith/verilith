# Where verilith-lz4 departs from liblz4

verilith-lz4 decodes exactly what `src/spec.rs` accepts. The spec follows the LZ4
block and frame format documents and, where they leave a choice, liblz4
1.9.4. These are the cases where verilith-lz4 and liblz4 differ. None changes the
content of an input both accept, and nothing liblz4's compressors write
is affected (the round-trip tests check this).

## Decoding

| case | verilith-lz4 | liblz4 | why |
| --- | --- | --- | --- |
| A match offset of 0 | rejected | accepted: `LZ4_decompress_safe` copies from the output position itself, so the output holds whatever the buffer held before the call | The block format says 0 is invalid. Output that depends on the buffer's old contents cannot be specified. This is the only case in the corrupted-input tests where liblz4 accepts and verilith-lz4 does not (31 of 40,000 corrupted blocks). |
| End-of-block rules (the last 5 bytes are literals; the last match starts at least 12 bytes before the end) | not enforced: any block that ends with literals and stays in bounds is decoded | enforced in part, and against the capacity of the output buffer, not the decoded size: the same block can be accepted with one capacity and rejected with another | The format document puts these rules on the compressor and says a decoder may rely on them, not that it must check them. A verdict that depends on spare capacity cannot be a property of the input. verilith-lz4's compressor is proven to follow the rules. In the tests, verilith-lz4 accepts some corrupted blocks liblz4 rejects for this reason; the content always agrees when both accept. |
| A block size word of `0x80000000` (the "stored" bit with size 0) | the end mark, as in liblz4 | the end mark | The format says the end mark is `0x00000000`; liblz4 masks the top bit first, and verilith-lz4 follows it so the two agree. |
| Legacy frames (magic `0x184C2102`) | rejected (`ERROR_frameType_unknown`) | decoded | Not in the frame format document. |
| Memory used by `LZ4F_decompress` | given a whole frame and room for its content in one call, it decodes straight into the caller's buffer and allocates nothing; otherwise the whole compressed frame is collected, then decoded, then handed out | one block at a time | The proven decoder takes a whole frame. A streaming decoder proven the way verilith-zstd's is would remove this. Block sizes are checked against the header's maximum as they arrive, so a hostile size word cannot make it collect more than the stream holds. |
| A frame decoded with a dictionary (`LZ4F_decompress_usingDict`) | decoded into the context's own buffer, then handed out, even when it arrives whole with room for its content; the dictionary's last 64 KiB are copied into the context when it is given | decoded straight into the caller's buffer when it can; the caller's dictionary is used where it is, and must stay there until the frame ends | The proven decoder needs the dictionary right before the content it decodes. Both take the dictionary until the frame's first block and drop it at the frame's end, and neither checks the frame's dictionary ID against it. |
| The hint `LZ4F_decompress` returns | 0 at the end of a frame, otherwise a nonzero count of bytes it is waiting for | the size of the next block to feed | Callers may only rely on zero or nonzero. |
| Error codes | `ERROR_frameType_unknown` for a wrong magic number, `ERROR_maxBlockSize_invalid` for a block larger than the header allows, `ERROR_GENERIC` for a bad header, `ERROR_decompressionFailed` for everything else in a frame; `-1` from the block calls | more specific codes, and negative positions from the block calls | The verdict is what is proven; the code is the adapter's best match. |

## Compressing

| case | verilith-lz4 | liblz4 |
| --- | --- | --- |
| Compression levels 3 and up (`LZ4F_preferences_t.compressionLevel`), which select LZ4 HC | compressed with the fast compressor: valid, but larger | the HC compressor |
| `LZ4F_compressFrame` on small inputs | block size and block mode as asked | picks a smaller block size and independent blocks when the input fits in one block |
| `LZ4_compress_fast_extState` | ignores the state memory (its table is on the stack) | uses it |
| Bytes of a compressed block | its own; the same size as liblz4's to within 0.05% on Silesia | |

## Not provided

`LZ4_compress_destSize`, `LZ4_decompress_safe_partial`, the streaming
block API (`LZ4_stream_t`, `LZ4_compress_fast_continue`,
`LZ4_decompress_safe_continue`), the unsafe `LZ4_decompress_fast`, all of
`lz4hc.h`, the streaming frame compression API (`LZ4F_compressBegin`,
`LZ4F_compressUpdate`, `LZ4F_flush`, `LZ4F_compressEnd`) and the
`LZ4F_CDict` functions (compressing with a dictionary).
