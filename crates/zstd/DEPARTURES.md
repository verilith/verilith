# Where verilith-zstd departs from libzstd

verilith-zstd decodes exactly what `src/spec.rs` accepts. The spec follows RFC 8878
and, where the RFC leaves a choice, libzstd 1.5.x. These are the cases
where it departs from one of them. Each departure from libzstd rejects
input that libzstd accepts; none changes the output of a stream that both
accept, and no stream from
libzstd's encoder is affected (the round-trip tests check this).

| case | verilith-zstd | libzstd | why |
| --- | --- | --- | --- |
| Match offset larger than the window (`Window_Size`) | rejected | accepted by one-shot `ZSTD_decompress` as long as it stays within the output (streaming has to stay within its buffer) | The RFC bounds offsets by the window. Rejecting larger ones makes one-shot and streaming agree, and lets streaming keep only one window of output. |
| Block size, and a compressed block's decoded size, above `min(Window_Size, 128 KiB)` | rejected, in one-shot and streaming | checked only in streaming; one-shot checks only 128 KiB | The RFC's `Block_Maximum_Size`. |
| Huffman literal streams not consumed exactly (bits left over, or read past the start) | rejected | accepted when its fast 4-stream decoder (x86-64) or the double-symbol decoder's last-symbol step is used: those check only that the output has the right length | The RFC says a stream is fully consumed at the end. Seen in 10 of 3000 corrupted test frames. |
| Sequences bitstream not consumed exactly | rejected | accepts bits left over, up to what the last state update would read, and over-reads | Same. Seen in 1 of 3000. |
| Reserved bits of the sequences section's modes byte | must be zero | ignored | Reserved in the RFC. Seen in 1 of 3000. |
| FSE table description that runs past the end of its input | rejected | can read past the end when the description is near the end of the block (`hbSize >= 8`) and wrap around | No valid description needs it. |
| Huffman code lengths over 11 | up to 12 accepted | same (`HUF_TABLELOG_MAX` = 12) | RFC 8878 says 11; verilith-zstd follows libzstd, so nothing libzstd accepts here is lost. |
| Offsets with a dictionary | up to the window plus the dictionary's content size, anywhere in the frame | one-shot: anything within the dictionary and the output so far; streaming: the same, until the output passes the window | RFC 8878 §5: the dictionary can be reached past the window only until the frame's output passes the window. Allowing it throughout keeps one rule for the whole frame; it accepts everything the RFC does, and the few frames it accepts beyond that, libzstd's one-shot decoder accepts too, with the same content. |
| Streaming with a dictionary | the output kept is the last window plus the dictionary's size (of dictionary and output), at most twice that and three blocks | the window, and the dictionary while it can be reached | Follows from the offsets row: a match may reach that far anywhere in the frame. |
| Dictionaries in memory | copied when loaded: the `_byReference` functions and `ZSTD_DCtx_refPrefix` copy too, and each context that uses a `ZSTD_DDict` keeps its own copy | referenced where the caller keeps them | The decoder keeps the content in a buffer it writes the frame after. The caller's memory is never held. Dictionaries of 4 GiB or more are refused (`memory_allocation`). |
| Loading a dictionary while a streamed frame is under way | refused (`stage_wrong`) | the same | |
| `ZSTD_DCtx_loadDictionary_advanced`, `ZSTD_DCtx_refPrefix_advanced`, `ZSTD_createDDict_advanced` (content types other than libzstd's default) | not provided | provided | `ZSTD_DCtx_loadDictionary` reads a dictionary as `ZSTD_dct_auto` does, and `ZSTD_DCtx_refPrefix` as `ZSTD_dct_rawContent`. |
| Empty input to the one-shot functions | `srcSize_wrong` | 0 bytes of output | The proven decoder gives empty output for empty input; the adapter has refused it since before dictionaries (seen in 5 of the 4000 corrupted frames in `tests/dict.rs`). |
| Legacy frames (v0.1 to v0.7) | rejected (`prefix_unknown`) | decoded when built with legacy support | Not in RFC 8878. |
| Magicless frames (`ZSTD_f_zstd1_magicless`) | not supported (`ZSTD_d_format` must be `ZSTD_f_zstd1`) | supported | Rarely used. |
| Window log above 31 | rejected | same on 64-bit hosts | |
| 32-bit targets (wasm32) | one-shot output at most 2 GiB; dictionaries below 128 MiB; streamed windows above 256 MiB rejected (`Fail::Limit`, `frameParameter_windowTooLarge`) | window log above 30 rejected | What the proofs need for every length and bit position to fit a 32-bit `usize`. libzstd's own default `ZSTD_d_windowLogMax` (27) is below the streaming bound. |
| Error codes on corrupt input | the first layout error libzstd would report (unknown magic, truncated input, reserved frame bits, dictionary, window too large); otherwise `corruption_detected`, or `checksum_wrong` when only the checksum is wrong | depends on how far its decoder got: for example `dstSize_tooSmall` when the output buffer fills before the corruption is reached | The verdict (error or not) is what is proven; the code is the adapter's best match. |
