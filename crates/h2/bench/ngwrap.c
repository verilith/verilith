// nghttp2's frame layer, for the benchmark: nghttp2_frame.c's own decode
// and encode functions, with the frame-level checks nghttp2_session.c's
// inbound state machine makes before and after calling them (length
// against SETTINGS_MAX_FRAME_SIZE, stream identifier, fixed lengths,
// padding, SETTINGS values). The session's stream and flow-control work
// is not included, so this is a lower bound for nghttp2.
#include <stdint.h>
#include <string.h>
#include "nghttp2_frame.h"
#include "nghttp2_helper.h"

#define MAXF 16384

static int unpad(const nghttp2_frame_hd *hd, const uint8_t *p, size_t fixed,
                 size_t *a, size_t *z) {
  size_t n = hd->length;
  if (hd->flags & NGHTTP2_FLAG_PADDED) {
    if (n < 1 + fixed) return -1;
    size_t pad = p[0];
    if (pad > n - 1 - fixed) return -1;
    *a = 1 + fixed;
    *z = n - pad;
  } else {
    if (n < fixed) return -1;
    *a = fixed;
    *z = n;
  }
  return 0;
}

// Decodes every frame in b; returns the number decoded, or -1 on an error.
// *acc gets a sum over the fields, so nothing is optimized away.
long ng_parse_all(const uint8_t *b, size_t n, uint64_t *acc) {
  size_t off = 0;
  long count = 0;
  uint64_t s = 0;
  nghttp2_frame f;
  nghttp2_settings_entry iv[1];
  while (off + 9 <= n) {
    nghttp2_frame_unpack_frame_hd(&f.hd, b + off);
    if (f.hd.length > MAXF) return -1;
    if (off + 9 + f.hd.length > n) break;
    const uint8_t *p = b + off + 9;
    size_t a = 0, z = 0;
    switch (f.hd.type) {
    case NGHTTP2_DATA:
      if (f.hd.stream_id == 0 || unpad(&f.hd, p, 0, &a, &z)) return -1;
      s += z - a + (uintptr_t)(p + a);
      break;
    case NGHTTP2_HEADERS: {
      size_t fixed = (f.hd.flags & NGHTTP2_FLAG_PRIORITY) ? 5 : 0;
      if (f.hd.stream_id == 0 || unpad(&f.hd, p, fixed, &a, &z)) return -1;
      f.headers.padlen = (f.hd.flags & NGHTTP2_FLAG_PADDED) ? p[0] : 0;
      if (fixed) nghttp2_frame_unpack_headers_payload(&f.headers, p + a - 5);
      s += z - a + (uintptr_t)(p + a) + (uint32_t)f.headers.pri_spec.stream_id;
      break;
    }
    case NGHTTP2_PRIORITY:
      if (f.hd.stream_id == 0 || f.hd.length != 5) return -1;
      nghttp2_frame_unpack_priority_payload(&f.priority, p);
      s += (uint32_t)f.priority.pri_spec.stream_id + (uint32_t)f.priority.pri_spec.weight;
      break;
    case NGHTTP2_RST_STREAM:
      if (f.hd.stream_id == 0 || f.hd.length != 4) return -1;
      nghttp2_frame_unpack_rst_stream_payload(&f.rst_stream, p);
      s += f.rst_stream.error_code;
      break;
    case NGHTTP2_SETTINGS: {
      if (f.hd.stream_id != 0 || f.hd.length % 6 ||
          ((f.hd.flags & NGHTTP2_FLAG_ACK) && f.hd.length)) return -1;
      size_t k = f.hd.length / 6;
      for (size_t i = 0; i < k; i++) {
        nghttp2_frame_unpack_settings_entry(&iv[0], p + 6 * i);
        uint32_t v = iv[0].value;
        switch (iv[0].settings_id) {
        case NGHTTP2_SETTINGS_ENABLE_PUSH:
        case NGHTTP2_SETTINGS_ENABLE_CONNECT_PROTOCOL:
        case NGHTTP2_SETTINGS_NO_RFC7540_PRIORITIES:
          if (v > 1) return -1;
          break;
        case NGHTTP2_SETTINGS_INITIAL_WINDOW_SIZE:
          if (v > NGHTTP2_MAX_WINDOW_SIZE) return -1;
          break;
        case NGHTTP2_SETTINGS_MAX_FRAME_SIZE:
          if (v < NGHTTP2_MAX_FRAME_SIZE_MIN || v > NGHTTP2_MAX_FRAME_SIZE_MAX) return -1;
          break;
        }
        s += v;
      }
      break;
    }
    case NGHTTP2_PUSH_PROMISE:
      if (f.hd.stream_id == 0 || unpad(&f.hd, p, 4, &a, &z)) return -1;
      nghttp2_frame_unpack_push_promise_payload(&f.push_promise, p + a - 4);
      s += (uint32_t)f.push_promise.promised_stream_id + z - a;
      break;
    case NGHTTP2_PING:
      if (f.hd.stream_id != 0 || f.hd.length != 8) return -1;
      nghttp2_frame_unpack_ping_payload(&f.ping, p);
      s += f.ping.opaque_data[7];
      break;
    case NGHTTP2_GOAWAY:
      if (f.hd.stream_id != 0 || f.hd.length < 8) return -1;
      nghttp2_frame_unpack_goaway_payload(&f.goaway, p, (uint8_t *)p + 8, f.hd.length - 8);
      s += f.goaway.error_code + f.goaway.opaque_data_len;
      break;
    case NGHTTP2_WINDOW_UPDATE:
      if (f.hd.length != 4) return -1;
      nghttp2_frame_unpack_window_update_payload(&f.window_update, p);
      if (f.window_update.window_size_increment == 0) return -1;
      s += (uint32_t)f.window_update.window_size_increment;
      break;
    case NGHTTP2_CONTINUATION:
      if (f.hd.stream_id == 0) return -1;
      s += f.hd.length;
      break;
    default:
      s += f.hd.length;
    }
    s += f.hd.stream_id;
    off += 9 + f.hd.length;
    count++;
  }
  *acc += s;
  return count;
}

// Writes the frame header for each (len, type, flags, stream) quadruple.
void ng_pack_heads(const uint32_t *q, size_t k, uint8_t *out) {
  nghttp2_frame_hd hd;
  for (size_t i = 0; i < k; i++) {
    hd.length = q[4 * i];
    hd.type = (uint8_t)q[4 * i + 1];
    hd.flags = (uint8_t)q[4 * i + 2];
    hd.stream_id = (int32_t)q[4 * i + 3];
    hd.reserved = 0;
    nghttp2_frame_pack_frame_hd(out + 9 * i, &hd);
  }
}
