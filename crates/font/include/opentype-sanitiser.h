// vfont's stand-in for OTS's <opentype-sanitiser.h>: the same classes and
// calls, with ots::OTSContext::Process() running the verified sanitizer.
// Header only; link with libverilith_font.a.
//
// What differs from OTS:
//  - Process() writes the whole font with one Write() call, at the
//    stream's current position, after sanitizing has finished. It never
//    seeks. If the font is refused, nothing is written.
//  - Message() is never called: vfont does not say why a font was refused.
//  - GetTableAction() is never called: which tables are sanitized, kept or
//    dropped is fixed (see README.md). There is no pass-through.
//  - The output of a TrueType Collection is the single font `index`
//    (default 0), not a collection.
#ifndef VFONT_OPENTYPE_SANITISER_H_
#define VFONT_OPENTYPE_SANITISER_H_

#include <sys/types.h>

#include <cstddef>
#include <cstdint>
#include <cstring>

#include "vfont.h"

#define OTS_TAG(c1, c2, c3, c4) \
  ((uint32_t)((((uint8_t)(c1)) << 24) | (((uint8_t)(c2)) << 16) | \
              (((uint8_t)(c3)) << 8) | ((uint8_t)(c4))))
#define OTS_UNTAG(tag) \
  ((char)((tag) >> 24)), ((char)((tag) >> 16)), ((char)((tag) >> 8)), \
      ((char)(tag))

namespace ots {

// Where the sanitized font is written.
class OTSStream {
 public:
  OTSStream() {}
  virtual ~OTSStream() {}

  // The most bytes the stream can hold.
  virtual size_t size() = 0;
  virtual bool WriteRaw(const void *data, size_t length) = 0;
  virtual bool Seek(off_t position) = 0;
  virtual off_t Tell() const = 0;

  bool Write(const void *data, size_t length) {
    return length == 0 || WriteRaw(data, length);
  }

  virtual bool Pad(size_t bytes) {
    static const uint8_t zeros[4] = {0, 0, 0, 0};
    while (bytes >= 4) {
      if (!WriteRaw(zeros, 4)) return false;
      bytes -= 4;
    }
    return bytes == 0 || WriteRaw(zeros, bytes);
  }

  bool WriteU8(uint8_t v) { return Write(&v, 1); }
  bool WriteU16(uint16_t v) {
    const uint8_t b[2] = {(uint8_t)(v >> 8), (uint8_t)v};
    return Write(b, 2);
  }
  bool WriteS16(int16_t v) { return WriteU16((uint16_t)v); }
  bool WriteU24(uint32_t v) {
    const uint8_t b[3] = {(uint8_t)(v >> 16), (uint8_t)(v >> 8), (uint8_t)v};
    return Write(b, 3);
  }
  bool WriteU32(uint32_t v) {
    const uint8_t b[4] = {(uint8_t)(v >> 24), (uint8_t)(v >> 16),
                          (uint8_t)(v >> 8), (uint8_t)v};
    return Write(b, 4);
  }
  bool WriteS32(int32_t v) { return WriteU32((uint32_t)v); }
  bool WriteR64(uint64_t v) { return Write(&v, 8); }
};

enum TableAction {
  TABLE_ACTION_DEFAULT,
  TABLE_ACTION_SANITIZE,
  TABLE_ACTION_PASSTHRU,
  TABLE_ACTION_DROP
};

class OTSContext {
 public:
  OTSContext() {}
  virtual ~OTSContext() {}

  // Sanitizes the `length` bytes at `input` and writes the rebuilt font to
  // `output`. Returns false, writing nothing, if the font is refused or
  // does not fit in the stream.
  bool Process(OTSStream *output, const uint8_t *input, size_t length,
               uint32_t index = 0) {
    uint8_t *font = nullptr;
    size_t font_length = 0;
    if (output == nullptr ||
        !vfont_sanitize(input, length, index, &font, &font_length)) {
      return false;
    }
    const bool ok =
        font_length <= output->size() && output->Write(font, font_length);
    vfont_free(font, font_length);
    return ok;
  }

  // Kept so that code written for OTS compiles. vfont calls neither.
  virtual void Message(int /*level*/, const char * /*format*/, ...) {}
  virtual TableAction GetTableAction(uint32_t /*tag*/) {
    return TABLE_ACTION_DEFAULT;
  }
};

}  // namespace ots

#endif  // VFONT_OPENTYPE_SANITISER_H_
