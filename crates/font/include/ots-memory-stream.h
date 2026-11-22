// vfont's stand-in for OTS's <ots-memory-stream.h>: streams that write
// into memory. Header only.
#ifndef VFONT_OTS_MEMORY_STREAM_H_
#define VFONT_OTS_MEMORY_STREAM_H_

#include <cstring>
#include <vector>

#include "opentype-sanitiser.h"

namespace ots {

// Writes into a buffer the caller owns.
class MemoryStream : public OTSStream {
 public:
  MemoryStream(void *ptr, size_t length)
      : ptr_(static_cast<uint8_t *>(ptr)), length_(length), off_(0) {}

  size_t size() override { return length_; }

  bool WriteRaw(const void *data, size_t length) override {
    if (length > length_ - off_) return false;
    std::memcpy(ptr_ + off_, data, length);
    off_ += length;
    return true;
  }

  bool Seek(off_t position) override {
    if (position < 0 || static_cast<size_t>(position) > length_) return false;
    off_ = static_cast<size_t>(position);
    return true;
  }

  off_t Tell() const override { return static_cast<off_t>(off_); }

 private:
  uint8_t *const ptr_;
  const size_t length_;
  size_t off_;
};

// Writes into a buffer that grows as needed, up to `limit` bytes.
class ExpandingMemoryStream : public OTSStream {
 public:
  ExpandingMemoryStream(size_t initial, size_t limit)
      : limit_(limit), off_(0) {
    buf_.reserve(initial < limit ? initial : limit);
  }

  // The bytes written so far: Tell() of them once writing is done.
  void *get() { return buf_.data(); }

  size_t size() override { return limit_; }

  bool WriteRaw(const void *data, size_t length) override {
    if (off_ > limit_ || length > limit_ - off_) return false;
    if (off_ + length > buf_.size()) buf_.resize(off_ + length);
    std::memcpy(buf_.data() + off_, data, length);
    off_ += length;
    return true;
  }

  bool Seek(off_t position) override {
    if (position < 0 || static_cast<size_t>(position) > limit_) return false;
    off_ = static_cast<size_t>(position);
    if (off_ > buf_.size()) buf_.resize(off_);
    return true;
  }

  off_t Tell() const override { return static_cast<off_t>(off_); }

 private:
  std::vector<uint8_t> buf_;
  const size_t limit_;
  size_t off_;
};

}  // namespace ots

#endif  // VFONT_OTS_MEMORY_STREAM_H_
