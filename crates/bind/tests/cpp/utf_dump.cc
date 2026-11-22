// Runs every simdutf function Node and V8 use over a seeded corpus and prints the
// results, one line per call. Built once against real simdutf and once
// against include/simdutf.h (vtext); run.sh diffs the two outputs.
//
//   utf_dump [cases]
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "simdutf.h"

static uint64_t state = 0x9E3779B97F4A7C15ull;
static uint64_t rnd() {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return state;
}

static uint64_t hash(const void *p, size_t n) {
  const unsigned char *b = static_cast<const unsigned char *>(p);
  uint64_t h = 1469598103934665603ull;
  for (size_t i = 0; i < n; i++) h = (h ^ b[i]) * 1099511628211ull;
  return h;
}

static void line(const char *what, size_t c, long a, long b = 0,
                 uint64_t h = 0) {
  printf("%zu %s %ld %ld %016llx\n", c, what, a, b, (unsigned long long)h);
}

// A decode for Uint8Array.fromBase64: the error, the units read, and the
// bytes written.
static void from64(const std::string &what, size_t c, simdutf::result d,
                   const char *out, size_t len) {
  printf("%zu %s %d %zu %zu:%016llx\n", c, what.c_str(), int(d.error), d.count,
         len, (unsigned long long)hash(out, len));
}

// UTF-8 text: mostly valid characters of every length, sometimes damaged.
static std::string utf8_text(size_t n) {
  std::string s;
  while (s.size() < n) {
    uint32_t k = rnd() % 10, c;
    if (k < 5) c = rnd() % 0x80;
    else if (k < 7) c = 0x80 + rnd() % 0x780;
    else if (k < 9) c = 0x800 + rnd() % 0xF800;
    else c = 0x10000 + rnd() % 0x100000;
    if (c >= 0xD800 && c < 0xE000) c = 0xFFFD;
    if (c < 0x80) s += char(c);
    else if (c < 0x800) { s += char(0xC0 | c >> 6); s += char(0x80 | (c & 63)); }
    else if (c < 0x10000) {
      s += char(0xE0 | c >> 12); s += char(0x80 | (c >> 6 & 63));
      s += char(0x80 | (c & 63));
    } else {
      s += char(0xF0 | c >> 18); s += char(0x80 | (c >> 12 & 63));
      s += char(0x80 | (c >> 6 & 63)); s += char(0x80 | (c & 63));
    }
  }
  if (rnd() % 2 && !s.empty()) {
    size_t m = 1 + rnd() % 3;
    for (size_t i = 0; i < m; i++) s[rnd() % s.size()] = char(rnd());
  }
  return s;
}

static std::u16string utf16_text(size_t n) {
  std::u16string s;
  while (s.size() < n) {
    uint32_t k = rnd() % 10;
    if (k < 5) s += char16_t(rnd() % 0x80);
    else if (k < 7) s += char16_t(0x80 + rnd() % 0x80);
    else if (k < 9) {
      char16_t u = char16_t(0x100 + rnd() % 0xFF00);
      if (u >= 0xD800 && u < 0xE000) u = 0x20AC;
      s += u;
    } else {
      s += char16_t(0xD800 + rnd() % 0x400);
      s += char16_t(0xDC00 + rnd() % 0x400);
    }
  }
  if (rnd() % 3 == 0 && !s.empty()) s[rnd() % s.size()] = char16_t(0xD800 + rnd() % 0x800);
  return s;
}

static std::string bytes(size_t n, bool ascii) {
  std::string s(n, 0);
  for (auto &c : s) c = char(ascii ? rnd() % 0x80 : rnd());
  if (ascii && n && rnd() % 2) s[rnd() % n] = char(0x80 | rnd());
  return s;
}

static const char *B64 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/-_= \t\n\r\f";

// Base64 text: an encoding, then sometimes whitespace, damage, a lost tail.
static std::string b64_text(size_t n, bool url) {
  std::string bin = bytes(n, false);
  auto opt = url ? simdutf::base64_url : simdutf::base64_default;
  if (rnd() % 4 == 0) opt = simdutf::base64_options(opt ^ simdutf::base64_reverse_padding);
  std::string s(simdutf::base64_length_from_binary(n, opt), 0);
  s.resize(simdutf::binary_to_base64(bin.data(), n, s.data(), opt));
  uint32_t k = rnd() % 8;
  if (k == 0 && !s.empty()) s.insert(rnd() % s.size(), 1, " \t\n\r\f"[rnd() % 5]);
  if (k == 1 && !s.empty()) s[rnd() % s.size()] = B64[rnd() % 72];
  if (k == 2 && !s.empty()) s.resize(rnd() % s.size());
  if (k == 3) s += std::string(rnd() % 3, '=');
  if (k == 4) s += "  \n";
  if (k == 5 && !s.empty()) s[rnd() % s.size()] = char(rnd());
  if (k == 6) { s = ""; for (size_t i = 0, m = rnd() % 12; i < m; i++) s += B64[rnd() % 72]; }
  return s;
}

// A safe decode. With a big enough buffer, the exact result. With a smaller
// one, only whether it succeeded with the bytes of the full decode (2), failed
// (0), or succeeded with other bytes (3): simdutf's small-buffer path decodes
// in chunks and reports errors that depend on where they end (and fails on
// some valid inputs with whitespace after the padding), while any error makes
// Node fall back to its own decoder.
static void safe(const char *what, size_t c, simdutf::result d, bool big,
                 const char *out, size_t outlen, const std::string &full) {
  bool ok = d.error == simdutf::SUCCESS;
  if (big) {
    line(what, c, d.error, ok ? outlen : 0, ok ? hash(out, outlen) : 0);
  } else {
    std::string small = std::string(what) + "/small";
    line(small.c_str(), c, !ok ? 0 : std::string(out, outlen) == full ? 2 : 3);
  }
}

int main(int argc, char **argv) {
  size_t cases = argc > 1 ? strtoul(argv[1], 0, 10) : 20000;
  for (size_t c = 0; c < cases; c++) {
    size_t n = rnd() % 4 == 0 ? rnd() % 4000 : rnd() % 80;

    // UTF-8 side.
    std::string u8 = utf8_text(n);
    line("validate_utf8", c, simdutf::validate_utf8(u8.data(), u8.size()));
    auto r = simdutf::validate_utf8_with_errors(u8.data(), u8.size());
    line("validate_utf8_with_errors", c, r.error, r.count);
    bool v8 = r.error == simdutf::SUCCESS;
    if (v8) {
      size_t m = simdutf::utf16_length_from_utf8(u8.data(), u8.size());
      std::vector<char16_t> o(m + 1);
      size_t w = simdutf::convert_utf8_to_utf16(u8.data(), u8.size(), o.data());
      line("convert_utf8_to_utf16", c, m, w, hash(o.data(), 2 * w));
      w = simdutf::convert_utf8_to_utf16le(u8.data(), u8.size(), o.data());
      line("convert_utf8_to_utf16le", c, m, w, hash(o.data(), 2 * w));
      size_t l = simdutf::latin1_length_from_utf8(u8.data(), u8.size());
      std::vector<char> o1(l + 1);
      auto e = simdutf::convert_utf8_to_latin1_with_errors(u8.data(), u8.size(), o1.data());
      line("convert_utf8_to_latin1_with_errors", c, e.error,
           e.count, e.error ? 0 : hash(o1.data(), e.count));
      w = simdutf::convert_valid_utf8_to_utf16(u8.data(), u8.size(), o.data());
      line("convert_valid_utf8_to_utf16", c, m, w, hash(o.data(), 2 * w));
    } else {
      // Invalid input: simdutf's converters return 0 (the output is unspecified).
      std::vector<char16_t> o(2 * u8.size() + 2);
      line("convert_utf8_to_utf16/bad", c,
           simdutf::convert_utf8_to_utf16(u8.data(), u8.size(), o.data()));
    }

    {
      // Valid or not: the error and its position, and the text if valid.
      std::vector<char16_t> o(2 * u8.size() + 2);
      auto e = simdutf::convert_utf8_to_utf16_with_errors(u8.data(), u8.size(), o.data());
      line("convert_utf8_to_utf16_with_errors", c, e.error, e.count,
           e.error ? 0 : hash(o.data(), 2 * e.count));
      // Not NUL: simdutf 7.7.0's find returns a position inside the text
      // for a NUL that is not there.
      char want = char(1 + rnd() % 0x7F);
      line("find", c, simdutf::find(u8.data(), u8.data() + u8.size(), want) - u8.data());
    }
    {
      // UTF-32, one unit at a time as merve calls it, then a run.
      std::vector<char32_t> u32(n % 50);
      for (auto &u : u32) {
        uint32_t k = rnd() % 16;
        u = k < 6 ? rnd() % 0x80 : k < 10 ? rnd() % 0x800 : k < 14 ? rnd() % 0x10000
            : k < 15 ? rnd() % 0x110000 : char32_t(rnd());
      }
      std::vector<char> o(4 * u32.size() + 4);
      for (size_t i = 0; i < u32.size() && i < 4; i++) {
        size_t w = simdutf::convert_utf32_to_utf8(&u32[i], 1, o.data());
        line("convert_utf32_to_utf8/1", c, w, 0, hash(o.data(), w));
      }
      size_t w = simdutf::convert_utf32_to_utf8(u32.data(), u32.size(), o.data());
      line("convert_utf32_to_utf8", c, w, 0, hash(o.data(), w));
    }

    // ASCII and Latin-1.
    std::string a = bytes(n, true);
    line("validate_ascii", c, simdutf::validate_ascii(a.data(), a.size()));
    r = simdutf::validate_ascii_with_errors(a.data(), a.size());
    line("validate_ascii_with_errors", c, r.error, r.count);
    std::string l1 = bytes(n, rnd() % 2);
    {
      size_t m = simdutf::utf8_length_from_latin1(l1.data(), l1.size());
      std::vector<char> o(m + 1);
      size_t w = simdutf::convert_latin1_to_utf8(l1.data(), l1.size(), o.data());
      line("convert_latin1_to_utf8", c, m, w, hash(o.data(), w));
      size_t cap = m ? rnd() % (m + 1) : 0;
      std::vector<char> os(cap + 1);
      w = simdutf::convert_latin1_to_utf8_safe(l1.data(), l1.size(), os.data(), cap);
      line("convert_latin1_to_utf8_safe", c, cap, w, hash(os.data(), w));
      std::vector<char16_t> o16(l1.size() + 1);
      w = simdutf::convert_latin1_to_utf16le(l1.data(), l1.size(), o16.data());
      line("convert_latin1_to_utf16le", c, w, 0, hash(o16.data(), 2 * w));
    }
    // Latin-1 as UTF-8 to Latin-1, which can fail with TOO_LARGE.
    {
      std::string u = utf8_text(n % 40);
      std::vector<char> o(u.size() + 1);
      auto e = simdutf::convert_utf8_to_latin1_with_errors(u.data(), u.size(), o.data());
      line("convert_utf8_to_latin1_with_errors/mixed", c, e.error, e.count,
           e.error ? 0 : hash(o.data(), e.count));
    }

    // UTF-16 side.
    std::u16string u16 = utf16_text(n);
    {
      size_t m = simdutf::utf8_length_from_utf16(u16.data(), u16.size());
      size_t m2 = simdutf::utf8_length_from_utf16le(u16.data(), u16.size());
      std::vector<char> o(3 * u16.size() + 1);
      size_t w = simdutf::convert_utf16_to_utf8(u16.data(), u16.size(), o.data());
      // The length of ill-formed text is unspecified (simdutf's own kernels
      // disagree about an unpaired surrogate), so it is printed for
      // well-formed text only.
      bool ok16 = simdutf::validate_utf16(u16.data(), u16.size());
      line("convert_utf16_to_utf8", c, ok16 ? m : 0, w, hash(o.data(), w));
      w = simdutf::convert_utf16le_to_utf8(u16.data(), u16.size(), o.data());
      line("convert_utf16le_to_utf8", c, ok16 ? m2 : 0, w, hash(o.data(), w));
      std::vector<char> o1(u16.size() + 1);
      std::u16string narrow = u16;
      if (rnd() % 2)
        for (auto &u : narrow) u &= 0xFF;
      w = simdutf::convert_utf16_to_latin1(narrow.data(), narrow.size(), o1.data());
      line("convert_utf16_to_latin1", c, w, 0, hash(o1.data(), w));

      // Well-formedness: texts with unpaired surrogates, more of them here.
      std::u16string t = u16;
      for (size_t i = 0, k = rnd() % 4; i < k && !t.empty(); i++)
        t[rnd() % t.size()] = char16_t(0xD800 + rnd() % 0x800);
      line("validate_utf16", c, simdutf::validate_utf16(t.data(), t.size()));
      auto e = simdutf::validate_utf16_with_errors(t.data(), t.size());
      line("validate_utf16_with_errors", c, e.error, e.count);
      e = simdutf::utf8_length_from_utf16_with_replacement(t.data(), t.size());
      line("utf8_length_from_utf16_with_replacement", c, e.error, e.count);
      std::u16string fixed(t.size(), 0);
      simdutf::to_well_formed_utf16(t.data(), t.size(), fixed.data());
      line("to_well_formed_utf16", c, 0, 0, hash(fixed.data(), 2 * fixed.size()));
      simdutf::to_well_formed_utf16(t.data(), t.size(), t.data());
      line("to_well_formed_utf16/in-place", c, t == fixed);
    }

    // Base64.
    for (int url = 0; url < 2; url++) {
      auto opt = url ? simdutf::base64_url : simdutf::base64_default;
      std::string bin = bytes(n % 200, false);
      size_t m = simdutf::base64_length_from_binary(bin.size(), opt);
      std::string enc(m, 0);
      size_t w = simdutf::binary_to_base64(bin.data(), bin.size(), enc.data(), opt);
      line("binary_to_base64", c, m, w, hash(enc.data(), w));
      w = simdutf::base64_length_from_binary(bin.size(), simdutf::base64_options(opt | 2));
      line("base64_length_from_binary/rev", c, w);

      std::string s = b64_text(n % 300, url);
      size_t ml = simdutf::maximal_binary_length_from_base64(s.data(), s.size());
      std::vector<char> o(ml + 1);
      auto d = simdutf::base64_to_binary(s.data(), s.size(), o.data(), opt);
      std::string full = d.error ? "-" : std::string(o.data(), d.count);
      line("base64_to_binary", c, d.error, d.error ? 0 : d.count,
           d.error ? 0 : hash(o.data(), d.count));
      if (!d.error) line("base64_to_binary/max", c, ml);

      std::u16string s16(s.begin(), s.end());
      if (rnd() % 8 == 0 && !s16.empty()) s16[rnd() % s16.size()] = char16_t(0x100 + rnd() % 0xFF00);
      size_t ml16 = simdutf::maximal_binary_length_from_base64(s16.data(), s16.size());
      std::vector<char> o16(ml16 + 1);
      d = simdutf::base64_to_binary(s16.data(), s16.size(), o16.data(), opt);
      std::string full16 = d.error ? "-" : std::string(o16.data(), d.count);
      line("base64_to_binary/16", c, d.error, d.error ? 0 : d.count,
           d.error ? 0 : hash(o16.data(), d.count));
      if (!d.error) line("base64_to_binary/16/max", c, ml16);

      // The safe forms, with a big enough and sometimes a too small buffer.
      size_t cap = rnd() % 2 ? ml : (ml ? rnd() % ml : 0);
      std::vector<char> os(cap + 1);
      size_t outlen = cap;
      d = simdutf::base64_to_binary_safe(s.data(), s.size(), os.data(), outlen, opt);
      safe("base64_to_binary_safe", c, d, cap >= ml, os.data(), outlen, full);
      outlen = cap;
      d = simdutf::base64_to_binary_safe(s16.data(), s16.size(), os.data(), outlen, opt);
      safe("base64_to_binary_safe/16", c, d, cap >= ml16, os.data(), outlen, full16);

      // Uint8Array.fromBase64 and setFromBase64 as V8 calls them: each
      // last-chunk mode, decoding up to a bad character, into a buffer of
      // the maximal length; then into a smaller one, as setFromBase64 does
      // for a short array. Everything is compared: the error, the number of
      // units read, and the bytes written.
      static const simdutf::last_chunk_handling_options modes[] = {
          simdutf::loose, simdutf::strict, simdutf::stop_before_partial};
      static const char *names[] = {"loose", "strict", "partial"};
      for (int k = 0; k < 3; k++) {
        std::string what = std::string("from_base64/") + names[k];
        std::vector<char> ob(ml + 1);
        size_t len = ml;
        d = simdutf::base64_to_binary_safe(s.data(), s.size(), ob.data(), len, opt, modes[k], true);
        from64(what, c, d, ob.data(), len);
        std::vector<char> ob16(ml16 + 1);
        len = ml16;
        d = simdutf::base64_to_binary_safe(s16.data(), s16.size(), ob16.data(), len, opt, modes[k], true);
        from64(what + "/16", c, d, ob16.data(), len);
        len = ml16;
        d = simdutf::atomic_base64_to_binary_safe(s16.data(), s16.size(), ob16.data(), len, opt, modes[k], true);
        from64(what + "/16/atomic", c, d, ob16.data(), len);
        auto plain = simdutf::base64_to_binary(s.data(), s.size(), ob.data(), opt, modes[k]);
        line((what + "/plain").c_str(), c, plain.error, plain.error ? 0 : plain.count,
             plain.error ? 0 : hash(ob.data(), plain.count));
        if (ml > 0) {
          size_t small = rnd() % ml;
          std::vector<char> osm(small + 1);
          len = small;
          d = simdutf::base64_to_binary_safe(s.data(), s.size(), osm.data(), len, opt, modes[k], true);
          from64(what + "/short", c, d, osm.data(), len);
        }
      }
      {
        std::string out(m, 0);
        size_t wa = simdutf::atomic_binary_to_base64(bin.data(), bin.size(), out.data(), opt);
        line("atomic_binary_to_base64", c, wa, 0, hash(out.data(), wa));
      }
    }
  }
  return 0;
}
