/*
 * simdjson.h: simdjson's On-Demand C++ API, over vjson.
 *
 * A header-only stand-in for https://github.com/simdjson/simdjson's
 * single-header simdjson.h, covering the simdjson::ondemand API that
 * Node.js uses: parser::iterate, document, value, object, array, field and
 * raw_json_string, with the error_code values and messages of simdjson
 * 3.x/4.x. Parsing runs in vjson (its verified parser); this file walks the
 * token tape vjson returns. Link with -lverilith_bind.
 *
 * One difference: simdjson validates lazily, so a document whose unread
 * parts are malformed can still be read up to the error. vjson checks the
 * whole text first, so iterate() fails on any malformed JSON.
 */
#ifndef SIMDJSON_H
#define SIMDJSON_H

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <ostream>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

#include "vbind.h"

#define SIMDJSON_VERSION "5.0.3"
#define simdjson_warn_unused [[nodiscard]]

namespace simdjson {

constexpr size_t SIMDJSON_PADDING = 64;

enum error_code {
  SUCCESS = 0,
  CAPACITY,
  MEMALLOC,
  TAPE_ERROR,
  DEPTH_ERROR,
  STRING_ERROR,
  T_ATOM_ERROR,
  F_ATOM_ERROR,
  N_ATOM_ERROR,
  NUMBER_ERROR,
  BIGINT_ERROR,
  UTF8_ERROR,
  UNINITIALIZED,
  EMPTY,
  UNESCAPED_CHARS,
  UNCLOSED_STRING,
  UNSUPPORTED_ARCHITECTURE,
  INCORRECT_TYPE,
  NUMBER_OUT_OF_RANGE,
  INDEX_OUT_OF_BOUNDS,
  NO_SUCH_FIELD,
  IO_ERROR,
  INVALID_JSON_POINTER,
  INVALID_URI_FRAGMENT,
  UNEXPECTED_ERROR,
  PARSER_IN_USE,
  OUT_OF_ORDER_ITERATION,
  INSUFFICIENT_PADDING,
  INCOMPLETE_ARRAY_OR_OBJECT,
  SCALAR_DOCUMENT_AS_VALUE,
  OUT_OF_BOUNDS,
  TRAILING_CONTENT,
  OUT_OF_CAPACITY,
  NUM_ERROR_CODES
};

inline const char* error_message(error_code error) noexcept {
  static const char* const messages[] = {
      "SUCCESS: No error",
      "CAPACITY: This parser can't support a document that big",
      "MEMALLOC: Error allocating memory, we're most likely out of memory",
      "TAPE_ERROR: The JSON document has an improper structure: missing or "
      "superfluous commas, braces, missing keys, etc.  This is a fatal and "
      "unrecoverable error.",
      "DEPTH_ERROR: The JSON document was too deep (too many nested objects "
      "and arrays)",
      "STRING_ERROR: Problem while parsing a string",
      "T_ATOM_ERROR: Problem while parsing an atom starting with the letter "
      "'t'",
      "F_ATOM_ERROR: Problem while parsing an atom starting with the letter "
      "'f'",
      "N_ATOM_ERROR: Problem while parsing an atom starting with the letter "
      "'n'",
      "NUMBER_ERROR: Problem while parsing a number",
      "BIGINT_ERROR: Big integer value that cannot be represented using 64 "
      "bits",
      "UTF8_ERROR: The input is not valid UTF-8",
      "UNINITIALIZED: Uninitialized",
      "EMPTY: no JSON found",
      "UNESCAPED_CHARS: Within strings, some characters must be escaped, we "
      "found unescaped characters",
      "UNCLOSED_STRING: A string is opened, but never closed.",
      "UNSUPPORTED_ARCHITECTURE: simdjson does not have an implementation "
      "supported by this CPU architecture. Please report this error to the "
      "core team as it should never happen.",
      "INCORRECT_TYPE: The JSON element does not have the requested type.",
      "NUMBER_OUT_OF_RANGE: The JSON number is too large or too small to fit "
      "within the requested type.",
      "INDEX_OUT_OF_BOUNDS: Attempted to access an element of a JSON array "
      "that is beyond its length.",
      "NO_SUCH_FIELD: The JSON field referenced does not exist in this "
      "object.",
      "IO_ERROR: Error reading the file.",
      "INVALID_JSON_POINTER: Invalid JSON pointer syntax.",
      "INVALID_URI_FRAGMENT: Invalid URI fragment syntax.",
      "UNEXPECTED_ERROR: Unexpected error, consider reporting this problem as "
      "you may have found a bug in simdjson",
      "PARSER_IN_USE: Cannot parse a new document while a document is still "
      "in use.",
      "OUT_OF_ORDER_ITERATION: Objects and arrays can only be iterated when "
      "they are first encountered.",
      "INSUFFICIENT_PADDING: simdjson requires the input JSON string to have "
      "at least SIMDJSON_PADDING extra bytes allocated, beyond the string's "
      "length. Consider using the simdjson::padded_string class if needed.",
      "INCOMPLETE_ARRAY_OR_OBJECT: JSON document ended early in the middle of "
      "an object or array. This is a fatal and unrecoverable error.",
      "SCALAR_DOCUMENT_AS_VALUE: A JSON document made of a scalar (number, "
      "Boolean, null or string) is treated as a value. Use get_bool(), "
      "get_double(), etc. on the document instead. ",
      "OUT_OF_BOUNDS: Attempt to access location outside of document.",
      "TRAILING_CONTENT: Unexpected trailing content in the JSON input.",
      "OUT_OF_CAPACITY: The capacity was exceeded, we cannot allocate enough "
      "memory.",
  };
  if (int(error) < 0 || error >= NUM_ERROR_CODES) {
    return messages[UNEXPECTED_ERROR];
  }
  return messages[error];
}

inline std::ostream& operator<<(std::ostream& out, error_code error) {
  return out << error_message(error);
}

/* A view of a JSON text. vjson needs no padding; the capacity is kept so
 * that code written for simdjson compiles unchanged. */
class padded_string_view : public std::string_view {
 public:
  padded_string_view() noexcept = default;
  padded_string_view(const char* s, size_t len, size_t capacity) noexcept
      : std::string_view(s, len), capacity_(capacity) {}
  padded_string_view(const uint8_t* s, size_t len, size_t capacity) noexcept
      : padded_string_view(reinterpret_cast<const char*>(s), len, capacity) {}
  padded_string_view(const std::string& s) noexcept  // NOLINT
      : std::string_view(s), capacity_(s.capacity()) {}
  padded_string_view(std::string_view s, size_t capacity) noexcept
      : std::string_view(s), capacity_(capacity) {}
  size_t capacity() const noexcept { return capacity_; }
  size_t padding() const noexcept { return capacity_ - size(); }

 private:
  size_t capacity_{0};
};

/* An owned JSON text. */
class padded_string {
 public:
  padded_string() noexcept = default;
  explicit padded_string(size_t length) : s_(length, '\0') {}
  padded_string(const char* data, size_t length) : s_(data, length) {}
  padded_string(const std::string& s) : s_(s) {}  // NOLINT
  padded_string(std::string_view s) : s_(s) {}    // NOLINT
  size_t size() const noexcept { return s_.size(); }
  size_t length() const noexcept { return s_.size(); }
  const char* data() const noexcept { return s_.data(); }
  char* data() noexcept { return s_.data(); }
  operator std::string_view() const { return s_; }  // NOLINT
  operator padded_string_view() const noexcept {    // NOLINT
    return padded_string_view(s_.data(), s_.size(), s_.size());
  }

 private:
  std::string s_;
};

/* simdjson pads by growing the string's capacity. */
inline padded_string_view pad(std::string& s) noexcept {
  s.reserve(s.size() + SIMDJSON_PADDING);
  return padded_string_view(s.data(), s.size(), s.capacity());
}

inline padded_string_view pad_with_reserve(std::string& s) noexcept {
  return pad(s);
}

namespace ondemand {

enum class json_type { unknown = 0, array, object, number, string, boolean, null };

class parser;
class document;
class value;
class object;
class array;
class field;
class raw_json_string;

}  // namespace ondemand

/*
 * A value or an error. Like simdjson's, a result forwards the calls of the
 * type it holds (get_object, operator[], key, iteration, ...), passing an
 * error through, so calls can be chained and checked once at the end. The
 * forwarding members are templates' members, so each exists only for the
 * types that have the call.
 */
/* X, made to depend on U so that it is only needed once a member is used. */
template <class U, class X>
struct dep {
  using type = X;
};

template <class T>
struct simdjson_result {
  T first{};
  error_code second{UNINITIALIZED};

  simdjson_result() noexcept = default;
  simdjson_result(T&& v) noexcept : first(std::move(v)), second(SUCCESS) {}  // NOLINT
  simdjson_result(const T& v) noexcept : first(v), second(SUCCESS) {}        // NOLINT
  simdjson_result(error_code e) noexcept : second(e) {}                      // NOLINT

  simdjson_warn_unused error_code get(T& out) noexcept {
    if (!second) out = first;
    return second;
  }
  /* A value converted to U (e.g. a string_view into a std::string), or
   * read from what the result holds (a value into a string_view). */
  template <class U>
  simdjson_warn_unused error_code get(U& out) noexcept {
    if (second) return second;
    if constexpr (std::is_assignable_v<U&, const T&>) {
      out = first;
      return SUCCESS;
    } else {
      return first.get(out);
    }
  }
  void tie(T& out, error_code& e) noexcept {
    e = second;
    if (!second) out = first;
  }
  error_code error() const noexcept { return second; }
  T& value_unsafe() noexcept { return first; }
  operator T&() noexcept { return first; }  // NOLINT

  /* For a field, value() is the member's value; otherwise it is what the
   * result holds. */
  decltype(auto) value() noexcept {
    if constexpr (std::is_same_v<T, ondemand::field>) {
      using R = simdjson_result<typename dep<T, ondemand::value>::type>;
      if (second) return R(second);
      return R(first.value());
    } else {
      return static_cast<T&>(first);
    }
  }

#define SIMDJSON_VBIND_FORWARD(X, name)       \
  template <class U = T>                      \
  simdjson_result<typename dep<U, X>::type> name() noexcept {                         \
    if (second) return second;                \
    return static_cast<U&>(first).name();     \
  }
  SIMDJSON_VBIND_FORWARD(ondemand::object, get_object)
  SIMDJSON_VBIND_FORWARD(ondemand::array, get_array)
  SIMDJSON_VBIND_FORWARD(std::string_view, get_string)
  SIMDJSON_VBIND_FORWARD(ondemand::raw_json_string, get_raw_json_string)
  SIMDJSON_VBIND_FORWARD(bool, get_bool)
  SIMDJSON_VBIND_FORWARD(int64_t, get_int64)
  SIMDJSON_VBIND_FORWARD(uint64_t, get_uint64)
  SIMDJSON_VBIND_FORWARD(double, get_double)
  SIMDJSON_VBIND_FORWARD(bool, is_null)
  SIMDJSON_VBIND_FORWARD(bool, is_empty)
  SIMDJSON_VBIND_FORWARD(ondemand::json_type, type)
  SIMDJSON_VBIND_FORWARD(std::string_view, raw_json)
  SIMDJSON_VBIND_FORWARD(size_t, count_elements)
  SIMDJSON_VBIND_FORWARD(size_t, count_fields)
  SIMDJSON_VBIND_FORWARD(ondemand::raw_json_string, key)
  SIMDJSON_VBIND_FORWARD(std::string_view, unescaped_key)
#undef SIMDJSON_VBIND_FORWARD

  template <class string_type>
  simdjson_warn_unused error_code get_string(string_type& receiver,
                                             bool allow_replacement = false) noexcept {
    if (second) return second;
    return first.get_string(receiver, allow_replacement);
  }
  template <class U = T>
  simdjson_result<typename dep<U, ondemand::value>::type> operator[](std::string_view key) noexcept {
    if (second) return second;
    return static_cast<U&>(first)[key];
  }
  template <class U = T>
  simdjson_result<typename dep<U, ondemand::value>::type> find_field(std::string_view key) noexcept {
    if (second) return second;
    return static_cast<U&>(first).find_field(key);
  }
  template <class U = T>
  simdjson_result<typename dep<U, ondemand::value>::type> find_field_unordered(std::string_view key) noexcept {
    if (second) return second;
    return static_cast<U&>(first).find_field_unordered(key);
  }
  template <class U = T>
  simdjson_result<typename dep<U, ondemand::value>::type> at(size_t index) noexcept {
    if (second) return second;
    return static_cast<U&>(first).at(index);
  }

  /* Containers: a range-for over an errored object or array is empty. */
  template <class U = T>
  auto begin() noexcept -> decltype(std::declval<U&>().begin()) {
    if (second) return second;
    return first.begin();
  }
  template <class U = T>
  auto end() noexcept -> decltype(std::declval<U&>().end()) {
    if (second) return second;
    return first.end();
  }
  /* Iterators. */
  template <class U = T>
  auto operator*() noexcept -> decltype(*std::declval<U&>()) {
    return *first;
  }
  simdjson_result& operator++() noexcept {
    ++first;
    return *this;
  }
  bool operator!=(const simdjson_result& o) const noexcept {
    if (second || o.second) return false;
    return first != o.first;
  }
  bool operator==(const simdjson_result& o) const noexcept {
    return !(*this != o);
  }
};

namespace ondemand {

namespace detail {

/* Where a value sits: the document's tape and the token's index. */
struct cursor {
  vbind_json_doc* doc{nullptr};
  const vbind_json_tok* toks{nullptr};
  const char* src{nullptr};
  uint32_t i{0};

  const vbind_json_tok& tok() const { return toks[i]; }
  uint8_t kind() const { return tok().kind; }
  /* Index of the token after this value. */
  uint32_t next() const {
    uint8_t k = kind();
    if (k == VBIND_JSON_ARRAY_START || k == VBIND_JSON_OBJECT_START) {
      return tok().a + 1;
    }
    return i + 1;
  }
  cursor at(uint32_t j) const {
    cursor c = *this;
    c.i = j;
    return c;
  }
  std::string_view string() const {
    const uint8_t* p = nullptr;
    size_t n = 0;
    vbind_json_doc_string(doc, i, &p, &n);
    return std::string_view(reinterpret_cast<const char*>(p), n);
  }
  std::string_view raw_body() const {
    return std::string_view(src + tok().a, tok().b - tok().a);
  }
  std::string_view raw() const {
    const uint8_t* p = nullptr;
    size_t n = 0;
    vbind_json_doc_raw(doc, i, &p, &n);
    return std::string_view(reinterpret_cast<const char*>(p), n);
  }
};

inline error_code get_error(int r) {
  switch (r) {
    case VBIND_JSON_GET_OK: return SUCCESS;
    case VBIND_JSON_GET_OUT_OF_RANGE: return NUMBER_OUT_OF_RANGE;
    default: return INCORRECT_TYPE;
  }
}

}  // namespace detail

/* An object member's name, as written in the JSON text (escapes and all). */
class raw_json_string {
 public:
  raw_json_string() noexcept = default;
  explicit raw_json_string(std::string_view raw) noexcept : raw_(raw) {}
  const char* raw() const noexcept { return raw_.data(); }
  bool unsafe_is_equal(std::string_view s) const noexcept { return raw_ == s; }
  bool is_equal(std::string_view s) const noexcept { return raw_ == s; }
  friend bool operator==(const raw_json_string& a, std::string_view b) {
    return a.raw_ == b;
  }
  friend bool operator==(std::string_view a, const raw_json_string& b) {
    return b.raw_ == a;
  }
  friend bool operator!=(const raw_json_string& a, std::string_view b) {
    return !(a == b);
  }
  friend bool operator!=(std::string_view a, const raw_json_string& b) {
    return !(b == a);
  }

 private:
  std::string_view raw_;
};

class value {
 public:
  value() noexcept = default;
  explicit value(detail::cursor c) noexcept : c_(c) {}

  inline simdjson_result<object> get_object() noexcept;
  inline simdjson_result<array> get_array() noexcept;
  inline simdjson_result<std::string_view> get_string(
      bool allow_replacement = false) noexcept;
  template <class string_type>
  simdjson_warn_unused error_code get_string(string_type& receiver,
                                             bool allow_replacement = false) noexcept;
  inline simdjson_result<raw_json_string> get_raw_json_string() noexcept;
  inline simdjson_result<bool> get_bool() noexcept;
  inline simdjson_result<int64_t> get_int64() noexcept;
  inline simdjson_result<uint64_t> get_uint64() noexcept;
  inline simdjson_result<double> get_double() noexcept;
  inline simdjson_result<bool> is_null() noexcept;
  inline simdjson_result<json_type> type() noexcept;
  inline simdjson_result<std::string_view> raw_json() noexcept;
  inline std::string_view raw_json_token() noexcept;
  inline simdjson_result<value> find_field(std::string_view key) noexcept;
  inline simdjson_result<value> find_field_unordered(std::string_view key) noexcept;
  inline simdjson_result<value> operator[](std::string_view key) noexcept;
  inline simdjson_result<value> at(size_t index) noexcept;
  inline simdjson_result<size_t> count_elements() noexcept;
  inline simdjson_result<size_t> count_fields() noexcept;
  inline simdjson_result<bool> is_scalar() noexcept;
  inline simdjson_result<bool> is_string() noexcept;

  template <class T>
  simdjson_warn_unused error_code get(T& out) noexcept;

  const detail::cursor& cursor() const noexcept { return c_; }

 protected:
  detail::cursor c_{};
};

class array {
 public:
  class iterator {
   public:
    iterator() noexcept = default;
    explicit iterator(detail::cursor c) noexcept : c_(c) {}
    inline simdjson_result<value> operator*() noexcept;
    iterator& operator++() noexcept {
      c_.i = c_.next();
      return *this;
    }
    bool operator==(const iterator& o) const noexcept { return c_.i == o.c_.i; }
    bool operator!=(const iterator& o) const noexcept { return c_.i != o.c_.i; }

   private:
    detail::cursor c_{};
  };

  array() noexcept = default;
  explicit array(detail::cursor c) noexcept : c_(c) {}
  simdjson_result<iterator> begin() noexcept { return iterator(c_.at(c_.i + 1)); }
  simdjson_result<iterator> end() noexcept { return iterator(c_.at(c_.tok().a)); }
  simdjson_result<size_t> count_elements() noexcept {
    size_t n = 0;
    for (uint32_t j = c_.i + 1; j != c_.tok().a; j = c_.at(j).next()) n++;
    return n;
  }
  simdjson_result<bool> is_empty() noexcept { return c_.i + 1 == c_.tok().a; }
  simdjson_result<std::string_view> raw_json() noexcept { return c_.raw(); }
  inline simdjson_result<value> at(size_t index) noexcept;
  simdjson_result<bool> reset() noexcept { return false; }

 private:
  detail::cursor c_{};
};

class field {
 public:
  field() noexcept = default;
  explicit field(detail::cursor key) noexcept : key_(key), value_(key.at(key.i + 1)) {}
  simdjson_result<raw_json_string> key() noexcept {
    return raw_json_string(key_.raw_body());
  }
  simdjson_result<std::string_view> unescaped_key(
      bool allow_replacement = false) noexcept {
    (void)allow_replacement;
    return key_.string();
  }
  std::string_view key_raw_json_token() noexcept { return key_.raw(); }
  ondemand::value& value() noexcept { return value_; }

 private:
  detail::cursor key_{};
  ondemand::value value_{};
};

class object {
 public:
  class iterator {
   public:
    iterator() noexcept = default;
    explicit iterator(detail::cursor c) noexcept : c_(c) {}
    simdjson_result<field> operator*() noexcept { return field(c_); }
    iterator& operator++() noexcept {
      c_.i = c_.at(c_.i + 1).next();
      return *this;
    }
    bool operator==(const iterator& o) const noexcept { return c_.i == o.c_.i; }
    bool operator!=(const iterator& o) const noexcept { return c_.i != o.c_.i; }

   private:
    detail::cursor c_{};
  };

  object() noexcept = default;
  explicit object(detail::cursor c) noexcept : c_(c) {}
  simdjson_result<iterator> begin() noexcept { return iterator(c_.at(c_.i + 1)); }
  simdjson_result<iterator> end() noexcept { return iterator(c_.at(c_.tok().a)); }

  /* The first member whose unescaped name is key. */
  simdjson_result<value> find_field_unordered(std::string_view key) noexcept {
    for (uint32_t j = c_.i + 1; j != c_.tok().a; j = c_.at(j + 1).next()) {
      detail::cursor k = c_.at(j);
      bool eq = k.tok().escaped ? k.string() == key : k.raw_body() == key;
      if (eq) return value(c_.at(j + 1));
    }
    return NO_SUCH_FIELD;
  }
  simdjson_result<value> find_field(std::string_view key) noexcept {
    return find_field_unordered(key);
  }
  simdjson_result<value> operator[](std::string_view key) noexcept {
    return find_field_unordered(key);
  }
  simdjson_result<size_t> count_fields() noexcept {
    size_t n = 0;
    for (uint32_t j = c_.i + 1; j != c_.tok().a; j = c_.at(j + 1).next()) n++;
    return n;
  }
  simdjson_result<bool> is_empty() noexcept { return c_.i + 1 == c_.tok().a; }
  simdjson_result<std::string_view> raw_json() noexcept { return c_.raw(); }
  /* Objects can be read any number of times, so there is nothing to reset. */
  simdjson_result<bool> reset() noexcept { return false; }

 private:
  detail::cursor c_{};
};

/* A parsed document: the root value. */
class document : public value {
 public:
  document() noexcept = default;
  explicit document(detail::cursor c) noexcept : value(c) {}
  simdjson_result<value> get_value() noexcept { return value(c_); }
  void rewind() noexcept {}
  simdjson_result<bool> at_end() noexcept { return true; }
};

/* Parses with vjson. A parser owns one document at a time: iterating again
 * invalidates the previous document, as with simdjson. */
class parser {
 public:
  parser() noexcept : doc_(vbind_json_doc_new()) {}
  explicit parser(size_t max_capacity) noexcept : parser() { (void)max_capacity; }
  parser(const parser&) = delete;
  parser& operator=(const parser&) = delete;
  parser(parser&& o) noexcept : doc_(o.doc_) { o.doc_ = nullptr; }
  parser& operator=(parser&& o) noexcept {
    std::swap(doc_, o.doc_);
    return *this;
  }
  ~parser() {
    if (doc_) vbind_json_doc_free(doc_);
  }

  simdjson_result<document> iterate(const char* json, size_t len,
                                    size_t capacity = 0) & noexcept {
    (void)capacity;
    size_t err_offset = 0;
    int r = vbind_json_doc_parse(doc_, reinterpret_cast<const uint8_t*>(json),
                                 len, &err_offset);
    if (r != VBIND_JSON_OK) {
      char c = err_offset < len ? json[err_offset] : '\0';
      return parse_error(r, c);
    }
    size_t n = 0;
    detail::cursor c;
    c.doc = doc_;
    c.toks = vbind_json_doc_tokens(doc_, &n);
    c.src = json;
    c.i = 0;
    return document(c);
  }
  simdjson_result<document> iterate(const uint8_t* json, size_t len,
                                    size_t capacity = 0) & noexcept {
    return iterate(reinterpret_cast<const char*>(json), len, capacity);
  }
  simdjson_result<document> iterate(padded_string_view json) & noexcept {
    return iterate(json.data(), json.size(), json.capacity());
  }
  simdjson_result<document> iterate(const padded_string& json) & noexcept {
    return iterate(json.data(), json.size(), json.size());
  }
  simdjson_result<document> iterate(const std::string& json) & noexcept {
    return iterate(json.data(), json.size(), json.capacity());
  }
  simdjson_result<document> iterate(std::string_view json,
                                    size_t capacity) & noexcept {
    return iterate(json.data(), json.size(), capacity);
  }

 private:
  static error_code parse_error(int r, char at) {
    switch (r) {
      case VBIND_JSON_E_UNEXPECTED_END: return INCOMPLETE_ARRAY_OR_OBJECT;
      case VBIND_JSON_E_UNTERMINATED_STRING: return UNCLOSED_STRING;
      case VBIND_JSON_E_CONTROL_CHARACTER: return UNESCAPED_CHARS;
      case VBIND_JSON_E_INVALID_ESCAPE: return STRING_ERROR;
      case VBIND_JSON_E_INVALID_NUMBER: return NUMBER_ERROR;
      case VBIND_JSON_E_INVALID_LITERAL:
        return at == 'f' ? F_ATOM_ERROR : at == 'n' ? N_ATOM_ERROR : T_ATOM_ERROR;
      case VBIND_JSON_E_TOO_DEEP: return DEPTH_ERROR;
      case VBIND_JSON_E_TRAILING_DATA: return TRAILING_CONTENT;
      case VBIND_JSON_E_INVALID_UTF8: return UTF8_ERROR;
      case VBIND_JSON_E_TOO_LARGE: return CAPACITY;
      case VBIND_JSON_E_EMPTY: return EMPTY;
      default: return TAPE_ERROR;
    }
  }

  vbind_json_doc* doc_{nullptr};
};

/* ---- value ----------------------------------------------------------- */

inline simdjson_result<object> value::get_object() noexcept {
  if (c_.kind() != VBIND_JSON_OBJECT_START) return INCORRECT_TYPE;
  return object(c_);
}
inline simdjson_result<array> value::get_array() noexcept {
  if (c_.kind() != VBIND_JSON_ARRAY_START) return INCORRECT_TYPE;
  return array(c_);
}
inline simdjson_result<std::string_view> value::get_string(bool) noexcept {
  if (c_.kind() != VBIND_JSON_STRING) return INCORRECT_TYPE;
  return c_.string();
}
template <class string_type>
error_code value::get_string(string_type& receiver, bool allow_replacement) noexcept {
  std::string_view v;
  error_code e = get_string(allow_replacement).get(v);
  if (!e) receiver = string_type(v);
  return e;
}
inline simdjson_result<raw_json_string> value::get_raw_json_string() noexcept {
  if (c_.kind() != VBIND_JSON_STRING) return INCORRECT_TYPE;
  return raw_json_string(c_.raw_body());
}
inline simdjson_result<bool> value::get_bool() noexcept {
  if (c_.kind() == VBIND_JSON_TRUE) return true;
  if (c_.kind() == VBIND_JSON_FALSE) return false;
  return INCORRECT_TYPE;
}
inline simdjson_result<int64_t> value::get_int64() noexcept {
  int64_t v = 0;
  error_code e = detail::get_error(vbind_json_doc_i64(c_.doc, c_.i, &v));
  return e ? simdjson_result<int64_t>(e) : simdjson_result<int64_t>(v);
}
inline simdjson_result<uint64_t> value::get_uint64() noexcept {
  uint64_t v = 0;
  error_code e = detail::get_error(vbind_json_doc_u64(c_.doc, c_.i, &v));
  return e ? simdjson_result<uint64_t>(e) : simdjson_result<uint64_t>(v);
}
inline simdjson_result<double> value::get_double() noexcept {
  double v = 0;
  error_code e = detail::get_error(vbind_json_doc_f64(c_.doc, c_.i, &v));
  return e ? simdjson_result<double>(e) : simdjson_result<double>(v);
}
inline simdjson_result<bool> value::is_null() noexcept {
  return c_.kind() == VBIND_JSON_NULL;
}
inline simdjson_result<json_type> value::type() noexcept {
  switch (c_.kind()) {
    case VBIND_JSON_ARRAY_START: return json_type::array;
    case VBIND_JSON_OBJECT_START: return json_type::object;
    case VBIND_JSON_NUMBER: return json_type::number;
    case VBIND_JSON_STRING: return json_type::string;
    case VBIND_JSON_TRUE:
    case VBIND_JSON_FALSE: return json_type::boolean;
    case VBIND_JSON_NULL: return json_type::null;
    default: return TAPE_ERROR;
  }
}
inline simdjson_result<std::string_view> value::raw_json() noexcept {
  return c_.raw();
}
inline std::string_view value::raw_json_token() noexcept { return c_.raw(); }
inline simdjson_result<value> value::find_field_unordered(std::string_view key) noexcept {
  object o;
  error_code e = get_object().get(o);
  if (e) return e;
  return o.find_field_unordered(key);
}
inline simdjson_result<value> value::find_field(std::string_view key) noexcept {
  return find_field_unordered(key);
}
inline simdjson_result<value> value::operator[](std::string_view key) noexcept {
  return find_field_unordered(key);
}
inline simdjson_result<value> array::at(size_t index) noexcept {
  for (uint32_t j = c_.i + 1; j != c_.tok().a; j = c_.at(j).next()) {
    if (index-- == 0) return value(c_.at(j));
  }
  return INDEX_OUT_OF_BOUNDS;
}
inline simdjson_result<value> value::at(size_t index) noexcept {
  array a;
  error_code e = get_array().get(a);
  if (e) return e;
  return a.at(index);
}
inline simdjson_result<size_t> value::count_elements() noexcept {
  array a;
  error_code e = get_array().get(a);
  if (e) return e;
  return a.count_elements();
}
inline simdjson_result<size_t> value::count_fields() noexcept {
  object o;
  error_code e = get_object().get(o);
  if (e) return e;
  return o.count_fields();
}
inline simdjson_result<bool> value::is_scalar() noexcept {
  uint8_t k = c_.kind();
  return k != VBIND_JSON_ARRAY_START && k != VBIND_JSON_OBJECT_START;
}
inline simdjson_result<bool> value::is_string() noexcept {
  return c_.kind() == VBIND_JSON_STRING;
}

namespace detail {
template <class T>
struct getter;
template <>
struct getter<value> {
  static error_code get(value& v, value& out) { out = v; return SUCCESS; }
};
template <>
struct getter<object> {
  static error_code get(value& v, object& out) { return v.get_object().get(out); }
};
template <>
struct getter<array> {
  static error_code get(value& v, array& out) { return v.get_array().get(out); }
};
template <>
struct getter<std::string_view> {
  static error_code get(value& v, std::string_view& out) {
    return v.get_string().get(out);
  }
};
template <>
struct getter<raw_json_string> {
  static error_code get(value& v, raw_json_string& out) {
    return v.get_raw_json_string().get(out);
  }
};
template <>
struct getter<bool> {
  static error_code get(value& v, bool& out) { return v.get_bool().get(out); }
};
template <>
struct getter<int64_t> {
  static error_code get(value& v, int64_t& out) { return v.get_int64().get(out); }
};
template <>
struct getter<uint64_t> {
  static error_code get(value& v, uint64_t& out) { return v.get_uint64().get(out); }
};
template <>
struct getter<double> {
  static error_code get(value& v, double& out) { return v.get_double().get(out); }
};
}  // namespace detail

template <class T>
error_code value::get(T& out) noexcept {
  return detail::getter<T>::get(*this, out);
}

inline simdjson_result<value> array::iterator::operator*() noexcept {
  return value(c_);
}

}  // namespace ondemand

}  // namespace simdjson

#endif  // SIMDJSON_H
