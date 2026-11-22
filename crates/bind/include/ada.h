/*
 * ada.h: ada's C++ API (4.0), over vurl.
 *
 * A header-only stand-in for https://github.com/ada-url/ada's single-header
 * ada.h, covering what Node.js uses: ada::parse into ada::url_aggregator or
 * ada::url, the getters and setters, url_components, can_parse,
 * href_from_file, ada::idna, ada::unicode::percent_decode and URLPattern
 * (ada::url_pattern, ada::parse_url_pattern). Parsing and the setters run in
 * vurl (its verified parser); this file only adapts the types. URLPattern is
 * ada's own pattern code, in ada_url_pattern.h, with this file's ada::parse
 * under it. Needs C++20, as ada does. Link with -lverilith_bind.
 */
#ifndef ADA_H
#define ADA_H

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "vbind.h"

#define ADA_VERSION "4.0.0"
#define ADA_INCLUDE_URL_PATTERN 1
#define ada_lifetime_bound
#define ada_warn_unused
#define ada_log(...)
#define ADA_ASSERT_TRUE(COND)

/* tl::expected is defined in ada_url_pattern.h. */
namespace tl {
template <class E>
class unexpected;
}  // namespace tl

namespace ada {

enum { ADA_VERSION_MAJOR = 4, ADA_VERSION_MINOR = 0, ADA_VERSION_REVISION = 0 };

enum class errors : uint8_t { type_error };

/* ada::result is tl::expected<T, ada::errors>; this is the part of it that
 * callers use. */
template <class T>
class result {
 public:
  template <class U = T>
    requires(std::constructible_from<T, U &&> &&
             !std::same_as<std::remove_cvref_t<U>, result> &&
             !std::same_as<std::remove_cvref_t<U>, errors>)
  result(U&& v) : v_(std::in_place, std::forward<U>(v)) {}  // NOLINT
  result(errors e) : e_(e) {}  // NOLINT
  template <class E>
  result(const tl::unexpected<E>& e) : e_(e.value()) {}  // NOLINT
  result() : e_(errors::type_error) {}

  bool has_value() const noexcept { return v_.has_value(); }
  explicit operator bool() const noexcept { return has_value(); }
  T& value() & { return *v_; }
  const T& value() const& { return *v_; }
  T&& value() && { return std::move(*v_); }
  T& operator*() & { return *v_; }
  const T& operator*() const& { return *v_; }
  T* operator->() { return &*v_; }
  const T* operator->() const { return &*v_; }
  errors error() const noexcept { return e_; }
  template <class U>
  T value_or(U&& d) const& { return v_ ? *v_ : static_cast<T>(std::forward<U>(d)); }

 private:
  std::optional<T> v_;
  errors e_{};
};

namespace scheme {
enum type : uint8_t {
  HTTP = 0,
  NOT_SPECIAL = 1,
  HTTPS = 2,
  WS = 3,
  FTP = 4,
  WSS = 5,
  FILE = 6
};
inline bool is_special(type t) { return t != NOT_SPECIAL; }
inline uint16_t get_special_port(type t) {
  switch (t) {
    case HTTP: case WS: return 80;
    case HTTPS: case WSS: return 443;
    case FTP: return 21;
    default: return 0;
  }
}
}  // namespace scheme

enum class url_host_type : uint8_t { DEFAULT = 0, IPV4 = 1, IPV6 = 2 };

struct url_components {
  constexpr static uint32_t omitted = uint32_t(-1);
  uint32_t protocol_end{0};
  uint32_t username_end{0};
  uint32_t host_start{0};
  uint32_t host_end{0};
  uint32_t port{omitted};
  uint32_t pathname_start{0};
  uint32_t search_start{omitted};
  uint32_t hash_start{omitted};

  /* The same text as ada's. */
  std::string to_string() const {
    auto f = [](const char* name, uint32_t v) {
      return std::string("\t\"") + name + "\":\"" + std::to_string(v) + "\",\n";
    };
    return "{\n" + f("protocol_end", protocol_end) +
           f("username_end", username_end) + f("host_start", host_start) +
           f("host_end", host_end) + f("port", port) +
           f("pathname_start", pathname_start) +
           f("search_start", search_start) + f("hash_start", hash_start) +
           "\n}";
  }
};
static_assert(sizeof(url_components) == sizeof(vurl_url_components),
              "url_components must match vurl's layout");

namespace detail {
inline std::string_view sv(vurl_string s) {
  return s.data ? std::string_view(s.data, s.length) : std::string_view();
}
inline std::string take(vurl_owned_string s) {
  std::string r = s.data ? std::string(s.data, s.length) : std::string();
  vurl_free_owned_string(s);
  return r;
}
}  // namespace detail

struct url_base {
  virtual ~url_base() = default;
  bool is_valid{true};
  bool has_opaque_path{false};
  url_host_type host_type = url_host_type::DEFAULT;
  ada::scheme::type type{ada::scheme::type::NOT_SPECIAL};

  bool is_special() const noexcept { return type != scheme::NOT_SPECIAL; }
  uint16_t get_special_port() const noexcept {
    return scheme::get_special_port(type);
  }
  uint16_t scheme_default_port() const noexcept { return get_special_port(); }
};

/* A URL kept as one href with component offsets, as in ada. It owns a vurl
 * handle; every getter is a view into vurl's href. */
struct url_aggregator : url_base {
  url_aggregator() = default;
  url_aggregator(const url_aggregator& u) : url_base(u) {
    h_ = u.h_ ? vurl_copy(u.h_) : nullptr;
  }
  url_aggregator(url_aggregator&& u) noexcept : url_base(u), h_(u.h_) {
    u.h_ = nullptr;
  }
  url_aggregator& operator=(const url_aggregator& u) {
    if (this != &u) {
      url_aggregator t(u);
      *this = std::move(t);
    }
    return *this;
  }
  url_aggregator& operator=(url_aggregator&& u) noexcept {
    if (this != &u) {
      if (h_) vurl_free(h_);
      url_base::operator=(u);
      h_ = u.h_;
      u.h_ = nullptr;
    }
    return *this;
  }
  ~url_aggregator() override {
    if (h_) vurl_free(h_);
  }

  bool set_href(std::string_view input) {
    return update(vurl_set_href(h_, input.data(), input.size()));
  }
  bool set_host(std::string_view input) {
    return update(vurl_set_host(h_, input.data(), input.size()));
  }
  bool set_hostname(std::string_view input) {
    return update(vurl_set_hostname(h_, input.data(), input.size()));
  }
  bool set_protocol(std::string_view input) {
    return update(vurl_set_protocol(h_, input.data(), input.size()));
  }
  bool set_username(std::string_view input) {
    return update(vurl_set_username(h_, input.data(), input.size()));
  }
  bool set_password(std::string_view input) {
    return update(vurl_set_password(h_, input.data(), input.size()));
  }
  bool set_port(std::string_view input) {
    return update(vurl_set_port(h_, input.data(), input.size()));
  }
  bool set_pathname(std::string_view input) {
    return update(vurl_set_pathname(h_, input.data(), input.size()));
  }
  void set_search(std::string_view input) {
    vurl_set_search(h_, input.data(), input.size());
    update(true);
  }
  void set_hash(std::string_view input) {
    vurl_set_hash(h_, input.data(), input.size());
    update(true);
  }
  void clear_port() { vurl_clear_port(h_); update(true); }
  void clear_hash() { vurl_clear_hash(h_); update(true); }
  void clear_search() { vurl_clear_search(h_); update(true); }

  std::string get_origin() const noexcept {
    return detail::take(vurl_get_origin(h_));
  }
  std::string_view get_href() const noexcept {
    return detail::sv(vurl_get_href(h_));
  }
  std::string_view get_username() const noexcept {
    return detail::sv(vurl_get_username(h_));
  }
  std::string_view get_password() const noexcept {
    return detail::sv(vurl_get_password(h_));
  }
  std::string_view get_port() const noexcept {
    return detail::sv(vurl_get_port(h_));
  }
  std::string_view get_hash() const noexcept {
    return detail::sv(vurl_get_hash(h_));
  }
  std::string_view get_host() const noexcept {
    return detail::sv(vurl_get_host(h_));
  }
  std::string_view get_hostname() const noexcept {
    return detail::sv(vurl_get_hostname(h_));
  }
  std::string_view get_pathname() const noexcept {
    return detail::sv(vurl_get_pathname(h_));
  }
  uint32_t get_pathname_length() const noexcept {
    return uint32_t(get_pathname().size());
  }
  std::string_view get_search() const noexcept {
    return detail::sv(vurl_get_search(h_));
  }
  std::string_view get_protocol() const noexcept {
    return detail::sv(vurl_get_protocol(h_));
  }
  const url_components& get_components() const noexcept {
    static const url_components empty{};
    const vurl_url_components* c = vurl_get_components(h_);
    return c ? *reinterpret_cast<const url_components*>(c) : empty;
  }
  std::string to_string() const { return std::string(get_href()); }

  bool has_credentials() const noexcept { return vurl_has_credentials(h_); }
  bool has_empty_hostname() const noexcept {
    return vurl_has_empty_hostname(h_);
  }
  bool has_hostname() const noexcept { return vurl_has_hostname(h_); }
  bool has_non_empty_username() const noexcept {
    return vurl_has_non_empty_username(h_);
  }
  bool has_non_empty_password() const noexcept {
    return vurl_has_non_empty_password(h_);
  }
  bool has_port() const noexcept { return vurl_has_port(h_); }
  bool has_password() const noexcept { return vurl_has_password(h_); }
  bool has_hash() const noexcept { return vurl_has_hash(h_); }
  bool has_search() const noexcept { return vurl_has_search(h_); }
  bool has_valid_domain() const noexcept { return is_valid; }

  /* set_hostname on a copy, leaving this one as it is: the result, and
   * the edited URL in out when it differs from this one (out is left
   * without a handle otherwise). */
  bool with_hostname(std::string_view input, url_aggregator& out) const {
    bool ok = false;
    vurl_url h = vurl_with_hostname(h_, input.data(), input.size(), &ok);
    if (h) out = from_handle(h);
    return ok;
  }

  /* Whether this holds a vurl handle (a default-made one does not). */
  bool has_handle() const noexcept { return h_ != nullptr; }
  vurl_url handle() const noexcept { return h_; }

  /* Takes ownership of a vurl handle. */
  static url_aggregator from_handle(vurl_url h) {
    url_aggregator u;
    u.h_ = h;
    u.update(true);
    return u;
  }

 private:
  bool update(bool r) {
    is_valid = h_ && vurl_is_valid(h_);
    if (is_valid) {
      type = scheme::type(vurl_get_scheme_type(h_));
      host_type = url_host_type(vurl_get_host_type(h_));
      std::string_view p = get_pathname();
      has_opaque_path = !has_hostname() && (p.empty() || p[0] != '/');
    }
    return r;
  }

  vurl_url h_ = nullptr;
};

/* A URL kept as separate component strings, as in ada. Callers may edit the
 * fields directly; get_href serializes them as the URL Standard does. */
struct url : url_base {
  std::string username{};
  std::string password{};
  std::optional<std::string> host{};
  std::optional<uint16_t> port{};
  std::string path{};
  std::optional<std::string> query{};
  std::optional<std::string> hash{};

  bool has_empty_hostname() const noexcept { return host && host->empty(); }
  bool has_port() const noexcept { return port.has_value(); }
  bool has_hostname() const noexcept { return host.has_value(); }
  bool has_credentials() const noexcept {
    return !username.empty() || !password.empty();
  }
  bool has_hash() const noexcept { return hash.has_value(); }
  bool has_search() const noexcept { return query.has_value(); }
  bool has_valid_domain() const noexcept { return is_valid; }

  std::string get_protocol() const noexcept { return scheme_ + ":"; }
  std::string get_host() const noexcept {
    if (!host) return "";
    return port ? *host + ":" + std::to_string(*port) : *host;
  }
  std::string get_hostname() const noexcept { return host.value_or(""); }
  std::string_view get_pathname() const noexcept { return path; }
  size_t get_pathname_length() const noexcept { return path.size(); }
  std::string get_search() const noexcept {
    return query && !query->empty() ? "?" + *query : "";
  }
  std::string get_hash() const noexcept {
    return hash && !hash->empty() ? "#" + *hash : "";
  }
  const std::string& get_username() const noexcept { return username; }
  const std::string& get_password() const noexcept { return password; }
  std::string get_port() const noexcept {
    return port ? std::to_string(*port) : "";
  }

  std::string get_href() const noexcept {
    std::string out = get_protocol();
    if (host) {
      out += "//";
      if (has_credentials()) {
        out += username;
        if (!password.empty()) out += ":" + password;
        out += "@";
      }
      out += *host;
      if (port) out += ":" + std::to_string(*port);
    } else if (!has_opaque_path && path.size() > 1 && path[0] == '/' &&
               path[1] == '/') {
      out += "/.";
    }
    out += path;
    if (query) out += "?" + *query;
    if (hash) out += "#" + *hash;
    return out;
  }
  std::string to_string() const { return get_href(); }
  std::string get_origin() const noexcept {
    if (same_as(base())) return base().get_origin();
    return with([](url_aggregator&) { return true; }).get_origin();
  }
  url_components get_components() const noexcept {
    if (same_as(base())) return base().get_components();
    return with([](url_aggregator&) { return true; }).get_components();
  }

  bool set_href(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_href(v); });
  }
  bool set_host(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_host(v); });
  }
  bool set_hostname(std::string_view v) {
    /* The hostname setter changes only the host, so on the fast path only
     * the host fields are reloaded. */
    if (same_as(base())) {
      /* Most often only the new host is needed, and vurl gives it without
       * making the new URL. The fields then no longer match base(), so a
       * later edit or get_components reparses get_href(). */
      vurl_string nh{};
      uint8_t ht = 0;
      int k = vurl_hostname_after_set(base().handle(), v.data(), v.size(),
                                      &nh, &ht);
      if (k == 0) return false;
      if (k == 1) {
        host_type = url_host_type(ht);
        std::string_view h = detail::sv(nh);
        if (host) {
          host->assign(h);
        } else {
          host.emplace(h);
        }
        return true;
      }
      if (!src_.has_handle()) {
        /* The URL is shared (see share_src): edit a copy, which costs no
         * copying when the setter makes a new URL anyway. */
        url_aggregator n;
        bool r = shared_->with_hostname(v, n);
        if (n.has_handle()) {
          src_ = std::move(n);
          shared_.reset();
        }
        if (!r) return false;
      } else if (!src_.set_hostname(v)) {
        return false;
      }
      const url_aggregator& b = base();
      is_valid = b.is_valid;
      host_type = b.host_type;
      if (b.has_hostname()) {
        std::string_view h = b.get_hostname();
        if (host) {
          host->assign(h);
        } else {
          host.emplace(h);
        }
      } else {
        host = std::nullopt;
      }
      return true;
    }
    return edit([&](url_aggregator& u) { return u.set_hostname(v); });
  }
  bool set_protocol(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_protocol(v); });
  }
  bool set_username(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_username(v); });
  }
  bool set_password(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_password(v); });
  }
  bool set_port(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_port(v); });
  }
  bool set_pathname(std::string_view v) {
    return edit([&](url_aggregator& u) { return u.set_pathname(v); });
  }
  void set_search(std::string_view v) {
    edit([&](url_aggregator& u) { u.set_search(v); return true; });
  }
  void set_hash(std::string_view v) {
    edit([&](url_aggregator& u) { u.set_hash(v); return true; });
  }
  void clear_search() { query = std::nullopt; }
  void clear_pathname() { path.clear(); }

  /* Fills the fields from a parsed URL and keeps it for later edits. */
  void adopt(url_aggregator&& u) {
    load(u);
    src_ = std::move(u);
    shared_.reset();
  }

  /* Moves the parsed URL into shared, read-only storage, so that copies of
   * this url share it instead of copying it; the first edit that needs its
   * own copy makes one. */
  void share_src() {
    if (src_.has_handle()) {
      shared_ = std::make_shared<const url_aggregator>(std::move(src_));
      src_ = url_aggregator();
    }
  }

  /* Fills the fields from a parsed URL. */
  void load(const url_aggregator& u) {
    is_valid = u.is_valid;
    has_opaque_path = u.has_opaque_path;
    host_type = u.host_type;
    type = u.type;
    std::string_view proto = u.get_protocol();
    scheme_ = std::string(proto.substr(0, proto.empty() ? 0 : proto.size() - 1));
    username = std::string(u.get_username());
    password = std::string(u.get_password());
    if (u.has_hostname()) {
      host = std::string(u.get_hostname());
    } else {
      host = std::nullopt;
    }
    std::string_view p = u.get_port();
    if (p.empty()) {
      port = std::nullopt;
    } else {
      port = uint16_t(std::stoul(std::string(p)));
    }
    path = std::string(u.get_pathname());
    std::string_view s = u.get_search();
    if (u.has_search()) {
      query = std::string(s.empty() ? s : s.substr(1));
    } else {
      query = std::nullopt;
    }
    std::string_view h = u.get_hash();
    if (u.has_hash()) {
      hash = std::string(h.empty() ? h : h.substr(1));
    } else {
      hash = std::nullopt;
    }
  }

 private:
  /* Reparses the current fields, runs f on the result and returns it. */
  template <class F>
  url_aggregator with(F f) const {
    std::string href = get_href();
    url_aggregator u =
        url_aggregator::from_handle(vurl_parse(href.data(), href.size()));
    f(u);
    return u;
  }
  template <class F>
  bool edit(F f) {
    /* Fast path: the fields are still the ones loaded from src_, so src_ is
     * what reparsing get_href() would give. Edit it in place. If f fails it
     * may leave src_ changed; the fields are not, so the next same_as check
     * fails and that edit reparses. */
    if (same_as(base())) {
      url_aggregator& u = own();
      bool r = f(u);
      if (r) load(u);
      return r;
    }
    bool r = false;
    url_aggregator u = with([&](url_aggregator& a) {
      r = a.is_valid && f(a);
      return r;
    });
    if (r) {
      load(u);
      src_ = std::move(u);
      shared_.reset();
    }
    return r;
  }

  /* The parsed URL the fields were last loaded from. */
  const url_aggregator& base() const noexcept {
    return !src_.has_handle() && shared_ ? *shared_ : src_;
  }
  /* The same, as this url's own copy. */
  url_aggregator& own() {
    if (!src_.has_handle() && shared_) src_ = *shared_;
    shared_.reset();
    return src_;
  }

  /* Whether the fields are exactly what load(u) would set. */
  bool same_as(const url_aggregator& u) const noexcept {
    if (!u.has_handle() || !u.is_valid || is_valid != u.is_valid ||
        has_opaque_path != u.has_opaque_path || host_type != u.host_type ||
        type != u.type) {
      return false;
    }
    std::string_view proto = u.get_protocol();
    if (std::string_view(scheme_) !=
        proto.substr(0, proto.empty() ? 0 : proto.size() - 1)) {
      return false;
    }
    if (std::string_view(username) != u.get_username() ||
        std::string_view(password) != u.get_password() ||
        std::string_view(path) != u.get_pathname()) {
      return false;
    }
    if (u.has_hostname() != host.has_value() ||
        (host && std::string_view(*host) != u.get_hostname())) {
      return false;
    }
    std::string_view p = u.get_port();
    if (p.empty() == port.has_value() ||
        (port && std::to_string(*port) != p)) {
      return false;
    }
    std::string_view q = u.get_search();
    if (u.has_search() != query.has_value() ||
        (query && std::string_view(*query) != (q.empty() ? q : q.substr(1)))) {
      return false;
    }
    std::string_view h = u.get_hash();
    if (u.has_hash() != hash.has_value() ||
        (hash && std::string_view(*hash) != (h.empty() ? h : h.substr(1)))) {
      return false;
    }
    return true;
  }

  std::string scheme_{};
  /* The parsed URL the fields were last loaded from (may be invalid), or
   * no handle while shared_ holds it. */
  url_aggregator src_{};
  std::shared_ptr<const url_aggregator> shared_{};
};

template <class result_type = ada::url_aggregator>
result<result_type> parse(std::string_view input,
                          const result_type* base_url = nullptr);

template <>
inline result<url_aggregator> parse<url_aggregator>(
    std::string_view input, const url_aggregator* base_url) {
  vurl_url h;
  if (base_url) {
    std::string_view b = base_url->get_href();
    h = vurl_parse_with_base(input.data(), input.size(), b.data(), b.size());
  } else {
    h = vurl_parse(input.data(), input.size());
  }
  url_aggregator u = url_aggregator::from_handle(h);
  if (!u.is_valid) return errors::type_error;
  return u;
}

namespace detail {
/* The last short input parse<url> saw without a base, and its result.
 * Node parses the same input many times over: domainToASCII and
 * domainToUnicode parse "ws://x" on every call. */
struct parse_memo {
  std::string input;
  std::optional<url> result;
};
inline parse_memo& memo() {
  static thread_local parse_memo m;
  return m;
}
constexpr size_t memo_max = 64;
}  // namespace detail

template <>
inline result<url> parse<url>(std::string_view input, const url* base_url) {
  if (!base_url && input.size() <= detail::memo_max) {
    detail::parse_memo& m = detail::memo();
    if (m.result && m.input == input) return *m.result;
  }
  result<url_aggregator> a = [&] {
    if (!base_url) return parse<url_aggregator>(input);
    std::string b = base_url->get_href();
    vurl_url h =
        vurl_parse_with_base(input.data(), input.size(), b.data(), b.size());
    url_aggregator u = url_aggregator::from_handle(h);
    if (!u.is_valid) return result<url_aggregator>(errors::type_error);
    return result<url_aggregator>(std::move(u));
  }();
  if (!a) return errors::type_error;
  url u;
  u.adopt(std::move(*a));
  if (!base_url && input.size() <= detail::memo_max) {
    detail::parse_memo& m = detail::memo();
    m.input.assign(input);
    m.result = u;
    m.result->share_src();
  }
  return u;
}

inline bool can_parse(std::string_view input,
                      const std::string_view* base_input = nullptr) {
  if (base_input) {
    return vurl_can_parse_with_base(input.data(), input.size(),
                                    base_input->data(), base_input->size());
  }
  return vurl_can_parse(input.data(), input.size());
}

namespace idna {
inline std::string to_ascii(std::string_view input) {
  /* As in ada 4 and the URL Standard's "domain to ASCII": an ASCII domain
   * is lowercased, whatever its "xn--" labels hold. vurl's URL parser
   * treats an ASCII host the same way. */
  if (input.size() > 16384) return {};  /* ada's limit */
  bool ascii = true;
  for (char c : input) ascii = ascii && uint8_t(c) < 0x80;
  if (ascii) {
    std::string out(input);
    for (char& c : out) if (c >= 'A' && c <= 'Z') c = char(c + 32);
    return out;
  }
  return detail::take(vurl_idna_to_ascii(input.data(), input.size()));
}
inline std::string to_unicode(std::string_view input) {
  /* Only "xn--" labels change. */
  if (input.find("xn--") == std::string_view::npos) return std::string(input);
  return detail::take(vurl_idna_to_unicode(input.data(), input.size()));
}
}  // namespace idna

namespace unicode {
inline unsigned hex_value(char c) {
  if (c >= '0' && c <= '9') return unsigned(c - '0');
  if (c >= 'a' && c <= 'f') return unsigned(c - 'a' + 10);
  if (c >= 'A' && c <= 'F') return unsigned(c - 'A' + 10);
  return 16;
}
/* The URL Standard's percent-decode. first_percent is the index of the
 * first '%' in input, or npos. */
inline std::string percent_decode(std::string_view input,
                                  size_t first_percent) {
  if (first_percent == std::string_view::npos) return std::string(input);
  std::string out(input.substr(0, first_percent));
  out.reserve(input.size());
  for (size_t i = first_percent; i < input.size(); i++) {
    unsigned hi, lo;
    if (input[i] == '%' && i + 2 < input.size() &&
        (hi = hex_value(input[i + 1])) < 16 &&
        (lo = hex_value(input[i + 2])) < 16) {
      out += char(hi * 16 + lo);
      i += 2;
    } else {
      out += input[i];
    }
  }
  return out;
}
}  // namespace unicode

/* "file://" followed by a file path, parsed as the path of a file URL.
 * '?' and '#' are percent-encoded first, as ada does by parsing the input
 * as a path only. */
inline std::string href_from_file(std::string_view path) {
  std::string in = "file:///";
  size_t start = !path.empty() && (path[0] == '/' || path[0] == '\\') ? 1 : 0;
  for (size_t i = start; i < path.size(); i++) {
    char c = path[i];
    if (c == '?') {
      in += "%3F";
    } else if (c == '#') {
      in += "%23";
    } else {
      in += c;
    }
  }
  auto u = parse<url_aggregator>(in);
  return u ? std::string(u->get_href()) : std::string("file:///");
}


/* What ada's URLPattern code (ada_url_pattern.h) uses from the rest of ada:
 * character classes and the percent-encode sets of the URL Standard. None of
 * it parses a URL. */
[[noreturn]] inline void unreachable() { __builtin_unreachable(); }

namespace scheme {
inline type get_scheme_type(std::string_view scheme) noexcept {
  if (scheme == "http") return HTTP;
  if (scheme == "https") return HTTPS;
  if (scheme == "ws") return WS;
  if (scheme == "wss") return WSS;
  if (scheme == "ftp") return FTP;
  if (scheme == "file") return FILE;
  return NOT_SPECIAL;
}
inline bool is_special(std::string_view scheme) {
  return get_scheme_type(scheme) != NOT_SPECIAL;
}
inline uint16_t get_special_port(std::string_view scheme) noexcept {
  return get_special_port(get_scheme_type(scheme));
}
}  // namespace scheme

namespace character_sets {
/* One bit per byte value, as in ada. C0 controls and everything above '~'
 * are in every set. */
constexpr std::array<uint8_t, 32> make_set(std::string_view extra) {
  std::array<uint8_t, 32> set{};
  for (unsigned c = 0; c < 256; c++) {
    bool in = c <= 0x1f || c > 0x7e ||
              extra.find(char(c)) != std::string_view::npos;
    if (in) set[c >> 3] |= uint8_t(1 << (c & 7));
  }
  return set;
}
constexpr bool bit_at(const uint8_t set[], uint8_t c) {
  return (set[c >> 3] >> (c & 7)) & 1;
}
inline constexpr std::array<uint8_t, 32> fragment_set = make_set(" \"<>`");
inline constexpr std::array<uint8_t, 32> query_set = make_set(" \"#<>");
inline constexpr std::array<uint8_t, 32> userinfo_set =
    make_set(" \"#<>?^`{}/:;=@[\\]|");
inline constexpr const uint8_t* FRAGMENT_PERCENT_ENCODE = fragment_set.data();
inline constexpr const uint8_t* QUERY_PERCENT_ENCODE = query_set.data();
inline constexpr const uint8_t* USERINFO_PERCENT_ENCODE = userinfo_set.data();
}  // namespace character_sets

namespace unicode {
constexpr bool is_ascii_digit(char c) noexcept { return c >= '0' && c <= '9'; }
constexpr bool is_ascii_hex_digit(char c) noexcept {
  return is_ascii_digit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}
constexpr bool is_ascii(char32_t c) noexcept { return c < 0x80; }
/* Lowercases A-Z in place; true when every byte is ASCII. */
constexpr bool to_lower_ascii(char* input, size_t length) noexcept {
  bool ascii = true;
  for (size_t i = 0; i < length; i++) {
    if (uint8_t(input[i]) >= 0x80) ascii = false;
    if (input[i] >= 'A' && input[i] <= 'Z') input[i] = char(input[i] + 32);
  }
  return ascii;
}
inline size_t percent_encode_index(std::string_view input,
                                   const uint8_t character_set[]) {
  size_t i = 0;
  while (i < input.size() &&
         !character_sets::bit_at(character_set, uint8_t(input[i])))
    i++;
  return i;
}
inline std::string percent_encode(std::string_view input,
                                  const uint8_t character_set[],
                                  size_t index = 0) {
  static const char hex[] = "0123456789ABCDEF";
  std::string out(input.substr(0, index));
  for (size_t i = index; i < input.size(); i++) {
    uint8_t c = uint8_t(input[i]);
    if (character_sets::bit_at(character_set, c)) {
      out += '%';
      out += hex[c >> 4];
      out += hex[c & 15];
    } else {
      out += char(c);
    }
  }
  return out;
}
}  // namespace unicode

namespace idna {
inline bool is_ascii(std::string_view view) {
  for (char c : view) if (uint8_t(c) >= 0x80) return false;
  return true;
}
}  // namespace idna

namespace helpers {
inline void remove_ascii_tab_or_newline(std::string& input) {
  std::erase_if(input, [](char c) { return c == '\t' || c == '\n' || c == '\r'; });
}
}  // namespace helpers

namespace checkers {
/* ada's quick test for a host that the URL parser would read as an IPv4
 * address: its last label is a decimal number or 0x and hex digits. The
 * input has no upper-case letters. */
inline bool is_ipv4(std::string_view view) noexcept {
  if (view.ends_with('.')) view.remove_suffix(1);
  if (view.empty()) return false;
  size_t last_dot = view.rfind('.');
  if (last_dot != std::string_view::npos) view.remove_prefix(last_dot + 1);
  if (view.empty()) return false;
  auto all = [](std::string_view v, bool hex) {
    for (char c : v) {
      if (!(unicode::is_ascii_digit(c) || (hex && c >= 'a' && c <= 'f')))
        return false;
    }
    return true;
  };
  if (all(view, false)) return true;
  return view.starts_with("0x") && all(view.substr(2), true);
}
}  // namespace checkers

}  // namespace ada

#include "ada_url_pattern.h"

#endif  // ADA_H
