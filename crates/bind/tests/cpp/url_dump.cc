// Prints what ada's C++ API returns for each input, so the output with
// real ada and with vbind's ada.h can be diffed. Input: lines of
// "input<TAB>base" (base optional), with \n, \t and \\ escaped.
#include <cstdio>
#include <iostream>
#include <string>
#include "ada.h"

static std::string oneline(std::string s) {
  for (char& c : s) if (c == '\n' || c == '\t') c = ' ';
  return s;
}

static std::string unescape(const std::string& s) {
  std::string o;
  for (size_t i = 0; i < s.size(); i++) {
    if (s[i] == '\\' && i + 1 < s.size()) {
      char c = s[++i];
      o += c == 'n' ? '\n' : c == 't' ? '\t' : c == 'r' ? '\r' : c;
    } else {
      o += s[i];
    }
  }
  return o;
}

template <class U>
static void dump(const char* tag, U& u) {
  std::cout << tag << " " << u.get_href() << " | " << u.get_origin() << " | "
            << u.get_protocol() << " | " << u.get_username() << " | "
            << u.get_password() << " | " << u.get_host() << " | "
            << u.get_hostname() << " | " << u.get_port() << " | "
            << u.get_pathname() << " | " << u.get_search() << " | "
            << u.get_hash() << " | type=" << int(u.type)
            << " creds=" << u.has_credentials() << " host=" << u.has_hostname()
            << " port=" << u.has_port() << " search=" << u.has_search()
            << " hash=" << u.has_hash() << "\n";
}

int main() {
  std::string line;
  const char* setter_values[] = {"", "x", "example.com:81", "8080", "/a/../b", "?q=1", "#f",
                                 "user", "p@ss", "ftp", "[::1]", "%zz"};
  while (std::getline(std::cin, line)) {
    size_t tab = line.find('\t');
    std::string input = unescape(line.substr(0, tab));
    std::string base = tab == std::string::npos ? "" : unescape(line.substr(tab + 1));
    std::cout << "# " << line << "\n";
    ada::result<ada::url_aggregator> u;
    if (tab != std::string::npos) {
      auto b = ada::parse<ada::url_aggregator>(base);
      if (!b) { std::cout << "bad base\n"; continue; }
      u = ada::parse<ada::url_aggregator>(input, &*b);
      std::string_view bv = base;
      std::cout << "can_parse " << ada::can_parse(input, &bv) << "\n";
    } else {
      u = ada::parse<ada::url_aggregator>(input);
      std::cout << "can_parse " << ada::can_parse(input) << "\n";
    }
    if (!u) { std::cout << "invalid\n"; continue; }
    dump("agg", *u);
    std::cout << "components " << oneline(u->get_components().to_string()) << "\n";
    auto plain = ada::parse<ada::url>(u->get_href());
    if (plain) dump("url", *plain);
    for (const char* v : setter_values) {
      std::string_view sv = v;
#define TRY(name)                                                    \
      {                                                              \
        auto c = *u;                                                 \
        bool r = c.name(sv);                                         \
        std::cout << #name << "(" << v << ")=" << r << " " << c.get_href() << " " \
                  << oneline(c.get_components().to_string()) << "\n"; \
      }
      TRY(set_href) TRY(set_host) TRY(set_hostname) TRY(set_protocol)
      TRY(set_username) TRY(set_password) TRY(set_port) TRY(set_pathname)
      { auto c = *u; c.set_search(sv); std::cout << "set_search " << c.get_href() << "\n"; }
      { auto c = *u; c.set_hash(sv); std::cout << "set_hash " << c.get_href() << "\n"; }
    }
    // ada::url setters: straight after parsing, after a field edit, and
    // after an earlier setter (failed or not).
    if (plain) {
      for (const char* v : setter_values) {
        std::string_view sv = v;
#define UTRY(name)                                                   \
        {                                                            \
          auto c = *plain;                                           \
          bool r = c.name(sv);                                       \
          std::cout << "url." #name "(" << v << ")=" << r << " " << c.get_href() << "\n"; \
          c.hash = "h";                                              \
          r = c.name(sv);                                            \
          std::cout << "  edited " << r << " " << c.get_href() << "\n"; \
          r = c.set_port("1") && c.name(sv);                         \
          std::cout << "  again " << r << " " << c.get_href() << " " \
                    << oneline(c.get_components().to_string()) << "\n"; \
        }
        UTRY(set_href) UTRY(set_host) UTRY(set_hostname) UTRY(set_protocol)
        UTRY(set_username) UTRY(set_password) UTRY(set_port) UTRY(set_pathname)
      }
    }
    // ada::url field edits, as Node's url.format does.
    if (plain) {
      auto f = *plain;
      f.hash = std::nullopt; f.query = std::nullopt; f.username = ""; f.password = "";
      std::cout << "format " << f.get_href() << "\n";
      if (f.has_hostname()) {
        f.host = ada::idna::to_unicode(f.get_hostname());
        std::cout << "format_unicode " << f.get_href() << "\n";
      }
    }
  }
  for (const char* h : {"xn--bcher-kva.de", "BÜCHER.de", "a.xn--zz.b", "xn--nxasmq6b.com", "", "a..b"}) {
    std::cout << "idna " << ada::idna::to_ascii(h) << " | " << ada::idna::to_unicode(h) << "\n";
  }
  for (const char* p : {"/tmp/a b", "/x?y#z%", "relative/path", "//double", "\\back", "/a/../b", ""}) {
    std::cout << "href_from_file " << ada::href_from_file(p) << "\n";
  }
  for (const char* p : {"a%20b", "%", "%4", "%41%42", "%zz%2f"}) {
    std::string_view s = p;
    std::cout << "percent_decode " << ada::unicode::percent_decode(s, s.find('%')) << "\n";
  }
}
