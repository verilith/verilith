// Prints what ada's URLPattern returns for each test read from stdin, so the
// output with real ada and with vbind's ada.h can be diffed. Both use ada's
// std::regex provider. Input: the records run.sh writes from WPT's
// urlpatterntestdata.json, one "key<TAB>value" per line with newline, tab
// and backslash escaped, each record closed by "end". Build with
// -DADA_USE_UNSAFE_STD_REGEX_PROVIDER=1.
#include <algorithm>
#include <iostream>
#include <map>
#include <string>
#include <vector>
#include "ada.h"

using provider = ada::url_pattern_regex::std_regex_provider;

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

static std::string oneline(std::string s) {
  for (char& c : s) if (c == '\n' || c == '\t' || c == '\r') c = ' ';
  return s;
}

static void set(ada::url_pattern_init& init, const std::string& field, std::string v) {
  if (field == "protocol") init.protocol = v;
  else if (field == "username") init.username = v;
  else if (field == "password") init.password = v;
  else if (field == "hostname") init.hostname = v;
  else if (field == "port") init.port = v;
  else if (field == "pathname") init.pathname = v;
  else if (field == "search") init.search = v;
  else if (field == "hash") init.hash = v;
  else if (field == "baseURL") init.base_url = v;
}

static void show(const char* name, const ada::url_pattern_component_result& r) {
  std::cout << "  " << name << " [" << oneline(r.input) << "]";
  std::vector<std::string> groups;
  for (auto& [k, v] : r.groups) groups.push_back(k + "=" + (v ? oneline(*v) : "<none>"));
  std::sort(groups.begin(), groups.end());
  for (auto& g : groups) std::cout << " {" << g << "}";
  std::cout << "\n";
}

struct arg {
  bool is_string = false, is_init = false, has_base = false;
  std::string string, base;
  ada::url_pattern_init init;
};

int main() {
  std::string line;
  arg pattern, input;
  bool ignore_case = false, has_input = false;
  // Identifier code points, for the first record only.
  std::cout << "# identifiers\n";
  for (int first = 1; first >= 0; first--) {
    unsigned long sum = 0, count = 0;
    for (char32_t c = 0; c < 0x110000; c++) {
      if (ada::idna::valid_name_code_point(c, first)) { count++; sum = sum * 31 + c; }
    }
    std::cout << "first=" << first << " count=" << count << " sum=" << sum << "\n";
  }
  while (std::getline(std::cin, line)) {
    size_t tab = line.find('\t');
    std::string key = line.substr(0, tab);
    std::string value = tab == std::string::npos ? "" : unescape(line.substr(tab + 1));
    if (key == "#") { std::cout << "# " << line.substr(tab + 1) << "\n"; continue; }
    if (key != "end") {
      arg& a = key[0] == 'p' ? pattern : input;
      if (key[0] == 'i') has_input = true;
      std::string what = key.substr(key.find('.') + 1);
      if (what == "str") { a.is_string = true; a.string = value; }
      else if (what == "base") { a.has_base = true; a.base = value; }
      else if (what == "ignoreCase") ignore_case = true;
      else if (what == "none") {}
      else { a.is_init = true; set(a.init, what.substr(what.find('.') + 1), value); }
      continue;
    }
    {
      ada::url_pattern_options options{.ignore_case = ignore_case};
      std::string_view base = pattern.base;
      ada::url_pattern_input pin;
      if (pattern.is_string) pin = std::string_view(pattern.string);
      else pin = pattern.init;
      auto p = ada::parse_url_pattern<provider>(
          std::move(pin), pattern.has_base ? &base : nullptr, &options);
      if (!p) {
        std::cout << "pattern-error\n";
      } else {
        std::cout << "pattern " << p->get_protocol() << " | " << p->get_username()
                  << " | " << p->get_password() << " | " << p->get_hostname()
                  << " | " << p->get_port() << " | " << p->get_pathname() << " | "
                  << p->get_search() << " | " << p->get_hash()
                  << " | groups=" << p->has_regexp_groups()
                  << " icase=" << p->ignore_case() << "\n";
        if (has_input) {
          std::string_view ibase = input.base;
          ada::url_pattern_input in;
          if (input.is_string) in = std::string_view(input.string);
          else in = input.init;
          auto t = p->test(in, input.has_base ? &ibase : nullptr);
          auto r = p->exec(in, input.has_base ? &ibase : nullptr);
          std::cout << "test " << (t ? (*t ? "1" : "0") : "error") << "\n";
          if (!r) std::cout << "exec-error\n";
          else if (!*r) std::cout << "no-match\n";
          else {
            std::cout << "match\n";
            show("protocol", (*r)->protocol); show("username", (*r)->username);
            show("password", (*r)->password); show("hostname", (*r)->hostname);
            show("port", (*r)->port); show("pathname", (*r)->pathname);
            show("search", (*r)->search); show("hash", (*r)->hash);
          }
        }
      }
    }
    pattern = arg(); input = arg(); ignore_case = false; has_input = false;
  }
}
