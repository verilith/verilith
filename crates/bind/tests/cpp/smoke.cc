#include <cassert>
#include <cstdio>
#include <string>
#include "ada.h"
#include "simdjson.h"

int main() {
  auto u = ada::parse<ada::url_aggregator>("https://user:pw@EXAMPLE.com:8080/a/../b?q=1#h");
  assert(u);
  printf("%s\n", std::string(u->get_href()).c_str());
  assert(u->get_href() == "https://user:pw@example.com:8080/b?q=1#h");
  assert(u->type == ada::scheme::HTTPS);
  const auto& c = u->get_components();
  printf("%s\n", c.to_string().c_str());
  assert(u->set_hostname("foo.org"));
  assert(u->get_host() == "foo.org:8080");
  auto base = ada::parse("http://a/b/c");
  auto rel = ada::parse("../d", &base.value());
  assert(rel && rel->get_href() == "http://a/d");
  assert(!ada::parse("http://[::1"));
  auto x = ada::parse<ada::url>("https://u:p@h.com/p?q#f");
  x->hash = std::nullopt; x->query = std::nullopt; x->username = ""; x->password = "";
  assert(x->get_href() == "https://h.com/p");
  auto w = ada::parse<ada::url>("ws://x");
  assert(w->set_hostname("BÜCHER.de"));
  printf("%s\n", w->get_hostname().c_str());
  assert(ada::href_from_file("/tmp/a b?#%") == "file:///tmp/a%20b%3F%23%");
  assert(ada::idna::to_unicode("xn--bcher-kva.de") == "bücher.de");
  assert(ada::unicode::percent_decode("a%20b%zz", 1) == "a b%zz");
  std::string_view bs = "http://x/";
  assert(ada::can_parse("y", &bs) && !ada::can_parse("y"));

  simdjson::ondemand::parser p;
  std::string json = R"({"name":"a\"b","n":-12,"u":18446744073709551615,"d":1.5,"ok":true,
    "exports":{"./x":["a",{"b":null}]},"arr":[1,"s",[2]], "kA":3})";
  simdjson::ondemand::document doc;
  assert(!p.iterate(simdjson::pad(json)).get(doc));
  simdjson::ondemand::object o;
  assert(!doc.get_object().get(o));
  int fields = 0;
  for (auto f : o) {
    simdjson::ondemand::raw_json_string k;
    simdjson::ondemand::value v;
    assert(!f.key().get(k) && !f.value().get(v));
    std::string_view uk;
    assert(!f.unescaped_key().get(uk));
    fields++;
    if (k == "name") { std::optional<std::string> s; assert(!v.get_string(s)); assert(*s == "a\"b"); }
    if (k == "exports") {
      simdjson::ondemand::json_type t; assert(!v.type().get(t) && t == simdjson::ondemand::json_type::object);
      std::string_view raw; assert(!v.raw_json().get(raw)); printf("raw=%.*s\n", (int)raw.size(), raw.data());
      assert(raw == R"({"./x":["a",{"b":null}]})");
    }
    if (uk == "kA") { int64_t i; assert(!v.get_int64().get(i) && i == 3); }
  }
  assert(fields == 8);
  int64_t n; uint64_t uu; double d; bool b;
  assert(!o["n"].get_int64().get(n) && n == -12);
  assert(!o["u"].get_uint64().get(uu) && uu == 18446744073709551615ull);
  assert(!o["d"].get_double().get(d) && d == 1.5);
  assert(!o["ok"].get_bool().get(b) && b);
  assert(o["missing"].get_object().error() == simdjson::NO_SUCH_FIELD);
  assert(o["n"].get_string().error() == simdjson::INCORRECT_TYPE);
  simdjson::ondemand::array a; assert(!o["arr"].get_array().get(a));
  int cnt = 0; for (auto e : a) { (void)e; cnt++; } assert(cnt == 3);
  std::string bad = "{\"a\":}";
  simdjson::ondemand::document d2;
  auto err = p.iterate(simdjson::pad(bad)).get(d2);
  printf("bad: %s\n", simdjson::error_message(err));
  assert(err);
  std::string arr = "[1]";
  assert(!p.iterate(arr).get(d2));
  assert(d2.get_object().error() == simdjson::INCORRECT_TYPE);
  {
    std::string cfg = R"({"main":"a.js","disableExperimentalSEAWarning":true})";
    simdjson::ondemand::document d3;
    simdjson::ondemand::object o3;
    assert(!p.iterate(simdjson::pad(cfg)).get(d3) && !d3.get_object().get(o3));
    for (auto f : o3) {
      std::string_view k;
      assert(!f.unescaped_key().get(k));
      if (k == "main") {
        std::string main_path;
        assert(!f.value().get_string().get(main_path) && main_path == "a.js");
      }
    }
  }
  {
    // parse<url> remembers its last input: copies of that result must be
    // independent of each other and of the memo.
    auto a = ada::parse<ada::url>("ws://x");
    auto b = ada::parse<ada::url>("ws://x");
    assert(a->set_hostname("aaa.example"));
    assert(b->get_href() == "ws://x/");
    assert(a->get_href() == "ws://aaa.example/");
    assert(!b->set_hostname("bad host:1"));
    assert(b->get_href() == "ws://x/");
    b->set_pathname("/p");
    assert(b->get_href() == "ws://x/p");
    auto c = ada::parse<ada::url>("ws://x");
    assert(c->get_href() == "ws://x/" && c->get_hostname() == "x");
    ada::url d = *c;
    assert(d.set_hostname("d.d") && c->get_hostname() == "x" && d.get_href() == "ws://d.d/");
    c->host = "zz";  // a direct field edit forces the slow path
    assert(c->set_hostname("q.q") && c->get_href() == "ws://q.q/");
    assert(ada::parse<ada::url>("ws://x")->get_components().host_start > 0);
  }
  puts("ok");
}
