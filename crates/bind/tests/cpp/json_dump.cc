// Walks each JSON file given on the command line with simdjson's On-Demand
// API and prints what it reads, so the output with real simdjson and with
// vbind's simdjson.h can be diffed.
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include "simdjson.h"

using namespace simdjson;

static void walk(ondemand::value v, int depth) {
  ondemand::json_type t;
  if (auto e = v.type().get(t)) { std::cout << "type-error " << e << "\n"; return; }
  switch (t) {
    case ondemand::json_type::object: {
      ondemand::object o;
      if (v.get_object().get(o)) { std::cout << "object-error\n"; return; }
      std::cout << "{\n";
      for (auto f : o) {
        std::string_view k;
        ondemand::raw_json_string rk;
        if (f.unescaped_key().get(k)) { std::cout << "key-error\n"; return; }
        std::cout << "key " << k << "\n";
        ondemand::value fv;
        if (f.value().get(fv)) { std::cout << "value-error\n"; return; }
        walk(fv, depth + 1);
      }
      std::cout << "}\n";
      break;
    }
    case ondemand::json_type::array: {
      ondemand::array a;
      if (v.get_array().get(a)) { std::cout << "array-error\n"; return; }
      std::cout << "[\n";
      for (auto e : a) {
        ondemand::value ev;
        if (e.get(ev)) { std::cout << "elem-error\n"; return; }
        walk(ev, depth + 1);
      }
      std::cout << "]\n";
      break;
    }
    case ondemand::json_type::string: {
      std::string s;
      if (v.get_string(s)) { std::cout << "string-error\n"; return; }
      std::cout << "string " << s << "\n";
      break;
    }
    case ondemand::json_type::number: {
      int64_t i; uint64_t u; double d;
      auto ei = v.get_int64().get(i);
      std::cout << "number";
      if (!ei) std::cout << " i64=" << i;
      if (!v.get_uint64().get(u)) std::cout << " u64=" << u;
      if (!v.get_double().get(d)) { char b[64]; snprintf(b, sizeof b, "%.17g", d); std::cout << " f64=" << b; }
      std::cout << "\n";
      break;
    }
    case ondemand::json_type::boolean: {
      bool b;
      if (v.get_bool().get(b)) { std::cout << "bool-error\n"; return; }
      std::cout << (b ? "true\n" : "false\n");
      break;
    }
    case ondemand::json_type::null: std::cout << "null\n"; break;
    default: std::cout << "unknown\n";
  }
}

static void run(ondemand::parser& parser, std::string& text, int mode) {
  ondemand::document doc;
  if (parser.iterate(pad(text)).get(doc)) { std::cout << "iterate-error\n"; return; }
  if (mode == 2) {
    // A full walk of the whole tree.
    ondemand::value rv;
    ondemand::json_type t;
    if (doc.type().get(t)) { std::cout << "type-error\n"; return; }
    if (t != ondemand::json_type::object && t != ondemand::json_type::array) { std::cout << "scalar\n"; return; }
    if (doc.get_value().get(rv)) { std::cout << "value-error\n"; return; }
    walk(rv, 0);
    return;
  }
  ondemand::object root;
  if (auto e = doc.get_object().get(root)) {
    std::cout << "root-not-object " << (e == INCORRECT_TYPE) << "\n";
    return;
  }
  if (mode == 0) {
    // Lookups by name, as Node reads its config files.
    for (const char* k : {"name", "main", "type", "exports", "nodeOptions"}) {
      ondemand::value v;
      auto e = root[k].get(v);
      std::cout << "field " << k << " " << int(e);
      std::string_view s;
      if (!e && !v.get_string().get(s)) std::cout << " " << s;
      std::cout << "\n";
    }
    return;
  }
  // One pass in document order, as Node reads package.json: raw text of
  // containers, values of scalars.
  for (auto fld : root) {
    ondemand::raw_json_string rk;
    ondemand::value v;
    if (fld.key().get(rk) || fld.value().get(v)) { std::cout << "field-error\n"; break; }
    ondemand::json_type t;
    if (v.type().get(t)) { std::cout << "type-error\n"; break; }
    if (t == ondemand::json_type::object || t == ondemand::json_type::array) {
      std::string_view r;
      if (v.raw_json().get(r)) { std::cout << "raw-error\n"; break; }
      std::cout << "raw " << r << "\n";
    } else {
      walk(v, 1);
    }
  }
}

int main(int argc, char** argv) {
  ondemand::parser parser;
  for (int i = 1; i < argc; i++) {
    std::ifstream f(argv[i], std::ios::binary);
    std::stringstream ss;
    ss << f.rdbuf();
    std::string text = ss.str();
    for (int mode = 0; mode < 3; mode++) {
      std::cout << "# " << argv[i] << " mode " << mode << "\n";
      run(parser, text, mode);
    }
  }
}
