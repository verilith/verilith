// simdjson side of the like-for-like benchmark (bench/run.sh). For each
// file prints the best time of: parse only (DOM, parser reused), and parse
// then read every value (every number as a double, every string and key's
// length), which is the work vjson defers until values are read.
#include <chrono>
#include <cstdio>
#include <string>
#include "simdjson.h"
using namespace simdjson;
static std::string slurp(const char* p){FILE*f=fopen(p,"rb");fseek(f,0,SEEK_END);long n=ftell(f);fseek(f,0,SEEK_SET);std::string s(n,0);if(fread(&s[0],1,n,f)!=(size_t)n)exit(9);fclose(f);return s;}
struct Acc { double sum = 0; size_t bytes = 0; };
static void walk(dom::element e, Acc& a) {
  switch (e.type()) {
    case dom::element_type::ARRAY: for (auto c : dom::array(e)) walk(c, a); break;
    case dom::element_type::OBJECT: for (auto f : dom::object(e)) { a.bytes += f.key.size(); walk(f.value, a); } break;
    case dom::element_type::INT64: case dom::element_type::UINT64: case dom::element_type::DOUBLE: a.sum += double(e.get_double()); break;
    case dom::element_type::STRING: a.bytes += std::string_view(e).size(); break;
    default: break;
  }
}
int main(int c, char** v){
  for(int f=1;f<c;f++){
    std::string s=slurp(v[f]); padded_string ps(s);
    dom::parser parser;
    int reps = std::max<size_t>(1, 2000000 / s.size());
    double parse=1e9, read=1e9; Acc keep;
    for(int i=0;i<200;i++){
      auto t=std::chrono::steady_clock::now();
      for(int r=0;r<reps;r++) { auto d = parser.parse(ps); if(d.error()) return 3; }
      auto t2=std::chrono::steady_clock::now();
      for(int r=0;r<reps;r++) { auto d = parser.parse(ps); if(d.error()) return 3; Acc a; walk(d.value(), a); keep.sum += a.sum; keep.bytes += a.bytes; }
      auto t3=std::chrono::steady_clock::now();
      parse=std::min(parse,std::chrono::duration<double>(t2-t).count()/reps);
      read=std::min(read,std::chrono::duration<double>(t3-t2).count()/reps);
    }
    printf("%s %.0f %.0f %zu\n", v[f], s.size()/parse/1e6, s.size()/read/1e6, keep.bytes % 7);
  }
}
