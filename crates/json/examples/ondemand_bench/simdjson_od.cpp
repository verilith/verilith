// simdjson reference for four of the patterns in cases.rs: On Demand and DOM.
// c++ -O3 -mcpu=native -std=c++17 -I$SIMDJSON/singleheader simdjson_od.cpp \
//     $SIMDJSON/singleheader/simdjson.cpp -o simdjson_od && ./simdjson_od DIR [SECONDS]
#include "simdjson.h"
#include <chrono>
#include <cstdio>
#include <cstring>
#include <functional>
#include <string>
using namespace simdjson;
static const int64_t FIND_ID = 505874879103520768;

static uint64_t od_partial(ondemand::document &d) {
  uint64_t a = 0;
  for (ondemand::object t : d.find_field("statuses")) {
    a += std::string_view(t.find_field("created_at")).size();
    a += uint64_t(t.find_field("id"));
    a += std::string_view(t.find_field("text")).size();
    auto r = t.find_field("in_reply_to_status_id");
    if (!r.is_null()) a += uint64_t(r);
    ondemand::object u = t.find_field("user");
    a += uint64_t(u.find_field("id"));
    a += std::string_view(u.find_field("screen_name")).size();
    a += uint64_t(t.find_field("retweet_count"));
    a += uint64_t(t.find_field("favorite_count"));
  }
  return a;
}
static uint64_t dom_partial(dom::element d) {
  uint64_t a = 0;
  for (dom::object t : d["statuses"]) {
    a += std::string_view(t["created_at"]).size();
    a += uint64_t(t["id"]);
    a += std::string_view(t["text"]).size();
    auto r = t["in_reply_to_status_id"];
    if (!r.is_null()) a += uint64_t(r);
    dom::object u = t["user"];
    a += uint64_t(u["id"]);
    a += std::string_view(u["screen_name"]).size();
    a += uint64_t(t["retweet_count"]);
    a += uint64_t(t["favorite_count"]);
  }
  return a;
}
static uint64_t od_find(ondemand::document &d) {
  for (ondemand::object t : d.find_field("statuses"))
    if (int64_t(t.find_field("id")) == FIND_ID) return std::string_view(t.find_field("text")).size();
  return 0;
}
static uint64_t dom_find(dom::element d) {
  for (dom::object t : d["statuses"])
    if (int64_t(t["id"]) == FIND_ID) return std::string_view(t["text"]).size();
  return 0;
}
static uint64_t od_tail(ondemand::document &d) {
  return uint64_t(d.find_field("search_metadata").find_field("count"));
}
static uint64_t dom_tail(dom::element d) { return uint64_t(d["search_metadata"]["count"]); }
static uint64_t od_coords(ondemand::document &d) {
  double a = 0;
  for (ondemand::object f : d.find_field("features"))
    for (ondemand::array ring : f.find_field("geometry").find_field("coordinates"))
      for (ondemand::array pt : ring)
        for (double x : pt) a += x;
  uint64_t b; memcpy(&b, &a, 8); return b;
}
static uint64_t dom_coords(dom::element d) {
  double a = 0;
  for (dom::object f : d["features"])
    for (dom::array ring : f["geometry"]["coordinates"])
      for (dom::array pt : ring)
        for (double x : pt) a += x;
  uint64_t b; memcpy(&b, &a, 8); return b;
}
struct Case { const char *file, *name; uint64_t (*od)(ondemand::document &); uint64_t (*dm)(dom::element); };
int main(int argc, char **argv) {
  double budget = argc > 2 ? atof(argv[2]) : 1.0;
  Case cases[] = {
    {"twitter", "partial_tweets (8 fields per tweet)", od_partial, dom_partial},
    {"twitter", "find one tweet by id (halfway)", od_find, dom_find},
    {"twitter", "one field at the end", od_tail, dom_tail},
    {"canada", "sum every coordinate", od_coords, dom_coords},
  };
  printf("file\tpattern\tsimdjson od us\tsimdjson dom us\tsimdjson stage1 us\tchecksum\n");
  for (auto &c : cases) {
    padded_string json = padded_string::load(std::string(argv[1]) + "/" + c.file + ".json");
    ondemand::parser op; dom::parser dp;
    double best[3] = {1e9, 1e9, 1e9}; uint64_t sum[2] = {0, 0};
    auto t0 = std::chrono::steady_clock::now();
    for (int n = 0; n < 5 || std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < budget; n++)
      for (int i = 0; i < 3; i++) {
        auto t = std::chrono::steady_clock::now();
        if (i == 0) { ondemand::document d = op.iterate(json); sum[0] = c.od(d); }
        else if (i == 1) { dom::element d = dp.parse(json); sum[1] = c.dm(d); }
        // Stage 1 alone: `iterate` builds the structural index and reads nothing.
        else { ondemand::document d = op.iterate(json); (void)d; }
        double e = std::chrono::duration<double>(std::chrono::steady_clock::now() - t).count();
        if (e < best[i]) best[i] = e;
      }
    printf("%s\t%s\t%.1f\t%.1f\t%.1f\t%llx%s\n", c.file, c.name, best[0] * 1e6, best[1] * 1e6, best[2] * 1e6,
           (unsigned long long)sum[0], sum[0] == sum[1] ? "" : " MISMATCH");
  }
}
