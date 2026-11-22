// JSON, simdjson side of the native comparison with vjson (runners/vjson-run):
// parse with a reused dom::parser, then read every value (every number as a
// double, every string and key's length). This is vjson's like-for-like
// benchmark (vjson/bench/simdjson_bench.cpp), in the vbench protocol.
//
// Cases read/FILE for every *.json in $VBENCH_DATA.
// check = string and key bytes * 1000003 + numbers.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include "simdjson.h"
#include "runner.h"
using namespace simdjson;

struct Acc { double sum = 0; uint64_t bytes = 0, nums = 0; };

static void walk(dom::element e, Acc &a)
{
    switch (e.type()) {
    case dom::element_type::ARRAY:
        for (auto c : dom::array(e)) walk(c, a);
        break;
    case dom::element_type::OBJECT:
        for (auto f : dom::object(e)) { a.bytes += f.key.size(); walk(f.value, a); }
        break;
    case dom::element_type::INT64:
    case dom::element_type::UINT64:
    case dom::element_type::DOUBLE:
        a.sum += double(e.get_double().value_unsafe());
        a.nums++;
        break;
    case dom::element_type::STRING: a.bytes += std::string_view(e).size(); break;
    default: break;
    }
}

struct Item { padded_string doc; dom::parser parser; };

static uint64_t do_read(void *ctx)
{
    Item *it = (Item *)ctx;
    auto d = it->parser.parse(it->doc);
    if (d.error()) abort();
    Acc a;
    walk(d.value_unsafe(), a);
    return a.bytes * 1000003u + a.nums;
}

int main()
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 6 || strcmp(names[i] + l - 5, ".json")) continue;
        std::string p = std::string(dir) + "/" + names[i];
        Item *it = new Item;
        if (padded_string::load(p).get(it->doc)) { fprintf(stderr, "cannot load %s\n", p.c_str()); return 1; }
        do_read(it);
        names[i][l - 5] = 0;
        std::string cname = std::string("read/") + names[i];
        vb_case(cname.c_str(), it->doc.size(), do_read, it);
    }
    return vb_main();
}
