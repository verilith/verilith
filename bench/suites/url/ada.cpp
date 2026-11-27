// URL suite, native: ada's own C++ API (ada::parse into an
// ada::url_aggregator, which ada recommends and its C API wraps), the
// rival of verilith-url's Rust API (runners/vurl-run). Same cases and check
// value as url.c: parse/FILE parses every URL of FILE, reads href of the
// valid ones. ada::parse returns the URL by value, so nothing is allocated
// per URL beyond its href buffer (the C API allocates each URL as well).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string_view>
#include <vector>
#include "ada.h"
#include "runner.h"

struct Item { std::vector<std::string_view> urls; };

static uint64_t do_parse(void *ctx)
{
    Item *it = (Item *)ctx;
    uint64_t ok = 0, href = 0;
    for (std::string_view u : it->urls) {
        auto r = ada::parse<ada::url_aggregator>(u);
        if (r) {
            ok++;
            href += r->get_href().size();
        }
    }
    return (ok << 32) + href;
}

int main()
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]), len;
        if (l < 5 || strcmp(names[i] + l - 4, ".txt")) continue;
        char p[4096], cname[512];
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        char *text = (char *)vb_read_file(p, &len);
        Item *it = new Item;
        for (char *s = text; s < text + len;) {
            char *e = (char *)memchr(s, '\n', (size_t)(text + len - s));
            if (!e) e = text + len;
            size_t k = (size_t)(e - s);
            if (k && s[k - 1] == '\r') k--;
            if (k) it->urls.emplace_back(s, k);
            s = e + 1;
        }
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "parse/%s", names[i]);
        vb_case(cname, len, do_parse, it);
    }
    return vb_main();
}
