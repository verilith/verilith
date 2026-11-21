// ada and libcurl loops, timed from Rust. Each call parses every URL once
// and returns the total href length of the successes.
#include "ada.h"
#include <cstddef>
#include <cstring>
#include <string_view>

extern "C" {
typedef struct Curl_URL CURLU;
CURLU *curl_url(void);
void curl_url_cleanup(CURLU *);
int curl_url_set(CURLU *, int what, const char *part, unsigned int flags);
int curl_url_get(const CURLU *, int what, char **part, unsigned int flags);
void curl_free(void *);

size_t ada_loop(const char *const *p, const size_t *l, size_t n, size_t *ok) {
  size_t total = 0, good = 0;
  for (size_t i = 0; i < n; i++) {
    auto u = ada::parse<ada::url_aggregator>(std::string_view(p[i], l[i]));
    if (u) {
      good++;
      total += u->get_href().size();
    }
  }
  *ok = good;
  return total;
}

// Inputs must be NUL-terminated for curl.
size_t curl_loop(const char *const *p, size_t n, size_t *ok, int get) {
  size_t total = 0, good = 0;
  CURLU *h = curl_url();
  for (size_t i = 0; i < n; i++) {
    if (curl_url_set(h, 0 /* CURLUPART_URL */, p[i], 0) == 0) {
      good++;
      if (get) {
        char *buf;
        if (curl_url_get(h, 0, &buf, 0) == 0) {
          total += strlen(buf);
          curl_free(buf);
        }
      }
    }
  }
  curl_url_cleanup(h);
  *ok = good;
  return total;
}
}
