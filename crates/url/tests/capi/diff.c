// Differential test: runs each case through ada's C API (ada_*) and vurl's
// (vurl_*, the same functions) and reports every difference.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "ada_c.h"
#include "vurl_c.h"

typedef struct { const char* p; size_t n; } str;

static unsigned long ndiff, ncase;
static const char* ctx;
static unsigned long limit = 200;

static void show(str s) {
  putchar('"');
  for (size_t i = 0; i < s.n; i++) {
    unsigned char c = s.p[i];
    if (c >= 32 && c < 127 && c != '"' && c != '\\') putchar(c);
    else printf("\\x%02x", c);
  }
  putchar('"');
}

static void differ(const char* what, str a, str v) {
  ndiff++;
  if (ndiff > limit) return;
  printf("%s: %s: ada ", ctx, what);
  show(a);
  printf(" vurl ");
  show(v);
  printf("\n");
}

// Empty strings compare equal whatever their pointers (ada returns a null
// pointer for some empty components of valid URLs).
static void cmp_s(const char* what, ada_string a, ada_string v) {
  if (a.length == 0 && v.length == 0) return;
  if ((a.data == NULL) != (v.data == NULL) || a.length != v.length ||
      (a.length && memcmp(a.data, v.data, a.length)))
    differ(what, (str){a.data ? a.data : "(null)", a.data ? a.length : 6},
           (str){v.data ? v.data : "(null)", v.data ? v.length : 6});
}

static void cmp_o(const char* what, ada_owned_string a, ada_owned_string v) {
  cmp_s(what, (ada_string){a.data, a.length}, (ada_string){v.data, v.length});
  ada_free_owned_string(a);
  vurl_free_owned_string(v);
}

static void cmp_i(const char* what, long a, long v) {
  if (a != v) {
    char x[32], y[32];
    snprintf(x, 32, "%ld", a);
    snprintf(y, 32, "%ld", v);
    differ(what, (str){x, strlen(x)}, (str){y, strlen(y)});
  }
}

static void compare(ada_url a, ada_url v) {
  cmp_i("valid", ada_is_valid(a), vurl_is_valid(v));
  if (!ada_is_valid(a) || !vurl_is_valid(v)) {
    cmp_i("invalid href is null", ada_get_href(a).data == NULL, vurl_get_href(v).data == NULL);
    cmp_i("invalid components are null", ada_get_components(a) == NULL, vurl_get_components(v) == NULL);
    return;
  }
#define S(f) cmp_s(#f, ada_get_##f(a), vurl_get_##f(v))
  S(href); S(username); S(password); S(port); S(hash); S(host); S(hostname);
  S(pathname); S(search); S(protocol);
  cmp_o("origin", ada_get_origin(a), vurl_get_origin(v));
  // After a setter, ada can keep a stale host type (setting the host of
  // "file://1.2.3.4/" to "p" still reports IPv4), so compare with the type
  // ada gives the same href freshly parsed.
  ada_string h = ada_get_href(a);
  ada_url fresh = ada_parse(h.data, h.length);
  cmp_i("host_type", ada_get_host_type(fresh), vurl_get_host_type(v));
  ada_free(fresh);
  cmp_i("scheme_type", ada_get_scheme_type(a), vurl_get_scheme_type(v));
#define B(f) cmp_i(#f, ada_##f(a), vurl_##f(v))
  B(has_credentials); B(has_empty_hostname); B(has_hostname);
  B(has_non_empty_username); B(has_non_empty_password); B(has_port);
  B(has_password); B(has_hash); B(has_search);
  const ada_url_components* ca = ada_get_components(a);
  const ada_url_components* cv = vurl_get_components(v);
#define C(f) cmp_i("components." #f, ca->f, cv->f)
  C(protocol_end); C(username_end); C(host_start); C(host_end); C(port);
  C(pathname_start); C(search_start); C(hash_start);
}

static void params(str q) {
  ada_url_search_params a = ada_parse_search_params(q.p, q.n);
  ada_url_search_params v = vurl_parse_search_params(q.p, q.n);
  cmp_i("params.size", ada_search_params_size(a), vurl_search_params_size(v));
  cmp_o("params.to_string", ada_search_params_to_string(a), vurl_search_params_to_string(v));
  ada_url_search_params_entries_iter ea = ada_search_params_get_entries(a);
  ada_url_search_params_entries_iter ev = vurl_search_params_get_entries(v);
  while (ada_search_params_entries_iter_has_next(ea) || vurl_search_params_entries_iter_has_next(ev)) {
    cmp_i("params.has_next", ada_search_params_entries_iter_has_next(ea), vurl_search_params_entries_iter_has_next(ev));
    ada_string_pair pa = ada_search_params_entries_iter_next(ea);
    ada_string_pair pv = vurl_search_params_entries_iter_next(ev);
    cmp_s("params.key", pa.key, pv.key);
    cmp_s("params.value", pa.value, pv.value);
    cmp_s("params.get", ada_search_params_get(a, pa.key.data, pa.key.length),
          vurl_search_params_get(v, pv.key.data, pv.key.length));
    ada_strings sa = ada_search_params_get_all(a, pa.key.data, pa.key.length);
    ada_strings sv = vurl_search_params_get_all(v, pv.key.data, pv.key.length);
    cmp_i("params.get_all", ada_strings_size(sa), vurl_strings_size(sv));
    for (size_t i = 0; i < ada_strings_size(sa); i++) cmp_s("params.get_all[i]", ada_strings_get(sa, i), vurl_strings_get(sv, i));
    ada_free_strings(sa);
    vurl_free_strings(sv);
  }
  ada_free_search_params_entries_iter(ea);
  vurl_free_search_params_entries_iter(ev);
  ada_search_params_sort(a);
  vurl_search_params_sort(v);
  cmp_o("params.sorted", ada_search_params_to_string(a), vurl_search_params_to_string(v));
  ada_search_params_append(a, "a", 1, "x y", 3);
  vurl_search_params_append(v, "a", 1, "x y", 3);
  ada_search_params_set(a, "a", 1, "s", 1);
  vurl_search_params_set(v, "a", 1, "s", 1);
  cmp_o("params.set", ada_search_params_to_string(a), vurl_search_params_to_string(v));
  cmp_i("params.has", ada_search_params_has(a, "b", 1), vurl_search_params_has(v, "b", 1));
  cmp_i("params.has_value", ada_search_params_has_value(a, "a", 1, "s", 1), vurl_search_params_has_value(v, "a", 1, "s", 1));
  ada_search_params_remove_value(a, "a", 1, "s", 1);
  vurl_search_params_remove_value(v, "a", 1, "s", 1);
  ada_search_params_remove(a, "z", 1);
  vurl_search_params_remove(v, "z", 1);
  cmp_o("params.remove", ada_search_params_to_string(a), vurl_search_params_to_string(v));
  ada_search_params_reset(a, "?k=1", 4);
  vurl_search_params_reset(v, "?k=1", 4);
  cmp_o("params.reset", ada_search_params_to_string(a), vurl_search_params_to_string(v));
  ada_free_search_params(a);
  vurl_free_search_params(v);
}

static int field(const char** p, const char* end, str* s) {
  if (*p >= end || **p == '\n') return 0;
  size_t n = strtoul(*p, (char**)p, 10);
  (*p)++;
  s->p = *p;
  s->n = n;
  *p += n;
  return 1;
}

int main(int argc, char** argv) {
  if (argc > 2) limit = strtoul(argv[2], NULL, 10);
  FILE* f = fopen(argv[1], "rb");
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  char* buf = malloc(len);
  if (fread(buf, 1, len, f) != (size_t)len) return 2;
  const char *p = buf, *end = buf + len;
  char name[64];
  while (p < end) {
    char tag = *p++;
    str s[3];
    int k = 0;
    while (k < 3 && field(&p, end, &s[k])) k++;
    p++;
    ncase++;
    ctx = name;
    if (tag == 'P') {
      snprintf(name, sizeof name, "parse #%lu", ncase);
      ada_url a = k == 2 ? ada_parse_with_base(s[0].p, s[0].n, s[1].p, s[1].n) : ada_parse(s[0].p, s[0].n);
      ada_url v = k == 2 ? vurl_parse_with_base(s[0].p, s[0].n, s[1].p, s[1].n) : vurl_parse(s[0].p, s[0].n);
      unsigned long before = ndiff;
      compare(a, v);
      cmp_i("can_parse", k == 2 ? ada_can_parse_with_base(s[0].p, s[0].n, s[1].p, s[1].n) : ada_can_parse(s[0].p, s[0].n),
            k == 2 ? vurl_can_parse_with_base(s[0].p, s[0].n, s[1].p, s[1].n) : vurl_can_parse(s[0].p, s[0].n));
      ada_url ac = ada_copy(a), vc = vurl_copy(v);
      compare(ac, vc);
      if (ndiff != before && ndiff <= limit) { printf("  input "); show(s[0]); printf("\n"); }
      ada_free(a); vurl_free(v); ada_free(ac); vurl_free(vc);
    } else if (tag == 'S') {
      snprintf(name, sizeof name, "set %.*s #%lu", (int)s[1].n, s[1].p, ncase);
      ada_url a = ada_parse(s[0].p, s[0].n);
      ada_url v = vurl_parse(s[0].p, s[0].n);
      long ra = -1, rv = -1;
#define SET(X) if (s[1].n == strlen(#X) && !memcmp(s[1].p, #X, s[1].n)) { ra = ada_set_##X(a, s[2].p, s[2].n); rv = vurl_set_##X(v, s[2].p, s[2].n); }
#define SETV(X) if (s[1].n == strlen(#X) && !memcmp(s[1].p, #X, s[1].n)) { ada_set_##X(a, s[2].p, s[2].n); vurl_set_##X(v, s[2].p, s[2].n); }
      SET(href) SET(protocol) SET(username) SET(password) SET(host) SET(hostname) SET(port) SET(pathname)
      SETV(search) SETV(hash)
      unsigned long before = ndiff;
      cmp_i("result", ra, rv);
      compare(a, v);
      if (ndiff != before && ndiff <= limit) {
        printf("  href "); show(s[0]); printf(" value "); show(s[2]); printf("\n");
      }
      ada_clear_port(a); vurl_clear_port(v);
      ada_clear_search(a); vurl_clear_search(v);
      ada_clear_hash(a); vurl_clear_hash(v);
      compare(a, v);
      ada_free(a); vurl_free(v);
    } else if (tag == 'Q') {
      snprintf(name, sizeof name, "params #%lu", ncase);
      params(s[0]);
    }
  }
  // ada's standalone to_ascii accepts some labels that UTS #46 rejects (it
  // turns "XN--A.b" into "xn--a.b"; vurl returns "", the error result), so
  // that input is checked with to_unicode only.
  const char* d[] = {"example.com", "xn--nxasmq6b.com", "\xce\xb2\xcf\x8c\xce\xbb\xce\xbf\xcf\x82.com", "a..b",
                     "\xef\xbf\xbd", "Fa\xc3\x9f.de", "\xe2\x84\xab.com", "XN--A.b"};
  for (int i = 0; i < 8; i++) {
    ctx = d[i];
    if (i < 7) cmp_o("idna_to_ascii", ada_idna_to_ascii(d[i], strlen(d[i])), vurl_idna_to_ascii(d[i], strlen(d[i])));
    cmp_o("idna_to_unicode", ada_idna_to_unicode(d[i], strlen(d[i])), vurl_idna_to_unicode(d[i], strlen(d[i])));
  }
  // The maximum input length.
  ada_set_max_input_length(40);
  vurl_set_max_input_length(40);
  cmp_i("get_max_input_length", ada_get_max_input_length(), vurl_get_max_input_length());
  const char* longs[] = {"https://example.com/0123456789012345678", "https://example.com/01234567890123456789",
                         "https://example.com/0123456789012345 6", "https://EXAMPLE.com/%7e01234567890123456"};
  for (int i = 0; i < 4; i++) {
    ctx = longs[i];
    ada_url a = ada_parse(longs[i], strlen(longs[i]));
    ada_url v = vurl_parse(longs[i], strlen(longs[i]));
    compare(a, v);
    const char* vals[] = {"abcdefgh", "a b", "x"};
    for (int j = 0; j < 3; j++) {
      cmp_i("long set_pathname", ada_set_pathname(a, vals[j], strlen(vals[j])), vurl_set_pathname(v, vals[j], strlen(vals[j])));
      compare(a, v);
      cmp_i("long set_username", ada_set_username(a, vals[j], strlen(vals[j])), vurl_set_username(v, vals[j], strlen(vals[j])));
      compare(a, v);
      ada_set_search(a, vals[j], strlen(vals[j]));
      vurl_set_search(v, vals[j], strlen(vals[j]));
      compare(a, v);
    }
    ada_free(a);
    vurl_free(v);
  }
  ada_set_max_input_length(0xffffffff);
  vurl_set_max_input_length(0xffffffff);
  free(buf);
  printf("%lu cases, %lu differences\n", ncase, ndiff);
  return ndiff != 0;
}
